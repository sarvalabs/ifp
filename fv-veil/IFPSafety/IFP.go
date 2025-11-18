//------------ handler.go ------------------

package consensus

import (
	"context"
	"time"

	"github.com/pkg/errors"
	"github.com/sarvalabs/go-moi/common"
	"github.com/sarvalabs/go-moi/consensus/types"
	"github.com/sarvalabs/go-moi/network/message"
	"github.com/sarvalabs/go-polo"
)

// Handler is the main event loop for the consensus engine.It listens for the following events
// - Context cancellation
// - NewView ticks
// - Inbound messages
// - Slot closures
func (k *Engine) handler() {
	viewTicker := common.NewViewTicker(time.Unix(int64(k.cfg.GenesisTimestamp), 0),
		uint64(k.pool.ViewTimeOut().Seconds()))

	for {
		select {
		case <-k.ctx.Done():
			// If the context is done, close the view ticker and return
			viewTicker.Done()
			k.logger.Info("Closing Krama engine. Reason: context-closed")

			return
		case viewID := <-viewTicker.C():
			k.metrics.captureCurrentView(viewID)
			k.view.Store(viewID) // When a new view tick is received, update the current view and trigger the view handler.
			k.pool.UpdateCurrentView(viewID)
			k.viewTimeOutDuration.Store(time.Until(time.Now().Add(k.pool.ViewTimeOut())))

			k.handleNewView(k.ctx, viewID)
		case msg := <-k.transport.Messages():
			k.handleConsensusMessage(msg)
		case clusterID := <-k.icsCloseCh:
			// When a slot close event is received, gracefully close the context router, and clean up the slot.
			k.transport.GracefullyCloseContextRouter(clusterID)
			k.slots.CleanupSlot(clusterID)
			k.logger.Debug("Cleaning consensus slot", "cluster-id", clusterID)
		}
	}
}

// handleNewView checks if there are any failed views to handle first. If failed views exist, it processes them.
// Otherwise, it fetches interactions from the pool and creates a new cluster for the interactions.
func (k *Engine) handleNewView(ctx context.Context, viewID uint64) {
	for _, msg := range k.futureMsg {
		k.handleConsensusMessage(msg)
		k.dequeueFutureMsg()
	}

	proposedTS, err := k.safety.GetFailedViewTS()
	if err != nil {
		k.logger.Error("failed to get failed view ts", "error", err)
	}

	for _, ts := range proposedTS {
		if !k.isOperatorEligible(k.selfID, ts.Interactions()) {
			continue
		}

		if err = k.handleFailedView(ts.ConsensusInfo().View, ts); err != nil {
			k.logger.Error("failed to handle old view qc", "error", err)
		}
	}

	for _, batch := range k.pool.ProcessableBatches() {
		clusterID, err := types.GenerateClusterID()
		if err != nil {
			k.logger.Error("failed to create clusterID")

			continue
		}

		ixs := batch.Interactions()

		k.logger.Debug("Handling new ixs for view", "view-id", viewID)

		if !k.isOperatorEligible(k.selfID, ixs) {
			k.logger.Debug("operator not eligible", "view", viewID)

			continue
		} else {
			k.logger.Debug("Operator is eligible", "view", viewID)
		}

		slot, activeCluster, err := k.createICS(ctx, clusterID, ixs, ixs.Locks())
		if err != nil {
			k.logger.Debug("failed to create a slot", "view", viewID, "active-cluster", activeCluster, "err", err)
			k.slots.CleanupSlot(clusterID)

			return
		}

		go k.icsHandler(ctx, clusterID)
		slot.NewICSChan <- clusterID
	}
}

func (k *Engine) handleFailedView(failedView uint64, ts *common.Tesseract) error {
	clusterID, err := types.GenerateClusterID()
	if err != nil {
		k.logger.Error("failed to create clusterID")

		return err
	}

	slot, activeCluster, err := k.createICS(k.ctx, clusterID, ts.Interactions(), ts.ConsensusInfo().AccountLocks)
	if err != nil {
		k.logger.Debug("failed to create a slot", "view", failedView, "active-cluster", activeCluster)
		k.slots.CleanupSlot(clusterID)

		return err
	}

	go k.icsHandler(k.ctx, clusterID)
	slot.NewICSChan <- clusterID

	return nil
}

// handleConsensusMessage processes incoming consensus messages based on their type.
// It supports the following message types:
// - PREPARE
// - PREPARED
// - PROPOSAL
// - VOTEMSG
func (k *Engine) handleConsensusMessage(msg *types.ICSMSG) {
	switch msg.MsgType {
	case message.PREPARE:
		prepare := new(types.Prepare)
		if err := polo.Depolorize(prepare, msg.Payload); err != nil {
			k.logger.Error("failed to depolarize prepare msg", "err", err)

			return
		}

		if err := k.handlePrepare(context.Background(), msg, prepare); err != nil {
			k.logger.Error("failed to handle prepare msg", "err", err, "cluster-id", msg.ClusterID)
		}

	case message.PREPARED:
		prepared := new(types.Prepared)
		if err := polo.Depolorize(prepared, msg.Payload); err != nil {
			k.logger.Error("failed to depolarize prepared msg", "err", err)

			return
		}

		slot := k.slots.GetSlot(msg.ClusterID)
		if slot == nil {
			k.logger.Error("slot missing for cluster", "cluster-id", msg.ClusterID)

			return
		}

		slot.ForwardMsgToICSHandler(types.ConsensusMessage{
			PeerID:  msg.Sender,
			Payload: prepared,
		})

	case message.PROPOSAL:
		proposal := new(types.ProposalMsg)
		if err := proposal.FromBytes(msg.Payload); err != nil {
			k.logger.Error("failed to depolarize proposal msg", "err", err)

			return
		}

		if err := k.createICSForProposal(k.ctx, msg.Sender, proposal.Proposal()); err != nil {
			k.logger.Error("failed to handle proposal msg", "err", err, "cluster-id", msg.ClusterID)

			k.metrics.captureICSParticipationFailureCount(1)
			k.transport.GracefullyCloseContextRouter(msg.ClusterID)
			k.slots.CleanupSlot(msg.ClusterID)
			k.logger.Debug("Cleaning consensus slot", "cluster-id", msg.ClusterID)

			return
		}

	case message.VOTEMSG:
		vote := new(types.Vote)
		if err := vote.FromBytes(msg.Payload); err != nil {
			k.logger.Error("failed to depolarize vote msg", "err", err)

			return
		}

		slot := k.slots.GetSlot(msg.ClusterID)
		if slot == nil {
			k.logger.Error("slot missing for cluster", "cluster-id", msg.ClusterID)

			return
		}

		slot.ForwardMsgToKBFTHandler(types.ConsensusMessage{
			PeerID:  msg.Sender,
			Payload: vote,
		})

	default:
		k.logger.Error("Unsupported message type")
	}
}

func (k *Engine) createPreparedMsg(msg *types.Prepare) (*types.Prepared, error) {
	viewInfos, err := k.loadViewInfo(msg.Ps)
	if err != nil {
		return nil, err
	}

	responseMsg := &types.Prepared{
		View:  msg.View,
		Infos: viewInfos,
	}

	if err = responseMsg.Sign(k.vault.Sign); err != nil {
		return nil, err
	}

	return responseMsg, nil
}

/*
- Validate the view ID
- Load the view information of the participants and send the prepared message
*/
func (k *Engine) handlePrepare(
	ctx context.Context,
	msg *types.ICSMSG,
	prepare *types.Prepare,
) error {
	k.logger.Debug("Handling prepare message", "cluster-id", msg.ClusterID, "sender", msg.Sender)

	if k.view.Load() != prepare.View {
		if prepare.View-k.view.Load() == 1 {
			k.enqueueFutureMsg(msg)
		}

		k.logger.Debug("invalid view", "local view", k.view.Load(), "remote view", prepare.View)
		// leader view and the local view should match
		return errors.New("invalid view")
	}

	preparedMsg, err := k.createPreparedMsg(prepare)
	if err != nil {
		return err
	}

	rawData, err := preparedMsg.Bytes()
	if err != nil {
		return err
	}

	return k.transport.SendMessage(
		ctx,
		msg.Sender,
		types.NewICSMsg(k.selfID, msg.ClusterID, message.PREPARED, rawData),
	)
}

//-------------------------------------------------------
//-------------------------------------------------------
//--------------- ics_handler.go ------------------------
//-------------------------------------------------------
//-------------------------------------------------------

package consensus

import (
	"bytes"
	"context"
	"sort"
	"time"

	"github.com/pkg/errors"
	kramaid "github.com/sarvalabs/go-legacy-kramaid"
	identifiers "github.com/sarvalabs/go-moi-identifiers"
	"github.com/sarvalabs/go-moi/common"
	"github.com/sarvalabs/go-moi/consensus/kbft"
	ktypes "github.com/sarvalabs/go-moi/consensus/types"
	"github.com/sarvalabs/go-moi/crypto"
)

// icsHandler is the main handler for ICS Cluster.It handles the timeout events and messages
func (k *Engine) icsHandler(ctx context.Context, clusterID common.ClusterID) {
	slot := k.slots.GetSlot(clusterID)
	cs := slot.ClusterState()

	k.metrics.captureActiveICSClusters(1)

	k.metrics.captureSlotCount(int(slot.SlotType), 1)

	defer func() {
		// signal the core handler to close the slot
		k.metrics.captureActiveICSClusters(-1)
		k.metrics.captureSlotCount(int(slot.SlotType), -1)

		k.closeICS(clusterID)
	}()

	for {
		select {
		case <-time.After(k.viewTimeOutDuration.Load().(time.Duration)): //nolint
			// we should handle this time out if bft is not started
			if slot.Stage.Load() == 0 {
				if slot.SlotType == ktypes.OperatorSlot {
					k.metrics.captureICSCreationFailureCount(1)
				}

				return
			}

		case msg := <-slot.BftOutboundChan:
			k.handleOutboundMessage(ctx, slot.ClusterID(), msg)
		case <-slot.NewICSChan:
			if err := k.sendPrepare(ctx, cs); err != nil {
				k.logger.Error("failed to send prepare msg", "error", err, "cluster-id", clusterID)

				return
			}
		case err := <-slot.BftStopChan:
			if err != nil {
				k.logger.Error("error occurred in bft", "cluster-id", clusterID)

				k.metrics.captureAgreementFailureCount(1)
			}

			return
		case msg := <-slot.Msgs:
			cMsg := msg.Payload

			switch m := cMsg.(type) {
			case *ktypes.Prepared:
				if err := k.handlePrepared(ctx, clusterID, m, msg.PeerID); err != nil {
					k.logger.Error("failed to handle prepared msg", "error", err)
				}

			case *ktypes.Proposal:
				if slot.SlotType == ktypes.ValidatorSlot {
					if err := k.handleProposal(ctx, slot.ClusterState(), m); err != nil {
						k.logger.Error("failed to handle proposal msg", "error", err)

						return
					}
				}

				slot.Stage.CompareAndSwap(0, 1)

				// Start the BFT handler
				icsEvidence := kbft.NewEvidence(cs.IxnHash(), cs.Operator(), cs.Size())
				bft := kbft.NewKBFTService( //nolint
					ctx,
					msg.PeerID,
					k.viewTimeOutDuration.Load().(time.Duration),
					k.cfg,
					k.vault, cs.VoteSet(), slot, k.safety, k.finalizedTesseractHandler,
					kbft.WithLogger(k.logger.With("cluster-id", clusterID)),
					kbft.WithWal(kbft.NullWal{}),
					kbft.WithEvidence(icsEvidence))

				go k.startBFT(bft)

				slot.ForwardMsgToKBFTHandler(msg)

			default:
				slot.ForwardMsgToKBFTHandler(msg)
			}
		}
	}
}

func (k *Engine) startBFT(bft *kbft.KBFT) {
	agreementInitTime := time.Now()

	bft.Start()

	k.metrics.captureAgreementTime(agreementInitTime)
}

// handleOutboundMessage processes the outbound vote messages.
func (k *Engine) handleOutboundMessage(
	ctx context.Context,
	clusterID common.ClusterID,
	msg ktypes.ConsensusMessage,
) {
	icsMsg, err := msg.ICSMsg(clusterID)
	if err != nil {
		k.logger.Error(
			"failed to create ICS msg from consensus msg",
			"krama-id", msg.Recipient,
			"error",
			err)

		return
	}

	k.logger.Debug("Handling outbound message", "cluster-id", clusterID,
		"recipient", msg.Recipient, "msg-type", icsMsg.MsgType)

	// we should broadcast the message if the recipient is empty
	if msg.Recipient == "" {
		k.transport.BroadcastMessage(ctx, icsMsg)
	}

	if err = k.transport.SendMessage(ctx, msg.Recipient, icsMsg); err != nil {
		k.logger.Error("failed to send message to peer", "krama-id", msg.Recipient)
	}
}

// handleProposal processes a proposal message by validating its aggregated signature,
// verifying quorum conditions, validating the highest QC, and executing the tesseract.
/*
	- validate aggregated signature
	- verify quorum conditions
	- verify highest Qc
	- validate tesseract
*/
func (k *Engine) handleProposal(ctx context.Context, cs *ktypes.ClusterState, proposal *ktypes.Proposal) error {
	k.logger.Debug("Handling proposal", "cluster-id", cs.ClusterID, "view", proposal.View())

	initTime := time.Now()
	defer k.metrics.captureProposalValidationTime(initTime)

	trueIndices := proposal.PrepareQc.SignerIndices.GetTrueIndices()
	rawPreparedMsgs := make([][]byte, 0, len(trueIndices))

	for _, index := range trueIndices {
		view := proposal.PrepareQc.PeerViews[index]
		if view == nil {
			continue
		}

		pm := &ktypes.Prepared{
			View:  proposal.View(),
			Infos: proposal.PrepareQc.PeerViews[index],
		}

		rawData, err := pm.SignBytes()
		if err != nil {
			return err
		}

		rawPreparedMsgs = append(rawPreparedMsgs, rawData)
	}

	publicKeys, err := cs.Committee().UpdateValidatorResponse(trueIndices)
	if err != nil {
		return errors.Wrap(err, "failed to update node responses")
	}

	if !cs.IsContextQuorum() {
		return common.ErrContextQuorumFailed
	}

	if !cs.IsRandomQuorum() {
		return common.ErrRandomQuorumFailed
	}

	verified, err := crypto.VerifyMultiSig(proposal.PrepareQc.Signature, rawPreparedMsgs, publicKeys)
	if err != nil {
		return errors.Wrap(err, "failed to verify prepare QC")
	}

	if !verified {
		return errors.Wrap(common.ErrSignatureVerificationFailed, "failed to verify prepare QC")
	}

	for peerIndex, info := range proposal.PrepareQc.PeerViews {
		_, _, peerID, _ := cs.Committee().GetKramaID(int32(peerIndex))
		if err = k.updateHighestVI(cs, info, peerID); err != nil {
			k.logger.Error("failed to validate highest QC", "error", err)
		}
	}

	// create a transition object with latest participant objects
	transition, err := k.state.LoadTransitionObjects(proposal.Ixs().Participants())
	if err != nil {
		return errors.Wrap(err, "failed to load transition objects")
	}

	if err = k.ExecuteAndValidate(proposal.Tesseract, transition); err != nil {
		return err
	}

	cs.SetStateTransition(transition)

	return nil
}

/*
- Validate the viewID
- Validate the BLS signature of the prepareQc
- Update the highest view info by validating the peer info view and qc
- If Quorum conditions are met, execute the interactions and start the BFT system
*/
func (k *Engine) handlePrepared(
	ctx context.Context,
	clusterID common.ClusterID,
	msg *ktypes.Prepared,
	sender kramaid.KramaID,
) error {
	k.logger.Debug("Handling prepared", "cluster-id", clusterID, "sender", sender)

	if k.view.Load() != msg.View {
		// leader view and the local view should match
		return errors.New("invalid view")
	}

	slot := k.slots.GetSlot(clusterID)
	cs := k.slots.GetSlot(clusterID).ClusterState()

	valIndex, publicKey, conflictingVote := cs.HasKramaID(sender)
	if conflictingVote {
		return common.ErrConflictingVote
	}

	if valIndex == -1 {
		return common.ErrPublicKeyNotFound
	}

	signBytes, err := msg.SignBytes()
	if err != nil {
		return err
	}

	verified, err := crypto.Verify(signBytes, msg.Signature, publicKey)
	if !verified || err != nil {
		return common.ErrSignatureVerificationFailed
	}

	if err = k.updateHighestVI(cs, msg.Infos, sender); err != nil {
		return errors.Wrap(err, "failed to update highest view info")
	}

	// save the view info sent by the peer
	cs.Committee().UpdateNodePreparedMsg(sender, msg)

	if !cs.IsContextQuorum() || !cs.IsRandomQuorum() {
		return nil
	}

	swapped := slot.Stage.CompareAndSwap(0, 1)

	if !swapped {
		return nil
	}

	localVI := slot.ClusterState().LocalViewInfo()

	lockedTS := make(map[identifiers.Address]*common.Tesseract)

	for index, highestVI := range slot.ClusterState().HighestViewInfo() {
		// Qc will be NIL for new accounts
		if highestVI.Qc == nil && localVI[index].Qc == nil {
			continue
		}

		highestViewTS, err := k.getTS(highestVI.Qc[0].TSHash, "")
		if err != nil {
			k.logger.Error("failed to load highest view tesseract", "ts-hash", highestVI.Qc[0].TSHash)

			return err
		}

		currentViewTS, err := k.getTS(localVI[index].Qc[0].TSHash, "")
		if err != nil {
			k.logger.Error("failed to load local view tesseract", "ts-hash", localVI[index].Qc[0].TSHash)

			return err
		}

		heightDiff := highestViewTS.Height(highestVI.Addr) - currentViewTS.Height(highestVI.Addr)

		if heightDiff == 0 {
			continue
		}

		if heightDiff > 1 {
			// TODO: Trigger sync
			return nil
		}

		if highestVI.Qc[0].Type == common.PRECOMMIT {
			return nil // TODO: Trigger sync
		}

		if highestVI.Qc[0].Type == common.PREVOTE {
			lockedTS[highestVI.Qc[0].Address] = highestViewTS

			continue
		}
	}

	ts, err := k.createProposalTS(lockedTS, slot.ClusterState())
	if err != nil {
		k.logger.Error("Error creating proposal", "error", err)

		return err
	}

	prepareQc, err := k.createPrepareQc(ctx, slot.ClusterState())
	if err != nil {
		return err
	}

	// update the cluster state with prepareQC and tesseract
	cs.SetPrepareQc(prepareQc)
	cs.SetTesseract(ts)

	k.metrics.captureICSCreationTime(slot.InitTime)

	// Start the BFT system
	bft := kbft.NewKBFTService( //nolint
		ctx,
		k.selfID,
		k.viewTimeOutDuration.Load().(time.Duration),
		k.cfg,
		k.vault, cs.VoteSet(), slot, k.safety, k.finalizedTesseractHandler,
		kbft.WithLogger(k.logger.With("cluster-id", clusterID)),
		kbft.WithWal(kbft.NullWal{}),
		kbft.WithEvidence(kbft.NewEvidence(cs.IxnHash(), cs.Operator(), cs.Size())))

	go k.startBFT(bft)

	return nil
}

func (k *Engine) sendPrepare(ctx context.Context, cs *ktypes.ClusterState) error {
	k.logger.Debug(
		"send prepare",
		"ix-Hash", cs.Ixns().Hashes(),
		"cluster-id", cs.ClusterID,
		"address", cs.Participants.Addrs(),
	)

	prepareMsg := &ktypes.Prepare{
		View: cs.CurrentView(),
		Ixns: cs.Ixns().Hashes(),
		Ps:   cs.Participants.Addrs(),
	}

	if k.trustedPeersPresent {
		// Choose 10 trusted nodes, as a maximum of 8 nodes are required while updating the context
		cs.TrustedPeers = k.getTrustedPeers(10)
	}

	// choose the stochastic nodes using flux
	contextNodes, _, _ := ktypes.DistinctNodes(k.selfID, cs.Committee().Sets)

	stochasticNodes, err := k.getStochasticNodes(ctx, StochasticSetSize, contextNodes)
	if err != nil {
		return errors.Wrap(err, "unable to retrieve random nodes")
	}

	publicKeys, err := k.state.GetPublicKeys(context.Background(), stochasticNodes...)
	if err != nil {
		return errors.Wrap(err, "failed to fetch the public key of random nodes.")
	}

	// update the committee with the stochastic node set
	cs.UpdateNodeSet(
		cs.Committee().StochasticSetPosition(),
		ktypes.NewNodeSet(stochasticNodes, publicKeys, uint32(StochasticSetSize)),
	)

	failedCount, err := k.sendPrepareMsg(ctx, cs.ClusterID, prepareMsg, cs.Committee())
	if err != nil {
		return nil
	}

	k.logger.Error("failed to send prepare msg", "count", failedCount)

	return nil
}

func (k *Engine) loadViewInfo(ps []identifiers.Address) ([]*common.ViewInfo, error) {
	infos := make([]*common.ViewInfo, 0, len(ps))

	for _, addr := range ps {
		isRegistered, err := k.state.IsAccountRegistered(addr)
		if err != nil {
			return nil, err
		}

		if !isRegistered {
			infos = append(infos, &common.ViewInfo{
				Addr:        addr,
				LastView:    0,
				CurrentLock: k.accountLockStatus(addr),
				Qc:          nil,
			})

			continue
		}

		safetyData, err := k.safety.GetLatestSafetyInfo(addr)
		if err != nil {
			return nil, err
		}

		infos = append(infos, &common.ViewInfo{
			Addr:        addr,
			LastView:    safetyData.LastView(),
			CurrentLock: k.accountLockStatus(addr),
			Qc:          safetyData.Qc,
		})
	}

	sort.Slice(infos, func(i, j int) bool {
		return bytes.Compare(infos[i].Addr.Bytes(), infos[j].Addr.Bytes()) < 0
	})

	return infos, nil
}

func (k *Engine) validatePeerHighestQc(remote *common.ViewInfo, peerID kramaid.KramaID) error {
	k.logger.Debug(
		"validating peer qc",
		"peer-id", peerID,
		"addr", remote.Addr,
	)

	for _, qc := range remote.Qc {
		if qc.View == common.GenesisView {
			continue
		}

		k.logger.Debug(
			"validating qc",
			"view", qc.View,
			"addr", qc.Address,
			"type", qc.Type,
			"signers", qc.SignerIndices.String(),
			"peer-id", peerID,
			"signature", qc.Signature,
		)

		ts, err := k.getTS(qc.TSHash, peerID)
		if err != nil {
			return err
		}

		ics, err := k.GetICSCommittee(ts, ts.CommitInfo())
		if err != nil {
			return err
		}

		isVerified, err := k.verifyQc(ts.Addresses(), ts.Participants(), qc.View, ics, qc)
		if err != nil {
			return errors.Wrap(err, "failed to verify QC")
		}

		if !isVerified {
			return common.ErrSignatureVerificationFailed
		}
	}

	return nil
}

// updateHighestVI updates the highest view info by validating the peer info view and qc.
func (k *Engine) updateHighestVI(cs *ktypes.ClusterState, peerInfo common.Views, peerID kramaid.KramaID) error {
	for i, viewInfo := range cs.HighestViewInfo() {
		if len(peerInfo) <= i {
			return nil
		}

		// check if peer viewID is greater than our viewID
		if peerInfo[i].LastView <= viewInfo.LastView {
			continue
		}

		if peerInfo[i].Addr != viewInfo.Addr {
			return errors.New("View Order doesn't match")
		}

		// verify the bls signature of the QC
		if err := k.validatePeerHighestQc(viewInfo, peerID); err != nil {
			return err
		}

		cs.HighestViewInfo()[i] = peerInfo[i]
	}

	return nil
}

// createPrepareQc creates a prepareQC by aggregating all PreparedMsg sent by the replicas.
func (k *Engine) createPrepareQc(
	ctx context.Context,
	cs *ktypes.ClusterState,
) (*ktypes.PreparedInfo, error) {
	initTime := time.Now()
	defer k.metrics.capturePrepareQCSigAggregationTime(initTime)

	infos, signatures := cs.Committee().ViewInfosAndSignatures()

	aggSign, err := crypto.AggregateSignatures(signatures)
	if err != nil {
		return nil, err
	}

	return &ktypes.PreparedInfo{
		View:          cs.CurrentView(),
		PeerViews:     infos,
		SignerIndices: cs.Committee().GetVoteset(),
		Signature:     aggSign,
	}, nil
}

func (k *Engine) createNewTSFromLockedTS(cs *ktypes.ClusterState, ts *common.Tesseract) (*common.Tesseract, error) {
	return common.NewTesseract(
		ts.Participants(),
		ts.InteractionsHash(),
		ts.ReceiptsHash(),
		ts.Epoch(),
		ts.Timestamp(),
		ts.FuelUsed(),
		ts.FuelLimit(),
		ts.ConsensusInfo(),
		nil,
		cs.SelfKramaID(),
		ts.Interactions(),
		ts.Receipts(),
		&common.CommitInfo{
			Operator:                  cs.SelfKramaID(),
			ClusterID:                 cs.ClusterID,
			View:                      cs.CurrentView(),
			RandomSet:                 cs.GetRandomNodes(),
			RandomSetSizeWithoutDelta: cs.Committee().RandomSetSizeWithOutDelta(),
		}), nil
}

// createProposalTS either creates a proposal tesseract from the locked tesseract
// or creates a new tesseract by executing the interactions.
func (k *Engine) createProposalTS(
	lockedTS map[identifiers.Address]*common.Tesseract,
	cs *ktypes.ClusterState,
) (*common.Tesseract, error) {
	var lockTS *common.Tesseract

	for addr, ts := range lockedTS {
		if ts.InteractionsHash() != cs.IxnHash() {
			k.logger.Error(
				"Ixns hash doesn't match with locked tesseract",
				"addr", addr,
				"locked-ts", ts.Hash(),
				"ixns-hash", cs.IxnHash(),
			)

			return nil, errors.New("ts lock mismatch")
		}

		lockTS = ts
	}

	if len(lockedTS) == 0 {
		return k.createProposalTesseract(cs)
	}

	return k.createNewTSFromLockedTS(cs, lockTS)
}

func (k *Engine) accountLockStatus(addr identifiers.Address) common.LockType {
	info, ok := k.accountLocks[addr]
	if !ok {
		return common.NoLock
	}

	return info.LockType
}


//-------------------------------------------------------
//-------------------------------------------------------
//--------------- kbft.go ------------------------
//-------------------------------------------------------
//-------------------------------------------------------

package kbft

import (
	"context"
	"sync"
	"time"

	"github.com/hashicorp/go-hclog"
	"github.com/pkg/errors"
	kramaid "github.com/sarvalabs/go-legacy-kramaid"
	identifiers "github.com/sarvalabs/go-moi-identifiers"
	"github.com/sarvalabs/go-moi/consensus/safety"

	"github.com/sarvalabs/go-moi/common"
	"github.com/sarvalabs/go-moi/common/config"
	"github.com/sarvalabs/go-moi/common/utils"
	ktypes "github.com/sarvalabs/go-moi/consensus/types"
	"github.com/sarvalabs/go-moi/crypto"
	mudracommon "github.com/sarvalabs/go-moi/crypto/common"
	"github.com/sarvalabs/go-moi/telemetry/tracing"
)

const (
	TestBFTimeout = 1 * time.Second
	MaxBFTimeout  = 4 * time.Second
	SlotDuration  = 2 * time.Second
)

type vault interface {
	Sign(data []byte, sigType mudracommon.SigType, signOptions ...crypto.SignOption) ([]byte, error)
	KramaID() kramaid.KramaID
}

// KBFT is a struct that represents the runner for the Krama Byzantine Fault Tolerant consensus engine
type KBFT struct {
	ViewState
	logger           hclog.Logger
	id               kramaid.KramaID
	config           *config.ConsensusConfig
	mx               sync.Mutex
	inboundMsgChan   chan ktypes.ConsensusMessage
	selfMsgChan      chan ktypes.ConsensusMessage
	outboundMsgChan  chan ktypes.ConsensusMessage
	toTicker         *Ticker
	ics              *ktypes.ClusterState
	nSteps           int
	closeChan        chan error
	ctx              context.Context
	ctxCancel        context.CancelFunc
	evidence         *Evidence
	vault            vault
	wal              WAL
	mux              *utils.TypeMux
	tesseractHandler func(tesseract *common.Tesseract) error
	safety           *safety.ConsensusSafety
	exitChan         chan error
	operator         kramaid.KramaID
}

// NewKBFTService initializes a new KBFT instance for the ICS, this service holds the core logic for BFT agreement
func NewKBFTService(
	ctx context.Context,
	operator kramaid.KramaID,
	timeout time.Duration,
	config *config.ConsensusConfig,
	vault vault,
	voteset *ktypes.HeightVoteSet,
	slot *ktypes.Slot,
	safety *safety.ConsensusSafety,
	tesseractHandler func(tesseract *common.Tesseract) error,
	opts ...Option,
) *KBFT {
	k := &KBFT{
		operator:         operator,
		id:               slot.ClusterState().SelfKramaID(),
		config:           config,
		outboundMsgChan:  slot.BftOutboundChan,
		inboundMsgChan:   slot.BftInboundChan,
		selfMsgChan:      make(chan ktypes.ConsensusMessage, 1000),
		vault:            vault,
		ics:              slot.ClusterState(),
		tesseractHandler: tesseractHandler,
		closeChan:        make(chan error),
		exitChan:         slot.BftStopChan,
		safety:           safety,
	}

	for _, opt := range opts {
		opt(k)
	}

	k.ctx, k.ctxCancel = context.WithTimeout(ctx, timeout)
	k.updateToState(voteset)

	return k
}

func (kbft *KBFT) updateToState(voteset *ktypes.HeightVoteSet) {
	kbft.toTicker = NewTicker(kbft.logger)
	kbft.Heights = kbft.ics.NewHeights()
	kbft.updateViewStep(kbft.ics.CurrentView(), ViewStepNewHeight)
	kbft.Proposal = nil
	kbft.ProposalTS = nil

	kbft.Votes = voteset
	kbft.CommitView = 0
	kbft.stepChange()
}

func (kbft *KBFT) scheduleView() {
	kbft.logger.Info("Scheduling View 0. TO:")
	kbft.scheduleTimeout(100*time.Millisecond, kbft.Heights, kbft.View, ViewStepNewHeight)
}

func (kbft *KBFT) handler(maxSteps int) error {
	defer func() {
		close(kbft.outboundMsgChan)
		close(kbft.selfMsgChan)

		kbft.toTicker.Stop()
		kbft.toTicker.Close()
		kbft.ctxCancel()
	}()

	for {
		if maxSteps > 0 {
			if kbft.nSteps >= maxSteps {
				kbft.nSteps = 0

				return errors.New("maximum steps reached")
			}
		}

		viewState := kbft.ViewState

		select {
		case err := <-kbft.closeChan:
			return err

		case <-kbft.ctx.Done():
			kbft.logger.Info("KBFT timeout occurred")

			return kbft.ctx.Err()

		case msg, ok := <-kbft.inboundMsgChan:
			if !ok {
				kbft.logger.Debug("Inbound message channel closed")

				return nil
			}

			kbft.logger.Debug("Handling external message", "sender", msg.PeerID)

			if err := kbft.handleMsg(msg); err != nil {
				kbft.logger.Error("Error handling external message", "sender", msg.PeerID)
			}

		case msg := <-kbft.selfMsgChan:
			kbft.logger.Debug("Handling internal message")

			if err := kbft.wal.WriteSync(msg, kbft.ics.ClusterID); err != nil {
				kbft.logger.Error("Error writing to write-ahead logger", "err", err)
			}

			if err := kbft.handleMsg(msg); err != nil {
				kbft.logger.Error("Error handling internal message", "sender", msg.PeerID)
			}

		case t := <-kbft.toTicker.TimeOutChan():
			kbft.logger.Trace("Handling timeout")
			kbft.handleTimeout(t, viewState)
		}
	}
}

func (kbft *KBFT) handleTimeout(ti timeoutInfo, r ViewState) {
	if !areHeightsEqual(ti.Height, r.Heights) || r.View > ti.View || (ti.View == r.View && ti.Step < r.Step) {
		kbft.logger.Debug(
			"Returning from time out",
			"timeout-height", ti.Height,
			"view-height", r.Heights,
			"timeout-view", ti.View,
			"view-number", r.View,
			"timeout-step", ti.Step,
			"view-step", r.Step,
		)

		return
	}

	kbft.mx.Lock()
	defer kbft.mx.Unlock()

	if ti.Step == ViewStepNewHeight {
		kbft.enterNewView(ti.Height, ti.View)
	}
}

func (kbft *KBFT) handleMsg(msg ktypes.ConsensusMessage) error {
	spanCtx, span := tracing.Span(kbft.ctx, "Krama.KBFT", "handleMsg")

	kbft.mx.Lock()
	defer func() {
		kbft.mx.Unlock()
		span.End()
	}()

	msgPayload, peerID := msg.Payload, msg.PeerID

	switch m := msgPayload.(type) {
	case *ktypes.Proposal:
		kbft.logger.Trace("Proposal message received", "from", peerID)

		if err := kbft.setProposal(m); err != nil {
			kbft.logger.Error("failed to set proposal", "err", err)
		}

	case *ktypes.Vote:
		kbft.logger.Trace("Vote message received", "vote-type", m.Type, "from", peerID)

		_, err := kbft.addVote(spanCtx, m, peerID)
		if err != nil {
			kbft.logger.Error("failed to add vote", "err", err)

			return nil
		}
	}

	return nil
}

func (kbft *KBFT) enterNewView(heights map[identifiers.Address]uint64, view uint64) {
	if !areHeightsEqual(kbft.Heights, heights) ||
		view < kbft.View ||
		(kbft.View == view && kbft.Step != ViewStepNewHeight) {
		return
	}

	kbft.logger.Trace("Entering new view", "view", view, "heights", heights)
	kbft.updateViewStep(view, ViewStepNewView)
	//	kbft.scheduleTimeout(kbft.viewTimeout(view), heights, view, ViewStepNewView)

	if view != 0 {
		kbft.Proposal = nil
		kbft.ProposalTS = nil

		if err := kbft.publishEventPolka(kbft.viewStateEvent()); err != nil {
			kbft.logger.Error("failed to publish new view step", "err", err)
		}
	}

	kbft.Votes.SetView(view + 1)

	if err := kbft.publishEventNewView(kbft.viewStateEvent()); err != nil {
		kbft.logger.Error("failed to publish new view", "err", err)
	}

	// Now ready to enter propose
	kbft.enterPropose(heights, view)
}

func (kbft *KBFT) isProposalReceived() bool {
	if kbft.Proposal == nil || kbft.ProposalTS == nil {
		return false
	}

	return true
}

func (kbft *KBFT) enterPropose(heights map[identifiers.Address]uint64, view uint64) {
	if !areHeightsEqual(kbft.Heights, heights) ||
		kbft.View > view ||
		(kbft.View == view && kbft.Step >= ViewStepPropose) {
		return
	}

	defer func() {
		kbft.updateViewStep(view, ViewStepPropose)
		kbft.stepChange()

		if kbft.isProposalReceived() {
			kbft.enterPrevote(heights, kbft.View)
		}
	}()

	// kbft.scheduleTimeout(kbft.proposeTimeout(view), heights, view, ViewStepPropose)

	if kbft.vault == nil {
		return
	}

	// if _, _, exists := kbft.ics.HasKramaID(kbft.vault.KramaID()); !exists {
	//	kbft.logger.Error("Validator not found in ICS set")
	//
	//	return
	//}

	if !kbft.isLeader(view, kbft.id) {
		return
	}

	if err := kbft.createProposal(heights, view); err != nil {
		kbft.Close(err)
	}
}

// createProposal will create a proposal message for the given height,view and tesseract
func (kbft *KBFT) createProposal(heights map[identifiers.Address]uint64, view uint64) error {
	kbft.logger.Info("Creating proposal", "heights", heights, "view", view)

	proposal := ktypes.NewProposal(kbft.ics.PrepareQc(), kbft.ics.Tesseract())

	// Send an internal message
	kbft.sendInternalMessage(
		ktypes.ConsensusMessage{
			PeerID:  kbft.id,
			Payload: proposal,
		},
	)

	return nil
}

func (kbft *KBFT) setProposal(p *ktypes.Proposal) error {
	if kbft.Proposal != nil {
		return errors.New("proposal already set")
	}

	if !areHeightsEqual(kbft.Heights, p.Heights()) || p.View() != kbft.View {
		return errors.New("invalid height or view")
	}

	kbft.Proposal = p

	// set the proposal tesseract
	kbft.ProposalTS = p.Tesseract

	if kbft.isLeader(kbft.View, kbft.id) {
		kbft.sendExternalMessage(ktypes.ConsensusMessage{
			PeerID:  kbft.id,
			Payload: p,
		})
	}

	if err := kbft.publishEventProposal(p); err != nil {
		kbft.logger.Error("failed to publish proposal", "err", err)
	}

	if kbft.Step <= ViewStepPropose && kbft.isProposalReceived() {
		kbft.enterPrevote(kbft.Heights, kbft.View)
	}

	return nil
}

func (kbft *KBFT) enterPrevote(h map[identifiers.Address]uint64, view uint64) {
	kbft.logger.Trace("Entered pre-vote")

	if !areHeightsEqual(kbft.Heights, h) || kbft.View > view || (kbft.View == view && kbft.Step >= ViewStepPrevote) {
		return
	}

	defer func() {
		kbft.updateViewStep(view, ViewStepPrevote)
		kbft.stepChange()
	}()

	if kbft.ProposalTS == nil {
		kbft.logger.Trace("Proposal tesseract is nil")
		kbft.sendVote(common.PREVOTE, common.NilHash, kbft.isLeader(view, kbft.id))

		return
	}

	kbft.sendVote(common.PREVOTE, kbft.ProposalTS.Hash(), kbft.isLeader(view, kbft.id))
}

func (kbft *KBFT) enterPreCommit(heights map[identifiers.Address]uint64, view uint64) {
	kbft.logger.Trace("Entered pre-commit", "view", view)

	if !areHeightsEqual(kbft.Heights, heights) ||
		kbft.View > view ||
		(view == kbft.View && kbft.Step >= ViewStepPrecommit) {
		return
	}

	defer func() {
		kbft.updateViewStep(view, ViewStepPrecommit)
		kbft.stepChange()
	}()

	// Before preCommit check for >2/3 preVotes
	tsHash, ok := kbft.Votes.Prevotes(view).SuperMajority()
	if !ok {
		return // Log that we have entered precommit without super majority
	}

	if err := kbft.publishEventPolka(kbft.viewStateEvent()); err != nil {
		kbft.logger.Error("failed to publish polka", "err", err)
	}

	// If Leader, send the prevote QC
	if kbft.isLeader(view, kbft.id) {
		kbft.sendQc(common.PREVOTE, tsHash)
	}

	if !kbft.ProposalTS.CompareHash(tsHash) {
		kbft.logger.Error(
			"Proposal doesn't match with super majority",
			"proposal", kbft.Proposal.Tesseract.Hash(),
			"view", kbft.View,
			"ts-hash", tsHash)

		return
	}

	qc, err := kbft.Votes.GetQC(tsHash, kbft.View, common.PREVOTE)
	if err != nil {
		kbft.logger.Error("failed to fetch prevote Qc", "error", err, "view", kbft.View, "ts-hash", tsHash)

		return
	}

	err = kbft.safety.UpdateSafetyInfo(kbft.Proposal, qc)
	if err != nil {
		kbft.logger.Error("failed to store safety information", "error", err, "view", kbft.View, "ts-hash", tsHash)

		return
	}

	kbft.sendVote(common.PRECOMMIT, tsHash, kbft.isLeader(view, kbft.id))
}

func (kbft *KBFT) enterCommit(heights map[identifiers.Address]uint64, view uint64) {
	if !areHeightsEqual(kbft.Heights, heights) || ViewStepCommit <= kbft.Step {
		return
	}

	defer func() {
		kbft.updateViewStep(kbft.View, ViewStepCommit)
		kbft.CommitView = view
		kbft.CommitTime = time.Now()

		kbft.stepChange()
		kbft.finalizeCommit(heights)
	}()

	tsHash, ok := kbft.Votes.Precommits(view).SuperMajority()
	if !ok {
		panic("expecting precommits")
	}

	qc, err := kbft.Votes.GetQC(tsHash, kbft.View, common.PRECOMMIT)
	if err != nil {
		kbft.logger.Error("failed to fetch precommit Qc", "error", err, "view", kbft.View, "ts-hash", tsHash)

		return
	}

	err = kbft.safety.UpdateSafetyInfo(kbft.Proposal, qc)
	if err != nil {
		kbft.logger.Error("failed to store safety information", "error", err, "view", kbft.View, "ts-hash", tsHash)

		return
	}

	if kbft.isLeader(view, kbft.id) {
		kbft.sendQc(common.PRECOMMIT, tsHash)
	}
}

func (kbft *KBFT) finalizeCommit(h map[identifiers.Address]uint64) {
	if !areHeightsEqual(kbft.Heights, h) {
		panic("unmatched heights")
	}

	tsHash, ok := kbft.Votes.Precommits(kbft.CommitView).SuperMajority()
	if !ok || tsHash.IsNil() {
		kbft.logger.Trace("Majority is not available")

		return
	}

	if kbft.Proposal == nil || !kbft.Proposal.Tesseract.CompareHash(tsHash) {
		kbft.logger.Trace("Proposal tesseract doesn't match with the majority")

		return
	}

	if !areHeightsEqual(kbft.Heights, h) || kbft.Step != ViewStepCommit {
		return
	}

	voteBitSet, sign := kbft.Votes.Precommits(kbft.View).GetQC()

	if err := kbft.updateConsensusInfoInTesseracts(voteBitSet, sign); err != nil {
		kbft.Close(err)

		return
	}

	if err := kbft.tesseractHandler(kbft.ProposalTS.Copy()); err != nil {
		kbft.Close(err)

		return
	}

	kbft.logger.Info("Consensus achieved on", "ts-hash", kbft.ProposalTS.Hash())
	// stop the bft engine
	kbft.Close(nil)
}

func (kbft *KBFT) addVote(ctx context.Context, v *ktypes.Vote, peerID kramaid.KramaID) (added bool, err error) {
	_, span := tracing.Span(ctx, "Krama.KBFT", "addVote")
	defer span.End()

	if !ktypes.AreVoteHeightsEqual(v.Heights, kbft.Heights) {
		kbft.logger.Trace("Invalid vote BFT height", "local-heights", kbft.Heights, "msg-heights", v.Heights)

		return added, err
	}

	height := kbft.Heights

	if kbft.ProposalTS != nil && v.TSHash != kbft.ProposalTS.Hash() {
		kbft.evidence.AddVote(v)
	}

	if v.IsQC {
		if !kbft.isLeader(v.View, peerID) {
			return false, errors.New("Invalid Leader")
		}

		added, err = kbft.Votes.AddQC(v, peerID)
		if err != nil || !added {
			kbft.evidence.AddVote(v)

			return added, err
		}
	} else {
		added, err = kbft.Votes.AddVote(v, peerID)
		if err != nil || !added {
			kbft.evidence.AddVote(v)

			return added, err
		}
	}

	if err := kbft.publishEventVote(v); err != nil {
		kbft.logger.Error("failed to publish vote", "err", err)
	}

	switch {
	case v.Type == common.PREVOTE:
		preVotes := kbft.Votes.Prevotes(v.View)

		switch {
		case kbft.View < v.View && preVotes.HasMajorityAny():
			kbft.logger.Error(
				"PreVote received for a future view",
				"current-view", kbft.View,
				"vote-view", v.View)

		case kbft.View == v.View && kbft.Step >= ViewStepPrevote:
			tsHash, ok := preVotes.SuperMajority()
			if ok && (kbft.isProposalReceived() || !tsHash.IsNil()) {
				kbft.enterPreCommit(height, v.View)
			}

		default:
			kbft.logger.Debug("Proposal not available")
		}

	case v.Type == common.PRECOMMIT:
		preCommits := kbft.Votes.Precommits(v.View)

		tsHash, ok := preCommits.SuperMajority()
		if ok {
			if !tsHash.IsNil() { // kbft.enterNewView(height, v.View) // kbft.enterPreCommit(height, v.View)
				kbft.enterCommit(height, v.View)
			}
		} else if kbft.View <= v.View && preCommits.HasMajorityAny() {
			kbft.logger.Error(
				"PreVote received for a future view",
				"current-view", kbft.View,
				"vote-view", v.View)
		}
	}

	return added, err
}

func (kbft *KBFT) sendInternalMessage(msg ktypes.ConsensusMessage) {
	kbft.selfMsgChan <- msg
}

func (kbft *KBFT) sendExternalMessage(msg ktypes.ConsensusMessage) {
	kbft.outboundMsgChan <- msg
}

func (kbft *KBFT) sendQc(msgType common.ConsensusMsgType, tsHash common.Hash) *ktypes.Vote {
	kbft.logger.Debug("Sending quorum certificate", "vote-type", msgType, "ts-hash", tsHash)

	if kbft.vault == nil {
		kbft.logger.Error("Vault service unavailable during sendVote")

		return nil
	}

	vote := &ktypes.Vote{
		Type:    msgType,
		View:    kbft.View,
		Heights: kbft.Heights,
		TSHash:  tsHash,
		IsQC:    true,
	}

	switch msgType {
	case common.PREVOTE:
		vote.SignerIndices, vote.Signature = kbft.Votes.Prevotes(kbft.View).GetQC()
	case common.PRECOMMIT:
		vote.SignerIndices, vote.Signature = kbft.Votes.Precommits(kbft.View).GetQC()

	default:
		kbft.logger.Error("Invalid vote type")
	}

	kbft.sendExternalMessage(ktypes.ConsensusMessage{PeerID: kbft.id, Payload: vote})

	return vote
}

// sendVote will send a signed vote message for the given vote-type and tesseract
func (kbft *KBFT) sendVote(msgType common.ConsensusMsgType, tsHash common.Hash, internalMessage bool) *ktypes.Vote {
	kbft.logger.Debug("Sending vote", "vote-type", msgType, "ts-hash", tsHash)

	if kbft.vault == nil {
		kbft.logger.Error("Vault service unavailable during sendVote")

		return nil
	}

	if _, _, exists := kbft.ics.HasKramaID(kbft.id); !exists {
		return nil
	}

	vote, err := kbft.signVote(msgType, tsHash)
	if err != nil {
		kbft.logger.Error("Error signing the vote message during sendVote", "err", err)

		return nil
	}

	if internalMessage {
		kbft.sendInternalMessage(ktypes.ConsensusMessage{PeerID: kbft.id, Payload: vote})

		return vote
	}

	kbft.sendExternalMessage(
		ktypes.ConsensusMessage{
			PeerID:    kbft.id,
			Recipient: kbft.ics.Operator(),
			Payload:   vote,
		})

	return vote
}

// signVote will create a vote message and sign it using the validator consensus key
func (kbft *KBFT) signVote(msgType common.ConsensusMsgType, tsHash common.Hash) (*ktypes.Vote, error) {
	valIndex, _, _ := kbft.ics.HasKramaID(kbft.id)

	if valIndex == -1 {
		return nil, common.ErrKramaIDNotFound
	}

	v := &ktypes.Vote{
		SignerIndex: valIndex,
		Heights:     kbft.Heights,
		TSHash:      tsHash,
		View:        kbft.View,
		Type:        msgType,
	}

	rawData, err := v.SignBytes()
	if err != nil {
		return nil, err
	}

	sign, err := kbft.vault.Sign(rawData, mudracommon.BlsBLST)
	if err != nil {
		return nil, err
	}

	v.Signature = make([]byte, len(sign))
	copy(v.Signature, sign)

	return v, nil
}

func (kbft *KBFT) updateConsensusInfoInTesseracts(
	preCommitBitSet *common.ArrayOfBits,
	signature []byte,
) (err error) {
	evidenceHash, data, err := kbft.evidence.FlushEvidence()
	if err != nil {
		return err
	}

	qc := &common.Qc{
		Type:          common.PRECOMMIT,
		View:          kbft.View,
		TSHash:        kbft.Proposal.Tesseract.Hash(),
		SignerIndices: preCommitBitSet,
		Signature:     signature,
	}
	// Add evidence data to the dirty list
	kbft.ics.AddDirty(evidenceHash, data)

	tesseract := kbft.ProposalTS

	// for addr, _ := range kbft.Heights {
	// TODO: check this out
	//	tesseract.SetEvidenceHash(addr, evidenceHash)
	// }

	tesseract.SetCommitQc(qc)

	rawData, err := tesseract.SignBytes()
	if err != nil {
		return err
	}

	seal, err := kbft.vault.Sign(rawData, mudracommon.BlsBLST)
	if err != nil {
		return errors.Wrap(err, "failed to sign the tesseract")
	}

	tesseract.SetSeal(seal)
	tesseract.SetSealBy(kbft.id)

	return nil
}

func (kbft *KBFT) isLeader(view uint64, kramaID kramaid.KramaID) bool {
	return kbft.operator == kramaID
}

// scheduleTimeout will schedule a timeout for the given step,view and height
func (kbft *KBFT) scheduleTimeout(d time.Duration, heights map[identifiers.Address]uint64,
	view uint64, step ViewStepType,
) {
	kbft.logger.Debug("Scheduling timeout", "step", step, "duration", d, "heights", heights)
	kbft.toTicker.ScheduleTimeout(timeoutInfo{d, heights, view, step})
}

// updateViewStep
func (kbft *KBFT) updateViewStep(view uint64, step ViewStepType) {
	kbft.View = view
	kbft.Step = step
}

func (kbft *KBFT) stepChange() {
	kbft.nSteps++

	if err := kbft.publishEventNewViewStep(kbft.viewStateEvent()); err != nil {
		kbft.logger.Error("failed to publish new view step", "err", err)
	}
}

func (kbft *KBFT) Start() {
	_, span := tracing.Span(kbft.ctx, "Krama.KBFT", "Start")
	defer span.End()
	// Start the ticker
	if err := kbft.toTicker.Start(); err != nil {
		kbft.logger.Error("Unable to start ticker", "err", err)
	}

	kbft.scheduleView()

	err := kbft.handler(0)

	kbft.exitChan <- err
}

func (kbft *KBFT) Close(err error) {
	kbft.logger.Info("Closing KBFT", "err", err)

	select {
	case kbft.closeChan <- err:
	default:
		go func() {
			kbft.closeChan <- err
		}()
	}
}

func (kbft *KBFT) post(ev interface{}) error {
	if kbft.mux != nil {
		return kbft.mux.Post(ev)
	}

	return nil
}

func (kbft *KBFT) publishEventProposal(proposal *ktypes.Proposal) error {
	return kbft.post(eventProposal{proposal})
}

func (kbft *KBFT) publishEventVote(vote *ktypes.Vote) error {
	return kbft.post(eventVote{vote: vote})
}

func (kbft *KBFT) publishEventPolka(state eventDataViewState) error {
	return kbft.post(eventPolka{state})
}

func (kbft *KBFT) publishEventNewViewStep(state eventDataViewState) error {
	return kbft.post(eventNewViewStep{state})
}

func (kbft *KBFT) publishEventNewView(state eventDataViewState) error {
	return kbft.post(eventNewView{state})
}

// areHeightsEqual is a function that checks if the heights of the two sets are equal.
func areHeightsEqual(systemHeights map[identifiers.Address]uint64, newHeights map[identifiers.Address]uint64) bool {
	if len(systemHeights) != len(newHeights) {
		return false
	}

	// Iterate over system heights
	for systemAddress, systemHeight := range systemHeights {
		newHeight, ok := newHeights[systemAddress]
		if !ok || systemHeight != newHeight {
			// if system address not found or system heights are not equal, return false
			return false
		}
	}

	// Heights match, return true
	return true
}

// areHeightsGreater is a function that checks if the second set of heights is greater than the first.
func areHeightsGreater(systemHeights map[identifiers.Address]uint64, newHeights map[identifiers.Address]uint64) bool {
	if len(systemHeights) != len(newHeights) {
		return false
	}

	// Iterate over system heights
	for systemAddress, systemHeight := range systemHeights {
		newHeight, ok := newHeights[systemAddress]
		if !ok || systemHeight <= newHeight {
			// if system address not found or system heights less than or equal to new height, return false
			return false
		}
	}

	// All heights are greater, return true
	return true
}

// func (kbft *KBFT) PrintMetrics() {
//	prevotes := kbft.Votes.Prevotes(0)
//	precommits := kbft.Votes.Precommits(0)
//	kbft.logger.Trace("Printing metrics")
//
//	if kbft.Proposal != nil {
//		prevoteSet := prevotes.votesByTesseract[kbft.Proposal.Ts.Hash()]
//		precommitSet := precommits.votesByTesseract[kbft.ProposalTS.Hash()]
//		kbft.logger.Debug("Validators", "list", prevotes.valset.committee.String())
//		kbft.logger.Debug("Pre-vote received", "prevote-array", prevoteSet.bitarray)
//		kbft.logger.Debug("Pre-commit received", "precommit-array", precommitSet.bitarray)
//	}
//}



//-------------------------------------------------------
//-------------------------------------------------------
//--------------- ics.go ------------------------
//-------------------------------------------------------
//-------------------------------------------------------


package types

import (
	"crypto/rand"
	"sync"
	"time"

	"github.com/mr-tron/base58"
	kramaid "github.com/sarvalabs/go-legacy-kramaid"
	identifiers "github.com/sarvalabs/go-moi-identifiers"
	"github.com/sarvalabs/go-moi/common"
	"github.com/sarvalabs/go-moi/common/utils"
	gtypes "github.com/sarvalabs/go-moi/state"
	"github.com/sarvalabs/go-polo"
)

type ClusterState struct {
	mtx                      sync.Mutex
	selfID                   kramaid.KramaID
	committee                *ICSCommittee
	voteSet                  *HeightVoteSet
	ixns                     common.Interactions
	ClusterID                common.ClusterID
	Proposer                 kramaid.KramaID
	operator                 kramaid.KramaID
	BinaryHash, IdentityHash common.Hash
	ICSHash                  common.Hash
	dirty                    map[common.Hash][]byte
	ts                       *common.Tesseract
	ICSReqTime               time.Time
	ICSRespCount             int
	operatorIncluded         bool
	Participants             common.Participants
	SuccessMsg               *ICSMSG
	Transition               *gtypes.Transition
	IsObserver               bool
	quorum                   []uint32
	// TODO: Load following view infos appropriately
	localViewInfo   common.Views
	highestViewInfo common.Views
	preparedQc      *PreparedInfo
	view            uint64
	TrustedPeers    []kramaid.KramaID
}

func (cs *ClusterState) SetPrepareQc(prepareQc *PreparedInfo) {
	cs.preparedQc = prepareQc
}

func (cs *ClusterState) Committee() *ICSCommittee {
	return cs.committee
}

// TODO: Check on locks

func NewICS(
	ixs common.Interactions,
	clusterID common.ClusterID,
	operator kramaid.KramaID,
	reqTime time.Time,
	selfID kramaid.KramaID,
	committee *ICSCommittee,
	participants map[identifiers.Address]*common.Participant,
	viewInfos common.Views,
	currentView uint64,
) *ClusterState {
	return &ClusterState{
		ixns:             ixs,
		selfID:           selfID,
		ClusterID:        clusterID,
		operator:         operator,
		operatorIncluded: false,
		dirty:            make(map[common.Hash][]byte),
		ICSReqTime:       reqTime,
		ICSRespCount:     0,
		Participants:     participants,
		committee:        committee,
		Transition:       gtypes.NewTransition(nil),
		localViewInfo:    viewInfos.Copy(),
		highestViewInfo:  viewInfos.Copy(),
		view:             currentView,
	}
}

func (cs *ClusterState) IxnHash() common.Hash {
	return cs.ixns.IxList()[0].Hash()
}

func (cs *ClusterState) SelfKramaID() kramaid.KramaID {
	return cs.selfID
}

func (cs *ClusterState) ParticipantHeight(addr identifiers.Address) uint64 {
	ps, ok := cs.Participants[addr]
	if ok {
		return ps.Height
	}

	return 0
}

func (cs *ClusterState) ParticipantTSHash(addr identifiers.Address) common.Hash {
	ps, ok := cs.Participants[addr]
	if ok {
		return ps.TSHash()
	}

	return common.NilHash
}

func (cs *ClusterState) CurrentView() uint64 {
	return cs.view
}

func (cs *ClusterState) Size() int {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	return cs.committee.TotalNodes()
}

func (cs *ClusterState) UpdateVoteSet(vs *HeightVoteSet) {
	cs.voteSet = vs
}

func (cs *ClusterState) VoteSet() *HeightVoteSet {
	return cs.voteSet
}

func (cs *ClusterState) GetNodeSet(nodeSetPosition int) *NodeSet {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	return cs.committee.Sets[nodeSetPosition]
}

func (cs *ClusterState) UpdateNodeSet(nodeSetPosition int, data *NodeSet) {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	cs.committee.UpdateNodeSet(nodeSetPosition, data)
}

func (cs *ClusterState) UpdateNodeSetResponses(nodeSetPosition int, responses *common.ArrayOfBits) {
	cs.committee.UpdateSetResponses(nodeSetPosition, responses)
}

func (cs *ClusterState) Operator() kramaid.KramaID {
	return cs.operator
}

func (cs *ClusterState) IncludeOperator() {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	cs.operatorIncluded = true
}

func (cs *ClusterState) IsOperatorIncluded() bool {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	return cs.operatorIncluded
}

func (cs *ClusterState) ExcludeParticipantsFromICS(addrs common.Addresses) {
	cs.Participants.ExcludeFromICS(addrs)

	for _, info := range cs.Participants {
		if info.ExcludedFromICS() {
			cs.committee.ExcludeParticipantsFromICS(info.NodeSetPosition)
		}
	}
}

func (cs *ClusterState) NewHeights() map[identifiers.Address]uint64 {
	heights := make(map[identifiers.Address]uint64, len(cs.Participants))
	for addr, ps := range cs.Participants {
		heights[addr] = ps.NewHeight()
	}

	return heights
}

// GetMetaData returns the cluster metadata including the vote messages
func (cs *ClusterState) GetMetaData(msgs []*ICSMSG) (*ICSMetaInfo, error) {
	m := &ICSMetaInfo{
		ClusterID:    string(cs.ClusterID),
		IxHash:       cs.ixns.IxList()[0].Hash(), // Need to be improved
		Operator:     string(cs.operator),
		ClusterSize:  cs.committee.TotalNodes(),
		BinaryHash:   cs.BinaryHash,
		IdentityHash: cs.IdentityHash,
		IcsHash:      cs.ICSHash,
		ReceiptHash:  common.NilHash, // FIXME: observer nodes should execute ixns
	}

	rawData, err := polo.Polorize(cs.GetSuccessMsg())
	if err != nil {
		return nil, err
	}

	m.Msgs = append(m.Msgs, rawData)

	for _, v := range msgs {
		rawData, err := polo.Polorize(v)
		if err != nil {
			return nil, err
		}

		m.Msgs = append(m.Msgs, rawData)
	}

	return m, nil
}

func (cs *ClusterState) GetBehaviouralContextDelta(
	nodeSetPosition int,
	newPeer kramaid.KramaID,
) (added, replaced kramaid.KramaID) {
	for _, info := range cs.committee.Sets[nodeSetPosition].Infos {
		if newPeer == info.ID { // cs.ICS.Nodes[setType].Responses.GetIndex(index)
			return
		}
	}

	if len(cs.committee.Sets[nodeSetPosition].Infos) >= gtypes.MaxBehaviourContextSize {
		replaced = cs.committee.Sets[nodeSetPosition].Infos[0].ID
	}

	return newPeer, replaced
}

func (cs *ClusterState) GetRandomContextDelta(
	nodeSetPosition int,
	requiredCount int,
	skipPeers ...kramaid.KramaID,
) (addedPeers, replacedPeers []kramaid.KramaID) {
	addedPeers = make([]kramaid.KramaID, 0, requiredCount)

	if cs.committee.Sets[nodeSetPosition] != nil {
		if count := len(cs.committee.Sets[nodeSetPosition].Infos) + requiredCount - gtypes.MaxRandomContextSize; count > 0 {
			replacedPeers = cs.committee.Sets[nodeSetPosition].KramaIDs()[0:count]
		}
	}

	if len(cs.TrustedPeers) > 0 {
		for _, trustedPeer := range cs.TrustedPeers {
			if !utils.ContainsKramaID(skipPeers, trustedPeer) {
				addedPeers = append(addedPeers, trustedPeer)
			}

			if len(addedPeers) == requiredCount {
				break
			}
		}

		return addedPeers, replacedPeers
	}

	set := cs.committee.RandomSet()
	for index, info := range set.Infos {
		if set.Responses.GetIndex(index) && !utils.ContainsKramaID(skipPeers, info.ID) {
			addedPeers = append(addedPeers, info.ID)
		}

		if len(addedPeers) == requiredCount {
			break
		}
	}

	return addedPeers, replacedPeers
}

func (cs *ClusterState) LocalViewInfo() []*common.ViewInfo {
	return cs.localViewInfo
}

func (cs *ClusterState) HighestViewInfo() common.Views {
	return cs.highestViewInfo
}

func (cs *ClusterState) IsContextQuorum() bool {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	return cs.committee.IsContextQuorum()
}

func (cs *ClusterState) IsRandomQuorum() bool {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	return cs.committee.RandomSet().GetRespCount() >= int(cs.committee.RandomQuorumSize())
}

func (cs *ClusterState) HasKramaID(kramaID kramaid.KramaID) (int32, []byte, bool) {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	return cs.committee.HasKramaID(kramaID)
}

// GetByIndex returns the krama id and bls public key of the validator based on the index
func (cs *ClusterState) GetByIndex(index int32) (kramaid.KramaID, []byte) {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	slots, slotIndex, kramaID, publicKey := cs.committee.GetKramaID(index)
	if slots == nil || !cs.committee.Sets[slots[0]].Responses.GetIndex(slotIndex) {
		return "", nil
	}

	return kramaID, publicKey
}

func (cs *ClusterState) GetICSVoteset() *common.ArrayOfBits {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	return cs.committee.GetVoteset()
}

func (cs *ClusterState) GetRandomNodes() []kramaid.KramaID {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	return cs.committee.RandomSet().KramaIDs()
}

func (cs *ClusterState) GetQuorum() []uint32 {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	if cs.quorum != nil {
		return cs.quorum
	}

	quorum := make([]uint32, len(cs.Participants)+1) // We add one here for random Set

	for _, ps := range cs.Participants {
		if ps.ExcludeFromICS {
			continue
		}

		quorum[ps.NodeSetPosition] = ps.ConsensusQuorum
	}

	quorum[len(quorum)-1] = cs.committee.RandomQuorumSize()

	cs.quorum = quorum

	return quorum
}

func (cs *ClusterState) GetSuccessMsg() *ICSMSG {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	return cs.SuccessMsg
}

func (cs *ClusterState) SetStateTransition(st *gtypes.Transition) {
	cs.Transition = st
}

func (cs *ClusterState) SetSuccessMsg(msg *ICSMSG) {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	cs.SuccessMsg = msg
}

func (cs *ClusterState) SetTesseract(ts *common.Tesseract) {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()
	cs.ts = ts
}

func (cs *ClusterState) Tesseract() *common.Tesseract {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	return cs.ts
}

func (cs *ClusterState) AddDirty(key common.Hash, data []byte) {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()
	cs.dirty[key] = data
}

func (cs *ClusterState) ExecutionContext() *common.ExecutionContext {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	return &common.ExecutionContext{
		CtxDelta: cs.ContextDelta(),
		Cluster:  cs.ClusterID,
		Time:     uint64(cs.ICSReqTime.Unix()),
	}
}

func (cs *ClusterState) GetDirty() map[common.Hash][]byte {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	return cs.dirty
}

func (cs *ClusterState) GetICSRespCount() int {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	return cs.ICSRespCount
}

func (cs *ClusterState) IncrementICSRespCount(count int) {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	cs.ICSRespCount += count
}

func (cs *ClusterState) ContextDelta() common.ContextDelta {
	contextDelta := make(common.ContextDelta)

	for addr, ps := range cs.Participants {
		if !ps.ExcludeFromICS && ps.ContextDelta != nil {
			contextDelta[addr] = ps.ContextDelta

			continue
		}
	}

	return contextDelta
}

func (cs *ClusterState) Ixns() common.Interactions {
	return cs.ixns
}

func (cs *ClusterState) PrepareQc() *PreparedInfo {
	cs.mtx.Lock()
	defer cs.mtx.Unlock()

	return cs.preparedQc
}

type AccountInfo struct {
	AccType       common.AccountType
	Address       identifiers.Address
	IsGenesis     bool
	ContextHash   common.Hash
	TesseractHash common.Hash
	Height        uint64
	Mode          string
}

func AccountInfoFromAccMetaInfo(metaInfo *common.AccountMetaInfo, isGenesis bool) *AccountInfo {
	return &AccountInfo{
		AccType:       metaInfo.Type,
		Address:       metaInfo.Address,
		IsGenesis:     isGenesis,
		Height:        metaInfo.Height,
		TesseractHash: metaInfo.TesseractHash,
	}
}

type AccountInfos map[identifiers.Address]*AccountInfo

func (a AccountInfos) GetLatestHash(addr identifiers.Address) common.Hash {
	if v, ok := a[addr]; ok {
		return v.TesseractHash
	}

	return common.NilHash
}

func (a AccountInfos) GetHeight(addr identifiers.Address) uint64 {
	if v, ok := a[addr]; ok {
		return v.Height
	}

	return 0
}

func (a AccountInfos) IsGenesis(addr identifiers.Address) bool {
	return a[addr].IsGenesis
}

func (a AccountInfos) Address() []identifiers.Address {
	addrs := make([]identifiers.Address, 0, len(a))

	for addr := range a {
		addrs = append(addrs, addr)
	}

	return addrs
}

func GenerateClusterID() (common.ClusterID, error) {
	randHash := make([]byte, 32)

	if _, err := rand.Read(randHash); err != nil {
		return "", err
	}

	return common.ClusterID(base58.Encode(randHash)), nil
}

type ICSOperatorInfo struct {
	KramaID  kramaid.KramaID
	Priority uint64
	Attempts uint8
}
