import Veil

veil module Krama

type participant
type node
type interaction
type view
-- type quorum
type context
-- What are these new types that are sshown in InfoView when I create these?
--def context := List node

--instantiate tot : TotalOrder view

--immutable relation is_byz : node →  Prop
variable (is_byz : node → Prop)

instantiate ctx : ByzQuorum node is_byz context
open ByzQuorum
-- We need a more involved definition of supermajority over contexts and quorum over ICS

immutable relation leader : node → interaction → view → Prop
function participant_set : interaction → List participant
-- or maybe, relation participant_set : interaction → List participant → Prop

-- Messages over the network
relation prepare_leader (sender : node) (ixn : interaction) (v : view)
relation prepare_node (sender : node) (receiver : node) (locked_qcs : List interaction) (v : view)
relation prepare_nil_node (sender : node) (receiver : node) (prepares : List interaction) (v : view)
relation propose_leader (sender : node) (ixn : interaction) (qc : List context) (v : view)
relation vote_node (sender : node) (receiver : node) (ixn : interaction) (v : view)
relation vote_leader (sender : node) (ixn : interaction) (qc : List context) (v : view)
relation commit_node (sender : node) (receiver : node) (ixn : interaction) (v : view)
relation commit_leader (sender : node) (ixn : interaction) (qc : List context) (v : view)


-- Node state variables
relation member_context: node → participant → Prop
function locked_qc : node → participant → interaction -- Function vs Relation?
relation voted_for_interaction : node → participant → view → interaction → Prop
relation sent_propose_leader : node → interaction → view → Prop
relation sent


--immutable relation leader : node → participant → view → Prop
immutable relation member_quorum : node → quorum → Prop
immutable relation member_context : node → context → Prop
immutable relation honest : node → Prop


relation receivedPrepare : node → Prop
relation sentPrepare : node → Prop
relation receivedPropose : node → Prop
relation sentPropose : node → Prop
relation receivedVote : node → Prop
relation sentVote : node → Prop
relation receivedCommit : node → Prop
relation sentCommit : node → Prop
relation blockCommitted : node → block → view → Prop

--#gen_state

-- Assumptions about leader for an interaction:

-- A transaction in a view has a unique leader
assumption leader N1 T V ∧ leader N2 T V → N1 = N2


-- Assumptions
