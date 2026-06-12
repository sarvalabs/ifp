-- IFPNTDP: IFPNTD with precommit_backed re-anchored to respond_precommit (the
-- "first node has witnessed the precommit-QC from operator") and locks_analog
-- formulated in Tendermint style:
--   precommit_backed(V, I) ∧ V < V2 ∧ prevoted(N, V2, J)
--     → J = I ∨ ancestor I J
-- (the IFP-chain analog of Tendermint's `V2 = V | V2 = nil`).
--
-- Delta from IFPNTD:
--   - operator_precommit no longer writes precommit_backed.
--   - respond_precommit writes precommit_backed v ixn := true (monotonic; first
--     honest responder flips it on; subsequent responders re-write true). All
--     preconditions of respond_precommit (operator's precommitted_operator +
--     supermajority of precommitted_node + node not having decided ixn before)
--     still witness a real precommit-QC at the moment of the flip.
--   - locks_analog_prevoted (decided-hypothesis form) is commented out and
--     replaced by locks_analog_precommit (precommit_backed-hypothesis form,
--     Tendermint-style).
--   - precommitted_operator_implies_precommit_backed is commented out: it no
--     longer holds — operator_precommit now sets precommitted_operator without
--     touching precommit_backed.

import Veil

veil module IFPProtocolNTDPH


class IFPByzQuorum (node : Type) (nset : Type) where
  is_byz : node → Prop
  member (n : node) (s : nset) : Prop
  supermajority (s : nset) : Prop

  supermajorities_intersect_in_honest :
    ∀ (s1 s2 : nset),
      (supermajority s1 ∧ supermajority s2) → (∃ (n : node), member n s1 ∧ member n s2 ∧ ¬ is_byz n)


-- `type declarations`
type view
type node
type interaction
type nodeset
type stage

-- `instantiations`
instantiate tot_view : TotalOrderWithMinimum view
instantiate ctx : IFPByzQuorum node nodeset

-- `individuals`
immutable individual prepare : stage
immutable individual propose : stage
immutable individual prevote : stage
immutable individual precommit : stage
immutable individual commit : stage

individual genesis : interaction

-- `mutable relations and functions`
relation cur_view: node → view → Bool
relation cur_stage : node → view → stage → Bool
relation sent_lock_in_prepare : node → view → interaction → stage → view → Bool
relation decided : node → view → interaction → Bool
relation locked : node → interaction → stage → view → Bool

-- Operator relations
relation operator: node → view → Bool
relation prepared_operator : node → view → Bool
relation proposed_repropose : node → view → interaction → Bool
relation proposed_extend : node → view → interaction → Bool
relation proposed_nil : node → view → Bool
relation prevoted_operator : node → view → interaction → Bool
relation precommitted_operator : node → view → interaction → Bool

-- Non-operator relations
relation prepared_node : node → view → Bool
relation prevoted_node : node → view → interaction → Bool
relation precommitted_node : node → view → interaction → Bool

-- Interaction relations
relation parent : interaction → interaction → Bool
relation ancestor : interaction → interaction → Bool
function height : interaction → Nat

-- Committed state
relation committed_ixn : node → interaction → Bool

-- ####################################################################
-- # Ghost Relations
-- ####################################################################

relation locked_at_view : node → view → Bool

-- "At view V, some operator proposed an interaction I (via repropose or extend)
-- such that A is an ancestor of I". Maintained by propose_repropose and
-- propose_extend; mirrors IFPU's proposed_for_descendant.
relation proposed_for_descendant : view → interaction → Bool

-- "Node N decided an interaction I at view V such that A is an ancestor of I".
-- Maintained by respond_precommit; mirrors IFPU's decided_for_descendant.
relation decided_for_descendant : node → interaction → view → Bool

-- Height-indexed ghosts (view-free; one accumulating set per node). No
-- invariants reference these yet — write-only ghost state, maintained alongside
-- the real `locked`/`decided` updates. Signatures drop the participant param
-- (cf. IFPJ) and the view index (not needed).
-- "Node N holds a lock on some interaction of height H."  ≡ ∃ I S V, locked N I S V ∧ height I = H
relation locked_at_height : node → Nat → Bool
-- "Node N holds a lock on a descendant of A of height H."  ≡ ∃ I S V, locked N I S V ∧ ancestor A I ∧ height I = H
relation locked_descendant_at_height : node → interaction → Nat → Bool
-- "Node N decided some interaction of height H."  ≡ ∃ V I, decided N V I ∧ height I = H
relation committed_at_height : node → Nat → Bool
-- "Node N decided a descendant of A of height H."  ≡ ∃ V I, decided N V I ∧ ancestor A I ∧ height I = H
relation committed_descendant_at_height : node → interaction → Nat → Bool

-- Ghost: a precommit-QC has been aggregated at (V, I) AND at least one node
-- has witnessed it via respond_precommit. Set by respond_precommit (whose
-- precondition guarantees a real supermajority of precommitted_node plus an
-- operator-side precommitted_operator witness, regardless of operator honesty).
-- Tied to that quorum by precommit_backed_fwd. No _bwd direction (avoids SMT
-- cost of asserting the ghost flip on every supermajority change in
-- respond_prevote).
relation precommit_backed : view → interaction → Bool

-- Operator's cached argmax over collected prepare responses. Set by
-- collect_prepares; consumed by the propose_* actions. Functional behaviour
-- (uniqueness per (op, v)) enforced by op_argmax_*_unique.
-- Mirrors Tendermint's `validValue`/`validRound` cached during prevote-handler
-- and consumed by `startRound`. Split into three 3-ary relations (rather than
-- one 5-ary) to keep #gen_spec's simp normalization tractable.
relation prepares_collected : node → view → Bool
relation op_argmax_ixn   : node → view → interaction → Bool
relation op_argmax_stage : node → view → stage → Bool
relation op_argmax_view  : node → view → view → Bool

-- Validator's cached argmax over received prepare responses (mirror of
-- op_argmax_*). Set by collect_recvd_locks; consumed by respond_propose_*.
-- Splits respond_propose's bundled quorum + argmax reasoning out of the
-- prevote actions into a single dedicated transition, so per-(invariant ×
-- prevote-action) proofs no longer have to re-derive the argmax.
relation recvd_collected   : node → view → Bool
relation argmax_recvd_ixn   : node → view → interaction → Bool
relation argmax_recvd_stage : node → view → stage → Bool
relation argmax_recvd_view  : node → view → view → Bool


#gen_state

-- `assumptions`

assumption ¬ (prepare = propose ∨ prepare = prevote ∨ prepare = precommit ∨ prepare = commit ∨
  propose = prevote ∨ propose = precommit ∨ propose = commit ∨ prevote = precommit ∨ prevote = commit ∨ precommit = commit)



-- `init`

after_init {
  parent I J := false;
  ancestor I J := decide $ (I = J);
  locked N I S V := decide $ (I = genesis ∧ S = precommit ∧ V = tot_view.zero);
  decided N V I := decide $ (I = genesis ∧ V = tot_view.zero)
  height I := 0;
  cur_stage N V S := decide $ (S = prepare);
  operator N V := false;
  cur_view N V := decide $ (V = tot_view.zero);
  prepared_operator N V := false;
  sent_lock_in_prepare N U L S V := false;
  proposed_repropose N V I := false;
  proposed_extend N V I := false;
  proposed_nil N V := false;
  prevoted_operator N V I := false;
  precommitted_operator N V I := false;
  prepared_node N V := false;
  prevoted_node N V I := false;
  precommitted_node N V I := false;
  committed_ixn N I := decide $ (I = genesis);
  locked_at_view N V := decide $ (V = tot_view.zero);
  proposed_for_descendant V A := false;
  decided_for_descendant N A V := decide $ (A = genesis ∧ V = tot_view.zero);
  locked_at_height N H := decide $ (H = 0);
  locked_descendant_at_height N A H := decide $ (A = genesis ∧ H = 0);
  committed_at_height N H := decide $ (H = 0);
  committed_descendant_at_height N A H := decide $ (A = genesis ∧ H = 0);
  precommit_backed V I := false;
  prepares_collected N V := false;
  op_argmax_ixn   N V I := false;
  op_argmax_stage N V S := false;
  op_argmax_view  N V VL := false;
  recvd_collected   N V := false;
  argmax_recvd_ixn   N V I := false;
  argmax_recvd_stage N V S := false;
  argmax_recvd_view  N V VL := false;
}

-- ####################################################################
-- # Actions
-- ####################################################################

action set_view (v_cur v_next : view) {
  require ∀ (n : node), cur_view n v_cur
  require tot_view.next v_cur v_next
  cur_view N V := decide $ (V = v_next)
}

action pick_operator (op : node) (v : view) {
  require v ≠ tot_view.zero
  require cur_view op v
  require ∀ (n : node), ¬ operator n v
  operator op v := true
}

action operator_prepare (op : node) (v : view) {
  require v ≠ tot_view.zero
  require cur_view op v
  require cur_stage op v prepare
  require operator op v
  require ¬ prepared_operator op v
  prepared_operator op v := true
}

action respond_prepare (n : node) (v : view) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v prepare
  require ¬ prepared_node n v
  require ∃ (op : node), (operator op v ∧ prepared_operator op v)
  prepared_node n v := true
  sent_lock_in_prepare n v IL SL VL := decide $
    (locked n IL SL VL ∧
     tot_view.lt VL v ∧
     (∀ (vl2 : view), tot_view.lt VL vl2 → ¬ ∃ (i2 : interaction) (s2 : stage), locked n i2 s2 vl2) ∧
     (SL = prevote → ¬ locked n IL precommit VL))
  cur_stage n v S := decide $ (S = propose)
}

-- ####################################################################
-- # Aggregation Action
-- ####################################################################

-- Operator collects prepare responses, computes the highest-view sent lock,
-- and caches it as `op_argmax`. Mirrors Tendermint: `validValue`/`validRound`
-- are set in the prevote-handler and consumed by `startRound`. Here, the
-- per-member prepare-quorum witness, the argmax computation, and the gap
-- check live in this single action; the propose_* actions then just consume
-- `op_argmax`.
action collect_prepares (op : node) (v : view) (s : nodeset) (n_max : node)
    (ixn_max : interaction) (s_max : stage) (v_max : view) {
  require v ≠ tot_view.zero
  require cur_view op v
  require operator op v
  require prepared_operator op v
  -- Operator's own prepare-response is in the bag (Go: localViewInfo seed).
  require prepared_node op v
  require ¬ prepares_collected op v

  -- Prepare-quorum witness (per-member QC-backed lock; matches Go's
  -- validatePeerHighestQc, consensus/ics_handler.go:512).
  require ctx.supermajority s
  require ∀ (n : node), ctx.member n s → (prepared_node n v ∧
    ∃ (vl : view) (ixnl : interaction) (sl : stage) (t : nodeset),
      sent_lock_in_prepare n v ixnl sl vl
      ∧ locked n ixnl sl vl
      ∧ tot_view.le vl v
      ∧ ctx.supermajority t
      ∧ (sl = prevote   → ∀ (nt : node), ctx.member nt t → prevoted_node    nt vl ixnl)
      ∧ (sl = precommit → ∀ (nt : node), ctx.member nt t → precommitted_node nt vl ixnl))

  -- Argmax witness: n_max identifies the highest-view sent lock at v.
  require sent_lock_in_prepare n_max v ixn_max s_max v_max
  require locked n_max ixn_max s_max v_max
  require ∃ (t_max : nodeset), ctx.supermajority t_max
    ∧ (s_max = prevote   → ∀ (nt : node), ctx.member nt t_max → prevoted_node    nt v_max ixn_max)
    ∧ (s_max = precommit → ∀ (nt : node), ctx.member nt t_max → precommitted_node nt v_max ixn_max)
  require ∀ (n_l : node) (ixn_l : interaction) (s_l : stage) (v_l : view),
    sent_lock_in_prepare n_l v ixn_l s_l v_l → tot_view.le v_l v_max
  -- (5) No sent_lock at views strictly above v_max (pure ∀ form, EPR).
  require ∀ (vl : view) (n : node) (i' : interaction) (s' : stage),
    (tot_view.lt v_max vl ∧ tot_view.lt vl v) →
      ¬ sent_lock_in_prepare n v i' s' vl

  -- Cache the result. Each decide-template assigns true on the chosen value
  -- only, so each op_argmax_* is functional-by-construction.
  prepares_collected op v := true
  op_argmax_ixn   op v I  := decide $ (I = ixn_max)
  op_argmax_stage op v S  := decide $ (S = s_max)
  op_argmax_view  op v VL := decide $ (VL = v_max)
}

-- ####################################################################
-- # Proposal Actions (Height-Based, matching Go implementation)
-- ####################################################################

-- Repropose: highest lock is at committed_height + 1 with prevote stage
action propose_repropose (op : node) (v : view) (ci : interaction) {
  require v ≠ tot_view.zero
  require cur_view op v
  require operator op v
  require prepared_operator op v
  require prepares_collected op v
  require cur_stage op v propose
  require ∀ (ix : interaction), ¬ proposed_repropose op v ix
  require ∀ (ix : interaction), ¬ proposed_extend op v ix
  require ¬ proposed_nil op v
  -- Consume operator's cached argmax. Argmax fields picked locally (rather
  -- than as action parameters) to keep action arity low for #gen_spec.
  let ixn_max : interaction ← pick
  let s_max : stage ← pick
  let v_max : view ← pick
  require op_argmax_ixn   op v ixn_max
  require op_argmax_stage op v s_max
  require op_argmax_view  op v v_max
  -- Height-based decision: heightDiff == 1 && PREVOTE → repropose
  require committed_ixn op ci
  require ancestor genesis ci
  require height ixn_max = height ci + 1
  require s_max = prevote
  proposed_repropose op v ixn_max := true;
  -- GHOST: proposed interaction at v is a descendant of A iff A is an ancestor of ixn_max.
  proposed_for_descendant v A := decide $ (proposed_for_descendant v A ∨ ancestor A ixn_max);
}

-- Extend: all locks at committed_height → fresh proposal
action propose_extend (op : node) (v : view) (ixn_propose : interaction) (ci : interaction) {
  require v ≠ tot_view.zero
  require ∀ (j : interaction), ¬ (parent j ixn_propose ∨ parent ixn_propose j)
  require ∀ (j : interaction), (ixn_propose ≠ j → ¬ (ancestor j ixn_propose ∨ ancestor ixn_propose j))
  require height ixn_propose = 0
  require cur_view op v
  require operator op v
  require prepared_operator op v
  require prepares_collected op v
  require cur_stage op v propose
  require ixn_propose ≠ genesis
  require ∀ (ix : interaction), ¬ proposed_repropose op v ix
  require ∀ (ix : interaction), ¬ proposed_extend op v ix
  require ¬ proposed_nil op v
  -- Consume operator's cached argmax (set by collect_prepares). Argmax fields
  -- picked locally to keep action arity low for #gen_spec.
  let ixn_max : interaction ← pick
  let s_max : stage ← pick
  let v_max : view ← pick
  require op_argmax_ixn   op v ixn_max
  require op_argmax_stage op v s_max
  require op_argmax_view  op v v_max
  -- Height-based decision: heightDiff == 0 → extend
  require committed_ixn op ci
  require ancestor genesis ci
  require height ixn_max = height ci
  require ci ≠ ixn_propose
  require ¬ (ancestor ci ixn_propose ∨ ancestor ixn_propose ci)
  parent ci ixn_propose := decide $ (ci ≠ ixn_propose);
  ancestor A ixn_propose := decide $ (ancestor A ixn_propose ∨ ancestor A ci ∨ A = ci ∨ A = ixn_propose);
  proposed_extend op v ixn_propose := true;
  height ixn_propose := height ci + 1;
  -- GHOST: parallel-safe — expand ancestor post-state for ixn_propose, matching
  -- the `ancestor A ixn_propose := ...` update template above.
  proposed_for_descendant v A := decide $ (proposed_for_descendant v A
    ∨ ancestor A ixn_propose ∨ ancestor A ci ∨ A = ci ∨ A = ixn_propose);
}

-- Nil: highest lock too far ahead, or precommit at committed_height + 1
action propose_nil (op : node) (v : view) (ci : interaction) {
  require v ≠ tot_view.zero
  require cur_view op v
  require operator op v
  require prepared_operator op v
  require prepares_collected op v
  require cur_stage op v propose
  require ∀ (ix : interaction), ¬ proposed_repropose op v ix
  require ∀ (ix : interaction), ¬ proposed_extend op v ix
  require ¬ proposed_nil op v
  -- Consume operator's cached argmax (picked locally for low action arity).
  let ixn_max : interaction ← pick
  let s_max : stage ← pick
  let v_max : view ← pick
  require op_argmax_ixn   op v ixn_max
  require op_argmax_stage op v s_max
  require op_argmax_view  op v v_max
  -- Height-based decision: heightDiff > 1 OR (heightDiff == 1 && PRECOMMIT) → nil
  require committed_ixn op ci
  require (height ixn_max > height ci + 1)
        ∨ (height ixn_max = height ci + 1 ∧ s_max = precommit)
  proposed_nil op v := true;
}

-- ####################################################################
-- # Respond/Vote Actions
-- ####################################################################

-- Validator-side analogue of collect_prepares. The quorum + argmax computation
-- previously bundled into respond_propose is moved here so it fires once per
-- (n, v) rather than once per prevote attempt. Result is cached in
-- argmax_recvd_*; the two respond_propose_* actions consume the cache.
action collect_recvd_locks (n : node) (v : view) (s : nodeset) (n_max : node)
    (ixn_max : interaction) (s_max : stage) (v_max : view) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v propose
  require prepared_node n v
  require ¬ recvd_collected n v

  -- Prepare-quorum witness (per-member QC-backed lock).
  require ctx.supermajority s
  require ∀ (m : node), ctx.member m s → (prepared_node m v ∧
    ∃ (vl : view) (ixnl : interaction) (sl : stage) (t : nodeset),
      sent_lock_in_prepare m v ixnl sl vl
      ∧ locked m ixnl sl vl
      ∧ tot_view.le vl v
      ∧ ctx.supermajority t
      ∧ (sl = prevote   → ∀ (nt : node), ctx.member nt t → prevoted_node    nt vl ixnl)
      ∧ (sl = precommit → ∀ (nt : node), ctx.member nt t → precommitted_node nt vl ixnl))

  -- Argmax witness: n_max identifies the highest-view sent lock at v.
  require sent_lock_in_prepare n_max v ixn_max s_max v_max
  require locked n_max ixn_max s_max v_max
  require ∃ (t_max : nodeset), ctx.supermajority t_max
    ∧ (s_max = prevote   → ∀ (nt : node), ctx.member nt t_max → prevoted_node    nt v_max ixn_max)
    ∧ (s_max = precommit → ∀ (nt : node), ctx.member nt t_max → precommitted_node nt v_max ixn_max)
  require ∀ (n_l : node) (ixn_l : interaction) (s_l : stage) (v_l : view),
    sent_lock_in_prepare n_l v ixn_l s_l v_l → tot_view.le v_l v_max
  -- No sent_lock at views strictly above v_max (pure ∀ form, EPR).
  require ∀ (vl : view) (n' : node) (i' : interaction) (s' : stage),
    (tot_view.lt v_max vl ∧ tot_view.lt vl v) →
      ¬ sent_lock_in_prepare n' v i' s' vl

  -- Cache the result. Functional-by-construction via `decide`.
  recvd_collected n v := true
  argmax_recvd_ixn   n v I  := decide $ (I = ixn_max)
  argmax_recvd_stage n v S  := decide $ (S = s_max)
  argmax_recvd_view  n v VL := decide $ (VL = v_max)
}

-- Repropose branch: argmax is a prevote-stage lock at the same interaction
-- the operator is reproposing.
action respond_propose_repropose (n : node) (v : view) (ixn : interaction) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v propose
  require ∃ (op : node), operator op v ∧ proposed_repropose op v ixn
  require ∀ (i : interaction), ¬ prevoted_node n v i
  require ixn ≠ genesis
  require recvd_collected n v
  let ixn_max : interaction ← pick
  let s_max : stage ← pick
  let v_max : view ← pick
  require argmax_recvd_ixn   n v ixn_max
  require argmax_recvd_stage n v s_max
  require argmax_recvd_view  n v v_max
  require s_max = prevote
  require ixn = ixn_max
  require height ixn = height ixn_max
  prevoted_node n v ixn := true
  cur_stage n v S := decide $ (S = prevote)
}

-- Extend branch: argmax is a precommit-stage lock and the operator is
-- proposing a fresh child of the locked interaction.
action respond_propose_extend (n : node) (v : view) (ixn : interaction) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v propose
  require ∃ (op : node), operator op v ∧ proposed_extend op v ixn
  require ∀ (i : interaction), ¬ prevoted_node n v i
  require ixn ≠ genesis
  require recvd_collected n v
  let ixn_max : interaction ← pick
  let s_max : stage ← pick
  let v_max : view ← pick
  require argmax_recvd_ixn   n v ixn_max
  require argmax_recvd_stage n v s_max
  require argmax_recvd_view  n v v_max
  require s_max = precommit
  require ixn ≠ ixn_max
  require parent ixn_max ixn
  require height ixn = height ixn_max + 1
  prevoted_node n v ixn := true
  cur_stage n v S := decide $ (S = prevote)
}

action operator_prevote (op : node) (v : view) (ixn : interaction) (s : nodeset) {
  require v ≠ tot_view.zero
  require ∀ (i : interaction), ¬ prevoted_operator op v i
  require cur_view op v
  require operator op v
  require cur_stage op v prevote
  require ctx.supermajority s
  require ∀ (n : node), ctx.member n s → prevoted_node n v ixn
  prevoted_operator op v ixn := true
}

action respond_prevote (n : node) (v : view) (ixn : interaction) (s : nodeset) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v prevote
  require ∃ (op : node), operator op v ∧ prevoted_operator op v ixn
  require ctx.supermajority s
  require ∀ (nc : node), ctx.member nc s → prevoted_node nc v ixn
  precommitted_node n v ixn := true
  if ( ¬ ∃ (u : view), (tot_view.le u v ∧ locked n ixn precommit u) ) then
    locked n ixn prevote v := true;
    locked_at_view n v := true;
    -- GHOST: new prevote lock at height (height ixn), on every ancestor A of ixn.
    locked_at_height n H := decide $ (locked_at_height n H ∨ H = height ixn);
    locked_descendant_at_height n A H := decide $ (locked_descendant_at_height n A H ∨ (ancestor A ixn ∧ H = height ixn));
  cur_stage n v S := decide $ (S = precommit)
}

action operator_precommit (op : node) (v : view) (ixn : interaction) (s : nodeset) {
  require v ≠ tot_view.zero
  require cur_view op v
  require operator op v
  require cur_stage op v precommit
  require ctx.supermajority s
  require ∀ (nc : node), ctx.member nc s → precommitted_node nc v ixn
  precommitted_operator op v ixn := true
}

action respond_precommit (n : node) (v : view) (ixn : interaction) (s : nodeset) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v precommit
  require ∃ (op : node), operator op v ∧ precommitted_operator op v ixn
  require ctx.supermajority s
  require ∀ (nc : node), ctx.member nc s → precommitted_node nc v ixn
  -- A node decides an interaction at most once across all views.
  require ∀ (v_old : view), ¬ decided n v_old ixn
  -- Ghost set (monotonic): first responding node flips it on; subsequent
  -- responders re-write `true`. The precommitted_operator/supermajority
  -- preconditions above are exactly precommit_backed's witness — equivalent
  -- to operator_precommit's old write, just deferred to the first witnessing.
  precommit_backed v ixn := true
  locked n ixn precommit v := true;
  locked_at_view n v := true;
  -- GHOST: new precommit lock at height (height ixn), on every ancestor A of ixn.
  locked_at_height n H := decide $ (locked_at_height n H ∨ H = height ixn);
  locked_descendant_at_height n A H := decide $ (locked_descendant_at_height n A H ∨ (ancestor A ixn ∧ H = height ixn));
  decided n v ixn := true
  -- GHOST: node decided a descendant of A at view v.
  decided_for_descendant n A v := decide $ (decided_for_descendant n A v ∨ ancestor A ixn);
  -- GHOST: node decided at height (height ixn), on every ancestor A of ixn.
  committed_at_height n H := decide $ (committed_at_height n H ∨ H = height ixn);
  committed_descendant_at_height n A H := decide $ (committed_descendant_at_height n A H ∨ (ancestor A ixn ∧ H = height ixn));
  -- Update committed interaction only if this is a newer decision
  if (∃ (ci_old : interaction), committed_ixn n ci_old ∧ height ixn > height ci_old) then
    committed_ixn n I := decide $ (I = ixn);
  cur_stage n v S := decide $ (S = commit)
}


-- Companion (relock side): the same reproposed block gets prevote-locked again
-- at the reproposal view V. When I is reproposed at V (proposed_repropose OP V I)
-- and some node N holds a prevote lock on that same I at exactly V, that lock
-- traces back to the operator's repropose decision: I was the cached argmax
-- interaction at prevote stage, with some argmax view VM. propose_repropose set
-- proposed_repropose op v ixn_max only after requiring op_argmax_ixn op v ixn_max,
-- op_argmax_stage op v prevote, op_argmax_view op v v_max; the op_argmax cache is
-- frozen once prepares_collected (collect_prepares requires ¬ prepares_collected),
-- so these argmax facts persist for all later locks acquired at V.
invariant [reproposed_relock_at_view_implies_argmax]
  (proposed_repropose OP V I ∧ locked N I prevote V) →
    ∃ (VM : view),
      op_argmax_ixn OP V I ∧ op_argmax_view OP V VM ∧ op_argmax_stage OP V prevote



-- [RISK 3 — feeder for RISK 2 (locks_analog_precommit); mutually inductive with it]
-- Step 3 — Conditional ancestry: the validator-side cached argmax interaction IM
-- descends from any precommit_backed I WHEN the argmax view V_max already dominates
-- the precommit view U (tot_view.le U V_max). Discharged at collect_recvd_locks by
-- crossing argmax_recvd_qc_backed's quorum at V_max with precommit_backed_fwd's
-- quorum at U to an honest m*; for V_max > U apply the IH locks_analog_precommit on
-- (U, V_max); for V_max = U close via unique_prevote_nodes (INV1) +
-- precommit_nodes_only_if_prevoted_for_same_ixn.
invariant [argmax_recvd_ixn_descends_from_precommit_backed_at_bounded_view]
  ∀ (U V_act V_max : view) (I IM : interaction) (N : node),
    (¬ ctx.is_byz N ∧
     precommit_backed U I ∧ I ≠ genesis ∧
     argmax_recvd_ixn N V_act IM ∧ argmax_recvd_view N V_act V_max ∧
     tot_view.lt U V_act ∧ tot_view.le U V_max) →
    (I = IM ∨ ancestor I IM)


-- B3a (repropose carrier): prevote-stage argmax ⇒ J itself prevote-certified at VM.
invariant [qc_anchored_repropose]
  (¬ ctx.is_byz N ∧ prevoted_node N V2 J ∧ J ≠ genesis ∧ V2 ≠ tot_view.zero ∧
   argmax_recvd_stage N V2 prevote) →
    ∃ (VM : view), argmax_recvd_view N V2 VM ∧ tot_view.lt VM V2 ∧
      (∃ (s : nodeset), ctx.supermajority s ∧
          ∀ (m : node), ctx.member m s → prevoted_node m VM J)

-- B3b (extend carrier): precommit-stage argmax ⇒ J's parent P precommit-certified at VM.
invariant [qc_anchored_extend]
  (¬ ctx.is_byz N ∧ prevoted_node N V2 J ∧ J ≠ genesis ∧ V2 ≠ tot_view.zero ∧
   argmax_recvd_stage N V2 precommit) →
    ∃ (VM : view), argmax_recvd_view N V2 VM ∧ tot_view.lt VM V2 ∧
      (∃ (P : interaction) (s : nodeset), ctx.supermajority s ∧ parent P J ∧
          ∀ (m : node), ctx.member m s → precommitted_node m VM P)

-- B3a+ (reproposal 2-chain): strengthens qc_anchored_repropose. When an honest N
-- prevotes J in the repropose branch (cached argmax is prevote-stage), J is not
-- only prevote-QC'd at an earlier view VM < V, its parent P is precommit-QC'd
-- (precommit_backed, unfolds to a supermajority via precommit_backed_fwd) AND has
-- been decided. The 2-chain commit shape: a reproposed interaction sits directly
-- on a committed (precommit-certified) parent. "committed" = decided _ _ P
-- (monotone), NOT committed_ixn, which is superseded as the chain grows.
invariant [reproposal_extends_decided_parent]
  (¬ ctx.is_byz N ∧ prevoted_node N V J ∧ J ≠ genesis ∧ V ≠ tot_view.zero ∧
   argmax_recvd_stage N V prevote) →
    (∃ (VM : view), tot_view.lt VM V ∧
       ∃ (s : nodeset), ctx.supermajority s ∧
         ∀ (m : node), ctx.member m s → prevoted_node m VM J) ∧
    (∃ (P : interaction), parent P J ∧
       (∃ (VP : view), precommit_backed VP P) ∧
       (∃ (M : node) (W : view), decided M W P))


-- B4: same-view precommit-QC and prevote-QC agree (two honest intersectors).
invariant [same_view_precommit_prevote_agree]
  (precommit_backed V I ∧ I ≠ genesis ∧ J ≠ genesis ∧
   (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (m : node), ctx.member m s → prevoted_node m V J)) →
    I = J

-- B5: two precommit-QCs at one view agree.
invariant [precommit_qc_unique_at_view]
  ((∃ (s1 : nodeset), ctx.supermajority s1 ∧
      ∀ (m : node), ctx.member m s1 → precommitted_node m V I1) ∧
   (∃ (s2 : nodeset), ctx.supermajority s2 ∧
      ∀ (m : node), ctx.member m s2 → precommitted_node m V I2)) →
    I1 = I2

-- -- B6 (the GAP as a descent-FREE leaf): in the gap regime VM < V < V2, an earlier
-- -- precommit for I floats down to a precommit-QC at U ≤ VM on the same I.
-- -- Concentrates the quorum-intersection + lock-trichotomy; expect /manual-prove.
-- invariant [precommit_floats_down_to_argmax]
--   (¬ ctx.is_byz N ∧ prevoted_node N V2 J ∧ J ≠ genesis ∧
--    precommit_backed V I ∧ I ≠ genesis ∧
--    argmax_recvd_view N V2 VM ∧ tot_view.lt VM V ∧ tot_view.lt V V2) →
--     ∃ (U : view), tot_view.le U VM ∧ precommit_backed U I

-- ####################################################################
-- # op_argmax cache invariants (S8 — Tendermint-style aggregation)
-- ####################################################################

-- Functional behaviour: at most one value per (op, v) per dimension.
-- Discharged by collect_prepares' `decide` update templates.
invariant [op_argmax_ixn_unique]
  (op_argmax_ixn OP V I1 ∧ op_argmax_ixn OP V I2) → I1 = I2

invariant [op_argmax_stage_unique]
  (op_argmax_stage OP V S1 ∧ op_argmax_stage OP V S2) → S1 = S2

invariant [op_argmax_view_unique]
  (op_argmax_view OP V VL1 ∧ op_argmax_view OP V VL2) → VL1 = VL2

-- Existence iff prepares collected, per dimension. Split forms (no ↔) for
-- simp tractability.
invariant [op_argmax_ixn_implies_collected]
  op_argmax_ixn OP V I → prepares_collected OP V

invariant [op_argmax_stage_implies_collected]
  op_argmax_stage OP V S → prepares_collected OP V

invariant [op_argmax_view_implies_collected]
  op_argmax_view OP V VL → prepares_collected OP V

invariant [collected_implies_op_argmax_ixn]
  prepares_collected OP V → ∃ (I : interaction), op_argmax_ixn OP V I

invariant [collected_implies_op_argmax_stage]
  prepares_collected OP V → ∃ (S : stage), op_argmax_stage OP V S

invariant [collected_implies_op_argmax_view]
  prepares_collected OP V → ∃ (VL : view), op_argmax_view OP V VL

-- op_argmax_is_highest_lock relocated to the top of the invariant list (sited
-- with main_safety) so its preservation across respond_prepare is discharged
-- early. The OLD universal-dominance clause was dropped for the same reason as
-- argmax_recvd_is_highest_lock — respond_prepare can extend sent_lock_in_prepare
-- with a VL > VM, making the universal structurally unprovable.

-- Argmax interaction is QC-backed at its claimed (view, stage) for honest op.
-- Discharged by the per-member QC-backing requires inside collect_prepares.
invariant [op_argmax_qc_backed]
  (¬ ctx.is_byz OP ∧ op_argmax_ixn OP V IM ∧ op_argmax_stage OP V SM ∧ op_argmax_view OP V VM) →
    (SM = prevote → ∃ (Q : nodeset), ctx.supermajority Q ∧
       ∀ (N : node), ctx.member N Q → prevoted_node N VM IM) ∧
    (SM = precommit → ∃ (Q : nodeset), ctx.supermajority Q ∧
       ∀ (N : node), ctx.member N Q → precommitted_node N VM IM)



-- %%%%%%%%% TESTED ALL BELOW HERE

-- B7 (GOAL, single self-referential invariant): every certificate at V2 > V is
-- I or a descendant of I. cert_qc = prevote_qc ∨ precommit_qc, inlined.
-- invariant [qc_descent]
--   (precommit_backed V I ∧ I ≠ genesis ∧ J ≠ genesis ∧ tot_view.lt V V2 ∧
--    ((∃ (s : nodeset), ctx.supermajority s ∧
--        ∀ (m : node), ctx.member m s → prevoted_node m V2 J) ∨
--     (∃ (s : nodeset), ctx.supermajority s ∧
--        ∀ (m : node), ctx.member m s → precommitted_node m V2 J))) →
--     (J = I ∨ ancestor I J)

-- [RISK 4 — unbounded feeder; should be unchanged but verify]
-- Step 1 — Lift collect_recvd_locks's action quorum into a state invariant.
-- Trivially provable at collect_recvd_locks (the action's `s` parameter is the
-- witness); preserved elsewhere by monotonicity of recvd_collected and
-- sent_lock_in_prepare. Makes the prepare-quorum directly visible to SMT in
-- downstream proofs so they don't have to re-derive it from the action body.
invariant [recvd_collected_implies_prepare_quorum]
  recvd_collected N VACT →
    ∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (m : node), ctx.member m s →
        prepared_node m VACT ∧
        ∃ (IL : interaction) (SL : stage) (VL : view),
          sent_lock_in_prepare m VACT IL SL VL ∧ locked m IL SL VL

-- ----- existing top-level invariants (already passing pre-edit) -----

-- Relocated from the freshness section (was failing at propose_repropose,
-- ~60s timeout). At propose_repropose the post-state `proposed_repropose op v
-- ixn_max := true` requires `∃ J. parent J ixn_max` in pre-state. The chain
-- routes through op_argmax_is_highest_lock → locked → no_lock_without_parent;
-- placing it above the cache-existence invariant keeps the chain visible.
invariant [no_proposal_without_parent]
  (¬ ctx.is_byz OP ∧ (proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

-- Relocated from the genesis-ancestry section (was failing at propose_repropose,
-- ~61s timeout). Chain: op_argmax_is_highest_lock → locked →
-- locked_descends_from_genesis → ancestor genesis ixn_max.
invariant [proposed_descends_from_genesis]
  (¬ ctx.is_byz OP ∧ (proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ I ≠ genesis) → ancestor genesis I

-- Existence witness: cached (IM, SM, VM) came from some actual sent_lock at V.
-- Existential-only form (no universal-dominance clause). Preservation at
-- respond_prepare hinges on the unrestricted `sent_lock_only_if_prepare`
-- (no ¬is_byz guard): combined with respond_prepare's `require ¬ prepared_node n v`,
-- the case `N_pre = n_action ∧ V = v_action` becomes unreachable, so the
-- pre-state witness survives in the unchanged slice.
invariant [op_argmax_is_highest_lock]
  (¬ ctx.is_byz OP ∧ op_argmax_ixn OP V IM ∧ op_argmax_stage OP V SM ∧ op_argmax_view OP V VM) →
    ∃ (N : node), sent_lock_in_prepare N V IM SM VM ∧ locked N IM SM VM

-- Validator-side mirror of op_argmax_is_highest_lock. Same preservation
-- argument at respond_prepare (unrestricted sent_lock_only_if_prepare + action
-- precondition contradict the substantive case).
invariant [argmax_recvd_is_highest_lock]
  (¬ ctx.is_byz N ∧ argmax_recvd_ixn N V IM ∧ argmax_recvd_stage N V SM ∧ argmax_recvd_view N V VM) →
    ∃ (M : node), sent_lock_in_prepare M V IM SM VM ∧ locked M IM SM VM


safety [main_safety]
  ∀ (n1 n2 : node) (v1 v2 : view) (i1 i2 : interaction),
    (¬ ctx.is_byz n1 ∧ ¬ ctx.is_byz n2 ∧
     decided n1 v1 i1 ∧
     decided n2 v2 i2) →
    (ancestor i1 i2 ∨ ancestor i2 i1)

-- Fork-location lemma: if two honest decisions are incomparable (main_safety
-- violated), the divergence is witnessed by a concrete fork — a common
-- interaction A with two DISTINCT children c1, c2, one an ancestor of each
-- decided interaction. Structural (tree-only): A := LCA(i1,i2), c1/c2 := the
-- first step off A toward i1 / i2, via ancestor_def_fwd + unique_parent.
-- NOT a safety proof on its own — it only extracts the fork witness. It reduces
-- main_safety to the local "no honest sibling-fork" consensus obligation
-- (no interaction has two distinct children each backing an honest decision).
invariant [safety_violation_locates_fork]
  ∀ (n1 n2 : node) (v1 v2 : view) (i1 i2 : interaction),
    (¬ ctx.is_byz n1 ∧ ¬ ctx.is_byz n2 ∧
     decided n1 v1 i1 ∧ decided n2 v2 i2 ∧
     ¬ ancestor i1 i2 ∧ ¬ ancestor i2 i1) →
    ∃ (A c1 c2 : interaction),
      parent A c1 ∧ parent A c2 ∧ c1 ≠ c2 ∧
      ancestor c1 i1 ∧ ancestor c2 i2

-- ####################################################################
-- # Decoupled qc_descent invariant set (replaces the LAP <-> F1 cycle)
-- # Design: IFPSafety/locks_analog_precommit_decoupling.md
-- # qc_descent (B7) is the single self-referential goal (self-loop on the
-- # J-side certificate view V2); B1-B6 are descent-free leaves. cert_qc /
-- # prevote_qc / precommit_qc are inlined as exists-supermajority predicates.
-- # NB: the design doc's certificate view "W" is written V2 here (a bare `W`
-- # collides with a global identifier in scope, so it does not auto-bind).
-- # NOTE: LAP (locks_analog_precommit) and F1 are intentionally KEPT for now;
-- # delete them + re-route locks_analog_decided only AFTER qc_descent verifies.
-- # qc_descent (B7) and precommit_floats_down_to_argmax (B6) are expected to
-- # need /manual-prove (the gap is this file's documented timeout point).
-- ####################################################################

-- B1: a witnessed precommit-QC sits strictly above the initial view.
invariant [precommit_backed_above_zero]
  precommit_backed V I → V ≠ tot_view.zero

-- B2: an honest prevote agrees with the prevoter's cached argmax (prevote-stage
-- ⇒ J is the argmax; precommit-stage ⇒ J's parent is the argmax). Descent-free.
invariant [prevote_matches_argmax]
  (¬ ctx.is_byz N ∧ prevoted_node N V2 J ∧ J ≠ genesis ∧ V2 ≠ tot_view.zero) →
    ∃ (IM : interaction), argmax_recvd_ixn N V2 IM ∧
      ((argmax_recvd_stage N V2 prevote ∧ J = IM) ∨
       (argmax_recvd_stage N V2 precommit ∧ parent IM J))

-- B3 (carrier, descent-FREE): every honest prevote extends a certificate at the
-- prevoter's cached argmax view VM < V2. Exposes argmax_recvd_view so the gap
-- leaf (B6) reuses the SAME VM. Split by the cached argmax stage (B2's
-- discriminator): prevote-stage ⇒ repropose anchor (J prevote-certified at VM),
-- precommit-stage ⇒ extend anchor (J's parent precommit-certified at VM). The two
-- guards partition realizable states (argmax_recvd_stage is set once at
-- collect_recvd_locks to the single s_max ∈ {prevote, precommit}), so together they
-- reconstitute the original disjunction; a consumer reads the stage off B2.


-- Bridge: any honest non-genesis prevote at non-zero V routes through the cache,
-- so downstream invariants (e.g. locks_analog_prevoted) can lift argmax facts
-- out of the prevote action body and into a cache lookup.
invariant [prevoted_node_implies_recvd_collected]
  (¬ ctx.is_byz N ∧ prevoted_node N V I ∧ I ≠ genesis ∧ V ≠ tot_view.zero) →
    recvd_collected N V

-- recvd_collected at V exists only after global cur_view has reached V.
-- Discharged at collect_recvd_locks via its `require cur_view n v` precondition;
-- combined with cur_view_global this pins V = cur_view at firing. Preserved by
-- set_view (cur_view only advances via tot_view.next) and trivially elsewhere.
-- Closes the trivial-preservation cases of argmax_recvd_ixn_descends_from_precommit_backed
-- on respond_precommit (new precommit_backed view V_pre = cur_view, so V_pre < V_act
-- is ruled out by V_act ≤ cur_view = V_pre) and on set_view (advance).
invariant [recvd_collected_at_past_view]
  (recvd_collected N V ∧ cur_view N1 VC) → tot_view.le V VC

  invariant [locks_analog_decided]
    ∀ (V V2 : view) (I I2 : interaction) (N1 N2 : node),
      (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
       I ≠ genesis ∧ I2 ≠ genesis ∧
       decided N1 V I ∧ decided N2 V2 I2 ∧
       tot_view.lt V V2) →
      (I = I2 ∨ ancestor I I2)


-- ####################################################################
-- # Top-level safety invariants (most likely to fail, sited with main_safety)
-- # Ordered: highest-risk-with-current-edit first.
-- ####################################################################

-- [RISK 1 — NEW (Approach 1)] The prepare-quorum members captured by
-- recvd_collected all have sent-lock views bounded by the cached argmax view
-- V_max. Strictly stronger than recvd_collected_implies_prepare_quorum — kept
-- as a separate invariant so existing consumers of the unbounded form don't
-- churn.
--
-- Discharge expected at collect_recvd_locks: the action-local supermajority
-- `s` and its per-member sent_lock_in_prepare existential combine with the
-- action's own argmax-dominance require
--   `∀ n_l ixn_l s_l v_l, sent_lock_in_prepare n_l v ixn_l s_l v_l → tot_view.le v_l v_max`
-- to give VL ≤ v_max per member. Preserved trivially elsewhere because
-- recvd_collected/argmax_recvd_view are only set by collect_recvd_locks, and the
-- per-member sent_lock_in_prepare/locked entries are monotonic.
--
-- Pruned-from-stack: RISK 1a (intersection witness) and the prior RISK 1
-- (precommit_backed_drops_below_argmax_view) were both removed in this pass —
-- their discharges at collect_recvd_locks were timing out together with this
-- invariant under Veil's WP/simp budget. With them gone, this is the only
-- new existentially-quantified invariant at collect_recvd_locks, which should
-- let it fit within the heartbeat budget. If it still times out, it gets a
-- manual proof (via /manual-prove). Once available as a state-level premise,
-- it can feed an upcoming manual proof of
-- (locks_analog_precommit × respond_propose_repropose), inlining the
-- cross-quorum + trichotomy chain there.
-- invariant [recvd_collected_implies_bounded_prepare_quorum]
--   (recvd_collected N VACT ∧ argmax_recvd_view N VACT VMAX) →
--     ∃ (s : nodeset), ctx.supermajority s ∧
--       ∀ (m : node), ctx.member m s →
--         prepared_node m VACT ∧
--         ∃ (IL : interaction) (SL : stage) (VL : view),
--           sent_lock_in_prepare m VACT IL SL VL ∧ locked m IL SL VL ∧
--           tot_view.le VL VMAX

-- [RISK 2 — target, times out on respond_propose_repropose]
-- Tendermint-style lock propagation, in IFP chain-extension form.
--   precommit_backed V I  (some honest node has witnessed a precommit-QC for I at V)
--     → any later honest prevote at V2 > V is on I or a descendant of I
-- The "V2 = nil" Tendermint disjunct is replaced by "ancestor I J" since IFP
-- proposals extend rather than carry a nil value.
--
-- Discharge plan (manual proof, /manual-prove):
-- At respond_propose_repropose, the post-state asserts prevoted_node n v ixn
-- with ixn = ixn_max from action. For any precommit_backed V I with V < v:
--   (a) Pull V_max from argmax_recvd_view n v V_max (action precondition).
--   (b) Case V ≤ V_max: apply Step 3 (argmax_recvd_ixn_descends_from_
--       precommit_backed_at_bounded_view) with U := V → I = ixn_max
--       ∨ ancestor I ixn_max; conclude.
--   (c) Case V > V_max:
--       - precommit_backed_fwd V → precommit-quorum t.
--       - RISK 1 (recvd_collected_implies_bounded_prepare_quorum) → prepare-
--         quorum s with VL ≤ V_max per member.
--       - supermajorities_intersect_in_honest s t → honest m* in s ∩ t.
--       - m* ∈ t ⇒ precommitted_node m* V I; precommit_node_locked_at_same_view
--         gives prevote-at-V or precommit-at-U′≤V.
--       - m* ∈ s ⇒ sent_lock m* v _ _ VL ∧ locked m* _ _ VL ∧ VL ≤ V_max;
--         highest_lock_sent kills the prevote-at-V and precommit-at-U′>V_max
--         branches. Remaining branch: locked m* I precommit U′ with U′≤V_max.
--       - precommit_lock_implies_precommit_backed → precommit_backed U′ I.
--       - Apply Step 3 with U := U′ → I = ixn_max ∨ ancestor I ixn_max.
--   For _extend, parent ixn_max ixn + ancestor_from_parent + ancestor_trans
--   gives ancestor I ixn (rather than I = ixn).

-- invariant [locks_analog_precommit]
--   ∀ (V V2 : view) (I J : interaction) (NP : node),
--     (¬ ctx.is_byz NP ∧
--      precommit_backed V I ∧ I ≠ genesis ∧ J ≠ genesis ∧
--      prevoted_node NP V2 J ∧
--      tot_view.lt V V2) →
--     (J = I ∨ ancestor I J)

-- ####################################################################
-- # argmax_recvd cache invariants (validator-side mirror of op_argmax_*)
-- ####################################################################

-- Functional behaviour: at most one value per (n, v) per dimension.
-- Discharged by collect_recvd_locks' `decide` update templates.
invariant [argmax_recvd_ixn_unique]
  (argmax_recvd_ixn N V I1 ∧ argmax_recvd_ixn N V I2) → I1 = I2

invariant [argmax_recvd_stage_unique]
  (argmax_recvd_stage N V S1 ∧ argmax_recvd_stage N V S2) → S1 = S2

invariant [argmax_recvd_view_unique]
  (argmax_recvd_view N V VL1 ∧ argmax_recvd_view N V VL2) → VL1 = VL2

-- Existence iff recvd_collected, per dimension. Split forms for simp tractability.
invariant [argmax_recvd_ixn_implies_collected]
  argmax_recvd_ixn N V I → recvd_collected N V

invariant [argmax_recvd_stage_implies_collected]
  argmax_recvd_stage N V S → recvd_collected N V

invariant [argmax_recvd_view_implies_collected]
  argmax_recvd_view N V VL → recvd_collected N V

invariant [collected_implies_argmax_recvd_ixn]
  recvd_collected N V → ∃ (I : interaction), argmax_recvd_ixn N V I

invariant [collected_implies_argmax_recvd_stage]
  recvd_collected N V → ∃ (S : stage), argmax_recvd_stage N V S

invariant [collected_implies_argmax_recvd_view]
  recvd_collected N V → ∃ (VL : view), argmax_recvd_view N V VL

-- Cache existence witness: the cached (IM, SM, VM) tuple came from some
-- actual sent_lock at V. Preserved monotonically (sent_lock_in_prepare and
-- locked never shrink).
-- The OLD universal-dominance clause
--   ∀ N' IL SL VL, sent_lock_in_prepare N' V IL SL VL → tot_view.le VL VM
-- argmax_recvd_is_highest_lock relocated to the top of the invariant list
-- (sited with main_safety). The OLD universal-dominance clause was structurally
-- unprovable at respond_prepare: late preparers can extend
-- `sent_lock_in_prepare` with a VL > VM (the holder had a lock above VM that
-- wasn't yet a sent_lock at V when collect_recvd_locks fired). Dropped.
-- The substantive use of "argmax dominates" is inlined into Step 3.5's proof
-- at collect_recvd_locks, where the action's prepare-quorum `s` and the
-- action's own argmax-dominance require make the snapshot reasoning local.

-- Cached argmax interaction is QC-backed at its claimed (view, stage) for honest validator.
invariant [argmax_recvd_qc_backed]
  (¬ ctx.is_byz N ∧ argmax_recvd_ixn N V IM ∧ argmax_recvd_stage N V SM ∧ argmax_recvd_view N V VM) →
    (SM = prevote → ∃ (Q : nodeset), ctx.supermajority Q ∧
       ∀ (N' : node), ctx.member N' Q → prevoted_node N' VM IM) ∧
    (SM = precommit → ∃ (Q : nodeset), ctx.supermajority Q ∧
       ∀ (N' : node), ctx.member N' Q → precommitted_node N' VM IM)


-- ####################################################################
-- # Argmax → precommit_backed ancestry bridge (Option 3)
-- ####################################################################
-- Substantive case: collect_prepares. Via intersection of the prepare-quorum
-- with precommit_backed_fwd's supermajority, an honest n* holds both
--   - precommitted_node at (V, I), hence a lock at U ≤ V on I, and
--   - sent_lock_in_prepare at V2 with QC-backed (ixnl, sl, vl), where vl ≤ v_max
-- so lock_height_monotone within n* + ancestor descent gives ancestor I IM.
-- All other actions preserve trivially: op_argmax_ixn, precommit_backed, and
-- ancestor are monotonic on pre-existing data; new ancestor entries from
-- propose_extend involve a fresh ixn_propose not equal to any pre-existing I/IM.
-- invariant [op_argmax_ancestor_of_precommit_backed]
--   ∀ (V V2 : view) (I IM : interaction) (OP : node),
--     (precommit_backed V I ∧ I ≠ genesis ∧
--      op_argmax_ixn OP V2 IM ∧
--      tot_view.lt V V2) →
--     (I = IM ∨ ancestor I IM)





-- ####################################################################
-- # Ghost Consistency Invariants (proposed/decided)
-- ####################################################################

-- proposed_for_descendant forward: proposed (repropose or extend) + ancestry → ghost
invariant [proposed_for_descendant_fwd]
  ((proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ ancestor A I) →
    proposed_for_descendant V A

-- proposed_for_descendant backward: ghost → ∃ proposed descendant
invariant [proposed_for_descendant_bwd]
  proposed_for_descendant V A →
    ∃ (OP : node) (I : interaction),
      (proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ ancestor A I

-- decided_for_descendant forward: decided + ancestry → ghost
invariant [decided_for_descendant_fwd]
  (decided N V I ∧ ancestor A I) → decided_for_descendant N A V

-- decided_for_descendant backward (honest only): ghost → ∃ decided descendant
invariant [decided_for_descendant_bwd]
  (¬ ctx.is_byz N ∧ decided_for_descendant N A V) →
    ∃ (I : interaction), decided N V I ∧ ancestor A I

-- Bridge: precommitted_node directly implies a prevote-QC was aggregated
-- (mirrors respond_prevote's `∃ op. operator op v ∧ prevoted_operator op v ixn`
-- precondition lifted into a state invariant, with the operator-role guard).
invariant [precommitted_node_implies_prevote_qc]
  precommitted_node N V I → (∃ (op : node), operator op V ∧ prevoted_operator op V I)


  -- Bridge for main_safety to feed this invariant.
  invariant [decided_implies_precommit_backed]
    (¬ ctx.is_byz N ∧ decided N V I ∧ I ≠ genesis) → precommit_backed V I

-- (IFPNTDP) Removed: precommitted_operator no longer implies precommit_backed.
-- operator_precommit sets precommitted_operator but not precommit_backed; only
-- the subsequent respond_precommit fires precommit_backed. The
-- decided_implies_precommit_backed bridge now holds trivially because both
-- updates happen atomically in respond_precommit, so this intermediate bridge
-- is no longer needed.
-- invariant [precommitted_operator_implies_precommit_backed]
--   precommitted_operator OP V I → precommit_backed V I

-- Honest non-genesis prevote at non-zero view is justified by some pre-existing
-- lock (monotonic witness). The dominance / argmax clause was dropped: it fails
-- preservation on respond_prepare when a late preparer m (honest, different
-- from the prevoter) first prepares at V with a lock view > the prevote's
-- v_max — protocol-allowed, since respond_propose's argmax is a snapshot, not
-- a forward-time-stable property.
invariant [prevote_justified_by_highest_lock]
  (¬ ctx.is_byz N ∧ prevoted_node N V I ∧ I ≠ genesis ∧ V ≠ tot_view.zero) →
    ∃ (n_max : node) (ixn_max : interaction) (s_max : stage) (v_max : view),
      locked n_max ixn_max s_max v_max ∧
      tot_view.lt v_max V ∧
      ((s_max = prevote ∧ ixn_max = I) ∨
       (s_max = precommit ∧ parent ixn_max I))

-- Strengthened: mirrors respond_prevote's exact post-condition. Either the
-- prevote lock is at the same view V (new lock set by respond_prevote), or a
-- pre-existing precommit lock at some U ≤ V. Rules out spurious states where
-- precommitted_node exists without the matching `locked` side-effect.
invariant [precommit_node_locked_at_same_view]
  (¬ ctx.is_byz N ∧ precommitted_node N V I ∧ I ≠ genesis) →
    (locked N I prevote V ∨ ∃ (U : view), tot_view.le U V ∧ locked N I precommit U)



-- Precommit locks are bounded by the holder's committed_ixn height. Established
-- atomically in respond_precommit (sets locked precommit + updates committed_ixn
-- when height ≥ old). Rules out spurious states where a precommit lock exists
-- without the matching committed_ixn bookkeeping.
invariant [precommit_lock_height_le_committed]
  (¬ ctx.is_byz N ∧ locked N I precommit V ∧ committed_ixn N CI) →
    height I ≤ height CI


-- ####################################################################
-- # Core Safety-Routing Invariants
-- ####################################################################

invariant [genesis_decided_only_at_zero]
  (¬ ctx.is_byz N ∧ decided N V genesis) → V = tot_view.zero

invariant [proposed_parent_height_le_committed]
  (¬ ctx.is_byz OP ∧
   (proposed_repropose OP V J ∨ proposed_extend OP V J) ∧
   parent I J ∧ committed_ixn OP CI) →
    height I ≤ height CI

invariant [decision_height_monotone]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   decided N1 V1 I1 ∧
   decided N2 V2 I2 ∧
   tot_view.lt V1 V2)
  → height I1 ≤ height I2

invariant [proposed_extend_parent_matches_committed]
  (¬ ctx.is_byz OP ∧ proposed_extend OP V J ∧ parent I J ∧
   committed_ixn OP CI ∧ height I = height CI) → I = CI

invariant [proposed_repropose_parent_matches_committed]
  (¬ ctx.is_byz OP ∧ proposed_repropose OP V J ∧ parent I J ∧
   committed_ixn OP CI ∧ height I = height CI) → I = CI

invariant [unique_decided_at_height]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   decided N1 V1 I1 ∧
   decided N2 V2 I2 ∧
   height I1 = height I2)
  → I1 = I2

invariant [committed_ixn_height_upper_bound]
  (¬ ctx.is_byz N ∧ decided N V I ∧ committed_ixn N CI) → height I ≤ height CI

invariant [genesis_decided_first]
  (decided N V J ∧ J ≠ genesis) →
    ∃ (u : view) (m : node), tot_view.lt u V ∧ decided m u genesis

invariant [committed_implies_parent_committed]
  (decided M V J ∧ parent I J ∧ J ≠ genesis) →
    ∃ (u : view) (n : node), tot_view.lt u V ∧ decided n u I


-- All nodes share the same cur_view (by synchronous set_view).
-- Required to rule out spurious split-view pre-states for locks_analog_*.
invariant [cur_view_global]
  (cur_view N1 V1 ∧ cur_view N2 V2) → V1 = V2

-- An honest node's prevote cannot be at a view later than the current global view.
-- Follows from: honest prevote requires cur_view at that view, combined with cur_view_global.
invariant [prevoted_node_view_bound]
  (¬ ctx.is_byz N2 ∧ cur_view N1 V1 ∧ prevoted_node N2 V2 I) →
    tot_view.le V2 V1

-- An honest node's precommit cannot be at a view later than the current global view.
invariant [precommitted_node_view_bound]
  (¬ ctx.is_byz N2 ∧ cur_view N1 V1 ∧ precommitted_node N2 V2 I) →
    tot_view.le V2 V1

-- ####################################################################
-- # precommit_backed support invariants
-- ####################################################################
-- precommit_backed is a stored ghost set in operator_precommit, where the
-- supermajority precondition guarantees a real precommitted_node quorum.
-- Tied to the underlying quorum by precommit_backed_fwd; no _bwd direction
-- (avoids SMT cost on respond_prevote — the ghost lags the supermajority
-- formation but is set as soon as any operator aggregates the QC).

-- Forward: ghost ⇒ supermajority of precommitted_node exists.
-- Established by operator_precommit's precondition; preserved by monotonicity
-- of precommitted_node (no action ever unsets it).
invariant [precommit_backed_fwd]
  precommit_backed V I →
    (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (n : node), ctx.member n s → precommitted_node n V I)

-- Uniqueness at a view: via precommit_backed_fwd + supermajority intersection
-- + unique_precommit_nodes.
invariant [unique_precommit_backed_at_view]
  (precommit_backed V I1 ∧ precommit_backed V I2) → I1 = I2

-- Uniqueness at a height: if two precommit-backed interactions share a height,
-- they're equal. Closes the equal-height case in locks_analog_precommit without
-- chain descent. Provable via precommit_backed_fwd + supermajorities_intersect_in_honest
-- + unique_locked_at_height (the honest intersector holds precommit locks for
-- both at the shared height, so the locks coincide).
invariant [unique_precommit_backed_at_height]
  (precommit_backed V1 I1 ∧ precommit_backed V2 I2 ∧
   I1 ≠ genesis ∧ I2 ≠ genesis ∧
   height I1 = height I2) → I1 = I2

-- ####################################################################
-- # Simple Invariants
-- ####################################################################

-- Honest nodes cannot prevote on two different interactions in a given view
invariant [unique_prevote_nodes]
  ∀ (v : view) (i1 i2 : interaction) (n : node),
    ¬ ctx.is_byz n → ((prevoted_node n v i1 ∧ prevoted_node n v i2) → i1 = i2)

-- Honest nodes cannot be prevote-locked for different interactions in a given view
invariant [unique_prevote_lock_in_view]
  ∀ (n1 n2 : node) (v : view) (i1 i2 : interaction),
    ¬ (ctx.is_byz n1 ∨ ctx.is_byz n2) → ((locked n1 i1 prevote v ∧ locked n2 i2 prevote v) → i1 = i2)

-- If an honest node has decided, then a quorum has prevote-locked
invariant [decided_only_if_quorum_prevote_locked]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ ctx.is_byz n → ( (decided n v ixn ∧ ixn ≠ genesis) →
      (∃ (s : nodeset), (ctx.supermajority s
        ∧ ∀ (nc : node), ¬ ctx.is_byz nc → (
          ctx.member nc s → ∃ (u : view), (tot_view.le u v ∧ prevoted_node nc v ixn ∧ (locked nc ixn prevote u ∨ locked nc ixn precommit u))) )) )

invariant [unique_locked_at_height]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
    locked N1 I1 precommit V1 ∧ locked N2 I2 precommit V2 ∧
    I1 ≠ genesis ∧ I2 ≠ genesis ∧ height I1 = height I2)
    → I1 = I2

-- Prevote lock implies a quorum prevoted for the interaction
invariant [prevote_lock_only_if_quorum_prevoted]
  locked N I prevote V → (∃ (s : nodeset), ctx.supermajority s ∧
    ∀ (NC : node), ctx.member NC s → prevoted_node NC V I)

-- If honest NC has precommitted for I at V, and honest N has a prevote lock for J at V, then I = J.
invariant [precommit_node_lock_consistency]
  (¬ ctx.is_byz N ∧ ¬ ctx.is_byz NC ∧ precommitted_node NC V I ∧
   locked N J prevote V ∧
   I ≠ genesis ∧ J ≠ genesis) → I = J

-- A single honest node can only have locks on one interaction per view
invariant [unique_lock_interaction_per_view]
  (¬ ctx.is_byz N ∧ locked N I1 S1 V ∧ locked N I2 S2 V) → I1 = I2

-- Cross-node lock uniqueness
invariant [cross_node_unique_lock]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   locked N1 I1 S1 V ∧ locked N2 I2 S2 V ∧
   I1 ≠ genesis ∧ I2 ≠ genesis)
  → I1 = I2

-- Precommit lock implies the node prevoted for the interaction
invariant [precommit_lock_implies_prevoted]
  (¬ ctx.is_byz N ∧ locked N I precommit V ∧ I ≠ genesis) → prevoted_node N V I

invariant [precommit_lock_implies_precommit_backed]
  (locked N I precommit V ∧ I ≠ genesis) → precommit_backed V I

-- Sent locks in prepare phase correspond to actual locks
invariant [locks_sent_only_if_locked]
  sent_lock_in_prepare N V IL SL VL → locked N IL SL VL

-- Genesis locks exist for all nodes
invariant [genesis_lock_existence]
  ∀ (n : node), locked n genesis precommit tot_view.zero

invariant [sent_lock_prepare_implies_cur_view_ge]
  (sent_lock_in_prepare N V IL SL VL ∧ cur_view N VCUR) → tot_view.le V VCUR

invariant [highest_lock_sent]
  sent_lock_in_prepare N V IL SL VL →
    (locked N IL SL VL ∧
     tot_view.lt VL V ∧
     (∀ i' s' v', (tot_view.lt VL v' ∧ tot_view.lt v' V) → ¬ locked N i' s' v') ∧
     (SL = prevote → ¬ locked N IL precommit VL))

invariant [precommit_next_view_discovery]
  ∀ (v v2 : view) (i : interaction), (
    (tot_view.next v v2 ∧
     v ≠ v2 ∧
     (∃ (op : node), (¬ ctx.is_byz op ∧ operator op v2 ∧ prepared_operator op v2)) ∧
     (∃ (m : node), (¬ ctx.is_byz m ∧ prepared_node m v2)) ∧
     i ≠ genesis ∧
     tot_view.zero ≠ v ∧
     (∀ (n : node), (¬ ctx.is_byz n →
      (locked n i precommit v ∧
       cur_stage n v commit ∧
       prepared_node n v2 ∧
       cur_view n v2
      )) )) →
    (∀ (n : node), ¬ ctx.is_byz n →
      sent_lock_in_prepare n v2 i precommit v)
  )

invariant [decided_implies_proposed]
  (¬ ctx.is_byz N ∧ decided N V I ∧ I ≠ genesis) →
    ∃ (op : node), proposed_repropose op V I ∨ proposed_extend op V I

invariant [no_lock_without_parent]
  (locked N I S V ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

invariant [no_decide_without_parent]
  (decided N V I ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

invariant [locked_descends_from_genesis]
  (locked N I S V ∧ I ≠ genesis) → ancestor genesis I

-- ####################################################################
-- # Ghost Consistency Invariants (locked)
-- ####################################################################

invariant [locked_at_view_fwd]
  locked N I S V → locked_at_view N V

invariant [locked_at_view_bwd]
  (¬ ctx.is_byz N ∧ locked_at_view N V) →
    ∃ (I : interaction) (S : stage), locked N I S V

-- ####################################################################
-- # Ancestor Parent Structural Invariants
-- ####################################################################

invariant [ancestor_refl]
  ∀ (I : interaction), ancestor I I

invariant [ancestor_from_parent]
  parent I J → ancestor I J

invariant [ancestor_trans]
  (ancestor I J ∧ ancestor J K) → ancestor I K

invariant [ancestor_antisymm]
  (ancestor I J ∧ ancestor J I) → I = J

invariant [ancestor_height_strict]
  (ancestor I J ∧ I ≠ J) → height I < height J

invariant [no_ancestor_equal_height]
  (height I = height J ∧ I ≠ J) → (¬ ancestor I J ∧ ¬ ancestor J I)

invariant [parent_height]
  parent I J → height J = height I + 1

invariant [ancestor_def_fwd]
  ancestor I J → (I = J ∨ parent I J ∨ ∃ (k : interaction), parent I k ∧ ancestor k J)

invariant [ancestor_def_bwd]
  (I = J ∨ parent I J ∨ ∃ (k : interaction), parent I k ∧ ancestor k J) → ancestor I J

invariant [unique_parent]
  parent J I ∧ parent K I → J = K

invariant [parent_irreflexive]
  ¬ parent I I

invariant [genesis_has_no_parent]
  ¬ parent I genesis

invariant [genesis_height_zero]
  (height I = 0 ∧ (∃ (v : view) (n : node), decided n v I)) ↔ I = genesis

invariant [parent_only_if_proposed]
  parent I J ∧ J ≠ genesis → ∃ (n : node) (v : view), proposed_extend n v J

-- ####################################################################
-- # Supporting Invariants
-- ####################################################################

invariant [unique_cur_view]
  cur_view N U ∧ cur_view N V → U = V

invariant [node_has_cur_view]
  ∀ (n : node), ∃ (v : view), cur_view n v

invariant [prepared_only_at_cur_or_past_view]
  (prepared_node N V ∧ ¬ ctx.is_byz N ∧ cur_view N V2) → tot_view.le V V2

invariant [proposed_extend_view_bound]
  (cur_view N1 V1 ∧ proposed_extend N2 V2 I) →
    tot_view.le V2 V1

invariant [proposed_repropose_view_bound]
  (cur_view N1 V1 ∧ proposed_repropose N2 V2 I) →
    tot_view.le V2 V1

invariant [lock_at_most_cur_view]
  (¬ ctx.is_byz N ∧ locked N I S V ∧ I ≠ genesis ∧ cur_view N VCUR)
  → tot_view.le V VCUR

invariant [sent_lock_only_at_past_view]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare N V IL SL VL ∧ cur_view N VCUR) → tot_view.le V VCUR

invariant [unique_stage]
  (¬ ctx.is_byz N ∧ cur_stage N V S1 ∧ cur_stage N V S2) → S1 = S2

invariant [unique_operator]
  (operator N1 V ∧ operator N2 V) → N1 = N2

invariant [proposed_only_by_operator]
  ((proposed_repropose N V I ∨ proposed_extend N V I) ∧ ¬ ctx.is_byz N) → operator N V

invariant [genesis_lock_only_at_zero]
  locked N genesis S V → (V = tot_view.zero ∧ S = precommit)

-- Dual of genesis_lock_only_at_zero: locks at view zero are only the genesis
-- init locks (every node, precommit stage). Init sets locked to exactly
-- (_, genesis, precommit, zero); respond_prevote and respond_precommit both
-- require v ≠ tot_view.zero, so no non-init lock at zero is reachable.
-- Trivially inductive; rules out SMT-planted phantom Byzantine locks at zero.
invariant [lock_at_zero_is_genesis_precommit]
  (locked N I S V ∧ V = tot_view.zero) → (I = genesis ∧ S = precommit)

invariant [lock_stage_valid]
  locked N I S V → (S = prevote ∨ S = precommit)

invariant [locked_only_if_prepared]
  (¬ ctx.is_byz N ∧ locked N I S V ∧ V ≠ tot_view.zero ∧ I ≠ genesis) → prepared_node N V

-- Stage negation invariants
invariant [stage_neg_1]
  ((cur_stage N V precommit ∨ cur_stage N V prevote ∨ cur_stage N V propose
  ∨ cur_stage N V prepare) ∧ I ≠ genesis ∧ ¬ ctx.is_byz N) → ¬ (decided N V I ∨ locked N I precommit V)

invariant [stage_neg_2]
  ((cur_stage N V prevote ∨ cur_stage N V propose
  ∨ cur_stage N V prepare) ∧ I ≠ genesis ∧ ¬ ctx.is_byz N) → ¬ (precommitted_node N V I ∨ precommitted_operator N V I ∨ locked N I S V)

invariant [stage_neg_3]
  ((cur_stage N V propose ∨ cur_stage N V prepare) ∧ I ≠ genesis ∧ ¬ ctx.is_byz N)
  → ¬ (prevoted_node N V I ∨ prevoted_operator N V I ∨ locked N I S V)

invariant [stage_init_prepare]
  (¬ prepared_node N V ∧ ¬ ctx.is_byz N) → cur_stage N V prepare

invariant [stage_neg_4]
  (cur_stage N V prepare ∧ ¬ ctx.is_byz N) →
    ¬ (prepared_node N V ∨ sent_lock_in_prepare N V IL SL VL)

invariant [genesis_not_in_pipeline]
  ¬ ( ¬ ctx.is_byz N ∧ (proposed_repropose N V genesis ∨ proposed_extend N V genesis ∨ prevoted_node N V genesis
  ∨ prevoted_operator N V genesis ∨ precommitted_node N V genesis
  ∨ precommitted_operator N V genesis))

invariant [prevote_stage_implies_prevoted]
  (cur_stage N V prevote ∧ ¬ ctx.is_byz N) → ∃ I, prevoted_node N V I

invariant [precommit_stage_implies_precommitted]
  (cur_stage N V precommit ∧ ¬ ctx.is_byz N) → ∃ I, precommitted_node N V I

invariant [cross_node_unique_prevote]
  (¬ (ctx.is_byz N1 ∨ ctx.is_byz N2) ∧ prevoted_node N1 V I1 ∧ prevoted_node N2 V I2) → I1 = I2

invariant [precommit_nodes_only_if_prevoted_for_same_ixn]
  (¬ ctx.is_byz N ∧ precommitted_node N V I) → prevoted_node N V I

invariant [precommitted_node_implies_lock]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ ctx.is_byz n → ((precommitted_node n v ixn ∧ ixn ≠ genesis) →
      ∃ (u : view), tot_view.le u v ∧ (locked n ixn prevote u ∨ locked n ixn precommit u))

invariant [precommit_quorum_prevoted_and_locked]
  (¬ ctx.is_byz NC ∧ precommitted_node NC V IXN ∧ IXN ≠ genesis) →
  (prevoted_node NC V IXN ∧
   ∃ (U : view), tot_view.le U V ∧ (locked NC IXN prevote U ∨ locked NC IXN precommit U))

invariant [decide_only_if_precommit_operator]
  (¬ ctx.is_byz N ∧ decided OP V I ∧ I ≠ genesis) → (∃ (op : node), (operator op V ∧ precommitted_operator op V I))

invariant [stage_2]
  (cur_stage N V prevote ∧ ¬ ctx.is_byz N)
  → (∃ (i : interaction), ((∃ (op : node), proposed_repropose op V i ∨ proposed_extend op V i) ∧ prevoted_node N V i) ∨ (∃ (op : node), proposed_nil op V))

invariant [unique_proposal]
  ¬ (ctx.is_byz N1 ∨ ctx.is_byz N2) → ( ((proposed_repropose N1 V I1 ∨ proposed_extend N1 V I1) ∧ (proposed_repropose N2 V I2 ∨ proposed_extend N2 V I2)) → (I1 = I2 ∧ N1 = N2) )

invariant [unique_proposed_interaction]
  ((proposed_repropose N V I1 ∨ proposed_extend N V I1) ∧ (proposed_repropose N V I2 ∨ proposed_extend N V I2)) → I1 = I2

invariant [prevote_implies_proposed]
  (prevoted_node N V I ∧ ¬ ctx.is_byz N) → (∃ (op : node), (operator op V ∧ (proposed_repropose op V I ∨ proposed_extend op V I)))

invariant [precommit_only_if_propose]
  (¬ ctx.is_byz N ∧ precommitted_node N V I) → (∃ (op : node), operator op V ∧ (proposed_repropose op V I ∨ proposed_extend op V I))

invariant [prepare_response_only_on_prepare]
  ¬ ctx.is_byz N → (prepared_node N V → ∃ (op : node), operator op V ∧ prepared_operator op V)

invariant [prevote_only_by_operator]
  ¬ ctx.is_byz N → (prevoted_operator OP V I → operator OP V)

invariant [precommit_only_by_operator]
  (¬ ctx.is_byz OP ∧ precommitted_operator OP V I) → operator OP V

invariant [prepared_node_has_lock_sent]
  (¬ ctx.is_byz N ∧ prepared_node N V ∧ V ≠ tot_view.zero ∧
   locked N IL SL VL ∧
   tot_view.lt VL V ∧
   (∀ (vl2 : view), (tot_view.lt VL vl2 ∧ tot_view.lt vl2 V) → ¬ ∃ (i2 : interaction) (s2 : stage), locked N i2 s2 vl2) ∧
   (SL = prevote → ¬ locked N IL precommit VL))
  → sent_lock_in_prepare N V IL SL VL

invariant [decision_requires_precommit_lock]
  (¬ ctx.is_byz N ∧ decided N V I ∧ I ≠ genesis) → locked N I precommit V

invariant [decisions_not_from_higher_views]
  (cur_view N V ∧ decided N U I) → tot_view.le U V

invariant [genesis_view_zero]
  (¬ ctx.is_byz N ∧ decided N V I ∧ tot_view.zero = V) → I = genesis

invariant [genesis_decided_at_zero]
  ∀ (n : node), decided n tot_view.zero genesis

invariant [decide_only_if_quorum_precommit]
  (¬ ctx.is_byz N ∧ decided N V I ∧ I ≠ genesis) →
    (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (n : node), ctx.member n s → precommitted_node n V I)

invariant [prevote_operator_only_if_quorum_prevoted]
  ¬ ctx.is_byz N → (prevoted_operator N V I →
    (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (NC : node), ctx.member NC s → prevoted_node NC V I))

invariant [precommit_operator_only_if_quorum_precommit]
  ¬ ctx.is_byz OP → (precommitted_operator OP V I →
    (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (n : node), ctx.member n s → precommitted_node n V I))

invariant [unique_lock_sent]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare N V IL1 SL1 VL1 ∧ sent_lock_in_prepare N V IL2 SL2 VL2) →
    (IL1 = IL2 ∧ SL1 = SL2 ∧ VL1 = VL2)

invariant [unique_precommit_nodes]
  (¬ ctx.is_byz N ∧ precommitted_node N V I ∧ precommitted_node N V J) → I = J

invariant [unique_prevote_operator]
  (¬ ctx.is_byz OP ∧ prevoted_operator OP V I ∧ prevoted_operator OP V J) → I = J

invariant [unique_precommit_operator]
  (¬ ctx.is_byz OP ∧ precommitted_operator OP V I ∧ precommitted_operator OP V J) → I = J

invariant [sent_lock_only_if_prepare]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare N V IL SL VL) → prepared_node N V

invariant [sent_lock_only_if_prepare_unrestricted]
  sent_lock_in_prepare N V IL SL VL → prepared_node N V

invariant [stage_1]
  (cur_stage N V propose ∧ ¬ ctx.is_byz N) →
    (∃ (il : interaction) (sl : stage) (vl : view), sent_lock_in_prepare N V il sl vl)

invariant [stage_3]
  (cur_stage N V precommit ∧ ¬ ctx.is_byz N) →
    (∃ (i : interaction), (prevoted_operator N V i ∨ precommitted_node N V i) ∧
     (locked N i prevote V ∨ (∃ (u : view), tot_view.le u V ∧ locked N i precommit u)))

invariant [stage_4]
  (cur_stage N V commit ∧ ¬ ctx.is_byz N) →
    (∃ (i : interaction), (precommitted_operator N V i ∨ decided N V i) ∧ locked N i precommit V)

invariant [prepared_operator_not_at_zero]
  (prepared_operator OP V ∧ ¬ ctx.is_byz OP) → V ≠ tot_view.zero

invariant [propose_only_if_operator_prepare]
  (¬ ctx.is_byz N ∧ (proposed_repropose N V I ∨ proposed_extend N V I)) → prepared_operator N V

invariant [propose_only_if_parent_locked]
  (¬ ctx.is_byz OP ∧ proposed_extend OP V J ∧ parent I J) →
    (∃ (u : view) (n : node) (s : stage), tot_view.le u V ∧ locked n I s u)

-- ####################################################################
-- # Committed State Invariants
-- ####################################################################

invariant [unique_committed_ixn]
  (committed_ixn N I1 ∧ committed_ixn N I2) → I1 = I2

invariant [node_has_committed_ixn]
  ∀ (n : node), ∃ (i : interaction), committed_ixn n i

invariant [committed_ixn_decided]
  (¬ ctx.is_byz N ∧ committed_ixn N I) →
    ∃ (V : view), decided N V I

invariant [committed_ixn_is_genesis_or_has_parent]
  (¬ ctx.is_byz N ∧ committed_ixn N I ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

invariant [committed_ixn_descends_from_genesis]
  (¬ ctx.is_byz N ∧ committed_ixn N I) → ancestor genesis I

invariant [committed_ixn_precommit_locked]
  (¬ ctx.is_byz N ∧ committed_ixn N I ∧ I ≠ genesis) →
    ∃ (V : view), locked N I precommit V

invariant [committed_ixn_unique_at_height]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   committed_ixn N1 I1 ∧ committed_ixn N2 I2 ∧
   height I1 = height I2) → I1 = I2

invariant [committed_ixn_height_positive]
  (¬ ctx.is_byz N ∧ committed_ixn N I ∧ I ≠ genesis) → height I ≥ 1

-- ####################################################################
-- # Height Positivity Invariants
-- ####################################################################

invariant [locked_height_positive]
  (locked N I S V ∧ I ≠ genesis) → height I ≥ 1

invariant [proposed_height_positive]
  ((proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ I ≠ genesis) →
    height I ≥ 1

invariant [decided_height_positive]
  (decided N V I ∧ I ≠ genesis) → height I ≥ 1

invariant [prevoted_height_positive]
  (¬ ctx.is_byz N ∧ prevoted_node N V I ∧ I ≠ genesis) → height I ≥ 1


set_option veil.smt.timeout 15000
set_option maxHeartbeats 4000000
#gen_spec

set_option veil.printCounterexamples true

#check_action propose_extendx
-- #check_action respond_propose_extend
-- #check_invariants


end IFPProtocolNTDPH
