-- IFPNT: IFPN extended with Tendermint-style precommit_backed ghost +
-- locks_analog invariants. Routes safety through a lock-propagation bundle
-- mirroring the `locks` invariant in tendermint/spec/ivy-proofs/classic_safety.ivy.
--
-- precommit_backed is a stored ghost relation, set inside operator_precommit
-- (whose precondition guarantees a real supermajority of precommitted_node,
-- regardless of operator honesty). Only the forward direction (ghost ⇒ quorum
-- witness) is asserted; no _bwd, so SMT doesn't have to flip the ghost on
-- respond_prevote's state changes.
--
-- Delta from IFPN:
--   - relation precommit_backed : view → interaction → Bool
--   - ghost set in operator_precommit
--   - invariants: precommit_backed_fwd,
--                 precommitted_operator_implies_precommit_backed,
--                 unique_precommit_backed_at_view,
--                 decided_implies_precommit_backed,
--                 locks_analog_precommit,
--                 cur_view_global, prevoted_node_view_bound,
--                 precommitted_node_view_bound

import Veil

veil module IFPProtocolNT


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

-- Ghost: a precommit-QC has been aggregated at (V, I).
-- Set by operator_precommit (whose precondition guarantees a real supermajority
-- of precommitted_node, regardless of operator honesty). Tied to that quorum
-- by precommit_backed_fwd. No _bwd direction (avoids SMT cost of asserting
-- the ghost flip on every supermajority change in respond_prevote).
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
  precommit_backed V I := false;
  prepares_collected N V := false;
  op_argmax_ixn   N V I := false;
  op_argmax_stage N V S := false;
  op_argmax_view  N V VL := false;
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

action respond_propose (n : node) (v : view) (ixn : interaction)
    (s : nodeset) (n_max : node) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v propose
  require ∃ (op : node), operator op v ∧ (proposed_repropose op v ixn ∨ proposed_extend op v ixn)
  require ∀ (i : interaction), ¬ prevoted_node n v i
  require ixn ≠ genesis
  -- Outer quorum `s` lifted to action parameter (Tendermint-style).
  require ctx.supermajority s
  require ∀ (m : node), ctx.member m s → (prepared_node m v ∧
    ∃ (vl : view) (ixnl : interaction) (sl : stage) (t : nodeset),
      sent_lock_in_prepare m v ixnl sl vl
      ∧ locked m ixnl sl vl
      ∧ tot_view.le vl v
      ∧ ctx.supermajority t
      ∧ ( sl = prevote → (∀ (nt : node), (ctx.member nt t → prevoted_node nt vl ixnl)) )
      ∧ ( sl = precommit → (∀ (nt : node), (ctx.member nt t → precommitted_node nt vl ixnl)) ))
  let ixn_max : interaction ← pick
  let s_max : stage ← pick
  let v_max : view ← pick
  -- Argmax witness `n_max` lifted to action parameter.
  require sent_lock_in_prepare n_max v ixn_max s_max v_max
  require locked n_max ixn_max s_max v_max
  require ∀ (n_l : node) (ixn_l : interaction) (s_l : stage) (v_l : view),
    sent_lock_in_prepare n_l v ixn_l s_l v_l → (
      height ixn_l < height ixn_max
      ∨ (height ixn_l = height ixn_max ∧ s_l = prevote ∧ s_max = precommit)
      ∨ (height ixn_l = height ixn_max ∧ s_l = s_max ∧ tot_view.le v_l v_max)
      ∨ (ixn_l = ixn_max ∧ s_l = s_max ∧ v_l = v_max)
    )
  -- Valid proposal: repropose or extend
  require s_max = prevote ∨ s_max = precommit
  require (s_max = prevote) → ixn_max = ixn
  require (s_max = precommit) →
    (ixn ≠ ixn_max ∧ parent ixn_max ixn
    ∧ height ixn = height ixn_max + 1)
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
  -- Ghost set: the precondition above is exactly precommit_backed's witness.
  precommit_backed v ixn := true
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
  locked n ixn precommit v := true;
  locked_at_view n v := true;
  decided n v ixn := true
  -- Update committed interaction only if this is a newer decision
  if (∃ (ci_old : interaction), committed_ixn n ci_old ∧ height ixn > height ci_old) then
    committed_ixn n I := decide $ (I = ixn);
  cur_stage n v S := decide $ (S = commit)
}


-- -- (A) Direct parent-equality lifting for repropose. When op reproposes J, the
-- -- parent of J is exactly op's committed_ixn. Provable from
-- --   parent_height (height J = height PI + 1)
-- -- + propose_repropose's `height ixn_max = height ci + 1` and `ixn_max = J`
-- -- + unique_committed_ixn (CI = ci, op's actual committed)
-- -- + proposed_repropose_parent_matches_committed (equal-height ⇒ equal).
-- -- Lifted to a single-step invariant so precommit_backed_repropose_link can
-- -- substitute PI ↦ CI without arithmetic + uniqueness search.
-- invariant [proposed_repropose_parent_is_op_committed]
--   (¬ ctx.is_byz OP ∧ proposed_repropose OP V J ∧
--    parent PI J ∧ committed_ixn OP CI ∧ cur_view OP V) → PI = CI

-- -- (A, extend variant) Same lifting for extend: parent of the freshly-proposed
-- -- interaction is op's committed_ixn. Provable from propose_extend's
-- -- `parent ci ixn_propose := decide $ (ci ≠ ixn_propose)` update + uniqueness.
-- invariant [proposed_extend_parent_is_op_committed]
--   (¬ ctx.is_byz OP ∧ proposed_extend OP V J ∧
--    parent PI J ∧ committed_ixn OP CI) → PI = CI

-- -- (I) Height-bound short-circuit for precommit_backed_repropose_link. Any
-- -- earlier precommit_backed I has strictly smaller height than the reproposed J.
-- -- Provable from
-- --   op_committed_height_ge_precommit_backed (height I ≤ height CI, where CI
-- --     is op's committed_ixn at V2 — uses cur_view OP V2 from
-- --     prepared_only_at_cur_or_past_view applied to op's prepared_node V2)
-- -- + propose_repropose's `height J = height ci + 1` and uniqueness CI = ci.
-- -- Closes the V = v_max corner case where SMT might otherwise try to derive
-- -- I = J = ixn_max via a long cross-node uniqueness chain: now `height I < height J`
-- -- excludes I = J structurally.
-- invariant [precommit_backed_height_lt_repropose]
--   ∀ (V V2 : view) (I J : interaction) (OP : node),
--     (¬ ctx.is_byz OP ∧ I ≠ genesis ∧
--      precommit_backed V I ∧ proposed_repropose OP V2 J ∧
--      tot_view.lt V V2) →
--     height I < height J

-- -- (1) Operator is also prepared as a node (i.e., responded to its own prepare),
-- -- per Option A's `require prepared_node op v` in the propose actions. Lifted
-- -- as an invariant so downstream proofs can chain prepared_node OP V →
-- -- sent_lock_in_prepare OP V _ _ _ (via prepared_node_has_lock_sent) without
-- -- re-deriving from the action body.
-- invariant [propose_only_if_self_prepared]
--   ((proposed_repropose OP V J ∨ proposed_extend OP V J) ∧ ¬ ctx.is_byz OP) →
--     prepared_node OP V

-- -- (2) Op's locks (any stage) at past views are bounded by the height of the
-- -- proposed interaction. Provable for the precommit case directly via
-- -- precommit_lock_height_le_committed + proposed_parent_height_le_committed +
-- -- parent_height. The prevote case is closed by Option A: op's prepared, so
-- -- op's highest lock is in sent_lock_in_prepare and dominated by argmax view;
-- -- combined with per-node lock_height_monotone and cross-node prevote-lock
-- -- uniqueness at v_max, op's prevote-lock height is bounded by ixn_max's
-- -- height, which equals height J for repropose (height ci + 1) and is at most
-- -- height J − 1 for extend (op's locks ≤ height committed = height J − 1).
-- invariant [proposed_op_lock_height_bound]
--   ((proposed_repropose OP V J ∨ proposed_extend OP V J) ∧
--    ¬ ctx.is_byz OP ∧ locked OP I S U ∧ tot_view.lt U V) →
--     height I ≤ height J

-- -- Lifts propose_repropose's argmax-witness precondition into a state invariant:
-- -- when op reproposes J at view V, the argmax witness `n_max` holds
-- -- `locked n_max J prevote v_max` for some v_max < V. By
-- -- prevote_lock_only_if_quorum_prevoted, that lock is itself backed by a
-- -- prevote-QC for J at v_max. Since proposed_repropose and prevoted_node are
-- -- both monotonic, the witness is preserved across all subsequent actions.
-- -- Lock-propagation hook: feeds locks_analog_precommit by giving a quorum
-- -- whose intersection with any earlier precommit_backed quorum yields an
-- -- honest node who prevoted both interactions.
-- invariant [repropose_implies_prevote_qc]
--   proposed_repropose OP V J →
--     ∃ (v_max : view), tot_view.lt v_max V ∧
--       ∃ (t : nodeset), ctx.supermajority t ∧
--         ∀ (nt : node), ctx.member nt t → prevoted_node nt v_max J


-- -- Height-only weakening of op_committed_descends_from_precommit_backed.
-- -- Pure height bound: any earlier precommit_backed has height ≤ OP's current
-- -- committed_ixn height. Cheaper for SMT (no ancestor reasoning) and feeds the
-- -- propose_repropose case where height(ixn_max) = height(ci) + 1.
-- invariant [op_committed_height_ge_precommit_backed]
--   ∀ (V V2 : view) (I CI : interaction) (OP : node),
--     (¬ ctx.is_byz OP ∧ I ≠ genesis ∧
--      precommit_backed V I ∧ tot_view.lt V V2 ∧
--      committed_ixn OP CI ∧ cur_view OP V2) →
--     height I ≤ height CI

-- -- Decomposition (B), parent-localized form (parallel to precommit_backed_extend_link).
-- -- Conclusion uses bare `ancestor I PI` (equivalent to `I = PI ∨ ancestor I PI`
-- -- via ancestor_refl) to avoid SMT case-splits on the disjunction.
-- invariant [precommit_backed_repropose_link]
--   ∀ (V V2 : view) (I J PI : interaction) (OP : node),
--     (¬ ctx.is_byz OP ∧ I ≠ genesis ∧ J ≠ genesis ∧
--      precommit_backed V I ∧ tot_view.lt V V2 ∧
--      proposed_repropose OP V2 J ∧ parent PI J) →
--     ancestor I PI

-- -- Decomposition (B), extend variant. Conclusion bare-ancestor form for the
-- -- same SMT reason.
-- invariant [precommit_backed_extend_link]
--   ∀ (V V2 : view) (I I2 PI : interaction) (OP : node),
--     (¬ ctx.is_byz OP ∧ I ≠ genesis ∧ I2 ≠ genesis ∧
--      precommit_backed V I ∧ tot_view.lt V V2 ∧
--      proposed_extend OP V2 I2 ∧ parent PI I2) →
--     ancestor I PI

-- -- Bridge (C): the operator's committed_ixn at a later view descends from any
-- -- earlier precommit-backed interaction. Bare-ancestor conclusion as above.
-- invariant [op_committed_descends_from_precommit_backed]
--   ∀ (V V2 : view) (I CI : interaction) (OP : node),
--     (¬ ctx.is_byz OP ∧ I ≠ genesis ∧
--      precommit_backed V I ∧ tot_view.lt V V2 ∧
--      committed_ixn OP CI ∧ cur_view OP V2) →
--     ancestor I CI

-- -- Height-only weakening of locks_analog_precommit. Decouples the height bound
-- -- from the chain (ancestor) conclusion. Provable by quorum intersection +
-- -- prevote_justified_by_own_highest_lock + lock_height_monotone alone, without
-- -- the height-to-ancestor bridge. Once this verifies, locks_analog_precommit can
-- -- route the (pre, new) substantive case through it: equal-height ⇒
-- -- unique_locked_at_height; strict ⇒ recursive descent through parent_height
-- -- and ancestor_from_parent.
-- invariant [precommit_backed_height_le]
--   ∀ (V V2 : view) (I I2 : interaction),
--     (I ≠ genesis ∧ I2 ≠ genesis ∧
--      precommit_backed V I ∧ precommit_backed V2 I2 ∧
--      tot_view.lt V V2) →
--     height I ≤ height I2

-- -- ####################################################################
-- -- # op_argmax cache invariants (S8 — Tendermint-style aggregation)
-- -- ####################################################################

-- -- Functional behaviour: at most one value per (op, v) per dimension.
-- -- Discharged by collect_prepares' `decide` update templates.
-- invariant [op_argmax_ixn_unique]
--   (op_argmax_ixn OP V I1 ∧ op_argmax_ixn OP V I2) → I1 = I2

-- invariant [op_argmax_stage_unique]
--   (op_argmax_stage OP V S1 ∧ op_argmax_stage OP V S2) → S1 = S2

-- invariant [op_argmax_view_unique]
--   (op_argmax_view OP V VL1 ∧ op_argmax_view OP V VL2) → VL1 = VL2

-- -- Existence iff prepares collected, per dimension. Split forms (no ↔) for
-- -- simp tractability.
-- invariant [op_argmax_ixn_implies_collected]
--   op_argmax_ixn OP V I → prepares_collected OP V

-- invariant [op_argmax_stage_implies_collected]
--   op_argmax_stage OP V S → prepares_collected OP V

-- invariant [op_argmax_view_implies_collected]
--   op_argmax_view OP V VL → prepares_collected OP V

-- invariant [collected_implies_op_argmax_ixn]
--   prepares_collected OP V → ∃ (I : interaction), op_argmax_ixn OP V I

-- invariant [collected_implies_op_argmax_stage]
--   prepares_collected OP V → ∃ (S : stage), op_argmax_stage OP V S

-- invariant [collected_implies_op_argmax_view]
--   prepares_collected OP V → ∃ (VL : view), op_argmax_view OP V VL

-- -- Argmax cache faithfully reflects the highest sent-lock at v (for honest op).
-- -- Discharged by the argmax + gap requires inside collect_prepares.
-- invariant [op_argmax_is_highest_lock]
--   (¬ ctx.is_byz OP ∧ op_argmax_ixn OP V IM ∧ op_argmax_stage OP V SM ∧ op_argmax_view OP V VM) →
--     (∃ (N : node), sent_lock_in_prepare N V IM SM VM ∧ locked N IM SM VM) ∧
--     (∀ (N : node) (IL : interaction) (SL : stage) (VL : view),
--        sent_lock_in_prepare N V IL SL VL → tot_view.le VL VM)

-- -- Argmax interaction is QC-backed at its claimed (view, stage) for honest op.
-- -- Discharged by the per-member QC-backing requires inside collect_prepares.
-- invariant [op_argmax_qc_backed]
--   (¬ ctx.is_byz OP ∧ op_argmax_ixn OP V IM ∧ op_argmax_stage OP V SM ∧ op_argmax_view OP V VM) →
--     (SM = prevote → ∃ (Q : nodeset), ctx.supermajority Q ∧
--        ∀ (N : node), ctx.member N Q → prevoted_node N VM IM) ∧
--     (SM = precommit → ∃ (Q : nodeset), ctx.supermajority Q ∧
--        ∀ (N : node), ctx.member N Q → precommitted_node N VM IM)


safety [main_safety]
  ∀ (n1 n2 : node) (v1 v2 : view) (i1 i2 : interaction),
    (¬ ctx.is_byz n1 ∧ ¬ ctx.is_byz n2 ∧
     decided n1 v1 i1 ∧
     decided n2 v2 i2) →
    (ancestor i1 i2 ∨ ancestor i2 i1)

-- Bridge: precommitted_node directly implies a prevote-QC was aggregated
-- (mirrors respond_prevote's `∃ op. operator op v ∧ prevoted_operator op v ixn`
-- precondition lifted into a state invariant, with the operator-role guard).
invariant [precommitted_node_implies_prevote_qc]
  precommitted_node N V I → (∃ (op : node), operator op V ∧ prevoted_operator op V I)

  invariant [locks_analog_precommit]
    ∀ (V V2 : view) (I I2 : interaction),
      (I ≠ genesis ∧ I2 ≠ genesis ∧
       precommit_backed V I ∧ precommit_backed V2 I2 ∧
       tot_view.lt V V2) →
      (I = I2 ∨ ancestor I I2)

  -- Bridge for main_safety to feed this invariant.
  invariant [decided_implies_precommit_backed]
    (¬ ctx.is_byz N ∧ decided N V I ∧ I ≠ genesis) → precommit_backed V I

-- Bridge: precommitted_operator entails precommit_backed at the same (V, I).
-- precommitted_operator is only written by operator_precommit, which sets
-- precommit_backed at the same call. So at the moment precommitted_operator
-- becomes true, precommit_backed becomes true too. Both monotonic.
-- Required so that decided_implies_precommit_backed can chain through
-- respond_precommit's `∃ op. operator op v ∧ precommitted_operator op v ixn`
-- precondition to derive precommit_backed.
invariant [precommitted_operator_implies_precommit_backed]
  precommitted_operator OP V I → precommit_backed V I

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
-- # Main Safety Property
-- ####################################################################


-- An honest non-genesis prevote at non-zero V is justified by N's OWN most-recent
-- lock (at v_max < V): the lock either is a prevote-lock on I, or a precommit-lock
-- whose ixn is the parent of I. Lifts respond_propose's argmax precondition (over
-- sent_lock_in_prepare, which by sent_lock_only_if_prepare/locks_sent_only_if_locked
-- captures N's own locks when N is prepared at V) into a state invariant.
invariant [prevote_justified_by_own_highest_lock]
  (¬ ctx.is_byz N ∧ prevoted_node N V I ∧ I ≠ genesis ∧ V ≠ tot_view.zero) →
    ∃ (ixn_max : interaction) (s_max : stage) (v_max : view),
      locked N ixn_max s_max v_max ∧
      tot_view.lt v_max V ∧
      ((s_max = prevote ∧ ixn_max = I) ∨
       (s_max = precommit ∧ parent ixn_max I)) ∧
      (∀ (i' : interaction) (s' : stage) (v' : view),
         locked N i' s' v' ∧ tot_view.lt v' V →
         tot_view.le v' v_max)
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

-- ####################################################################
-- # locks_analog — Tendermint-style lock-propagation bundle
-- ####################################################################

-- If I was precommit-backed at V, then any honest node's later prevote
-- must be on I or a descendant of I (mirrors Tendermint's `locks` invariant's
-- prevote clause).
-- invariant [locks_analog_prevote]
--   ∀ (V V2 : view) (I I2 : interaction) (N : node),
--     (¬ ctx.is_byz N ∧
--      I ≠ genesis ∧
--      precommit_backed V I ∧
--      tot_view.lt V V2 ∧
--      prevoted_node N V2 I2) →
--     (I2 = I ∨ ancestor I I2)

-- If I was precommit-backed at V, then any honest node's precommit at V' ≥ V
-- sits on I's chain (ancestor relation in either direction).


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
-- # Core Invariants
-- ####################################################################

-- INV1: Honest nodes cannot prevote on two different interactions in a given view
invariant [INV1_unique_prevote_nodes]
  ∀ (v : view) (i1 i2 : interaction) (n : node),
    ¬ ctx.is_byz n → ((prevoted_node n v i1 ∧ prevoted_node n v i2) → i1 = i2)

-- INV2: Honest nodes cannot be prevote-locked for different interactions in a given view
invariant [INV2_unique_prevote_lock_in_view]
  ∀ (n1 n2 : node) (v : view) (i1 i2 : interaction),
    ¬ (ctx.is_byz n1 ∨ ctx.is_byz n2) → ((locked n1 i1 prevote v ∧ locked n2 i2 prevote v) → i1 = i2)

-- INV3: If an honest node has decided, then a quorum has prevote-locked
invariant [INV3_decided_only_if_quorum_prevote_locked]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ ctx.is_byz n → ( (decided n v ixn ∧ ixn ≠ genesis) →
      (∃ (s : nodeset), (ctx.supermajority s
        ∧ ∀ (nc : node), ¬ ctx.is_byz nc → (
          ctx.member nc s → ∃ (u : view), (tot_view.le u v ∧ prevoted_node nc v ixn ∧ (locked nc ixn prevote u ∨ locked nc ixn precommit u))) )) )

 -- ####################################################################
-- # Height-Based Uniqueness Invariants
-- ####################################################################

invariant [unique_locked_at_height]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
    locked N1 I1 precommit V1 ∧ locked N2 I2 precommit V2 ∧
    I1 ≠ genesis ∧ I2 ≠ genesis ∧ height I1 = height I2)
    → I1 = I2

-- ####################################################################
-- # Safety Routing Lemmas
-- ####################################################################

-- -- Same view: two honest decisions at the same view agree.
-- invariant [safety_same_view]
--   ∀ (N1 N2 : node) (V : view) (I1 I2 : interaction),
--     (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
--      decided N1 V I1 ∧ decided N2 V I2) →
--     I1 = I2

-- -- Cross view: the earlier decision is on the ancestor chain of the later.
-- invariant [safety_cross_view]
--   ∀ (N1 N2 : node) (V1 V2 : view) (I1 I2 : interaction),
--     (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
--      decided N1 V1 I1 ∧ decided N2 V2 I2 ∧
--      tot_view.lt V1 V2) →
--     (I1 = I2 ∨ ancestor I1 I2)

-- Supporting: Prevote lock implies a quorum prevoted for the interaction
invariant [prevote_lock_only_if_quorum_prevoted]
  locked N I prevote V → (∃ (s : nodeset), ctx.supermajority s ∧
    ∀ (NC : node), ctx.member NC s → prevoted_node NC V I)

-- Supporting (cross-node): If honest NC has precommitted for I at V, and honest N has a prevote lock
-- for J at V, then I = J.
invariant [precommit_node_lock_consistency]
  (¬ ctx.is_byz N ∧ ¬ ctx.is_byz NC ∧ precommitted_node NC V I ∧
   locked N J prevote V ∧
   I ≠ genesis ∧ J ≠ genesis) → I = J

-- Supporting: A single honest node can only have locks on one interaction per view
invariant [unique_lock_interaction_per_view]
  (¬ ctx.is_byz N ∧ locked N I1 S1 V ∧ locked N I2 S2 V) → I1 = I2

-- Cross-node lock uniqueness
invariant [cross_node_unique_lock]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   locked N1 I1 S1 V ∧ locked N2 I2 S2 V ∧
   I1 ≠ genesis ∧ I2 ≠ genesis)
  → I1 = I2

-- Supporting: Precommit lock implies the node prevoted for the interaction
invariant [precommit_lock_implies_prevoted]
  (¬ ctx.is_byz N ∧ locked N I precommit V ∧ I ≠ genesis) → prevoted_node N V I

-- Supporting: Sent locks in prepare phase correspond to actual locks
invariant [locks_sent_only_if_locked]
  sent_lock_in_prepare N V IL SL VL → locked N IL SL VL

-- Supporting: Genesis locks exist for all nodes
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

-- Stepping stone for INV4: consecutive view case
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

-- ####################################################################
-- # Freshness Invariants
-- ####################################################################

invariant [no_lock_without_parent]
  (locked N I S V ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

invariant [no_proposal_without_parent]
  ((proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

invariant [no_decide_without_parent]
  (decided N V I ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

-- ####################################################################
-- # Genesis Ancestry Invariants
-- ####################################################################

invariant [proposed_descends_from_genesis]
  ((proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ I ≠ genesis) → ancestor genesis I

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
-- # Decision–Proposal Linking Invariant
-- ####################################################################

invariant [decided_implies_proposed]
  (¬ ctx.is_byz N ∧ decided N V I ∧ I ≠ genesis) →
    ∃ (op : node), proposed_repropose op V I ∨ proposed_extend op V I

-- ####################################################################
-- # Ancestor Structural Invariants
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


-- ####################################################################
-- # Supporting Invariants (structural)
-- ####################################################################

invariant [unique_cur_view]
  cur_view N U ∧ cur_view N V → U = V

invariant [node_has_cur_view]
  ∀ (n : node), ∃ (v : view), cur_view n v

invariant [prepared_only_at_cur_or_past_view]
  (prepared_node N V ∧ ¬ ctx.is_byz N ∧ cur_view N V2) → tot_view.le V V2

invariant [proposed_extend_view_bound]
  (¬ ctx.is_byz N2 ∧ cur_view N1 V1 ∧ proposed_extend N2 V2 I) →
    tot_view.le V2 V1

invariant [proposed_repropose_view_bound]
  (¬ ctx.is_byz N2 ∧ cur_view N1 V1 ∧ proposed_repropose N2 V2 I) →
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

-- Cross-node unique prevote
invariant [cross_node_unique_prevote]
  (¬ (ctx.is_byz N1 ∨ ctx.is_byz N2) ∧ prevoted_node N1 V I1 ∧ prevoted_node N2 V I2) → I1 = I2

-- Precommitted node implies it prevoted for the same interaction
invariant [precommit_nodes_only_if_prevoted_for_same_ixn]
  (¬ ctx.is_byz N ∧ precommitted_node N V I) → prevoted_node N V I

-- Precommitted node implies a lock exists for it
invariant [precommitted_node_implies_lock]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ ctx.is_byz n → ((precommitted_node n v ixn ∧ ixn ≠ genesis) →
      ∃ (u : view), tot_view.le u v ∧ (locked n ixn prevote u ∨ locked n ixn precommit u))

invariant [precommit_quorum_prevoted_and_locked]
  (¬ ctx.is_byz NC ∧ precommitted_node NC V IXN ∧ IXN ≠ genesis) →
  (prevoted_node NC V IXN ∧
   ∃ (U : view), tot_view.le U V ∧ (locked NC IXN prevote U ∨ locked NC IXN precommit U))

-- Decision requires a precommit operator
invariant [decide_only_if_precommit_operator]
  (¬ ctx.is_byz N ∧ decided OP V I ∧ I ≠ genesis) → (∃ (op : node), (operator op V ∧ precommitted_operator op V I))

-- At prevote stage, node prevoted for the proposed interaction
invariant [stage_2]
  (cur_stage N V prevote ∧ ¬ ctx.is_byz N)
  → (∃ (i : interaction), ((∃ (op : node), proposed_repropose op V i ∨ proposed_extend op V i) ∧ prevoted_node N V i) ∨ (∃ (op : node), proposed_nil op V))

-- Only one proposal per view
invariant [unique_proposal]
  ¬ (ctx.is_byz N1 ∨ ctx.is_byz N2) → ( ((proposed_repropose N1 V I1 ∨ proposed_extend N1 V I1) ∧ (proposed_repropose N2 V I2 ∨ proposed_extend N2 V I2)) → (I1 = I2 ∧ N1 = N2) )

invariant [unique_proposed_interaction]
  ((proposed_repropose N V I1 ∨ proposed_extend N V I1) ∧ (proposed_repropose N V I2 ∨ proposed_extend N V I2)) → I1 = I2

-- Honest node prevoted → a proposal exists
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

-- ####################################################################
-- # Decision Invariants
-- ####################################################################

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

-- ####################################################################
-- # Ancestor/Parent Structural Invariants (additional)
-- ####################################################################

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
-- # Operator/Quorum Invariants
-- ####################################################################

invariant [prevote_operator_only_if_quorum_prevoted]
  ¬ ctx.is_byz N → (prevoted_operator N V I →
    (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (NC : node), ctx.member NC s → prevoted_node NC V I))

invariant [precommit_operator_only_if_quorum_precommit]
  ¬ ctx.is_byz OP → (precommitted_operator OP V I →
    (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (n : node), ctx.member n s → precommitted_node n V I))

-- ####################################################################
-- # Uniqueness Invariants (additional)
-- ####################################################################

invariant [unique_lock_sent]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare N V IL1 SL1 VL1 ∧ sent_lock_in_prepare N V IL2 SL2 VL2) →
    (IL1 = IL2 ∧ SL1 = SL2 ∧ VL1 = VL2)

invariant [unique_precommit_nodes]
  (¬ ctx.is_byz N ∧ precommitted_node N V I ∧ precommitted_node N V J) → I = J

invariant [unique_prevote_operator]
  (¬ ctx.is_byz OP ∧ prevoted_operator OP V I ∧ prevoted_operator OP V J) → I = J

invariant [unique_precommit_operator]
  (¬ ctx.is_byz OP ∧ precommitted_operator OP V I ∧ precommitted_operator OP V J) → I = J

-- ####################################################################
-- # Additional Supporting Invariants
-- ####################################################################

invariant [sent_lock_only_if_prepare]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare N V IL SL VL) → prepared_node N V

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
-- # View-Height Monotonicity Invariants
-- ####################################################################

invariant [prevoted_height_ge_locks]
  (¬ ctx.is_byz N ∧ prevoted_node N V I ∧ I ≠ genesis ∧
   locked N J S U ∧ tot_view.lt U V)
  → height J ≤ height I

invariant [lock_height_monotone]
  (¬ ctx.is_byz N ∧
   locked N I1 S1 V1 ∧ locked N I2 S2 V2 ∧
   tot_view.le V1 V2)
  → height I1 ≤ height I2

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


set_option veil.smt.timeout 13000
#gen_spec

set_option veil.printCounterexamples true

#check_action collect_prepares


-- theorem operator_precommit_locks_analog_precommit (ρ : Type) (σ : Type) (view : Type)
--     [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
--     [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
--     [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
--     (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
--     (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
--     [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
--     [χ_rep :
--       ∀ __veil_f,
--         Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
--           (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
--     [χ_rep_lawful :
--       ∀ __veil_f,
--         Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
--           (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
--     [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
--     [operator_precommit_dec_0 :
--       delta% @IFPProtocolNT._veil_dec_type_907530 view interaction χ nodeset node ctx stage χ_rep] :
--     ∀ (op : node) (v : view) (ixn : interaction),
--       Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
--         (@operator_precommit.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
--           interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
--           stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub operator_precommit_dec_0 op v ixn)
--         (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
--           interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
--           ρ_sub)
--         (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
--           interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
--           χ χ_rep χ_rep_lawful σ_sub ρ_sub)
--         (@locks_analog_precommit ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
--           interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
--           stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
--   by
--   veil_human
--   intro hv_nz hcv hop hcs x hsm hpc V V2 I I2 hI hI2 hb1 hb2 hlt
--   -- Destructure hinv. precommit_backed_height_le is now declared at the top of
--   -- the invariant block (before safety), so it sits at position 1 and all other
--   -- invariants are shifted +1 from the original layout.
--   -- Positions: 1=precommit_backed_height_le (h_pbhl), 4=locks_analog_precommit (IH),
--   -- 8=precommit_node_locked_at_same_view, 10=prevote_justified_by_own_highest_lock,
--   -- 22=precommitted_node_view_bound, 23=precommit_backed_fwd,
--   -- 28=unique_locked_at_height, 33=precommit_lock_implies_prevoted,
--   -- 48=ancestor_from_parent, 49=ancestor_trans, 51=ancestor_height_strict,
--   -- 52=no_ancestor_equal_height, 53=parent_height,
--   -- 76=precommit_nodes_only_if_prevoted_for_same_ixn. Trailing `_` catches rest.
--   obtain ⟨h_pbhl, _, _, h_lap, _, _, _, h_pcnlsv, _, h_pjohl, _, _, _, _, _, _, _, _, _,
--           _, _, h_pcnvb, h_pbf, _, _, _, _, h_ulh, _, _, _, _, h_pcli, _, _,
--           _, _, _, _, _, _, _, _, _, _, _, _, h_afp, h_atrans, _, h_ahs, h_naeh,
--           h_ph, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
--           _, h_pcn_pv, _⟩ := hinv
--   by_cases h1new : V = v ∧ I = ixn
--   · -- Case: (V, I) = (v, ixn). After subst, v↦V and ixn↦I (Lean eliminates the RHS).
--     obtain ⟨hVeq, hIeq⟩ := h1new
--     subst hVeq
--     subst hIeq
--     -- Inner case-split now uses the surviving names V, I.
--     by_cases h2new : V2 = V ∧ I2 = I
--     · -- Both new: I = I2, left disjunct holds
--       obtain ⟨_, hI2eq⟩ := h2new
--       subst hI2eq
--       exact Or.inl rfl
--     · -- (new, pre): impossible — pre-state precommit_backed V2 I2 with V2 > V (=action's v)
--       -- contradicts cur_view op V via precommit_backed_fwd + quorum-honest + precommitted_node_view_bound.
--       have hb2pre : st.precommit_backed V2 I2 = true :=
--         hb2 (fun hVeqV2 hIneqI2 => h2new ⟨hVeqV2.symm, hIneqI2.symm⟩)
--       obtain ⟨s2, hs2_sm, hs2_mem⟩ := h_pbf V2 I2 hb2pre
--       obtain ⟨n_star, hn_s2, _, hn_honest⟩ :=
--         ctx.supermajorities_intersect_in_honest s2 s2 ⟨hs2_sm, hs2_sm⟩
--       have hpn_n_V2_I2 : st.precommitted_node n_star V2 I2 = true := hs2_mem n_star hn_s2
--       have h_le : TotalOrderWithMinimum.le V2 V :=
--         h_pcnvb n_star op V V2 I2 hn_honest hcv hpn_n_V2_I2
--       have hlt_split := (tot_view.le_lt V V2).mp hlt
--       exact absurd (tot_view.le_antisymm V V2 hlt_split.1 h_le) hlt_split.2
--   · -- Case: (V, I) ≠ (v, ixn) — hb1 yields pre-state precommit_backed V I
--     have hb1pre : st.precommit_backed V I = true :=
--       hb1 (fun hveqV hixneqI => h1new ⟨hveqV.symm, hixneqI.symm⟩)
--     by_cases h2new : V2 = v ∧ I2 = ixn
--     · -- (pre, new): substantive lock-propagation case
--       -- After subst, v↦V2, ixn↦I2. Goal: I = I2 ∨ ancestor I I2 with hlt : lt V V2.
--       obtain ⟨hV2eq, hI2eq⟩ := h2new
--       subst hV2eq
--       subst hI2eq
--       -- Pre-instantiate the honest intersection witness so SMT doesn't search for it.
--       obtain ⟨s1, hs1_sm, hs1_mem⟩ := h_pbf V I hb1pre
--       obtain ⟨n_star, hn_s1, hn_x, hn_honest⟩ :=
--         ctx.supermajorities_intersect_in_honest s1 x ⟨hs1_sm, hsm⟩
--       have hpn_n_V_I : st.precommitted_node n_star V I = true := hs1_mem n_star hn_s1
--       have hpn_n_V2_I2 : st.precommitted_node n_star V2 I2 = true := hpc n_star hn_x
--       -- Stage 2: pre-instantiate lock-propagation witnesses on n_star
--       -- precommit ⇒ prevote at (n*, V2, I2)
--       have hpv_n_V2_I2 : st.prevoted_node n_star V2 I2 = true :=
--         h_pcn_pv n_star V2 I2 hn_honest hpn_n_V2_I2
--       -- n*'s highest lock at views < V2 dominates all earlier locks
--       obtain ⟨ixn_max, s_max, v_max, h_lock_max, h_lt_vmax_V2, h_or_max, h_dom⟩ :=
--         h_pjohl n_star V2 I2 hn_honest hpv_n_V2_I2 hI2 hv_nz
--       -- n*'s lock on I at some U_I ≤ V (prevote@V or precommit@U≤V)
--       have h_lock_I_or := h_pcnlsv n_star V I hn_honest hpn_n_V_I hI
--       veil_solve_wp
--     · -- (pre, pre): both witnesses pre-state, apply IH locks_analog_precommit
--       have hb2pre : st.precommit_backed V2 I2 = true :=
--         hb2 (fun hveqV2 hixneqI2 => h2new ⟨hveqV2.symm, hixneqI2.symm⟩)
--       exact h_lap V V2 I I2 hI hI2 hb1pre hb2pre hlt

end IFPProtocolNT
