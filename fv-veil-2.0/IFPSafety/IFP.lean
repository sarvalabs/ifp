/-
# Completed safety proof of restricted IFP without Byzantine actions.

We prove the safety property
    safety [main_safety]
      ¬is_byz n1 ∧ ¬is_byz n2 ∧ decided n1 v1 i1 ∧ decided n2 v2 i2
        → ancestor i1 i2 ∨ ancestor i2 i1

179 supporting invariants, discharged by Veil's SMT
automation and 18 manually proven theorems

Scope of this restricted IFP model:
- The two fixed participants share a single consensus set (context);
- Within a single epoch
- Synchronous view changes .
- Honest-execution model: every node follows the protocol — no Byzantine actions

################################################################################
BYZANTINE-FALSE INVARIANTS (58)
################################################################################

Every invariant below is sound for the honest-execution model proved here. 58 of
them become FALSE the moment the Byzantine actions are
added, so this list exists to stop this file being mistaken for a
Byzantine-tolerant invariant set. The adversarial actions there are :
message injection plus arbitrary state changes of a byzantine node's own state.

These 58 invariants can be grouped as follows.

A. REPAIRABLE by adding ¬is_byz (48). All applied in IFPB.lean.

  [byz_send_lock / byz_prepare — forged prepare-phase messages]
    locks_sent_only_if_locked, highest_lock_sent,
    sent_lock_prepare_implies_cur_view_ge, sent_lock_only_if_prepare_unrestricted,
    recvd_collected_implies_prepare_quorum,
    recvd_collected_implies_bounded_prepare_quorum

  [byz_lock / byz_unlock — lock havoc]
    lock_stage_valid, no_lock_without_parent, locked_descends_from_genesis,
    locked_height_positive, genesis_lock_only_at_zero,
    lock_at_zero_is_genesis_precommit, genesis_lock_existence,
    prevote_lock_only_if_quorum_prevoted, precommit_lock_implies_precommit_backed

  [byz_decide / byz_undecide — decision havoc]
    no_decide_without_parent, decided_height_positive, genesis_decided_first,
    genesis_decided_at_zero, genesis_height_zero, decisions_not_from_higher_views,
    decide_only_if_precommit_operator, committed_descendant_at_height_implies_locked_descendant

  [byz_state — bulk self-slice havoc of the caches and committed frontier]
    unique_highest_decided_ixn, node_has_highest_decided_ixn,
    highest_decided_ixn_implies_precommit_backed, recvd_collected_at_past_view,
    op_argmax_ixn_unique, op_argmax_stage_unique, op_argmax_view_unique,
    op_argmax_ixn_implies_collected, op_argmax_stage_implies_collected,
    op_argmax_view_implies_collected, collected_implies_op_argmax_ixn,
    collected_implies_op_argmax_stage, collected_implies_op_argmax_view,
    argmax_recvd_ixn_unique, argmax_recvd_stage_unique, argmax_recvd_view_unique,
    argmax_recvd_ixn_implies_collected, argmax_recvd_stage_implies_collected,
    argmax_recvd_view_implies_collected, collected_implies_argmax_recvd_ixn,
    collected_implies_argmax_recvd_stage, collected_implies_argmax_recvd_view

  [byz_repropose / byz_extend — forged proposals]
    proposed_extend_view_bound, proposed_repropose_view_bound,
    proposed_height_positive

B. NOT REPAIRABLE by a guard (10).
        op_argmax_is_highest_lock, argmax_recvd_is_highest_lock,
        prevote_justified_by_highest_lock
        propose_only_if_parent_locked
        precommit_backed_implies_decided
        extended_argmax_committed, reproposed_argmax_parent_committed,
        committed_implies_parent_committed,
        parent_implies_parent_precommit_backed
        reproposal_extends_decided_parent

C. NOT false, but the honest proof route here does not survive.
     same_view_precommit_prevote_agree, precommit_qc_unique_at_view,
     unique_prevote_lock_in_view, precommit_node_lock_consistency,
     cross_node_unique_lock, unique_locked_at_height
-/

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

-- `stages`
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
relation prevoted_operator : node → view → interaction → Bool
relation precommitted_operator : node → view → interaction → Bool

-- Node relations
relation prepared_node : node → view → Bool
relation prevoted_node : node → view → interaction → Bool
relation precommitted_node : node → view → interaction → Bool

-- Interaction relations
relation parent : interaction → interaction → Bool
relation ancestor : interaction → interaction → Bool
function height : interaction → Nat


-- ####################################################################
-- # Additional Relations
-- These relations are not used in the `require` statements and are
-- simply additional information for the proof and invariants
-- ####################################################################

-- "Interaction was extended (proposed in propose_extend; 'born') at view V."
relation born_at : interaction → view → Bool

-- "Interaction's parent was extended (born) at view V."
relation parent_born_at : interaction → view → Bool

-- highest interaction decided by a node
relation highest_decided_ixn : node → interaction → Bool

-- "Node N holds a lock on a descendant of A of height H."
-- ≡ ∃ I S V, locked N I S V ∧ ancestor A I ∧ height I = H
relation locked_descendant_at_height : node → interaction → Nat → Bool

-- "Node N decided a descendant of A of height H."
-- ≡ ∃ V I, decided N V I ∧ ancestor A I ∧ height I = H
relation committed_descendant_at_height : node → interaction → Nat → Bool


-- "A precommit-QC has been aggregated at the view for the interaction and
-- at least one node has witnessed it via respond_precommit.
relation precommit_backed : view → interaction → Bool

-- Operator's cached highest lock (argmax) over collected prepare responses.
-- Set by collect_prepares; consumed by the propose_* actions.
relation prepares_collected : node → view → Bool
relation op_argmax_ixn   : node → view → interaction → Bool
relation op_argmax_stage : node → view → stage → Bool
relation op_argmax_view  : node → view → view → Bool

-- Validator's cached argmax over received prepare responses (mirror of
-- op_argmax_*).
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
  prevoted_operator N V I := false;
  precommitted_operator N V I := false;
  prepared_node N V := false;
  prevoted_node N V I := false;
  precommitted_node N V I := false;
  highest_decided_ixn N I := decide $ (I = genesis);
  locked_descendant_at_height N A H := decide $ (A = genesis ∧ H = 0);
  committed_descendant_at_height N A H := decide $ (A = genesis ∧ H = 0);
  born_at I V := decide $ (I = genesis ∧ V = tot_view.zero);
  parent_born_at C VP := false;
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

-- Operator collects prepare responses, computes the highest-view sent lock,
-- and stores it as `op_argmax`. The propose_* actions then just use `op_argmax`.
action collect_prepares (op : node) (v : view) (s : nodeset) (n_max : node)
    (ixn_max : interaction) (s_max : stage) (v_max : view) {
  -- (0) Sanity checks.
  require v ≠ tot_view.zero
  require cur_view op v
  require operator op v
  require prepared_operator op v
  require prepared_node op v
  require ¬ prepares_collected op v

  -- (1) Prepare-quorum witness: a quorum of nodes each sent a genuine
  -- prepare-response. NO per-member QC check here — only the highest lock's QC
  -- is verified, in the argmax witness below (step 3).
  require ctx.supermajority s
  require ∀ (n : node), ctx.member n s → (prepared_node n v ∧
    ∃ (vl : view) (ixnl : interaction) (sl : stage),
      sent_lock_in_prepare n v ixnl sl vl
      ∧ locked n ixnl sl vl
      ∧ tot_view.le vl v)

  -- (2) Argmax witness: n_max identifies the highest-view sent lock at v.
  require sent_lock_in_prepare n_max v ixn_max s_max v_max
  require locked n_max ixn_max s_max v_max
  require ∀ (n_l : node) (ixn_l : interaction) (s_l : stage) (v_l : view),
    sent_lock_in_prepare n_l v ixn_l s_l v_l → tot_view.le v_l v_max
  require ∀ (vl : view) (n : node) (i' : interaction) (s' : stage),
    (tot_view.lt v_max vl ∧ tot_view.lt vl v) →
      ¬ sent_lock_in_prepare n v i' s' vl

  -- (3) Verify the QC backing the highest lock.
  require ∃ (t_max : nodeset), ctx.supermajority t_max
    ∧ (s_max = prevote   → ∀ (nt : node), ctx.member nt t_max → prevoted_node    nt v_max ixn_max)
    ∧ (s_max = precommit → ∀ (nt : node), ctx.member nt t_max → precommitted_node nt v_max ixn_max)

  -- (4) Store the result.
  prepares_collected op v := true
  op_argmax_ixn   op v I  := decide $ (I = ixn_max)
  op_argmax_stage op v S  := decide $ (S = s_max)
  op_argmax_view  op v VL := decide $ (VL = v_max)
}

-- Repropose: highest lock is at committed_height + 1 and is from prevote stage
action propose_repropose (op : node) (v : view) (ci : interaction) {
  require v ≠ tot_view.zero
  require cur_view op v
  require operator op v
  require prepared_operator op v
  require prepares_collected op v
  require cur_stage op v propose
  require ∀ (ix : interaction), ¬ proposed_repropose op v ix
  require ∀ (ix : interaction), ¬ proposed_extend op v ix
  -- Use operator's argmax from collect_prepares.
  let ixn_max : interaction ← pick
  let s_max : stage ← pick
  let v_max : view ← pick
  require op_argmax_ixn   op v ixn_max
  require op_argmax_stage op v s_max
  require op_argmax_view  op v v_max
  -- heightDiff == 1 && PREVOTE → repropose
  require highest_decided_ixn op ci
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
  -- Use operator's argmax from collect_prepares
  let ixn_max : interaction ← pick
  let s_max : stage ← pick
  let v_max : view ← pick
  require op_argmax_ixn   op v ixn_max
  require op_argmax_stage op v s_max
  require op_argmax_view  op v v_max
  -- heightDiff == 0 → extend
  require highest_decided_ixn op ci
  require ancestor genesis ci
  require height ixn_max = height ci
  require ci ≠ ixn_propose
  require ¬ (ancestor ci ixn_propose ∨ ancestor ixn_propose ci)
  parent ci ixn_propose := decide $ (ci ≠ ixn_propose);
  ancestor A ixn_propose := decide $ (ancestor A ixn_propose ∨ ancestor A ci ∨ A = ci ∨ A = ixn_propose);
  proposed_extend op v ixn_propose := true;
  height ixn_propose := height ci + 1;
  -- GHOST (reproposal-run): record I's birth + the parent→child extend bridge.
  born_at I V := decide $ (born_at I V ∨ (I = ixn_propose ∧ V = v));
  -- C's parent is ci; ci was born at the VP for which born_at ci VP holds.
  parent_born_at C VP := decide $ (parent_born_at C VP ∨ (C = ixn_propose ∧ born_at ci VP));
}

-- Validator-side analog of collect_prepares.
action collect_recvd_locks (n : node) (v : view) (s : nodeset) (n_max : node)
    (ixn_max : interaction) (s_max : stage) (v_max : view) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v propose
  require prepared_node n v
  require ¬ recvd_collected n v

  -- Prepare-quorum witness: a quorum of nodes each sent a genuine (locked)
  -- prepare-response. NO per-member QC check here — only the highest lock's QC
  -- is verified, in the argmax witness below (step 3).
  require ctx.supermajority s
  require ∀ (m : node), ctx.member m s → (prepared_node m v ∧
    ∃ (vl : view) (ixnl : interaction) (sl : stage),
      sent_lock_in_prepare m v ixnl sl vl
      ∧ locked m ixnl sl vl
      ∧ tot_view.le vl v)

  -- Argmax witness: n_max identifies the highest-view sent lock at v, and
  -- (step 3) that highest lock is verified QC-backed (`t_max` supermajority).
  require sent_lock_in_prepare n_max v ixn_max s_max v_max
  require locked n_max ixn_max s_max v_max
  require ∀ (n_l : node) (ixn_l : interaction) (s_l : stage) (v_l : view),
    sent_lock_in_prepare n_l v ixn_l s_l v_l → tot_view.le v_l v_max
  -- No sent_lock at views strictly above v_max (pure ∀ form, EPR).
  require ∀ (vl : view) (n' : node) (i' : interaction) (s' : stage),
    (tot_view.lt v_max vl ∧ tot_view.lt vl v) →
      ¬ sent_lock_in_prepare n' v i' s' vl
  require ∃ (t_max : nodeset), ctx.supermajority t_max
    ∧ (s_max = prevote   → ∀ (nt : node), ctx.member nt t_max → prevoted_node    nt v_max ixn_max)
    ∧ (s_max = precommit → ∀ (nt : node), ctx.member nt t_max → precommitted_node nt v_max ixn_max)

  -- Store the result.
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
    -- GHOST: new prevote lock at height (height ixn), on every ancestor A of ixn.
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
  precommit_backed v ixn := true
  locked n ixn precommit v := true;
  -- GHOST: new precommit lock at height (height ixn), on every ancestor A of ixn.
  locked_descendant_at_height n A H := decide $ (locked_descendant_at_height n A H ∨ (ancestor A ixn ∧ H = height ixn));
  decided n v ixn := true
  -- GHOST: node decided a descendant of A at height (height ixn), on every ancestor A of ixn.
  committed_descendant_at_height n A H := decide $ (committed_descendant_at_height n A H ∨ (ancestor A ixn ∧ H = height ixn));
  -- Update highest_decided_ixn only if this is a newer decision
  if (∃ (ci_old : interaction), highest_decided_ixn n ci_old ∧ height ixn > height ci_old) then
    highest_decided_ixn n I := decide $ (I = ixn);
  cur_stage n v S := decide $ (S = commit)
}


invariant [locks_analog_precommit]
  ∀ (V V2 : view) (I J : interaction) (NP : node),
    (¬ ctx.is_byz NP ∧
     precommit_backed V I ∧ I ≠ genesis ∧ J ≠ genesis ∧
     prevoted_node NP V2 J ∧
     tot_view.lt V V2) →
    (J = I ∨ ancestor I J)


invariant [argmax_recvd_ixn_descends_from_precommit_backed_at_bounded_view]
  ∀ (U V_act V_max : view) (I IM : interaction) (N : node),
    (¬ ctx.is_byz N ∧
     precommit_backed U I ∧ I ≠ genesis ∧
     argmax_recvd_ixn N V_act IM ∧ argmax_recvd_view N V_act V_max ∧
     tot_view.lt U V_act ∧ tot_view.le U V_max) →
    (I = IM ∨ ancestor I IM)

invariant [recvd_collected_implies_bounded_prepare_quorum]
  (recvd_collected N VACT ∧ argmax_recvd_view N VACT VMAX) →
    ∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (m : node), ctx.member m s →
        prepared_node m VACT ∧
        ∃ (IL : interaction) (SL : stage) (VL : view),
          sent_lock_in_prepare m VACT IL SL VL ∧ locked m IL SL VL ∧
          tot_view.le VL VMAX

invariant [reproposed_argmax_parent_committed]
  (¬ ctx.is_byz OP ∧
   op_argmax_ixn OP V I ∧ op_argmax_stage OP V prevote ∧
   op_argmax_view OP V U ∧ I ≠ genesis) →
    ∃ (J : interaction) (W : view), parent J I ∧ tot_view.lt W U ∧ precommit_backed W J

invariant [extended_argmax_committed]
  (¬ ctx.is_byz OP ∧ proposed_extend OP V IX ∧
   op_argmax_ixn OP V I ∧ op_argmax_stage OP V precommit ∧
   op_argmax_view OP V U ∧ I ≠ genesis) →
    precommit_backed U I

invariant [extended_ixn_not_committed_before]
  proposed_extend OP V I → ∀ (U : view), tot_view.lt U V → ¬ precommit_backed U I

invariant [prevote_matches_argmax]
  (¬ ctx.is_byz N ∧ prevoted_node N V2 J ∧ J ≠ genesis ∧ V2 ≠ tot_view.zero) →
    ∃ (IM : interaction), argmax_recvd_ixn N V2 IM ∧
      ((argmax_recvd_stage N V2 prevote ∧ J = IM) ∨
       (argmax_recvd_stage N V2 precommit ∧ parent IM J))

invariant [locks_analog_decided]
  ∀ (V V2 : view) (I I2 : interaction) (N1 N2 : node),
    (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
     I ≠ genesis ∧ I2 ≠ genesis ∧
     decided N1 V I ∧ decided N2 V2 I2 ∧
     tot_view.lt V V2) →
    (I = I2 ∨ ancestor I I2)

invariant [reproposed_relock_at_view_implies_argmax]
  (proposed_repropose OP V I ∧ locked N I prevote V) →
    ∃ (VM : view),
      op_argmax_ixn OP V I ∧ op_argmax_view OP V VM ∧ op_argmax_stage OP V prevote

invariant [reproposal_extends_decided_parent]
  (¬ ctx.is_byz N ∧ prevoted_node N V J ∧ J ≠ genesis ∧ V ≠ tot_view.zero ∧
   argmax_recvd_stage N V prevote) →
    (∃ (VM : view), tot_view.lt VM V ∧
       ∃ (s : nodeset), ctx.supermajority s ∧
         ∀ (m : node), ctx.member m s → prevoted_node m VM J)

invariant [same_view_precommit_prevote_agree]
  (precommit_backed V I ∧ I ≠ genesis ∧ J ≠ genesis ∧
   (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (m : node), ctx.member m s → prevoted_node m V J)) →
    I = J

invariant [precommit_qc_unique_at_view]
  ((∃ (s1 : nodeset), ctx.supermajority s1 ∧
      ∀ (m : node), ctx.member m s1 → precommitted_node m V I1) ∧
   (∃ (s2 : nodeset), ctx.supermajority s2 ∧
      ∀ (m : node), ctx.member m s2 → precommitted_node m V I2)) →
    I1 = I2

-- ####################################################################
-- # op_argmax cache invariants
-- ####################################################################

invariant [op_argmax_ixn_unique]
  (op_argmax_ixn OP V I1 ∧ op_argmax_ixn OP V I2) → I1 = I2

invariant [op_argmax_stage_unique]
  (op_argmax_stage OP V S1 ∧ op_argmax_stage OP V S2) → S1 = S2

invariant [op_argmax_view_unique]
  (op_argmax_view OP V VL1 ∧ op_argmax_view OP V VL2) → VL1 = VL2

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

invariant [op_argmax_qc_backed]
  (¬ ctx.is_byz OP ∧ op_argmax_ixn OP V IM ∧ op_argmax_stage OP V SM ∧ op_argmax_view OP V VM) →
    (SM = prevote → ∃ (Q : nodeset), ctx.supermajority Q ∧
       ∀ (N : node), ctx.member N Q → prevoted_node N VM IM) ∧
    (SM = precommit → ∃ (Q : nodeset), ctx.supermajority Q ∧
       ∀ (N : node), ctx.member N Q → precommitted_node N VM IM)

invariant [recvd_collected_implies_prepare_quorum]
  recvd_collected N VACT →
    ∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (m : node), ctx.member m s →
        prepared_node m VACT ∧
        ∃ (IL : interaction) (SL : stage) (VL : view),
          sent_lock_in_prepare m VACT IL SL VL ∧ locked m IL SL VL

invariant [no_proposal_without_parent]
  (¬ ctx.is_byz OP ∧ (proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

invariant [proposed_descends_from_genesis]
  (¬ ctx.is_byz OP ∧ (proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ I ≠ genesis) → ancestor genesis I

invariant [op_argmax_is_highest_lock]
  (¬ ctx.is_byz OP ∧ op_argmax_ixn OP V IM ∧ op_argmax_stage OP V SM ∧ op_argmax_view OP V VM) →
    ∃ (N : node), sent_lock_in_prepare N V IM SM VM ∧ locked N IM SM VM

invariant [argmax_recvd_is_highest_lock]
  (¬ ctx.is_byz N ∧ argmax_recvd_ixn N V IM ∧ argmax_recvd_stage N V SM ∧ argmax_recvd_view N V VM) →
    ∃ (M : node), sent_lock_in_prepare M V IM SM VM ∧ locked M IM SM VM

safety [main_safety]
  ∀ (n1 n2 : node) (v1 v2 : view) (i1 i2 : interaction),
    (¬ ctx.is_byz n1 ∧ ¬ ctx.is_byz n2 ∧
     decided n1 v1 i1 ∧
     decided n2 v2 i2) →
    (ancestor i1 i2 ∨ ancestor i2 i1)

invariant [safety_violation_locates_fork]
  ∀ (n1 n2 : node) (v1 v2 : view) (i1 i2 : interaction),
    (¬ ctx.is_byz n1 ∧ ¬ ctx.is_byz n2 ∧
     decided n1 v1 i1 ∧ decided n2 v2 i2 ∧
     ¬ ancestor i1 i2 ∧ ¬ ancestor i2 i1) →
    ∃ (A c1 c2 : interaction),
      parent A c1 ∧ parent A c2 ∧ c1 ≠ c2 ∧
      ancestor c1 i1 ∧ ancestor c2 i2

invariant [precommit_backed_above_zero]
  precommit_backed V I → V ≠ tot_view.zero

invariant [prevoted_node_implies_recvd_collected]
  (¬ ctx.is_byz N ∧ prevoted_node N V I ∧ I ≠ genesis ∧ V ≠ tot_view.zero) →
    recvd_collected N V

invariant [recvd_collected_at_past_view]
  (recvd_collected N V ∧ cur_view N1 VC) → tot_view.le V VC

-- ####################################################################
-- # argmax_recvd cache invariants
-- ####################################################################

invariant [argmax_recvd_ixn_unique]
  (argmax_recvd_ixn N V I1 ∧ argmax_recvd_ixn N V I2) → I1 = I2

invariant [argmax_recvd_stage_unique]
  (argmax_recvd_stage N V S1 ∧ argmax_recvd_stage N V S2) → S1 = S2

invariant [argmax_recvd_view_unique]
  (argmax_recvd_view N V VL1 ∧ argmax_recvd_view N V VL2) → VL1 = VL2

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

invariant [argmax_recvd_qc_backed]
  (¬ ctx.is_byz N ∧ argmax_recvd_ixn N V IM ∧ argmax_recvd_stage N V SM ∧ argmax_recvd_view N V VM) →
    (SM = prevote → ∃ (Q : nodeset), ctx.supermajority Q ∧
       ∀ (N' : node), ctx.member N' Q → prevoted_node N' VM IM) ∧
    (SM = precommit → ∃ (Q : nodeset), ctx.supermajority Q ∧
       ∀ (N' : node), ctx.member N' Q → precommitted_node N' VM IM)

invariant [precommitted_node_implies_prevote_qc]
  precommitted_node N V I → (∃ (op : node), operator op V ∧ prevoted_operator op V I)

invariant [decided_implies_precommit_backed]
    (¬ ctx.is_byz N ∧ decided N V I ∧ I ≠ genesis) → precommit_backed V I

invariant [prevote_justified_by_highest_lock]
  (¬ ctx.is_byz N ∧ prevoted_node N V I ∧ I ≠ genesis ∧ V ≠ tot_view.zero) →
    ∃ (n_max : node) (ixn_max : interaction) (s_max : stage) (v_max : view),
      locked n_max ixn_max s_max v_max ∧
      tot_view.lt v_max V ∧
      ((s_max = prevote ∧ ixn_max = I) ∨
       (s_max = precommit ∧ parent ixn_max I))

invariant [precommit_node_locked_at_same_view]
  (¬ ctx.is_byz N ∧ precommitted_node N V I ∧ I ≠ genesis) →
    (locked N I prevote V ∨ ∃ (U : view), tot_view.le U V ∧ locked N I precommit U)

invariant [precommit_lock_height_le_committed]
  (¬ ctx.is_byz N ∧ locked N I precommit V ∧ highest_decided_ixn N CI) →
    height I ≤ height CI

-- ####################################################################
-- # Core Safety-Routing Invariants
-- ####################################################################

invariant [genesis_decided_only_at_zero]
  (¬ ctx.is_byz N ∧ decided N V genesis) → V = tot_view.zero

invariant [proposed_parent_height_le_committed]
  (¬ ctx.is_byz OP ∧
   (proposed_repropose OP V J ∨ proposed_extend OP V J) ∧
   parent I J ∧ highest_decided_ixn OP CI) →
    height I ≤ height CI

invariant [decision_height_monotone]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   decided N1 V1 I1 ∧
   decided N2 V2 I2 ∧
   tot_view.lt V1 V2)
  → height I1 ≤ height I2

invariant [proposed_extend_parent_matches_committed]
  (¬ ctx.is_byz OP ∧ proposed_extend OP V J ∧ parent I J ∧
   highest_decided_ixn OP CI ∧ height I = height CI) → I = CI

invariant [proposed_repropose_parent_matches_committed]
  (¬ ctx.is_byz OP ∧ proposed_repropose OP V J ∧ parent I J ∧
   highest_decided_ixn OP CI ∧ height I = height CI) → I = CI

invariant [unique_decided_at_height]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   decided N1 V1 I1 ∧
   decided N2 V2 I2 ∧
   height I1 = height I2)
  → I1 = I2

invariant [highest_decided_ixn_height_upper_bound]
  (¬ ctx.is_byz N ∧ decided N V I ∧ highest_decided_ixn N CI) → height I ≤ height CI

invariant [genesis_decided_first]
  (decided N V J ∧ J ≠ genesis) →
    ∃ (u : view) (m : node), tot_view.lt u V ∧ decided m u genesis

invariant [committed_implies_parent_committed]
  (decided M V J ∧ parent I J ∧ J ≠ genesis) →
    ∃ (u : view) (n : node), tot_view.lt u V ∧ decided n u I

invariant [cur_view_global]
  (cur_view N1 V1 ∧ cur_view N2 V2) → V1 = V2

invariant [prevoted_node_view_bound]
  (¬ ctx.is_byz N2 ∧ cur_view N1 V1 ∧ prevoted_node N2 V2 I) →
    tot_view.le V2 V1

invariant [precommitted_node_view_bound]
  (¬ ctx.is_byz N2 ∧ cur_view N1 V1 ∧ precommitted_node N2 V2 I) →
    tot_view.le V2 V1

invariant [precommit_backed_fwd]
  precommit_backed V I →
    (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (n : node), ctx.member n s → precommitted_node n V I)

invariant [unique_precommit_backed_at_view]
  (precommit_backed V I1 ∧ precommit_backed V I2) → I1 = I2

invariant [unique_precommit_backed_at_height]
  (precommit_backed V1 I1 ∧ precommit_backed V2 I2 ∧
   I1 ≠ genesis ∧ I2 ≠ genesis ∧
   height I1 = height I2) → I1 = I2

-- ####################################################################
-- # Simple Invariants
-- ####################################################################

invariant [unique_prevote_nodes]
  ∀ (v : view) (i1 i2 : interaction) (n : node),
    ¬ ctx.is_byz n → ((prevoted_node n v i1 ∧ prevoted_node n v i2) → i1 = i2)

invariant [unique_prevote_lock_in_view]
  ∀ (n1 n2 : node) (v : view) (i1 i2 : interaction),
    ¬ (ctx.is_byz n1 ∨ ctx.is_byz n2) → ((locked n1 i1 prevote v ∧ locked n2 i2 prevote v) → i1 = i2)

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

invariant [prevote_lock_only_if_quorum_prevoted]
  locked N I prevote V → (∃ (s : nodeset), ctx.supermajority s ∧
    ∀ (NC : node), ctx.member NC s → prevoted_node NC V I)

invariant [precommit_node_lock_consistency]
  (¬ ctx.is_byz N ∧ ¬ ctx.is_byz NC ∧ precommitted_node NC V I ∧
   locked N J prevote V ∧
   I ≠ genesis ∧ J ≠ genesis) → I = J

invariant [unique_lock_interaction_per_view]
  (¬ ctx.is_byz N ∧ locked N I1 S1 V ∧ locked N I2 S2 V) → I1 = I2

invariant [cross_node_unique_lock]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   locked N1 I1 S1 V ∧ locked N2 I2 S2 V ∧
   I1 ≠ genesis ∧ I2 ≠ genesis)
  → I1 = I2

invariant [precommit_lock_implies_prevoted]
  (¬ ctx.is_byz N ∧ locked N I precommit V ∧ I ≠ genesis) → prevoted_node N V I

invariant [precommit_lock_implies_precommit_backed]
  (locked N I precommit V ∧ I ≠ genesis) → precommit_backed V I

invariant [locks_sent_only_if_locked]
  sent_lock_in_prepare N V IL SL VL → locked N IL SL VL

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

invariant [locked_descendant_at_height_fwd]
  (locked N I S V ∧ ancestor A I) → locked_descendant_at_height N A (height I)

invariant [committed_descendant_at_height_fwd]
  (decided N V I ∧ ancestor A I) → committed_descendant_at_height N A (height I)

invariant [locked_descendant_at_height_bwd]
  (¬ ctx.is_byz N ∧ locked_descendant_at_height N A H) →
    ∃ (I : interaction) (S : stage) (V : view),
      locked N I S V ∧ ancestor A I ∧ height I = H

invariant [committed_descendant_at_height_bwd]
  (¬ ctx.is_byz N ∧ committed_descendant_at_height N A H) →
    ∃ (V : view) (I : interaction), decided N V I ∧ ancestor A I ∧ height I = H

invariant [locked_descendant_height_bound]
  (¬ ctx.is_byz N ∧ locked_descendant_at_height N A H) → height A ≤ H

invariant [committed_descendant_height_bound]
  (¬ ctx.is_byz N ∧ committed_descendant_at_height N A H) → height A ≤ H

invariant [committed_descendant_at_height_implies_locked_descendant]
  committed_descendant_at_height N A H → locked_descendant_at_height N A H

invariant [genesis_locked_descendant_at_height_zero]
  ∀ (n : node), locked_descendant_at_height n genesis 0

invariant [genesis_committed_descendant_at_height_zero]
  ∀ (n : node), committed_descendant_at_height n genesis 0

invariant [extended_implies_born_at]
  proposed_extend OP V I → born_at I V

invariant [born_at_implies_extended]
  (born_at I V ∧ I ≠ genesis) → ∃ (op : node), proposed_extend op V I

invariant [born_at_implies_parent]
  (born_at I V ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

invariant [born_at_unique]
  (born_at I V1 ∧ born_at I V2) → V1 = V2

invariant [parent_born_at_implies_parent]
  (parent_born_at C VP ∧ C ≠ genesis) → ∃ (P : interaction), parent P C ∧ born_at P VP


invariant [parent_born_at_unique]
  (parent_born_at C VP1 ∧ parent_born_at C VP2) → VP1 = VP2

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

invariant [lock_at_zero_is_genesis_precommit]
  (locked N I S V ∧ V = tot_view.zero) → (I = genesis ∧ S = precommit)

invariant [lock_stage_valid]
  locked N I S V → (S = prevote ∨ S = precommit)

invariant [locked_only_if_prepared]
  (¬ ctx.is_byz N ∧ locked N I S V ∧ V ≠ tot_view.zero ∧ I ≠ genesis) → prepared_node N V

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
  → (∃ (i : interaction), ((∃ (op : node), proposed_repropose op V i ∨ proposed_extend op V i) ∧ prevoted_node N V i))

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
-- # Highest Decided Ixn Invariants
-- ####################################################################

invariant [unique_highest_decided_ixn]
  (highest_decided_ixn N I1 ∧ highest_decided_ixn N I2) → I1 = I2

invariant [node_has_highest_decided_ixn]
  ∀ (n : node), ∃ (i : interaction), highest_decided_ixn n i

invariant [highest_decided_ixn_decided]
  (¬ ctx.is_byz N ∧ highest_decided_ixn N I) →
    ∃ (V : view), decided N V I

invariant [highest_decided_ixn_is_genesis_or_has_parent]
  (¬ ctx.is_byz N ∧ highest_decided_ixn N I ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

invariant [highest_decided_ixn_descends_from_genesis]
  (¬ ctx.is_byz N ∧ highest_decided_ixn N I) → ancestor genesis I

invariant [highest_decided_ixn_precommit_locked]
  (¬ ctx.is_byz N ∧ highest_decided_ixn N I ∧ I ≠ genesis) →
    ∃ (V : view), locked N I precommit V

invariant [highest_decided_ixn_unique_at_height]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   highest_decided_ixn N1 I1 ∧ highest_decided_ixn N2 I2 ∧
   height I1 = height I2) → I1 = I2

invariant [highest_decided_ixn_height_positive]
  (¬ ctx.is_byz N ∧ highest_decided_ixn N I ∧ I ≠ genesis) → height I ≥ 1

invariant [precommit_backed_height_zero_is_genesis]
  (precommit_backed V I ∧ height I = 0) → I = genesis

invariant [locked_height_positive]
  (locked N I S V ∧ I ≠ genesis) → height I ≥ 1

invariant [proposed_height_positive]
  ((proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ I ≠ genesis) →
    height I ≥ 1

invariant [decided_height_positive]
  (decided N V I ∧ I ≠ genesis) → height I ≥ 1

invariant [prevoted_height_positive]
  (¬ ctx.is_byz N ∧ prevoted_node N V I ∧ I ≠ genesis) → height I ≥ 1

invariant [precommit_backed_implies_decided]
  precommit_backed V I → ∃ (n : node), decided n V I

invariant [highest_decided_ixn_implies_precommit_backed]
  (highest_decided_ixn N I ∧ I ≠ genesis) → ∃ (W : view), precommit_backed W I

invariant [parent_implies_parent_precommit_backed]
  (parent I J ∧ I ≠ genesis) → ∃ (W : view), precommit_backed W I

invariant [reproposed_implies_argmax]
  proposed_repropose OP V I →
    (prepares_collected OP V ∧ op_argmax_ixn OP V I ∧
     op_argmax_stage OP V prevote ∧ ∃ (VM : view), op_argmax_view OP V VM)


set_option veil.smt.timeout 15000
set_option maxHeartbeats 4000000
#gen_spec

set_option veil.printCounterexamples true

--  #check_action respond_prevote



theorem respond_prevote_op_argmax_is_highest_lock (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_prevote_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532375 view interaction χ node nodeset stage χ_rep]
    [respond_prevote_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1532428 nodeset node ctx]
    [respond_prevote_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532505 view interaction nodeset χ node ctx stage χ_rep]
    [respond_prevote_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532590 node view interaction χ nodeset stage tot_view χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_prevote.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_prevote_dec_0 respond_prevote_dec_1
          respond_prevote_dec_2 respond_prevote_dec_3 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@op_argmax_is_highest_lock ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  -- Operator-side mirror of respond_prevote_argmax_recvd_is_highest_lock.
  -- op_argmax_* and sent_lock_in_prepare are frame-unchanged at respond_prevote;
  -- only `locked` grows (guarded prevote-lock add), so the pre-state instance of
  -- THIS invariant (hinv position 26) closes both `split_ifs` branches:
  --   then (no lock written): `exact h_self`.
  --   else (new lock added): witness lock discharges the new-tuple guard via `fun _ => h_lock`.
  intro hv_nz hcv hcs x hop hpr hsm hmem
  obtain ⟨_, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          h_self, _⟩ := hinv
  split_ifs
  · exact h_self
  · intro OP V IM SM VM h_byz h_ai h_as h_av
    obtain ⟨M, h_sent, h_lock⟩ := h_self OP V IM SM VM h_byz h_ai h_as h_av
    exact ⟨M, h_sent, fun _ => h_lock⟩



theorem respond_prevote_argmax_recvd_is_highest_lock (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_prevote_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532375 view interaction χ node nodeset stage χ_rep]
    [respond_prevote_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1532428 nodeset node ctx]
    [respond_prevote_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532505 view interaction nodeset χ node ctx stage χ_rep]
    [respond_prevote_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532590 node view interaction χ nodeset stage tot_view χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_prevote.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_prevote_dec_0 respond_prevote_dec_1
          respond_prevote_dec_2 respond_prevote_dec_3 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@argmax_recvd_is_highest_lock ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  -- veil_wp presents respond_prevote's guarded prevote-lock add as an `if ∃u… then A else
  -- B` in the GOAL, with the invariant's ∀-binders INSIDE each branch. argmax_recvd_* and
  -- sent_lock_in_prepare are frame-unchanged, so the pre-state instance of THIS invariant
  -- (hinv position 27) closes both branches:
  --   then (∃u holds ⇒ ¬(∃u) is false ⇒ no lock written ⇒ st.locked unchanged): `exact h_self`.
  --   else (new lock added): witness lock discharges the new-tuple guard via `fun _ => h_lock`.
  intro hv_nz hcv hcs x hop hpr hsm hmem
  obtain ⟨_, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, h_self, _⟩ := hinv
  split_ifs
  · exact h_self
  · intro N V IM SM VM h_byz h_ai h_as h_av
    obtain ⟨M, h_sent, h_lock⟩ := h_self N V IM SM VM h_byz h_ai h_as h_av
    exact ⟨M, h_sent, fun _ => h_lock⟩

theorem respond_prevote_committed_descendant_at_height_implies_locked_descendant (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_prevote_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532375 view interaction χ node nodeset stage χ_rep]
    [respond_prevote_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1532428 nodeset node ctx]
    [respond_prevote_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532505 view interaction nodeset χ node ctx stage χ_rep]
    [respond_prevote_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532590 node view interaction χ nodeset stage tot_view χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_prevote.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_prevote_dec_0 respond_prevote_dec_1
          respond_prevote_dec_2 respond_prevote_dec_3 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@committed_descendant_at_height_implies_locked_descendant ρ σ view view_dec_eq view_inhabited node node_dec_eq
          node_inhabited interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited
          stage stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  -- committed_descendant_at_height is frame-unchanged at respond_prevote; the
  -- locked_descendant_at_height ghost only GROWS (row-rewrite
  -- `decide (old ∨ (ancestor A ixn ∧ H = height ixn))` under the relock guard), so
  -- the pre-state instance (hinv position 88) supplies the old bit in both branches.
  intro hv_nz hcv hcs x hop hpr hsm hmem
  have h_self := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  split_ifs
  · exact h_self
  · intro N A H h_cd
    have h_pre := h_self N A H h_cd
    by_cases hN : n = N
    · rw [if_pos hN, hN]
      exact Or.inl h_pre
    · rw [if_neg hN]
      exact h_pre

theorem respond_prevote_reproposed_relock_at_view_implies_argmax (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_prevote_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532375 view interaction χ node nodeset stage χ_rep]
    [respond_prevote_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1532428 nodeset node ctx]
    [respond_prevote_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532505 view interaction nodeset χ node ctx stage χ_rep]
    [respond_prevote_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532590 node view interaction χ nodeset stage tot_view χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_prevote.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_prevote_dec_0 respond_prevote_dec_1
          respond_prevote_dec_2 respond_prevote_dec_3 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@reproposed_relock_at_view_implies_argmax ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited
          interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage
          stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  -- The bridge leaf (reproposed_implies_argmax, #181 = last conjunct) closes both
  -- split_ifs branches from the proposed_repropose antecedent alone:
  -- proposed_repropose and the op_argmax_* cache are frame-unchanged at
  -- respond_prevote, so the (possibly new) prevote-lock hypothesis is never
  -- consulted. Goal conclusion is the exists_and_left-narrowed form
  -- `op_argmax_ixn ∧ (∃ x, op_argmax_view x) ∧ op_argmax_stage`.
  intro hv_nz hcv hcs x hop hpr hsm hmem
  have h_bridge := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  split_ifs
  · intro OP V I N h_pr _h_lk
    obtain ⟨_h_pc, h_ai, h_as, VM, h_av⟩ := h_bridge OP V I h_pr
    exact ⟨h_ai, ⟨VM, h_av⟩, h_as⟩
  · intro OP V I N h_pr _h_lk
    obtain ⟨_h_pc, h_ai, h_as, VM, h_av⟩ := h_bridge OP V I h_pr
    exact ⟨h_ai, ⟨VM, h_av⟩, h_as⟩


theorem propose_repropose_proposed_repropose_parent_matches_committed (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [propose_repropose_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_908506 node view χ interaction nodeset stage χ_rep]
    [propose_repropose_dec_1 :
      delta% @IFPProtocolNTDPH._veil_dec_type_908583 node view χ interaction nodeset stage χ_rep] :
    ∀ (op : node) (v : view) (ci : interaction),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@propose_repropose.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub propose_repropose_dec_0 propose_repropose_dec_1
          op v ci)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@proposed_repropose_parent_matches_committed ρ σ view view_dec_eq view_inhabited node node_dec_eq
          node_inhabited interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited
          stage stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hop hpo hpc hcs hnr hne t t_1 t_2 ham_i ham_s ham_v hci hgen hht hpv
    OP V J I CI hbyz hpp hpar hcom hheq
  subst hpv
  -- Extract needed invariants from hinv (positions = source declaration order).
  have h_rapc := hinv.2.2.2.1
  have h_prpmc := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_upbh := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_plipb := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_ph := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_up := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_ghz := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_cipl := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_ciuah := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_cihp := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_pbhzg := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases h_match : op = OP ∧ v = V ∧ t = J
  · -- New tuple (OP,V,J) = (op,v,t): `t` is the freshly-reproposed interaction.
    obtain ⟨rfl, rfl, rfl⟩ := h_match
    -- t ≠ genesis: height t = height ci + 1 ≥ 1.
    have ht_ng : ¬ t = st.genesis := by
      intro hc
      obtain ⟨hh0, _⟩ := (h_ghz t).mpr hc
      omega
    -- Ungated reproposed_argmax_parent_committed: t's parent P is precommit-backed.
    obtain ⟨P, hP_par, W, hW_lt, hP_pb⟩ := h_rapc op v t t_2 hbyz ham_i ham_s ham_v ht_ng
    -- unique_parent ⇒ P = I; carry the precommit-backing to I.
    have hPI : P = I := h_up P t I hP_par hpar
    rw [hPI] at hP_pb
    -- height I = height ci (parent_height) and height CI = height ci.
    have hht_tI : st.height t = st.height I + 1 := h_ph I t hpar
    have hhIci : st.height I = st.height ci := by omega
    have hhCIci : st.height CI = st.height ci := by omega
    -- CI = ci (highest_decided_ixn_unique_at_height); reduce the goal to I = ci.
    have hCIci : CI = ci := h_ciuah op op CI ci hbyz hbyz hcom hci hhCIci
    rw [hCIci]
    -- Genesis frontier split.
    by_cases hcig : ci = st.genesis
    · have hci0 : st.height ci = 0 := ((h_ghz ci).mpr hcig).1
      have hI0 : st.height I = 0 := by omega
      exact (h_pbhzg W I hP_pb hI0).trans hcig.symm
    · have hci_pos : st.height ci ≥ 1 := h_cihp op ci hbyz hci hcig
      have hI_ng : ¬ I = st.genesis := by
        intro hc
        obtain ⟨hh0, _⟩ := (h_ghz I).mpr hc
        omega
      obtain ⟨Vc, hlock⟩ := h_cipl op ci hbyz hci hcig
      have hci_pb : st.precommit_backed Vc ci = true := h_plipb op ci Vc hlock hcig
      exact h_upbh W I Vc ci hP_pb hci_pb hI_ng hcig hhIci
  · -- Pre-existing repropose: (OP,V,J) ≠ (op,v,t); pre-state invariant discharges it.
    have hpre : st.proposed_repropose OP V J = true := by
      apply hpp
      intro hoOP hvV htJ
      exact h_match ⟨hoOP, hvV, htJ⟩
    exact h_prpmc OP V J I CI hbyz hpre hpar hcom hheq


theorem propose_extend_locked_descendant_at_height_bwd (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [propose_extend_dec_0 : delta% @IFPProtocolNTDPH._veil_dec_type_1012722 interaction χ view node nodeset stage χ_rep]
    [propose_extend_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1012797 interaction χ view node nodeset stage χ_rep]
    [propose_extend_dec_2 : delta% @IFPProtocolNTDPH._veil_dec_type_1012881 node view χ interaction nodeset stage χ_rep]
    [propose_extend_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1012968 node view χ interaction nodeset stage χ_rep] :
    ∀ (op : node) (v : view) (ixn_propose : interaction) (ci : interaction),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@propose_extend.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub propose_extend_dec_0 propose_extend_dec_1
          propose_extend_dec_2 propose_extend_dec_3 op v ixn_propose ci)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@locked_descendant_at_height_bwd ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited
          interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage
          stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz h_nopar h_noanc h_h0 hcv hop hpo hpc hcs h_ng h_nrepr h_next
    t t_1 t_2 hari hstg hav hci hgen_ci hht_max hci_ne hanc1 hanc2
    N A H h_byz h_ldah
  -- `locked_descendant_at_height N A H` is on a relation propose_extend never
  -- touches, so it is the pre-state fact: conjunct #84 of hinv gives a witness.
  -- (Bundle order here differs from IFPNTDPH2: locked_descendant_at_height_bwd is
  -- #84, not #3 — there are 83 conjuncts ahead of it, incl the indented
  -- decided_implies_precommit_backed at #44 and safety[main_safety].)
  obtain ⟨I, ⟨S, V, h_locked⟩, h_anc, h_ht⟩ :=
    hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      N A H h_byz h_ldah
  -- Freshness: the witness I cannot be the brand-new ixn_propose. I is locked
  -- (h_locked); locked_height_positive (hinv conjunct #174) gives height I ≥ 1,
  -- contradicting ixn_propose's height 0 (h_h0). With I ≠ ixn_propose, both
  -- `if ixn_propose = I` guards take the else-branch.
  have h_lhp := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_ne : ¬ ixn_propose = I := by
    intro h_eq
    rw [← h_eq] at h_locked
    have h_pos := h_lhp N ixn_propose S V h_locked h_ng
    omega
  exact ⟨I, ⟨S, V, h_locked⟩,
    by rw [if_neg h_ne]; exact h_anc,
    by rw [if_neg h_ne]; exact h_ht⟩

theorem collect_recvd_locks_argmax_recvd_qc_backed (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [collect_recvd_locks_dec_0 : delta% @IFPProtocolNTDPH._veil_dec_type_1167942 nodeset node ctx]
    [collect_recvd_locks_dec_1 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1168068 view nodeset χ node ctx interaction stage χ_rep tot_view]
    [collect_recvd_locks_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1168172 view χ node interaction stage nodeset χ_rep tot_view]
    [collect_recvd_locks_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1168284 view χ node interaction stage tot_view nodeset χ_rep]
    [collect_recvd_locks_dec_4 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1168414 interaction stage view χ node nodeset ctx χ_rep] :
    ∀ (n : node) (v : view) (s : nodeset) (n_max : node) (ixn_max : interaction) (s_max : stage) (v_max : view),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@collect_recvd_locks.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub collect_recvd_locks_dec_0
          collect_recvd_locks_dec_1 collect_recvd_locks_dec_2 collect_recvd_locks_dec_3 collect_recvd_locks_dec_4 n v s
          n_max ixn_max s_max v_max)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@argmax_recvd_qc_backed ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs hpn hnrc hsm hmem hsl_max hlk_max hdom hgap tmax htmax_sm htmax_pv
    htmax_pc N V IM SM VM h_byz h_ixn h_stage h_view
  by_cases h_match : n = N ∧ v = V
  · -- New write at (n, v): the argmax_recvd_* updates decode to (ixn_max, s_max, v_max),
    -- and the action's step-3 precondition (tmax) is exactly the QC-backing witness.
    rw [if_pos h_match] at h_ixn h_stage h_view
    subst IM SM VM
    exact ⟨fun he => ⟨tmax, htmax_sm, htmax_pv he⟩, fun he => ⟨tmax, htmax_sm, htmax_pc he⟩⟩
  · -- Pre-state: (N, V) ≠ (n, v). collect_recvd_locks leaves argmax_recvd_* and
    -- prevoted_node / precommitted_node at (N, V) untouched, so the pre-state instance
    -- of argmax_recvd_qc_backed (hinv conjunct 42) applies.
    rw [if_neg h_match] at h_ixn h_stage h_view
    exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      N V IM SM VM h_byz h_ixn h_stage h_view



theorem respond_propose_repropose_reproposal_extends_decided_parent (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_propose_repropose_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1292099 view interaction χ node nodeset stage χ_rep]
    [respond_propose_repropose_dec_1 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1292170 node view χ interaction nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_propose_repropose.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_propose_repropose_dec_0
          respond_propose_repropose_dec_1 n v ixn)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@reproposal_extends_decided_parent ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited
          interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage
          stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs op_w hop hpr h_no_prev hixn_ng hrc t t_1 t_2
    hari has hav h_stage_eq h_ixn_eq h_height_eq N V J hnbyz h_prev_post hJ_ng hV_nz h_argstage
  -- hinv positions (same declaration order as the locks_analog_precommit proof below):
  -- reproposal_extends_decided_parent=10, argmax_recvd_is_highest_lock=27,
  -- argmax_recvd_qc_backed=42, highest_lock_sent=76 (main_safety counted at 28).
  obtain ⟨_, _, _, _, _,
          _, _, _, _, h_repr,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, h_arihl, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, h_qcb, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          h_hls,
          _⟩ := hinv
  subst h_ixn_eq
  by_cases h_match : N = n ∧ V = v ∧ J = ixn
  · -- New prevote at (n, v, ixn): the cached argmax is prevote-stage, hence QC-backed
    -- at v_max (argmax_recvd_qc_backed), and v_max < v via highest_lock_sent applied to
    -- the argmax witness (argmax_recvd_is_highest_lock).
    obtain ⟨hNeq, hVeq, hJeq⟩ := h_match
    subst N; subst V; subst J
    obtain ⟨Q, hQ_sm, hQ_mem⟩ := (h_qcb n v ixn t_1 t_2 hnbyz hari has hav).1 h_stage_eq
    obtain ⟨M, h_sent, _⟩ := h_arihl n v ixn t_1 t_2 hnbyz hari has hav
    have h_vmax_lt : tot_view.lt t_2 v := (h_hls M v ixn t_1 t_2 h_sent).2.1
    exact ⟨t_2, h_vmax_lt, Q, hQ_sm, fun m hm => by simp [hQ_mem m hm]⟩
  · -- Pre-existing prevote: (N, V, J) ≠ (n, v, ixn), so the pre-state invariant applies
    -- and its witnesses survive (prevoted_node only grows under this action).
    have h_neq : n = N → v = V → ¬ ixn = J := by
      intro hnN hvV hixnJ
      exact h_match ⟨hnN.symm, hvV.symm, hixnJ.symm⟩
    obtain ⟨VM, hVM_lt, s, hs_sm, hs_mem⟩ :=
      h_repr N V J hnbyz (h_prev_post h_neq) hJ_ng hV_nz h_argstage
    exact ⟨VM, hVM_lt, s, hs_sm, fun m hm => by simp [hs_mem m hm]⟩

theorem respond_propose_extend_locks_analog_precommit (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_propose_extend_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1376353 view interaction χ node nodeset stage χ_rep]
    [respond_propose_extend_dec_1 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1376424 node view χ interaction nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_propose_extend.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_propose_extend_dec_0
          respond_propose_extend_dec_1 n v ixn)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@locks_analog_precommit ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs op_w hop hpr h_no_prev hixn_ng hrc t t_1 t_2
    hari has hav h_stage_eq h_ixn_neq h_parent h_height_eq V V2 I J NP hnbyz hpb hI_ng hJ_ng h_prev_post hlt
  -- Mirrors respond_propose_repropose_locks_analog_precommit. The ONLY structural
  -- difference: the new prevote J = ixn is the FRESH CHILD of the argmax interaction
  -- t (= ixn_max) — `require parent ixn_max ixn` — rather than ixn = ixn_max. So Step 3
  -- (h_step3) yields `I = t ∨ ancestor I t`; h_lift raises both branches to the goal
  -- `ixn = I ∨ ancestor I ixn` via h_anc_par (parent t ixn ⇒ ancestor t ixn) and
  -- h_anc_trans (transitivity). hinv positions for IFPNTDPH's CURRENT declaration order
  -- (main_safety + indented invariants counted):
  -- locks_analog_precommit=1, argmax_recvd_ixn_descends...=2,
  -- recvd_collected_implies_bounded_prepare_quorum=3, precommit_node_locked_at_same_view=46,
  -- precommit_backed_fwd=60, precommit_lock_implies_precommit_backed=72, highest_lock_sent=76,
  -- ancestor_from_parent=98, ancestor_trans=99.
  obtain ⟨h_lap,
          h_step3,
          h_rcibpq,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _,
          h_pcnlsv,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _,
          h_pbf,
          _, _, _, _, _,
          _, _, _, _, _,
          _,
          h_plipb,
          _, _, _,
          h_hls,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _,
          h_anc_par,
          h_anc_trans,
          _⟩ := hinv
  by_cases h_match : NP = n ∧ V2 = v ∧ J = ixn
  · obtain ⟨hNPeq, hV2eq, hJeq⟩ := h_match
    subst NP; subst V2; subst J
    -- Raise Step 3's `W = t ∨ ancestor W t` (t = ixn_max) to `ixn = W ∨ ancestor W ixn`,
    -- the goal with J = ixn, using parent t ixn (h_parent) + ancestor_from_parent + trans.
    have h_lift : ∀ (W : interaction),
        (W = t ∨ st.ancestor W t) → (ixn = W ∨ st.ancestor W ixn) := by
      intro W hW
      cases hW with
      | inl heq => exact Or.inr (by rw [heq]; exact h_anc_par t ixn h_parent)
      | inr hanc => exact Or.inr (h_anc_trans W t ixn hanc (h_anc_par t ixn h_parent))
    by_cases h_le : TotalOrderWithMinimum.le V t_2
    · exact h_lift I (h_step3 V v t_2 I t n hnbyz hpb hI_ng hari hav hlt h_le)
    · have le_lt_trans : ∀ {a b c : view},
          TotalOrderWithMinimum.le a b → TotalOrderWithMinimum.lt b c →
          TotalOrderWithMinimum.lt a c := by
        intros a b c hab hbc
        have ⟨hbc_le, hbc_ne⟩ := (tot_view.le_lt _ _).mp hbc
        refine (tot_view.le_lt _ _).mpr ⟨tot_view.le_trans _ _ _ hab hbc_le, ?_⟩
        rintro rfl
        exact hbc_ne (tot_view.le_antisymm _ _ hab hbc_le).symm
      have h_t2_lt_V : TotalOrderWithMinimum.lt t_2 V := by
        rcases tot_view.le_total V t_2 with hVT | hTV
        · exact absurd hVT h_le
        · refine (tot_view.le_lt _ _).mpr ⟨hTV, ?_⟩
          rintro rfl
          exact h_le (tot_view.le_refl _)
      obtain ⟨t_set, ht_sm, ht_mem⟩ := h_pbf V I hpb
      obtain ⟨s_set, hs_sm, hs_mem⟩ := h_rcibpq n v t_2 hrc hav
      obtain ⟨mstar, hm_s, hm_t, hm_honest⟩ :=
        ctx.supermajorities_intersect_in_honest s_set t_set ⟨hs_sm, ht_sm⟩
      have hpc_m : st.precommitted_node mstar V I = true := ht_mem mstar hm_t
      obtain ⟨_, IL, SL, VL, h_slip, _, h_VL_le⟩ := hs_mem mstar hm_s
      obtain ⟨_, _, h_no_lock_btw, _⟩ := h_hls mstar v IL SL VL h_slip
      have h_VL_lt_V : TotalOrderWithMinimum.lt VL V := le_lt_trans h_VL_le h_t2_lt_V
      have h_lock_choice := h_pcnlsv mstar V I hm_honest hpc_m hI_ng
      cases h_lock_choice with
      | inl h_prev_V =>
        have h_no := h_no_lock_btw I th.prevote V h_VL_lt_V hlt
        exact absurd h_prev_V (fun h => by rw [h] at h_no; exact Bool.noConfusion h_no)
      | inr h_pre_exists =>
        obtain ⟨U, h_U_le_V, h_loc_U⟩ := h_pre_exists
        by_cases h_U_le_t2 : TotalOrderWithMinimum.le U t_2
        · have h_pb_U : st.precommit_backed U I = true := h_plipb mstar I U h_loc_U hI_ng
          have h_U_lt_v : TotalOrderWithMinimum.lt U v := le_lt_trans h_U_le_V hlt
          exact h_lift I (h_step3 U v t_2 I t n hnbyz h_pb_U hI_ng hari hav h_U_lt_v h_U_le_t2)
        · have h_t2_lt_U : TotalOrderWithMinimum.lt t_2 U := by
            rcases tot_view.le_total U t_2 with hUT | hTU
            · exact absurd hUT h_U_le_t2
            · refine (tot_view.le_lt _ _).mpr ⟨hTU, ?_⟩
              rintro rfl
              exact h_U_le_t2 (tot_view.le_refl _)
          have h_VL_lt_U : TotalOrderWithMinimum.lt VL U := le_lt_trans h_VL_le h_t2_lt_U
          have h_U_lt_v : TotalOrderWithMinimum.lt U v := le_lt_trans h_U_le_V hlt
          have h_no := h_no_lock_btw I th.precommit U h_VL_lt_U h_U_lt_v
          exact absurd h_loc_U (fun h => by rw [h] at h_no; exact Bool.noConfusion h_no)
  · have h_neq : n = NP → v = V2 → ¬ixn = J := by
      intro hnNP hvV2 hixnJ
      exact h_match ⟨hnNP.symm, hvV2.symm, hixnJ.symm⟩
    exact h_lap V V2 I J NP hnbyz hpb hI_ng hJ_ng (h_prev_post h_neq) hlt


-- Successfully Proven.
theorem collect_recvd_locks_recvd_collected_implies_bounded_prepare_quorum (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [collect_recvd_locks_dec_0 : delta% @IFPProtocolNTDPH._veil_dec_type_1167942 nodeset node ctx]
    [collect_recvd_locks_dec_1 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1168068 view nodeset χ node ctx interaction stage χ_rep tot_view]
    [collect_recvd_locks_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1168172 view χ node interaction stage nodeset χ_rep tot_view]
    [collect_recvd_locks_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1168284 view χ node interaction stage tot_view nodeset χ_rep]
    [collect_recvd_locks_dec_4 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1168414 interaction stage view χ node nodeset ctx χ_rep] :
    ∀ (n : node) (v : view) (s : nodeset) (n_max : node) (ixn_max : interaction) (s_max : stage) (v_max : view),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@collect_recvd_locks.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub collect_recvd_locks_dec_0
          collect_recvd_locks_dec_1 collect_recvd_locks_dec_2 collect_recvd_locks_dec_3 collect_recvd_locks_dec_4 n v s
          n_max ixn_max s_max v_max)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@recvd_collected_implies_bounded_prepare_quorum ρ σ view view_dec_eq view_inhabited node node_dec_eq
          node_inhabited interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited
          stage stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs hpn hnrc hsm hmem hsl_max hlk_max hdom hgap tmax htmax_sm htmax_pv
    htmax_pc N VACT VMAX h_rc h_av
  by_cases h_match : N = n ∧ VACT = v
  · -- New write at (n, v): the action's own prepare-quorum `s` witnesses RISK1, and
    -- VMAX = v_max via the argmax_recvd_view decide-update. VL ≤ VMAX comes from the
    -- argmax-dominance precondition `hdom`, NOT the per-member `vl ≤ v`.
    obtain ⟨hN, hV⟩ := h_match
    subst N
    subst VACT
    refine ⟨s, hsm, fun m hm => ?_⟩
    obtain ⟨h_prep, vl, ixnl, sl, h_sent, h_lock, _⟩ := hmem m hm
    refine ⟨h_prep, ixnl, sl, vl, h_sent, h_lock, ?_⟩
    have h_dom : tot_view.le vl v_max := hdom m ixnl sl vl h_sent
    rw [if_pos (And.intro rfl rfl)] at h_av
    rw [h_av]
    exact h_dom
  · -- Pre-state: (N, VACT) ≠ (n, v). collect_recvd_locks only writes recvd_collected /
    -- argmax_recvd_*, leaving sent_lock_in_prepare / locked / prepared_node untouched, so
    -- RISK1's pre-state instance (h_risk1 from hinv, declaration position 3) applies.
    obtain ⟨_, _, h_risk1, _⟩ := hinv
    have h_rc_pre : st.recvd_collected N VACT = true :=
      h_rc (fun hn hv => h_match ⟨hn.symm, hv.symm⟩)
    have h_match' : ¬(n = N ∧ v = VACT) := fun h => h_match ⟨h.1.symm, h.2.symm⟩
    rw [if_neg h_match'] at h_av
    exact h_risk1 N VACT VMAX h_rc_pre h_av

theorem respond_propose_repropose_locks_analog_precommit (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_propose_repropose_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1292099 view interaction χ node nodeset stage χ_rep]
    [respond_propose_repropose_dec_1 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1292170 node view χ interaction nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_propose_repropose.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_propose_repropose_dec_0
          respond_propose_repropose_dec_1 n v ixn)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@locks_analog_precommit ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs op_w hop hpr h_no_prev hixn_ng hrc t t_1 t_2
    hari has hav h_stage_eq h_ixn_eq h_height_eq V V2 I J NP hnbyz hpb hI_ng hJ_ng h_prev_post hlt
  -- PORTED from IFPNTDP.lean L2004-2159 (working). hinv positions for IFPNTDPH's
  -- CURRENT declaration order (main_safety + indented invariants counted):
  -- locks_analog_precommit=1, argmax_recvd_ixn_descends...=2,
  -- recvd_collected_implies_bounded_prepare_quorum=3, precommit_node_locked_at_same_view=46,
  -- precommit_backed_fwd=60, precommit_lock_implies_precommit_backed=72, highest_lock_sent=76.
  obtain ⟨h_lap,
          h_step3,
          h_rcibpq,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _,
          h_pcnlsv,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _,
          h_pbf,
          _, _, _, _, _,
          _, _, _, _, _,
          _,
          h_plipb,
          _, _, _,
          h_hls,
          _⟩ := hinv
  subst h_ixn_eq
  by_cases h_match : NP = n ∧ V2 = v ∧ J = ixn
  · obtain ⟨hNPeq, hV2eq, hJeq⟩ := h_match
    subst NP; subst V2; subst J
    by_cases h_le : TotalOrderWithMinimum.le V t_2
    · have h := h_step3 V v t_2 I ixn n hnbyz hpb hI_ng hari hav hlt h_le
      cases h with
      | inl heq => exact Or.inl heq.symm
      | inr hanc => exact Or.inr hanc
    · have le_lt_trans : ∀ {a b c : view},
          TotalOrderWithMinimum.le a b → TotalOrderWithMinimum.lt b c →
          TotalOrderWithMinimum.lt a c := by
        intros a b c hab hbc
        have ⟨hbc_le, hbc_ne⟩ := (tot_view.le_lt _ _).mp hbc
        refine (tot_view.le_lt _ _).mpr ⟨tot_view.le_trans _ _ _ hab hbc_le, ?_⟩
        rintro rfl
        exact hbc_ne (tot_view.le_antisymm _ _ hab hbc_le).symm
      have h_t2_lt_V : TotalOrderWithMinimum.lt t_2 V := by
        rcases tot_view.le_total V t_2 with hVT | hTV
        · exact absurd hVT h_le
        · refine (tot_view.le_lt _ _).mpr ⟨hTV, ?_⟩
          rintro rfl
          exact h_le (tot_view.le_refl _)
      obtain ⟨t_set, ht_sm, ht_mem⟩ := h_pbf V I hpb
      obtain ⟨s_set, hs_sm, hs_mem⟩ := h_rcibpq n v t_2 hrc hav
      obtain ⟨mstar, hm_s, hm_t, hm_honest⟩ :=
        ctx.supermajorities_intersect_in_honest s_set t_set ⟨hs_sm, ht_sm⟩
      have hpc_m : st.precommitted_node mstar V I = true := ht_mem mstar hm_t
      obtain ⟨_, IL, SL, VL, h_slip, _, h_VL_le⟩ := hs_mem mstar hm_s
      obtain ⟨_, _, h_no_lock_btw, _⟩ := h_hls mstar v IL SL VL h_slip
      have h_VL_lt_V : TotalOrderWithMinimum.lt VL V := le_lt_trans h_VL_le h_t2_lt_V
      have h_lock_choice := h_pcnlsv mstar V I hm_honest hpc_m hI_ng
      cases h_lock_choice with
      | inl h_prev_V =>
        have h_no := h_no_lock_btw I th.prevote V h_VL_lt_V hlt
        exact absurd h_prev_V (fun h => by rw [h] at h_no; exact Bool.noConfusion h_no)
      | inr h_pre_exists =>
        obtain ⟨U, h_U_le_V, h_loc_U⟩ := h_pre_exists
        by_cases h_U_le_t2 : TotalOrderWithMinimum.le U t_2
        · have h_pb_U : st.precommit_backed U I = true := h_plipb mstar I U h_loc_U hI_ng
          have h_U_lt_v : TotalOrderWithMinimum.lt U v := le_lt_trans h_U_le_V hlt
          have h := h_step3 U v t_2 I ixn n hnbyz h_pb_U hI_ng hari hav h_U_lt_v h_U_le_t2
          cases h with
          | inl heq => exact Or.inl heq.symm
          | inr hanc => exact Or.inr hanc
        · have h_t2_lt_U : TotalOrderWithMinimum.lt t_2 U := by
            rcases tot_view.le_total U t_2 with hUT | hTU
            · exact absurd hUT h_U_le_t2
            · refine (tot_view.le_lt _ _).mpr ⟨hTU, ?_⟩
              rintro rfl
              exact h_U_le_t2 (tot_view.le_refl _)
          have h_VL_lt_U : TotalOrderWithMinimum.lt VL U := le_lt_trans h_VL_le h_t2_lt_U
          have h_U_lt_v : TotalOrderWithMinimum.lt U v := le_lt_trans h_U_le_V hlt
          have h_no := h_no_lock_btw I th.precommit U h_VL_lt_U h_U_lt_v
          exact absurd h_loc_U (fun h => by rw [h] at h_no; exact Bool.noConfusion h_no)
  · have h_neq : n = NP → v = V2 → ¬ixn = J := by
      intro hnNP hvV2 hixnJ
      exact h_match ⟨hnNP.symm, hvV2.symm, hixnJ.symm⟩
    exact h_lap V V2 I J NP hnbyz hpb hI_ng hJ_ng (h_prev_post h_neq) hlt


theorem respond_prevote_recvd_collected_implies_bounded_prepare_quorum (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_prevote_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532375 view interaction χ node nodeset stage χ_rep]
    [respond_prevote_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1532428 nodeset node ctx]
    [respond_prevote_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532505 view interaction nodeset χ node ctx stage χ_rep]
    [respond_prevote_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532590 node view interaction χ nodeset stage tot_view χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_prevote.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_prevote_dec_0 respond_prevote_dec_1
          respond_prevote_dec_2 respond_prevote_dec_3 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@recvd_collected_implies_bounded_prepare_quorum ρ σ view view_dec_eq view_inhabited node node_dec_eq
          node_inhabited interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited
          stage stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  -- Same shape as respond_prevote_argmax_recvd_is_highest_lock: veil_wp yields
  -- `if ∃u… then A else B` with the invariant's ∀-binders inside each branch.
  -- recvd_collected / argmax_recvd_view / prepared_node / sent_lock_in_prepare are all
  -- frame-unchanged, so the pre-state instance (hinv position 3) closes the then-branch
  -- verbatim; in the else-branch each member's witness lock discharges the tuple guard.
  intro hv_nz hcv hcs x hop hpr hsm hmem
  obtain ⟨_, _, h_self, _⟩ := hinv
  split_ifs
  · exact h_self
  · intro N VACT VMAX h_rc h_av
    obtain ⟨s_w, hsm_w, hmem_w⟩ := h_self N VACT VMAX h_rc h_av
    refine ⟨s_w, hsm_w, fun m hm => ?_⟩
    obtain ⟨h_prep, IL, SL, VL, h_sent, h_lock, h_le⟩ := hmem_w m hm
    exact ⟨h_prep, IL, SL, VL, h_sent, fun _ => h_lock, h_le⟩


theorem respond_precommit_highest_decided_ixn_height_upper_bound (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_precommit_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693057 view interaction χ node nodeset stage χ_rep]
    [respond_precommit_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1693110 nodeset node ctx]
    [respond_precommit_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693187 view interaction nodeset χ node ctx stage χ_rep]
    [respond_precommit_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693266 node interaction χ view nodeset stage χ_rep]
    [respond_precommit_dec_4 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693359 node interaction χ view nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_precommit.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_precommit_dec_0 respond_precommit_dec_1
          respond_precommit_dec_2 respond_precommit_dec_3 respond_precommit_dec_4 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@highest_decided_ixn_height_upper_bound ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited
          interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage
          stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs x hop hpo hsm hmem hdec1
  -- Pre-state highest_decided_ixn_height_upper_bound is hinv conjunct #54.
  have h_ub := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  split_ifs with h_guard
  · -- Guard fired: some ci_old was committed strictly below height ixn, so
    -- highest_decided_ixn n is rewritten to {ixn}. New decision closes by refl;
    -- old decisions are ≤ height ci_old < height ixn by the pre-state bound.
    obtain ⟨ci_old, h_ci_old, h_lt⟩ := h_guard
    intro N V I CI h_byz hdec h_ci
    by_cases h_new : n = N ∧ v = V ∧ ixn = I
    · obtain ⟨hN, -, hI⟩ := h_new
      rw [if_pos hN] at h_ci
      rw [← hI, h_ci]
    · have h_old : st.decided N V I = true := hdec fun h1 h2 h3 => h_new ⟨h1, h2, h3⟩
      by_cases hN : n = N
      · rw [if_pos hN] at h_ci
        rw [hN] at h_ci_old
        have h54 := h_ub N V I ci_old h_byz h_old h_ci_old
        rw [h_ci]
        omega
      · rw [if_neg hN] at h_ci
        exact h_ub N V I CI h_byz h_old h_ci
  · -- Guard did not fire: highest_decided_ixn is unchanged and every committed ci
    -- already sits at height ≥ height ixn, bounding the new decision too.
    intro N V I CI h_byz hdec h_ci
    by_cases h_new : n = N ∧ v = V ∧ ixn = I
    · obtain ⟨hN, -, hI⟩ := h_new
      rw [← hN] at h_ci
      rw [← hI]
      rcases Nat.lt_or_ge (st.height CI) (st.height ixn) with h | h
      · exact absurd ⟨CI, h_ci, h⟩ h_guard
      · omega
    · have h_old : st.decided N V I = true := hdec fun h1 h2 h3 => h_new ⟨h1, h2, h3⟩
      exact h_ub N V I CI h_byz h_old h_ci

theorem respond_precommit_committed_descendant_height_bound (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_precommit_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693057 view interaction χ node nodeset stage χ_rep]
    [respond_precommit_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1693110 nodeset node ctx]
    [respond_precommit_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693187 view interaction nodeset χ node ctx stage χ_rep]
    [respond_precommit_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693266 node interaction χ view nodeset stage χ_rep]
    [respond_precommit_dec_4 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693359 node interaction χ view nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_precommit.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_precommit_dec_0 respond_precommit_dec_1
          respond_precommit_dec_2 respond_precommit_dec_3 respond_precommit_dec_4 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@committed_descendant_height_bound ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited
          interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage
          stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs x hop hpo hsm hmem hdec1 N A H h_byz h_cdah
  -- pre-state committed_descendant_height_bound (conjunct #87)
  have h_cb := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- ancestor_height_strict (conjunct #101)
  have h_ahs := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases hN : n = N
  · -- ghost marker for N is the just-written set: pre-existing or the new (ancestor A ixn, H = height ixn)
    rw [if_pos hN] at h_cdah
    rcases h_cdah with h_old | ⟨h_anc, h_H⟩
    · rw [hN] at h_old
      exact h_cb N A H h_byz h_old
    · by_cases h_eq : A = ixn
      · rw [h_eq]; omega
      · have := h_ahs A ixn h_anc h_eq; omega
  · rw [if_neg hN] at h_cdah
    exact h_cb N A H h_byz h_cdah

theorem respond_precommit_locked_descendant_height_bound (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_precommit_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693057 view interaction χ node nodeset stage χ_rep]
    [respond_precommit_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1693110 nodeset node ctx]
    [respond_precommit_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693187 view interaction nodeset χ node ctx stage χ_rep]
    [respond_precommit_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693266 node interaction χ view nodeset stage χ_rep]
    [respond_precommit_dec_4 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693359 node interaction χ view nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_precommit.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_precommit_dec_0 respond_precommit_dec_1
          respond_precommit_dec_2 respond_precommit_dec_3 respond_precommit_dec_4 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@locked_descendant_height_bound ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs x hop hpo hsm hmem hdec1 N A H h_byz h_ldah
  -- pre-state locked_descendant_height_bound (conjunct #86)
  have h_lb := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- ancestor_height_strict (conjunct #101)
  have h_ahs := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases hN : n = N
  · rw [if_pos hN] at h_ldah
    rcases h_ldah with h_old | ⟨h_anc, h_H⟩
    · rw [hN] at h_old
      exact h_lb N A H h_byz h_old
    · by_cases h_eq : A = ixn
      · rw [h_eq]; omega
      · have := h_ahs A ixn h_anc h_eq; omega
  · rw [if_neg hN] at h_ldah
    exact h_lb N A H h_byz h_ldah

theorem respond_precommit_committed_descendant_at_height_bwd (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_precommit_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693057 view interaction χ node nodeset stage χ_rep]
    [respond_precommit_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1693110 nodeset node ctx]
    [respond_precommit_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693187 view interaction nodeset χ node ctx stage χ_rep]
    [respond_precommit_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693266 node interaction χ view nodeset stage χ_rep]
    [respond_precommit_dec_4 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693359 node interaction χ view nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_precommit.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_precommit_dec_0 respond_precommit_dec_1
          respond_precommit_dec_2 respond_precommit_dec_3 respond_precommit_dec_4 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@committed_descendant_at_height_bwd ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited
          interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage
          stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs x hop hpo hsm hmem hdec1 N A H h_byz h_cdah
  -- pre-state committed_descendant_at_height_bwd (conjunct #85)
  have h_bwd := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases hN : n = N
  · rw [if_pos hN] at h_cdah
    rcases h_cdah with h_old | ⟨h_anc, h_H⟩
    · -- pre-existing ghost bit ⇒ pre-state witness, decided survives (monotone)
      rw [hN] at h_old
      obtain ⟨V, I, h_dec, h_anc2, h_ht⟩ := h_bwd N A H h_byz h_old
      exact ⟨V, I, fun _ => h_dec, h_anc2, h_ht⟩
    · -- new marker: the just-decided ixn is the witness (N = n, decided n v ixn)
      exact ⟨v, ixn, fun hguard => absurd rfl (hguard hN rfl), h_anc, h_H.symm⟩
  · rw [if_neg hN] at h_cdah
    obtain ⟨V, I, h_dec, h_anc2, h_ht⟩ := h_bwd N A H h_byz h_cdah
    exact ⟨V, I, fun _ => h_dec, h_anc2, h_ht⟩

theorem respond_precommit_locked_descendant_at_height_bwd (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_precommit_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693057 view interaction χ node nodeset stage χ_rep]
    [respond_precommit_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1693110 nodeset node ctx]
    [respond_precommit_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693187 view interaction nodeset χ node ctx stage χ_rep]
    [respond_precommit_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693266 node interaction χ view nodeset stage χ_rep]
    [respond_precommit_dec_4 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693359 node interaction χ view nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_precommit.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_precommit_dec_0 respond_precommit_dec_1
          respond_precommit_dec_2 respond_precommit_dec_3 respond_precommit_dec_4 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@locked_descendant_at_height_bwd ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited
          interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage
          stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs x hop hpo hsm hmem hdec1 N A H h_byz h_ldah
  -- pre-state locked_descendant_at_height_bwd (conjunct #84)
  have h_bwd := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases hN : n = N
  · rw [if_pos hN] at h_ldah
    rcases h_ldah with h_old | ⟨h_anc, h_H⟩
    · rw [hN] at h_old
      obtain ⟨I, ⟨S, V, h_lock⟩, h_anc2, h_ht⟩ := h_bwd N A H h_byz h_old
      exact ⟨I, ⟨S, V, fun _ => h_lock⟩, h_anc2, h_ht⟩
    · -- new marker: the just-created precommit lock on ixn at v is the witness
      exact ⟨ixn, ⟨th.precommit, v, fun hguard => absurd rfl (hguard hN rfl rfl)⟩, h_anc, h_H.symm⟩
  · rw [if_neg hN] at h_ldah
    obtain ⟨I, ⟨S, V, h_lock⟩, h_anc2, h_ht⟩ := h_bwd N A H h_byz h_ldah
    exact ⟨I, ⟨S, V, fun _ => h_lock⟩, h_anc2, h_ht⟩

theorem respond_precommit_committed_implies_parent_committed (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_precommit_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693057 view interaction χ node nodeset stage χ_rep]
    [respond_precommit_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1693110 nodeset node ctx]
    [respond_precommit_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693187 view interaction nodeset χ node ctx stage χ_rep]
    [respond_precommit_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693266 node interaction χ view nodeset stage χ_rep]
    [respond_precommit_dec_4 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693359 node interaction χ view nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_precommit.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_precommit_dec_0 respond_precommit_dec_1
          respond_precommit_dec_2 respond_precommit_dec_3 respond_precommit_dec_4 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@committed_implies_parent_committed ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited
          interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage
          stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs x hop hpo hsm hmem hdec1 M V J I hdec h_par h_Jg
  -- precommit_qc_unique_at_view (#12)
  have h_qcu := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  -- committed_implies_parent_committed pre-state (#56)
  have h_cipc := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- precommitted_node_view_bound (#59)
  have h_pvb := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- precommit_backed_fwd (#60)
  have h_pbf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- parent_irreflexive (#107)
  have h_pirr := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- genesis_decided_at_zero (#150)
  have h_gz := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- precommit_backed_implies_decided bridge (#178)
  have h_pbd := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- parent_implies_parent_precommit_backed (#180; #181 reproposed_implies_argmax follows, hence trailing .1)
  have h_pipb := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases h_new : n = M ∧ v = V ∧ ixn = J
  · -- CASE B: the tuple (M, V, J) is the new decision (n, v, ixn).
    obtain ⟨hM, hV, hJ⟩ := h_new
    subst hM; subst hV; subst hJ
    by_cases h_Ig : I = st.genesis
    · -- parent is genesis: decided by every node at view zero < v
      rw [h_Ig]
      exact ⟨tot_view.zero,
        (tot_view.le_lt tot_view.zero v).mpr ⟨tot_view.zero_lt v, fun h => hv_nz h.symm⟩,
        n, fun _ => h_gz n⟩
    · -- Non-genesis parent: by construction, `parent I ixn` was written at ixn's
      -- propose_extend birth with I = the proposer's highest_decided_ixn (an action
      -- require, binding Byzantine operators too), so I is precommit-backed at
      -- some W (#180) and hence decided at W by some node (#178). W ≠ v: the
      -- W-quorum from precommit_backed_fwd (#60) against this action's (v, ixn)
      -- precommit quorum forces I = ixn via precommit_qc_unique_at_view (#12),
      -- killed by parent_irreflexive (#107). W ≤ v: an honest member of the
      -- W-quorum precommitted at W while cur_view is v (#59). Hence W < v.
      obtain ⟨W, h_pb⟩ := h_pipb I ixn h_par h_Ig
      obtain ⟨n', h_dec'⟩ := h_pbd W I h_pb
      obtain ⟨s1, hs1_sm, hs1_mem⟩ := h_pbf W I h_pb
      obtain ⟨m1, hm1_mem, -, hm1_hon⟩ :=
        ctx.supermajorities_intersect_in_honest s1 s1 ⟨hs1_sm, hs1_sm⟩
      have h_le : tot_view.le W v := h_pvb m1 n v W I hm1_hon hcv (hs1_mem m1 hm1_mem)
      have h_ne : W ≠ v := by
        intro h_eq
        rw [h_eq] at hs1_mem
        have h_I : I = ixn := h_qcu v I ixn s1 hs1_sm hs1_mem s hsm hmem
        rw [h_I, h_pirr] at h_par
        exact Bool.noConfusion h_par
      exact ⟨W, (tot_view.le_lt W v).mpr ⟨h_le, h_ne⟩, n', fun _ => h_dec'⟩
  · -- CASE A: pre-existing decision — pre-state invariant + decided monotone.
    have h_dJ : st.decided M V J = true := hdec fun h1 h2 h3 => h_new ⟨h1, h2, h3⟩
    obtain ⟨u, h_lt, x₀, h_dI⟩ := h_cipc M V J I h_dJ h_par h_Jg
    exact ⟨u, h_lt, x₀, fun _ => h_dI⟩

end IFPProtocolNTDPH
