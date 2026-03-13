-- IFPInvGenU: IFP model based on IFPInvGenT with two additional ghost relations:
-- 1. proposed_for_descendant: "at view V, the proposed interaction is a descendant of A"
-- 2. decided_for_descendant: "node N decided a descendant of A at view V"
-- These bridge the two remaining gaps in the safety proof chain:
--   Gap 1: proposal extends locked descendants (via proposed_for_descendant)
--   Gap 2: decision inherits proposal ancestry (via decided_for_descendant)

import Veil

veil module IFPProtocolU


class IFPByzQuorum (node : Type) (nset : Type) where
  is_byz : node → Prop
  member (n : node) (s : nset) : Prop
  supermajority (s : nset) (c : nset) : Prop   -- s is a supermajority of context c  -- 2f + 1 nodes

  supermajority_s_belongs_to_c :
    ∀ (s c : nset), supermajority s c → ∀ (n : node), (member n s → member n c)

  supermajorities_intersect_in_honest :
    ∀ (s1 s2 c : nset),
      (supermajority s1 c ∧ supermajority s2 c) → (∃ (n : node), member n s1 ∧ member n s2 ∧ ¬ is_byz n)


-- `type declarations`
type view
type participant
type node
type interaction
type nodeset
type stage

-- `instantiations`
instantiate tot_view : TotalOrderWithMinimum view
instantiate ctx : IFPByzQuorum node nodeset

-- `individuals`
immutable individual p1_fixed : participant
immutable individual p2_fixed : participant

immutable individual prepare : stage
immutable individual propose : stage
immutable individual prevote : stage
immutable individual precommit : stage
immutable individual commit : stage

individual genesis : interaction

-- `immutable relations`
immutable relation interactions : interaction → participant → participant → Bool
immutable relation participant_context: participant → nodeset → Bool


-- `mutable relations and functions`
relation cur_view: node → view → Bool
relation cur_stage : node → view → participant → participant → stage → Bool
relation sent_lock_in_prepare_1 : node → view → participant → participant → interaction → stage → view → Bool
relation sent_lock_in_prepare_2 : node → view → participant → participant → interaction → stage → view → Bool
relation decided : node → view → participant → participant → interaction → Bool
relation locked : node → participant → interaction → stage → view → Bool

-- Operator relations
relation operator: node → view → participant → participant → Bool
relation prepared_operator : node → view → participant → participant → Bool
relation proposed : node → view → participant → participant → interaction → Bool
relation proposed_nil : node → view → participant → participant → Bool
relation prevoted_operator : node → view → participant → participant → interaction → Bool
relation precommitted_operator : node → view → participant → participant → interaction → Bool

-- Non-operator relations
relation prepared_node : node → view → participant → participant → Bool
relation prevoted_node : node → view → participant → participant → interaction → Bool
relation precommitted_node : node → view → participant → participant → interaction → Bool

-- Interaction relations
relation parent : interaction → interaction → Bool
relation ancestor : interaction → interaction → Bool
function height : interaction → Nat

-- ####################################################################
-- # Ghost Relations (HotStuff-style, maintained in actions)
-- ####################################################################

-- "Node N has some lock for participant P at exactly view V"
relation locked_at_view : node → participant → view → Bool

-- "Node N has a lock for participant P on some descendant of A at exactly view V"
-- i.e., ∃ I S, locked N P I S V ∧ ancestor A I
relation locked_for_descendant : node → participant → interaction → view → Bool

-- "At view V, the proposed interaction is a descendant of A"
-- i.e., ∃ op I, proposed op V p1_fixed p2_fixed I ∧ ancestor A I
relation proposed_for_descendant : view → interaction → Bool

-- "Node N decided a descendant of A at view V"
-- i.e., ∃ I, decided N V p1_fixed p2_fixed I ∧ ancestor A I
relation decided_for_descendant : node → interaction → view → Bool

-- ####################################################################
-- # Highest Lock Relations (EPR-friendly proposal support)
-- ####################################################################
-- Records the highest lock extracted by the operator from each context's
-- supermajority of prepare responses. Set by collect_and_extract, read by
-- propose_repropose/propose_extend/propose_nil/respond_propose.
-- Eliminates ∃∀∃∀ from propose and respond_propose preconditions.

relation highest_lock_1 : node → view → participant → participant → interaction → stage → view → Bool
relation highest_lock_2 : node → view → participant → participant → interaction → stage → view → Bool


#gen_state

-- `assumptions`

assumption ∀ (i : interaction) (p q : participant),
  interactions i p q → (p = p1_fixed ∧ q = p2_fixed)

assumption p1_fixed ≠ p2_fixed

assumption ¬ (prepare = propose ∨ prepare = prevote ∨ prepare = precommit ∨ prepare = commit ∨
  propose = prevote ∨ propose = precommit ∨ propose = commit ∨ prevote = precommit ∨ prevote = commit ∨ precommit = commit)

assumption (participant_context P C1 ∧ participant_context P C2) → C1 = C2

-- `init`

after_init {
  parent I J := false;
  ancestor I J := decide $ (I = J);
  locked N P I S V := decide $ (I = genesis ∧ S = precommit ∧ V = tot_view.zero ∧ (P = p1_fixed ∨ P = p2_fixed));
  decided N V P Q I := decide $ (I = genesis ∧ V = tot_view.zero ∧ (P = p1_fixed ∧ Q = p2_fixed))
  height I := 0;
  cur_stage N V P Q S := decide $ (S = prepare ∧ (P = p1_fixed ∧ Q = p2_fixed));
  operator N V P Q := false;
  cur_view N V := decide $ (V = tot_view.zero);
  prepared_operator N V P Q := false;
  sent_lock_in_prepare_1 N U P Q L S V := false;
  sent_lock_in_prepare_2 N U P Q L S V := false;
  proposed N V P Q I := false;
  proposed_nil N V P Q := false;
  prevoted_operator N V P Q I := false;
  precommitted_operator N V P Q I := false;
  prepared_node N V P Q := false;
  prevoted_node N V P Q I := false;
  precommitted_node N V P Q I := false;
  -- Ghost init (locked)
  locked_at_view N P V := decide $ (V = tot_view.zero ∧ (P = p1_fixed ∨ P = p2_fixed));
  locked_for_descendant N P A V := decide $ (A = genesis ∧ V = tot_view.zero ∧ (P = p1_fixed ∨ P = p2_fixed));
  -- Ghost init (proposed/decided)
  proposed_for_descendant V A := false;
  decided_for_descendant N A V := decide $ (A = genesis ∧ V = tot_view.zero);
  -- Highest lock init
  highest_lock_1 N V P Q I S VL := false;
  highest_lock_2 N V P Q I S VL := false;
}

-- ####################################################################
-- # Actions
-- ####################################################################

action set_view (v_cur v_next : view) {
  require ∀ (n : node), cur_view n v_cur
  require tot_view.next v_cur v_next
  cur_view N V := decide $ (V = v_next)
}

action pick_operator (op : node) (v : view) (p1 p2 : participant) {
  require v ≠ tot_view.zero
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require cur_view op v
  require ∃ (c1 : nodeset), participant_context p1 c1 ∧ ctx.member op c1
  require ∀ (n : node), ¬ operator n v p1 p2
  operator op v p1 p2 := true
}

action operator_prepare (op : node) (v : view) (p1 p2 : participant) {
  require v ≠ tot_view.zero
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require cur_view op v
  require cur_stage op v p1 p2 prepare
  require operator op v p1 p2
  require ∃ (c1 c2 : nodeset), ((ctx.member op c1 ∨ ctx.member op c2) ∧ participant_context p1 c1 ∧ participant_context p2 c2)
  require ¬ prepared_operator op v p1 p2
  require ∃ (i : interaction), interactions i p1 p2
  prepared_operator op v p1 p2 := true
}

action respond_prepare (n : node) (v : view) (p1 p2 : participant) (c1 c2 : nodeset) {
  require v ≠ tot_view.zero
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require participant_context p1 c1 ∧ participant_context p2 c2
  require cur_view n v
  require cur_stage n v p1 p2 prepare
  require ∀ (p q : participant), ¬ (prepared_node n v p p2 ∨ prepared_node n v p1 q)
  require ∃ (op : node), (operator op v p1 p2 ∧ prepared_operator op v p1 p2)
  require ctx.member n c1 ∨ ctx.member n c2
  prepared_node n v p1 p2 := true
  sent_lock_in_prepare_1 n v p1 p2 IL SL VL := decide $
    (locked n p1 IL SL VL ∧
     ∃ (c1 : nodeset), (ctx.member n c1 ∧ participant_context p1 c1) ∧
     tot_view.lt VL v ∧
     (∀ (vl2 : view), tot_view.lt VL vl2 → ¬ ∃ (i2 : interaction) (s2 : stage), locked n p1 i2 s2 vl2) ∧
     (SL = prevote → ¬ locked n p1 IL precommit VL)
     )
  sent_lock_in_prepare_2 n v p1 p2 IL SL VL := decide $
    (locked n p2 IL SL VL ∧
     ∃ (c2 : nodeset), (ctx.member n c2 ∧ participant_context p2 c2) ∧
     tot_view.lt VL v ∧
     (∀ (vl2 : view), tot_view.lt VL vl2 → ¬ ∃ (i2 : interaction) (s2 : stage), locked n p2 i2 s2 vl2) ∧
     (SL = prevote → ¬ locked n p2 IL precommit VL)
     )
  cur_stage n v p1 p2 S := decide $ (S = propose)
}

-- ####################################################################
-- # Collect and Extract: the operator collects prepare responses from
-- # supermajorities of both contexts and extracts the highest lock from each.
-- # This replaces the ∃∀∃∀ precondition blocks that were duplicated across
-- # propose_repropose, propose_extend, propose_nil, and respond_propose.
-- # Quantifier structure: ∀ only (all existentials are Skolemized as parameters).
-- ####################################################################
action collect_and_extract (op : node) (v : view) (p1 p2 : participant) (c1 c2 : nodeset)
    (s1 s2 : nodeset)
    (n_max_1 : node) (ixn_max_1 : interaction) (s_max_1 : stage) (v_max_1 : view)
    (n_max_2 : node) (ixn_max_2 : interaction) (s_max_2 : stage) (v_max_2 : view) {
  require v ≠ tot_view.zero
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require participant_context p1 c1 ∧ participant_context p2 c2
  require cur_view op v
  require operator op v p1 p2
  require ctx.member op c1 ∨ ctx.member op c2
  require prepared_operator op v p1 p2
  require cur_stage op v p1 p2 propose
  require ∀ (ix : interaction), ¬ proposed op v p1 p2 ix
  require ¬ proposed_nil op v p1 p2
  -- No existing highest_lock for this view
  require ∀ (i : interaction) (s : stage) (vl : view), ¬ highest_lock_1 op v p1 p2 i s vl
  require ∀ (i : interaction) (s : stage) (vl : view), ¬ highest_lock_2 op v p1 p2 i s vl

  -- Supermajority of c1: all members prepared
  require ctx.supermajority s1 c1
  require ∀ (n : node), ctx.member n s1 → prepared_node n v p1 p2

  -- Supermajority of c2: all members prepared
  require ctx.supermajority s2 c2
  require ∀ (n : node), ctx.member n s2 → prepared_node n v p1 p2

  -- Highest lock for c1: n_max_1 sent the highest lock among c1 members
  require ctx.member n_max_1 c1
  require interactions ixn_max_1 p1 p2
  require sent_lock_in_prepare_1 n_max_1 v p1 p2 ixn_max_1 s_max_1 v_max_1
  require locked n_max_1 p1 ixn_max_1 s_max_1 v_max_1
  require ∀ (n_l : node) (ixn_l : interaction) (s_l : stage) (v_l : view),
    (ctx.member n_l c1 ∧ sent_lock_in_prepare_1 n_l v p1 p2 ixn_l s_l v_l) → (
      interactions ixn_l p1 p2 ∧
      (
        height ixn_l < height ixn_max_1
        ∨ (height ixn_l = height ixn_max_1 ∧ s_l = prevote ∧ s_max_1 = precommit)
        ∨ (height ixn_l = height ixn_max_1 ∧ s_l = s_max_1 ∧ tot_view.le v_l v_max_1)
        ∨ (ixn_l = ixn_max_1 ∧ s_l = s_max_1 ∧ v_l = v_max_1)
      )
    )

  -- Highest lock for c2: n_max_2 sent the highest lock among c2 members
  require ctx.member n_max_2 c2
  require interactions ixn_max_2 p1 p2
  require sent_lock_in_prepare_2 n_max_2 v p1 p2 ixn_max_2 s_max_2 v_max_2
  require locked n_max_2 p2 ixn_max_2 s_max_2 v_max_2
  require ∀ (n_l : node) (ixn_l : interaction) (s_l : stage) (v_l : view),
    (ctx.member n_l c2 ∧ sent_lock_in_prepare_2 n_l v p1 p2 ixn_l s_l v_l) → (
      interactions ixn_l p1 p2 ∧
      (
        height ixn_l < height ixn_max_2
        ∨ (height ixn_l = height ixn_max_2 ∧ s_l = prevote ∧ s_max_2 = precommit)
        ∨ (height ixn_l = height ixn_max_2 ∧ s_l = s_max_2 ∧ tot_view.le v_l v_max_2)
        ∨ (ixn_l = ixn_max_2 ∧ s_l = s_max_2 ∧ v_l = v_max_2)
      )
    )

  -- Record the highest locks
  highest_lock_1 op v p1 p2 ixn_max_1 s_max_1 v_max_1 := true
  highest_lock_2 op v p1 p2 ixn_max_2 s_max_2 v_max_2 := true
}

-- Repropose: both highest locks are prevote locks for the same interaction
action propose_repropose (op : node) (v : view) (p1 p2 : participant) {
  require v ≠ tot_view.zero
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require operator op v p1 p2
  require cur_stage op v p1 p2 propose
  require ∀ (ix : interaction), ¬ proposed op v p1 p2 ix
  require ¬ proposed_nil op v p1 p2
  let ixn_max_1 : interaction ← pick
  let s_max_1 : stage ← pick
  let v_max_1 : view ← pick
  let ixn_max_2 : interaction ← pick
  let s_max_2 : stage ← pick
  let v_max_2 : view ← pick
  require highest_lock_1 op v p1 p2 ixn_max_1 s_max_1 v_max_1
  require highest_lock_2 op v p1 p2 ixn_max_2 s_max_2 v_max_2
  require s_max_1 = prevote ∧ s_max_2 = prevote ∧ ixn_max_1 = ixn_max_2
  proposed op v p1 p2 ixn_max_1 := true;
  -- GHOST: proposed interaction is a descendant of A iff A is an ancestor of ixn_max_1
  proposed_for_descendant v A := decide $ (proposed_for_descendant v A ∨ ancestor A ixn_max_1);
}

-- Extend: both highest locks are precommit locks for the same interaction
action propose_extend (op : node) (v : view) (p1 p2 : participant) (ixn_propose : interaction) {
  require v ≠ tot_view.zero
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require operator op v p1 p2
  require cur_stage op v p1 p2 propose
  require ∀ (ix : interaction), ¬ proposed op v p1 p2 ix
  require ¬ proposed_nil op v p1 p2
  require ixn_propose ≠ genesis
  require ∀ (j : interaction), ¬ (parent j ixn_propose ∨ parent ixn_propose j)
  require ∀ (j : interaction), (ixn_propose ≠ j → ¬ (ancestor j ixn_propose ∨ ancestor ixn_propose j))
  require height ixn_propose = 0
  let ixn_max_1 : interaction ← pick
  let s_max_1 : stage ← pick
  let v_max_1 : view ← pick
  let ixn_max_2 : interaction ← pick
  let s_max_2 : stage ← pick
  let v_max_2 : view ← pick
  require highest_lock_1 op v p1 p2 ixn_max_1 s_max_1 v_max_1
  require highest_lock_2 op v p1 p2 ixn_max_2 s_max_2 v_max_2
  require s_max_1 = precommit ∧ s_max_2 = precommit ∧ ixn_max_1 = ixn_max_2
  require ixn_max_1 ≠ ixn_propose
  require ¬ (ancestor ixn_max_1 ixn_propose ∨ ancestor ixn_propose ixn_max_1)
  parent ixn_max_1 ixn_propose := decide $ (ixn_max_1 ≠ ixn_propose);
  ancestor A ixn_propose := decide $ (ancestor A ixn_propose ∨ ancestor A ixn_max_1 ∨ A = ixn_max_1 ∨ A = ixn_propose);
  proposed op v p1 p2 ixn_propose := true;
  height ixn_propose := height ixn_max_1 + 1;
  -- GHOST: parallel-safe version — expand ancestor post-state for ixn_propose
  proposed_for_descendant v A := decide $ (proposed_for_descendant v A
    ∨ ancestor A ixn_propose ∨ ancestor A ixn_max_1 ∨ A = ixn_max_1 ∨ A = ixn_propose);
}

-- Nil proposal: both highest locks are prevote locks for different interactions
action propose_nil (op : node) (v : view) (p1 p2 : participant) {
  require v ≠ tot_view.zero
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require operator op v p1 p2
  require cur_stage op v p1 p2 propose
  require ∀ (ix : interaction), ¬ proposed op v p1 p2 ix
  require ¬ proposed_nil op v p1 p2
  let ixn_max_1 : interaction ← pick
  let s_max_1 : stage ← pick
  let v_max_1 : view ← pick
  let ixn_max_2 : interaction ← pick
  let s_max_2 : stage ← pick
  let v_max_2 : view ← pick
  require highest_lock_1 op v p1 p2 ixn_max_1 s_max_1 v_max_1
  require highest_lock_2 op v p1 p2 ixn_max_2 s_max_2 v_max_2
  require s_max_1 = prevote ∧ s_max_2 = prevote ∧ ixn_max_1 ≠ ixn_max_2
  proposed_nil op v p1 p2 := true;
}

action respond_propose (n : node) (v : view) (p1 p2 : participant) (c1 c2 : nodeset) (ixn : interaction) {
  require v ≠ tot_view.zero
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require participant_context p1 c1 ∧ participant_context p2 c2
  require cur_view n v
  require cur_stage n v p1 p2 propose
  require interactions ixn p1 p2
  require ∃ (op : node), operator op v p1 p2 ∧ proposed op v p1 p2 ixn
  require ∀ (i : interaction), ¬ prevoted_node n v p1 p2 i
  require ixn ≠ genesis
  require ctx.member n c1 ∨ ctx.member n c2
  -- Node validates proposal against highest locks (replaces ∃∀∃∀ blocks)
  require ∃ (op : node) (i1 i2 : interaction) (s1' s2' : stage) (v1 v2 : view),
    operator op v p1 p2 ∧
    highest_lock_1 op v p1 p2 i1 s1' v1 ∧
    highest_lock_2 op v p1 p2 i2 s2' v2 ∧
    ((s1' = prevote ∧ s2' = prevote ∧ i1 = i2 ∧ i1 = ixn)
     ∨ (s1' = precommit ∧ s2' = precommit ∧ i1 = i2
        ∧ ixn ≠ i1 ∧ parent i1 ixn ∧ height ixn = height i1 + 1))
  prevoted_node n v p1 p2 ixn := true
  cur_stage n v p1 p2 S := decide $ (S = prevote)
}

action operator_prevote (op : node) (v : view) (p1 p2 : participant) (c1 c2 : nodeset) (ixn : interaction) {
  require v ≠ tot_view.zero
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require ∀ (i : interaction), ¬ prevoted_operator op v p1 p2 i
  require cur_view op v
  require operator op v p1 p2
  require interactions ixn p1 p2
  require participant_context p1 c1 ∧ participant_context p2 c2
  require ctx.member op c1 ∨ ctx.member op c2
  require cur_stage op v p1 p2 prevote
  require ∃ (s1 s2 : nodeset), ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    (∀ (n: node), (ctx.member n s1 ∨ ctx.member n s2) → prevoted_node n v p1 p2 ixn)
  prevoted_operator op v p1 p2 ixn := true
}

action respond_prevote (n : node) (v : view) (p1 p2 : participant) (c1 c2 : nodeset) (ixn : interaction) {
  require v ≠ tot_view.zero
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require cur_view n v
  require cur_stage n v p1 p2 prevote
  require interactions ixn p1 p2
  require participant_context p1 c1 ∧ participant_context p2 c2
  require ctx.member n c1 ∨ ctx.member n c2
  require ∃ (op : node), operator op v p1 p2 ∧ prevoted_operator op v p1 p2 ixn
  require ∃ (s1 s2 : nodeset), ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → prevoted_node nc v p1 p2 ixn
  precommitted_node n v p1 p2 ixn := true
  if ( ctx.member n c1 ∧ ¬ ∃ (u : view), (tot_view.le u v ∧ locked n p1 ixn precommit u) ) then
    locked n p1 ixn prevote v := true;
    -- GHOST: new prevote lock at view v for p1
    locked_at_view n p1 v := true;
    locked_for_descendant n p1 A v := decide $ (locked_for_descendant n p1 A v ∨ ancestor A ixn);
  if ( ctx.member n c2 ∧ ¬ ∃ (u : view), (tot_view.le u v ∧ locked n p2 ixn precommit u) ) then
    locked n p2 ixn prevote v := true;
    -- GHOST: new prevote lock at view v for p2
    locked_at_view n p2 v := true;
    locked_for_descendant n p2 A v := decide $ (locked_for_descendant n p2 A v ∨ ancestor A ixn);
  cur_stage n v p1 p2 S := decide $ (S = precommit)
}

action operator_precommit (op : node) (v : view) (p1 p2 : participant) (c1 c2 : nodeset) (ixn : interaction) {
  require v ≠ tot_view.zero
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require cur_view op v
  require operator op v p1 p2
  require ctx.member op c1 ∨ ctx.member op c2
  require cur_stage op v p1 p2 precommit
  require interactions ixn p1 p2
  require participant_context p1 c1 ∧ participant_context p2 c2
  require ∃ (s1 s2 : nodeset), ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → precommitted_node nc v p1 p2 ixn
  precommitted_operator op v p1 p2 ixn := true
}

action respond_precommit (n : node) (v : view) (p1 p2 : participant) (c1 c2 : nodeset) (ixn : interaction) {
  require v ≠ tot_view.zero
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require cur_view n v
  require cur_stage n v p1 p2 precommit
  require interactions ixn p1 p2
  require participant_context p1 c1 ∧ participant_context p2 c2
  require ctx.member n c1 ∨ ctx.member n c2
  require ∃ (op : node), operator op v p1 p2 ∧ precommitted_operator op v p1 p2 ixn
  require ∃ (s1 s2 : nodeset), ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → precommitted_node nc v p1 p2 ixn
  if (ctx.member n c1) then
    locked n p1 ixn precommit v := true;
    -- GHOST: new precommit lock at view v for p1
    locked_at_view n p1 v := true;
    locked_for_descendant n p1 A v := decide $ (locked_for_descendant n p1 A v ∨ ancestor A ixn);
  if (ctx.member n c2) then
    locked n p2 ixn precommit v := true;
    -- GHOST: new precommit lock at view v for p2
    locked_at_view n p2 v := true;
    locked_for_descendant n p2 A v := decide $ (locked_for_descendant n p2 A v ∨ ancestor A ixn);
  decided n v p1 p2 ixn := true
  -- GHOST: node decided a descendant of A at view v
  decided_for_descendant n A v := decide $ (decided_for_descendant n A v ∨ ancestor A ixn);
  cur_stage n v p1 p2 S := decide $ (S = commit)
}



-- ####################################################################
-- # Core Invariants
-- ####################################################################

-- INV1: Honest nodes cannot prevote on two different interactions in a given view
invariant [INV1_unique_prevote_nodes]
  ∀ (v : view) (i1 i2 : interaction) (n : node),
    ¬ ctx.is_byz n → ((prevoted_node n v p1_fixed p2_fixed i1 ∧ prevoted_node n v p1_fixed p2_fixed i2) → i1 = i2)

-- INV2: Honest nodes cannot be prevote-locked for different interactions in a given view
invariant [INV2_unique_prevote_lock_in_view]
  ∀ (n1 n2 : node) (v : view) (i1 i2 : interaction),
    ¬ (ctx.is_byz n1 ∨ ctx.is_byz n2) → (( (locked n1 p1_fixed i1 prevote v ∧ locked n2 p1_fixed i2 prevote v) ∨ (locked n1 p2_fixed i1 prevote v ∧ locked n2 p2_fixed i2 prevote v) ) → i1 = i2)

-- INV3: If an honest node has decided, then a quorum has prevote-locked
invariant [INV3_decided_only_if_quorum_prevote_locked]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ ctx.is_byz n → ( (decided n v p1_fixed p2_fixed ixn ∧ ixn ≠ genesis) →
      (∃ (c1 c2 s1 s2 : nodeset), (participant_context p1_fixed c1 ∧ participant_context p2_fixed c2 ∧ interactions ixn p1_fixed p2_fixed ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
        ∧ ∀ (nc : node), (
          (ctx.member nc s1 → ∃ (u : view), (tot_view.le u v ∧ prevoted_node nc v p1_fixed p2_fixed ixn ∧ (locked nc p1_fixed ixn prevote u ∨ locked nc p1_fixed ixn precommit u))) ∧
          (ctx.member nc s2 → ∃ (u : view), (tot_view.le u v ∧ prevoted_node nc v p1_fixed p2_fixed ixn ∧ (locked nc p2_fixed ixn prevote u ∨ locked nc p2_fixed ixn precommit u))) )) ) )

-- INV4: If a quorum has prevote-locked on ixn at view v, then in later views where a proposal
-- occurs, a lock for a descendant of ixn from view ≥ v is discovered.
-- Uses locked_for_descendant ghost to avoid existential witness for ancestor relationship.
-- invariant [INV4_quorum_locked_implies_lock_of_descendant_discovered]
--   ∀ (p1 p2 : participant) (ixn : interaction) (v vp : view),
--   (∃ (c1 c2 s1 s2 : nodeset), (interactions ixn p1 p2 ∧ participant_context p1 c1 ∧ participant_context p2 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
--   ∧ ∀ (n : node), ((ctx.member n s1 → locked n p1 ixn prevote v) ∧ (ctx.member n s2 → locked n p2 ixn prevote v)))
--   ∧ tot_view.lt v vp ) →
--   ((∃ (op : node), (∃ (ixn_prop : interaction), proposed op vp p1 p2 ixn_prop) ∨ proposed_nil op vp p1 p2) → (
--   ( ∃ (n1 : node) (c1 : nodeset) (ixnl1 : interaction) (sl1 : stage) (vl1 : view), (ctx.member n1 c1 ∧ participant_context p1 c1 ∧ sent_lock_in_prepare_1 n1 vp p1 p2 ixnl1 sl1 vl1 ∧ tot_view.le v vl1 ∧ locked_for_descendant n1 p1 ixn vl1) )
--   ∧ ( ∃ (n2 : node) (c2 : nodeset) (ixnl2 : interaction) (sl2 : stage) (vl2 : view), (ctx.member n2 c2 ∧ participant_context p2 c2 ∧ sent_lock_in_prepare_2 n2 vp p1 p2 ixnl2 sl2 vl2 ∧ tot_view.le v vl2 ∧ locked_for_descendant n2 p2 ixn vl2) )
--   ))

-- Supporting: Prevote lock implies a quorum prevoted for the interaction
invariant [prevote_lock_only_if_quorum_prevoted]
  (¬ ctx.is_byz N ∧ (locked N p1_fixed I prevote V ∨ locked N p2_fixed I prevote V)) → (∃ (c1 c2 s1 s2 : nodeset), participant_context p1_fixed c1 ∧ participant_context p2_fixed c2 ∧ interactions I p1_fixed p2_fixed ∧
    ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧ ∀ (NC : node), (ctx.member NC s1 ∨ ctx.member NC s2) → (prevoted_node NC V p1_fixed p2_fixed I))

-- Supporting (cross-node): If honest NC has precommitted for I at V, and honest N has a prevote lock
-- for J at V, then I = J.
invariant [precommit_node_lock_consistency]
  (¬ ctx.is_byz N ∧ ¬ ctx.is_byz NC ∧ precommitted_node NC V p1_fixed p2_fixed I ∧
   locked N P J prevote V ∧ (P = p1_fixed ∨ P = p2_fixed) ∧
   I ≠ genesis ∧ J ≠ genesis) → I = J

-- Supporting: A single honest node can only have locks on one interaction per view per participant
invariant [unique_lock_interaction_per_view]
  (¬ ctx.is_byz N ∧ locked N P I1 S1 V ∧ locked N P I2 S2 V ∧ (P = p1_fixed ∨ P = p2_fixed)) → I1 = I2

-- Supporting: Precommit lock implies the node prevoted for the interaction
invariant [precommit_lock_implies_prevoted]
  (¬ ctx.is_byz N ∧ (locked N p1_fixed I precommit V ∨ locked N p2_fixed I precommit V) ∧ I ≠ genesis) → prevoted_node N V p1_fixed p2_fixed I

-- Supporting: Sent locks in prepare phase correspond to actual locks (p1)
invariant [locks_sent_only_if_locked_1]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare_1 N V p1_fixed p2_fixed IL SL VL) → locked N p1_fixed IL SL VL

-- Supporting: Sent locks in prepare phase correspond to actual locks (p2)
invariant [locks_sent_only_if_locked_2]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare_2 N V p1_fixed p2_fixed IL SL VL) → locked N p2_fixed IL SL VL

-- Supporting: Genesis locks exist for all context members
invariant [genesis_lock_existence]
  ((participant_context p1_fixed C1 ∧ ctx.member N C1) → locked N p1_fixed genesis precommit tot_view.zero)
  ∧ ((participant_context p2_fixed C2 ∧ ctx.member N C2) → locked N p2_fixed genesis precommit tot_view.zero)

invariant [highest_lock_sent]
  (sent_lock_in_prepare_1 N V p1_fixed p2_fixed IL SL VL →
    (locked N p1_fixed IL SL VL ∧
     tot_view.lt VL V ∧
     (∀ i' s' v', (tot_view.lt VL v' ∧ tot_view.lt v' V) → ¬ locked N p1_fixed i' s' v') ∧
     (SL = prevote → ¬ locked N p1_fixed IL precommit VL)))
  ∧
  (sent_lock_in_prepare_2 N V p1_fixed p2_fixed IL SL VL →
    (locked N p2_fixed IL SL VL ∧
     tot_view.lt VL V ∧
     (∀ i' s' v', (tot_view.lt VL v' ∧ tot_view.lt v' V) → ¬ locked N p2_fixed i' s' v') ∧
     (SL = prevote → ¬ locked N p2_fixed IL precommit VL)))

-- Stepping stone for INV4: consecutive view case
invariant [precommit_next_view_discovery]
  ∀ (v v2 : view) (i : interaction)  (c1 c2: nodeset), (
    (interactions i p1_fixed p2_fixed ∧
     tot_view.next v v2 ∧
     v ≠ v2 ∧
     (∃ (op : node),  (¬ ctx.is_byz op ∧ operator op v2 p1_fixed p2_fixed ∧ prepared_operator op v2 p1_fixed p2_fixed)) ∧
     (∃ (m : node), (¬ ctx.is_byz m ∧ prepared_node m v2 p1_fixed p2_fixed)) ∧
     participant_context p1_fixed c1 ∧ participant_context p2_fixed c2 ∧
     i ≠ genesis ∧
     tot_view.zero ≠ v ∧
     (∀ (n : node), (¬ ctx.is_byz n →
      ((ctx.member n c1 → locked n p1_fixed i precommit v ) ∧
       (ctx.member n c2 → locked n p2_fixed i precommit v) ∧
       cur_stage n v p1_fixed p2_fixed commit ∧
       prepared_node n v2 p1_fixed p2_fixed ∧
       cur_view n v2
      )) )) →
    (∀ (n : node), ¬ ctx.is_byz n → (
      (ctx.member n c1 → (sent_lock_in_prepare_1 n v2 p1_fixed p2_fixed i precommit v)) ∧
      (ctx.member n c2 → (sent_lock_in_prepare_2 n v2 p1_fixed p2_fixed i precommit v)))
    )
  )

-- ####################################################################
-- # Ghost Consistency Invariants (locked)
-- ####################################################################

-- locked_at_view forward: any lock implies the view-level ghost
invariant [locked_at_view_fwd]
  (locked N P I S V ∧ (P = p1_fixed ∨ P = p2_fixed)) → locked_at_view N P V

-- locked_at_view backward (honest only): ghost implies a real lock exists
invariant [locked_at_view_bwd]
  (¬ ctx.is_byz N ∧ locked_at_view N P V ∧ (P = p1_fixed ∨ P = p2_fixed)) →
    ∃ (I : interaction) (S : stage), locked N P I S V

-- locked_for_descendant forward: real lock + ancestry implies ghost
invariant [locked_for_descendant_fwd]
  (locked N P I S V ∧ ancestor A I ∧ (P = p1_fixed ∨ P = p2_fixed)) →
    locked_for_descendant N P A V

-- locked_for_descendant backward (honest only): ghost implies a real lock on a descendant
invariant [locked_for_descendant_bwd]
  (¬ ctx.is_byz N ∧ locked_for_descendant N P A V ∧ (P = p1_fixed ∨ P = p2_fixed)) →
    ∃ (I : interaction) (S : stage), locked N P I S V ∧ ancestor A I

-- ####################################################################
-- # Ghost Consistency Invariants (proposed/decided)
-- ####################################################################

-- proposed_for_descendant forward: proposed + ancestry → ghost
invariant [proposed_for_descendant_fwd]
  (proposed OP V p1_fixed p2_fixed I ∧ ancestor A I) → proposed_for_descendant V A

-- proposed_for_descendant backward: ghost → ∃ proposed descendant
invariant [proposed_for_descendant_bwd]
  proposed_for_descendant V A →
    ∃ (OP : node) (I : interaction), proposed OP V p1_fixed p2_fixed I ∧ ancestor A I

-- decided_for_descendant forward: decided + ancestry → ghost
invariant [decided_for_descendant_fwd]
  (decided N V p1_fixed p2_fixed I ∧ ancestor A I) → decided_for_descendant N A V

-- decided_for_descendant backward (honest only): ghost → ∃ decided descendant
invariant [decided_for_descendant_bwd]
  (¬ ctx.is_byz N ∧ decided_for_descendant N A V) →
    ∃ (I : interaction), decided N V p1_fixed p2_fixed I ∧ ancestor A I

-- ####################################################################
-- # Lock Descendant Monotonicity (core ghost invariant)
-- ####################################################################

invariant [lock_descendant_monotone]
  (¬ ctx.is_byz N ∧ locked_for_descendant N P A V ∧ locked N P I S U ∧
   (P = p1_fixed ∨ P = p2_fixed) ∧ tot_view.le V U) → ancestor A I

-- ####################################################################
-- # Proposal–Highest Lock Linking Invariants
-- ####################################################################

-- The proposed interaction at view V is a descendant of the highest lock's interaction (c1)
invariant [proposed_is_descendant_of_highest_lock_1]
  (proposed OP V p1_fixed p2_fixed IPROP ∧
   highest_lock_1 OP V p1_fixed p2_fixed I1 S1 V1) →
   ancestor I1 IPROP

-- The proposed interaction at view V is a descendant of the highest lock's interaction (c2)
invariant [proposed_is_descendant_of_highest_lock_2]
  (proposed OP V p1_fixed p2_fixed IPROP ∧
   highest_lock_2 OP V p1_fixed p2_fixed I2 S2 V2) →
   ancestor I2 IPROP

-- ####################################################################
-- # Decision–Proposal Linking Invariant
-- ####################################################################

-- Any decided interaction was proposed at that view
invariant [decided_implies_proposed]
  (¬ ctx.is_byz N ∧ decided N V p1_fixed p2_fixed I ∧ I ≠ genesis) →
    ∃ (op : node), proposed op V p1_fixed p2_fixed I

-- If J is decided and has parent I, then I was decided at an earlier view
invariant [committed_implies_parent_committed]
  (decided M V p1_fixed p2_fixed J ∧ parent I J ∧ J ≠ genesis) →
    ∃ (u : view) (n : node), tot_view.lt u V ∧ decided n u p1_fixed p2_fixed I

-- Any non-genesis decision implies genesis was decided earlier
invariant [genesis_decided_first]
  (decided N V p1_fixed p2_fixed J ∧ J ≠ genesis) →
    ∃ (u : view) (m : node), tot_view.lt u V ∧ decided m u p1_fixed p2_fixed genesis

-- A decided non-genesis interaction requires the deciding node to hold a precommit lock
invariant [decision_requires_precommit_lock]
  (¬ ctx.is_byz N ∧ decided N V p1_fixed p2_fixed I ∧ I ≠ genesis) →
    (∃ (c1 c2 : nodeset), participant_context p1_fixed c1 ∧ participant_context p2_fixed c2 ∧
      (ctx.member N c1 → locked N p1_fixed I precommit V) ∧
      (ctx.member N c2 → locked N p2_fixed I precommit V))

-- Decisions only at past or current view
invariant [decisions_not_from_higher_views]
  (cur_view N V ∧ decided N U p1_fixed p2_fixed I) → tot_view.le U V

-- Genesis was decided at view zero
invariant [genesis_view_zero]
  (¬ ctx.is_byz N ∧ decided N V p1_fixed p2_fixed I ∧ tot_view.zero = V) → I = genesis

-- ####################################################################
-- # Ancestor Structural Invariants
-- ####################################################################
-- These give SMT direct access to key properties of ancestor without
-- needing to discover witnesses via ancestor_def_fwd/bwd unfolding.

-- Reflexivity
invariant [ancestor_refl]
  ∀ (I : interaction), ancestor I I

-- Parent implies ancestor
invariant [ancestor_from_parent]
  parent I J → ancestor I J

-- Transitivity (avoids SMT needing to find intermediate witness k)
invariant [ancestor_trans]
  (ancestor I J ∧ ancestor J K) → ancestor I K

-- Anti-symmetry (no cycles; follows from height monotonicity)
invariant [ancestor_antisymm]
  (ancestor I J ∧ ancestor J I) → I = J

-- Strict ancestor means strictly lower height
invariant [ancestor_height_strict]
  (ancestor I J ∧ I ≠ J) → height I < height J

-- Contrapositive: equal height + different → no ancestry in either direction
invariant [no_ancestor_equal_height]
  (height I = height J ∧ I ≠ J) → (¬ ancestor I J ∧ ¬ ancestor J I)

-- Parent increases height by exactly 1
invariant [parent_height]
  parent I J → height J = height I + 1

-- Ancestor is at most the transitive closure of parent (kept from IFPInvGenH)
invariant [ancestor_def_fwd]
  ancestor I J → (I = J ∨ parent I J ∨ ∃ (k : interaction), parent I k ∧ ancestor k J)

invariant [ancestor_def_bwd]
  (I = J ∨ parent I J ∨ ∃ (k : interaction), parent I k ∧ ancestor k J) → ancestor I J

-- Each interaction has at most one parent
invariant [unique_parent]
  parent J I ∧ parent K I → J = K

-- No interaction is its own parent
invariant [parent_irreflexive]
  ¬ parent I I

-- Genesis has no parent
invariant [genesis_has_no_parent]
  ¬ parent I genesis

-- Height 0 among decided interactions ↔ genesis
invariant [genesis_height_zero]
  (height I = 0 ∧ (∃ (v : view) (n : node), decided n v p1_fixed p2_fixed I)) ↔ I = genesis

-- Parent edges only exist because of propose_extend
invariant [parent_only_if_proposed]
  parent I J ∧ J ≠ genesis → ∃ (n : node) (v : view), proposed n v p1_fixed p2_fixed J


-- ####################################################################
-- # Highest Lock Invariants
-- ####################################################################

-- highest_lock_1 only set by collect_and_extract when operator is valid
invariant [highest_lock_1_valid]
  highest_lock_1 OP V p1_fixed p2_fixed I1 S1 V1 →
    operator OP V p1_fixed p2_fixed ∧ prepared_operator OP V p1_fixed p2_fixed

-- highest_lock_2 only set by collect_and_extract when operator is valid
invariant [highest_lock_2_valid]
  highest_lock_2 OP V p1_fixed p2_fixed I2 S2 V2 →
    operator OP V p1_fixed p2_fixed ∧ prepared_operator OP V p1_fixed p2_fixed

-- highest_lock_1 corresponds to a real sent lock from c1
invariant [highest_lock_1_is_sent_lock]
  highest_lock_1 OP V p1_fixed p2_fixed I1 S1 V1 →
    ∃ (n1 : node) (c1 : nodeset), ctx.member n1 c1 ∧ participant_context p1_fixed c1
      ∧ sent_lock_in_prepare_1 n1 V p1_fixed p2_fixed I1 S1 V1

-- highest_lock_2 corresponds to a real sent lock from c2
invariant [highest_lock_2_is_sent_lock]
  highest_lock_2 OP V p1_fixed p2_fixed I2 S2 V2 →
    ∃ (n2 : node) (c2 : nodeset), ctx.member n2 c2 ∧ participant_context p2_fixed c2
      ∧ sent_lock_in_prepare_2 n2 V p1_fixed p2_fixed I2 S2 V2

-- At most one highest_lock_1 per operator per view
invariant [unique_highest_lock_1]
  (highest_lock_1 OP V p1_fixed p2_fixed I1 S1 V1 ∧ highest_lock_1 OP V p1_fixed p2_fixed I2 S2 V2)
  → (I1 = I2 ∧ S1 = S2 ∧ V1 = V2)

-- At most one highest_lock_2 per operator per view
invariant [unique_highest_lock_2]
  (highest_lock_2 OP V p1_fixed p2_fixed I1 S1 V1 ∧ highest_lock_2 OP V p1_fixed p2_fixed I2 S2 V2)
  → (I1 = I2 ∧ S1 = S2 ∧ V1 = V2)

-- highest_lock_1 is actually highest: dominates all other sent locks from c1
invariant [highest_lock_1_dominates]
  (highest_lock_1 OP V p1_fixed p2_fixed I1 S1 V1 ∧
   ∃ (c1 : nodeset), participant_context p1_fixed c1 ∧
     ctx.member NL c1 ∧ sent_lock_in_prepare_1 NL V p1_fixed p2_fixed IL SL VL) →
    (height IL < height I1
     ∨ (height IL = height I1 ∧ SL = prevote ∧ S1 = precommit)
     ∨ (height IL = height I1 ∧ SL = S1 ∧ tot_view.le VL V1)
     ∨ (IL = I1 ∧ SL = S1 ∧ VL = V1))

-- highest_lock_2 is actually highest: dominates all other sent locks from c2
invariant [highest_lock_2_dominates]
  (highest_lock_2 OP V p1_fixed p2_fixed I2 S2 V2 ∧
   ∃ (c2 : nodeset), participant_context p2_fixed c2 ∧
     ctx.member NL c2 ∧ sent_lock_in_prepare_2 NL V p1_fixed p2_fixed IL SL VL) →
    (height IL < height I2
     ∨ (height IL = height I2 ∧ SL = prevote ∧ S2 = precommit)
     ∨ (height IL = height I2 ∧ SL = S2 ∧ tot_view.le VL V2)
     ∨ (IL = I2 ∧ SL = S2 ∧ VL = V2))


-- ####################################################################
-- # Supporting Invariants (structural)
-- ####################################################################

-- Each node has exactly one current view
invariant [unique_cur_view]
  cur_view N U ∧ cur_view N V → U = V

-- Every node always has some current view
invariant [node_has_cur_view]
  ∀ (n : node), ∃ (v : view), cur_view n v

-- Nodes can only be prepared for views they have reached
invariant [prepared_only_at_cur_or_past_view]
  (prepared_node N V p1_fixed p2_fixed ∧ ¬ ctx.is_byz N ∧ cur_view N V2) → tot_view.le V V2

-- Sent lock entries can only exist for views the node has reached
invariant [sent_lock_only_at_past_view]
  ((¬ ctx.is_byz N ∧ sent_lock_in_prepare_1 N V p1_fixed p2_fixed IL SL VL ∧ cur_view N VCUR) → tot_view.le V VCUR)
  ∧
  ((¬ ctx.is_byz N ∧ sent_lock_in_prepare_2 N V p1_fixed p2_fixed IL SL VL ∧ cur_view N VCUR) → tot_view.le V VCUR)

-- One stage per node per view
invariant [unique_stage]
  (¬ ctx.is_byz N ∧ cur_stage N V p1_fixed p2_fixed S1 ∧ cur_stage N V p1_fixed p2_fixed S2) → S1 = S2

-- At most one operator per view
invariant [unique_operator]
  (operator N1 V p1_fixed p2_fixed ∧ operator N2 V p1_fixed p2_fixed) → N1 = N2

-- Only the operator can have proposed
invariant [proposed_only_by_operator]
  (proposed N V p1_fixed p2_fixed I ∧ ¬ ctx.is_byz N) → operator N V p1_fixed p2_fixed

-- Genesis locks are only at view zero with precommit stage
invariant [genesis_lock_only_at_zero]
  (locked N P genesis S V) → (V = tot_view.zero ∧ S = precommit)

invariant [lock_stage_valid]
  (locked N P I S V) → (P = p1_fixed ∨ P = p2_fixed) → (S = prevote ∨ S = precommit)

-- Non-genesis locks require preparation at the same view
invariant [locked_only_if_prepared]
  (¬ ctx.is_byz N ∧ (locked N p1_fixed I S V ∨ locked N p2_fixed I S V) ∧ V ≠ tot_view.zero ∧ I ≠ genesis) → prepared_node N V p1_fixed p2_fixed

-- Stage negation invariants
invariant [stage_neg_1]
  ((cur_stage N V p1_fixed p2_fixed precommit ∨ cur_stage N V p1_fixed p2_fixed prevote ∨ cur_stage N V p1_fixed p2_fixed propose
  ∨ cur_stage N V p1_fixed p2_fixed prepare) ∧ I ≠ genesis ∧ ¬ ctx.is_byz N) → ¬ (decided N V p1_fixed p2_fixed I ∨ locked N p1_fixed I precommit V ∨ locked N p2_fixed I precommit V)

invariant [stage_neg_2]
  ((cur_stage N V p1_fixed p2_fixed prevote ∨ cur_stage N V p1_fixed p2_fixed propose
  ∨ cur_stage N V p1_fixed p2_fixed prepare) ∧ I ≠ genesis ∧ ¬ ctx.is_byz N) → ¬ (precommitted_node N V p1_fixed p2_fixed I ∨ precommitted_operator N V p1_fixed p2_fixed I ∨ locked N p1_fixed I S V ∨ locked N p2_fixed I S V)

invariant [stage_neg_3]
  ((cur_stage N V p1_fixed p2_fixed propose ∨ cur_stage N V p1_fixed p2_fixed prepare) ∧ I ≠ genesis ∧ ¬ ctx.is_byz N)
  → ¬ (prevoted_node N V p1_fixed p2_fixed I ∨ prevoted_operator N V p1_fixed p2_fixed I ∨ locked N p1_fixed I S V ∨ locked N p2_fixed I S V)

invariant [stage_init_prepare]
  (¬ prepared_node N V p1_fixed p2_fixed ∧ ¬ ctx.is_byz N) → cur_stage N V p1_fixed p2_fixed prepare

invariant [stage_neg_4]
  (cur_stage N V p1_fixed p2_fixed prepare ∧ ¬ ctx.is_byz N) →
    ¬ (prepared_node N V p1_fixed p2_fixed ∨
       sent_lock_in_prepare_1 N V p1_fixed p2_fixed IL SL VL ∨
       sent_lock_in_prepare_2 N V p1_fixed p2_fixed IL SL VL)

-- Genesis never enters the pipeline
invariant [genesis_not_in_pipeline]
  ¬ ( ¬ ctx.is_byz N ∧ (proposed N V p1_fixed p2_fixed genesis ∨ prevoted_node N V p1_fixed p2_fixed genesis
  ∨ prevoted_operator N V p1_fixed p2_fixed genesis ∨ precommitted_node N V p1_fixed p2_fixed genesis
  ∨ precommitted_operator N V p1_fixed p2_fixed genesis))

invariant [prevote_stage_implies_prevoted]
  (cur_stage N V p1_fixed p2_fixed prevote ∧ ¬ ctx.is_byz N) → ∃ I, prevoted_node N V p1_fixed p2_fixed I

invariant [precommit_stage_implies_precommitted]
  (cur_stage N V p1_fixed p2_fixed precommit ∧ ¬ ctx.is_byz N) → ∃ I, precommitted_node N V p1_fixed p2_fixed I

-- Cross-node unique prevote
invariant [cross_node_unique_prevote]
  (¬ (ctx.is_byz N1 ∨ ctx.is_byz N2) ∧ prevoted_node N1 V p1_fixed p2_fixed I1 ∧ prevoted_node N2 V p1_fixed p2_fixed I2) → I1 = I2

-- Precommitted node implies it prevoted for the same interaction
invariant [precommit_nodes_only_if_prevoted_for_same_ixn]
  (¬ ctx.is_byz N ∧ precommitted_node N V p1_fixed p2_fixed I) → prevoted_node N V p1_fixed p2_fixed I

-- Precommitted node implies a lock exists for it
invariant [precommitted_node_implies_lock]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ ctx.is_byz n → ((precommitted_node n v p1_fixed p2_fixed ixn ∧ ixn ≠ genesis) →
      (∃ (c1 c2 : nodeset),
        participant_context p1_fixed c1 ∧ participant_context p2_fixed c2 ∧
        (ctx.member n c1 → ∃ (u : view), tot_view.le u v ∧ (locked n p1_fixed ixn prevote u ∨ locked n p1_fixed ixn precommit u)) ∧
        (ctx.member n c2 → ∃ (u : view), tot_view.le u v ∧ (locked n p2_fixed ixn prevote u ∨ locked n p2_fixed ixn precommit u))))

-- Decision requires a precommit operator
invariant [decide_only_if_precommit_operator]
  (¬ ctx.is_byz N ∧ decided OP V P Q I ∧ I ≠ genesis) → (∃ (op : node), (operator op V P Q ∧ precommitted_operator op V P Q I))

-- At prevote stage, node prevoted for the proposed interaction
invariant [stage_2]
  (cur_stage N V p1_fixed p2_fixed prevote ∧ ¬ ctx.is_byz N)
  → (∃ (i : interaction), ((∃ (op : node), proposed op V p1_fixed p2_fixed i) ∧ prevoted_node N V p1_fixed p2_fixed i) ∨ (∃ (op : node), proposed_nil op V p1_fixed p2_fixed))

-- Only one proposal per view
invariant [unique_proposal]
  ¬ (ctx.is_byz N1 ∨ ctx.is_byz N2) → ( (proposed N1 V p1_fixed p2_fixed I1 ∧ proposed N2 V p1_fixed p2_fixed I2) → (I1 = I2 ∧ N1 = N2) )

invariant [unique_proposed_interaction]
  (proposed N V p1_fixed p2_fixed I1 ∧ proposed N V p1_fixed p2_fixed I2) → I1 = I2

-- Honest node prevoted → a proposal exists
invariant [prevote_implies_proposed]
  (prevoted_node N V p1_fixed p2_fixed I ∧ ¬ ctx.is_byz N) → (∃ (op : node), (operator op V p1_fixed p2_fixed ∧ proposed op V p1_fixed p2_fixed I ))

invariant [precommit_only_if_propose]
  (¬ ctx.is_byz N ∧ precommitted_node N V p1_fixed p2_fixed I) → (∃ (op : node), operator op V p1_fixed p2_fixed ∧ proposed op V p1_fixed p2_fixed I)

invariant [prepare_response_only_on_prepare]
  ¬ ctx.is_byz N → (prepared_node N V P Q → ∃ (op : node), operator op V P Q ∧ prepared_operator op V P Q)

invariant [prevote_only_by_operator]
  ¬ ctx.is_byz N → (prevoted_operator OP V P Q I → operator OP V P Q)

invariant [precommit_only_by_operator]
  (¬ ctx.is_byz OP ∧ precommitted_operator OP V P Q I) → operator OP V P Q

invariant [prepared_node_has_lock_sent_1]
  (¬ ctx.is_byz N ∧ prepared_node N V p1_fixed p2_fixed ∧ V ≠ tot_view.zero ∧
   locked N p1_fixed IL SL VL ∧
   (∃ (c1 : nodeset), ctx.member N c1 ∧ participant_context p1_fixed c1) ∧
   tot_view.lt VL V ∧
   (∀ (vl2 : view), tot_view.lt VL vl2 → ¬ ∃ (i2 : interaction) (s2 : stage), locked N p1_fixed i2 s2 vl2) ∧
   (SL = prevote → ¬ locked N p1_fixed IL precommit VL))
  → sent_lock_in_prepare_1 N V p1_fixed p2_fixed IL SL VL

invariant [prepared_node_has_lock_sent_2]
  (¬ ctx.is_byz N ∧ prepared_node N V p1_fixed p2_fixed ∧ V ≠ tot_view.zero ∧
   locked N p2_fixed IL SL VL ∧
   (∃ (c2 : nodeset), ctx.member N c2 ∧ participant_context p2_fixed c2) ∧
   tot_view.lt VL V ∧
   (∀ (vl2 : view), tot_view.lt VL vl2 → ¬ ∃ (i2 : interaction) (s2 : stage), locked N p2_fixed i2 s2 vl2) ∧
   (SL = prevote → ¬ locked N p2_fixed IL precommit VL))
  → sent_lock_in_prepare_2 N V p1_fixed p2_fixed IL SL VL

-- ####################################################################
-- # Operator/Quorum Invariants
-- ####################################################################

-- Operator prevote implies a quorum prevoted
invariant [prevote_operator_only_if_quorum_prevoted]
  ¬ ctx.is_byz N → (prevoted_operator N V p1_fixed p2_fixed I →
    (∃ (c1 c2 s1 s2 : nodeset), participant_context p1_fixed c1 ∧ participant_context p2_fixed c2 ∧
      interactions I p1_fixed p2_fixed ∧
      ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
      ∀ (NC : node), (ctx.member NC s1 ∨ ctx.member NC s2) → prevoted_node NC V p1_fixed p2_fixed I))

-- Precommit operator implies a quorum precommitted
invariant [precommit_operator_only_if_quorum_precommit]
  ¬ ctx.is_byz OP → (precommitted_operator OP V p1_fixed p2_fixed I →
    (∃ (c1 c2 s1 s2 : nodeset), participant_context p1_fixed c1 ∧ participant_context p2_fixed c2 ∧
      interactions I p1_fixed p2_fixed ∧
      ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
      ∀ (n : node), (ctx.member n s1 ∨ ctx.member n s2) → precommitted_node n V p1_fixed p2_fixed I))

-- Decision implies a quorum precommitted
invariant [decide_only_if_quorum_precommit]
  (¬ ctx.is_byz N ∧ decided N V p1_fixed p2_fixed I ∧ I ≠ genesis) →
    (∃ (c1 c2 s1 s2 : nodeset), participant_context p1_fixed c1 ∧ participant_context p2_fixed c2 ∧
      interactions I p1_fixed p2_fixed ∧
      ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
      ∀ (n : node), (ctx.member n s1 ∨ ctx.member n s2) → precommitted_node n V p1_fixed p2_fixed I)

-- Operator must be from a participant context
invariant [operator_from_context]
  ¬ ctx.is_byz OP → (operator OP V P Q → ∃ (c : nodeset), participant_context P c ∧ ctx.member OP c)

-- ####################################################################
-- # Uniqueness Invariants
-- ####################################################################

-- At most one sent lock per node per view per context (c1)
invariant [unique_lock_sent_1]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare_1 N V p1_fixed p2_fixed IL1 SL1 VL1 ∧ sent_lock_in_prepare_1 N V p1_fixed p2_fixed IL2 SL2 VL2) →
    (IL1 = IL2 ∧ SL1 = SL2 ∧ VL1 = VL2)

-- At most one sent lock per node per view per context (c2)
invariant [unique_lock_sent_2]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare_2 N V p1_fixed p2_fixed IL1 SL1 VL1 ∧ sent_lock_in_prepare_2 N V p1_fixed p2_fixed IL2 SL2 VL2) →
    (IL1 = IL2 ∧ SL1 = SL2 ∧ VL1 = VL2)

-- A node can only precommit one interaction per view
invariant [unique_precommit_nodes]
  (¬ ctx.is_byz N ∧ precommitted_node N V p1_fixed p2_fixed I ∧ precommitted_node N V p1_fixed p2_fixed J) → I = J

-- An operator can only prevote one interaction per view
invariant [unique_prevote_operator]
  (¬ ctx.is_byz OP ∧ prevoted_operator OP V p1_fixed p2_fixed I ∧ prevoted_operator OP V p1_fixed p2_fixed J) → I = J

-- An operator can only precommit one interaction per view
invariant [unique_precommit_operator]
  (¬ ctx.is_byz OP ∧ precommitted_operator OP V p1_fixed p2_fixed I ∧ precommitted_operator OP V p1_fixed p2_fixed J) → I = J

-- ####################################################################
-- # Additional Supporting Invariants
-- ####################################################################

-- Sent lock implies prepared
invariant [sent_lock_only_if_prepare]
  (¬ ctx.is_byz N ∧ (sent_lock_in_prepare_1 N V p1_fixed p2_fixed IL SL VL ∨ sent_lock_in_prepare_2 N V p1_fixed p2_fixed IL SL VL)) →
    prepared_node N V p1_fixed p2_fixed

-- Propose stage implies a sent lock exists
invariant [stage_1]
  (cur_stage N V p1_fixed p2_fixed propose ∧ ¬ ctx.is_byz N) →
    (∃ (il : interaction) (sl : stage) (vl : view), (sent_lock_in_prepare_1 N V p1_fixed p2_fixed il sl vl ∨ sent_lock_in_prepare_2 N V p1_fixed p2_fixed il sl vl))

-- Precommit stage implies a prevote lock exists
invariant [stage_3]
  (cur_stage N V p1_fixed p2_fixed precommit ∧ ¬ ctx.is_byz N) →
    (∃ (i : interaction), (prevoted_operator N V p1_fixed p2_fixed i ∨ precommitted_node N V p1_fixed p2_fixed i) ∧ (locked N p1_fixed i prevote V ∨ locked N p2_fixed i prevote V))

-- Commit stage implies a precommit lock exists
invariant [stage_4]
  (cur_stage N V p1_fixed p2_fixed commit ∧ ¬ ctx.is_byz N) →
    (∃ (i : interaction), (precommitted_operator N V p1_fixed p2_fixed i ∨ decided N V p1_fixed p2_fixed i) ∧ (locked N p1_fixed i precommit V ∨ locked N p2_fixed i precommit V))

-- Prepared operator not at view zero
invariant [prepared_operator_not_at_zero]
  (prepared_operator OP V p1_fixed p2_fixed ∧ ¬ ctx.is_byz OP) → V ≠ tot_view.zero

-- Proposal implies operator prepared
invariant [propose_only_if_operator_prepare]
  (¬ ctx.is_byz N ∧ proposed N V p1_fixed p2_fixed I) → prepared_operator N V p1_fixed p2_fixed

-- Proposal requires a locked parent (for extend proposals)
invariant [propose_only_if_parent_locked]
  (¬ ctx.is_byz OP ∧ proposed OP V p1_fixed p2_fixed J ∧ parent I J) →
    (∃ (u : view) (n : node) (s : stage), tot_view.le u V ∧ (locked n p1_fixed I s u ∨ locked n p2_fixed I s u))

-- ####################################################################
-- # Main Safety Property
-- ####################################################################

safety [main_safety]
  ∀ (n1 n2 : node) (v1 v2 : view) (i1 i2 : interaction),
    (¬ ctx.is_byz n1 ∧ ¬ ctx.is_byz n2 ∧
     decided n1 v1 p1_fixed p2_fixed i1 ∧
     decided n2 v2 p1_fixed p2_fixed i2) →
    (ancestor i1 i2 ∨ ancestor i2 i1)

set_option synthInstance.maxSize 20000
#gen_spec


set_option veil.printCounterexamples true

#check_action respond_prepare

-- #check_invariants

end IFPProtocolU
