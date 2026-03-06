-- Approach D: Split `locked` by stage into `prevote_locked` and `precommit_locked`
-- This eliminates the `stage` argument from the lock relation.
-- The `stage` type is still needed for `cur_stage`, `sent_lock_in_prepare_*`, and
-- `highest_lock_in_propose_*` (which record *which kind* of lock was sent/computed).

import Veil

veil module IFPProtocolD


class IFPByzQuorum (node : Type) (nset : Type) where
  is_byz : node → Prop
  member (n : node) (s : nset) : Prop
  supermajority (s : nset) (c : nset) : Prop

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
-- sent_lock_in_prepare still carries stage to record which kind of lock was sent
relation sent_lock_in_prepare_1 : node → view → participant → participant → interaction → stage → view → Bool
relation sent_lock_in_prepare_2 : node → view → participant → participant → interaction → stage → view → Bool
relation decided : node → view → participant → participant → interaction → Bool

-- APPROACH D: Split locked into two relations (no stage argument)
relation prevote_locked : node → participant → interaction → view → Bool
relation precommit_locked : node → participant → interaction → view → Bool

-- Operator relations
relation operator: node → view → participant → participant → Bool
relation prepared_operator : node → view → participant → participant → Bool
relation proposed : node → view → participant → participant → interaction → Bool
relation proposed_nil : node → view → participant → participant → Bool
relation prevoted_operator : node → view → participant → participant → interaction → Bool
relation precommitted_operator : node → view → participant → participant → interaction → Bool
-- Highest lock computed by operator during propose (still carries stage for ordering logic)
relation highest_lock_in_propose_1 : node → view → participant → participant → interaction → stage → view → Bool
relation highest_lock_in_propose_2 : node → view → participant → participant → interaction → stage → view → Bool

-- Non-operator relations
relation prepared_node : node → view → participant → participant → Bool
relation prevoted_node : node → view → participant → participant → interaction → Bool
relation precommitted_node : node → view → participant → participant → interaction → Bool

-- Interaction relations
relation parent : interaction → interaction → Bool
relation ancestor : interaction → interaction → Bool
function height : interaction → Nat


#gen_state

ghost relation ixn_contexts (I : interaction) (C D : nodeset) :=
∃ (p q : participant), interactions I p q ∧ participant_context p C ∧ participant_context q D

-- Ghost: unified lock query (either prevote or precommit)
ghost relation locked_any (N : node) (P : participant) (I : interaction) (V : view) :=
  prevote_locked N P I V ∨ precommit_locked N P I V

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
  -- Genesis: only precommit locks at view zero
  prevote_locked N P I V := false;
  precommit_locked N P I V := decide $ (I = genesis ∧ V = tot_view.zero ∧ (P = p1_fixed ∨ P = p2_fixed));
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
  highest_lock_in_propose_1 N V P Q I S VL := false;
  highest_lock_in_propose_2 N V P Q I S VL := false;
}

-- `Actions`

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
  -- sent_lock_in_prepare_1: find highest lock for p1
  -- SL records which kind of lock was sent; references the split relations
  sent_lock_in_prepare_1 n v p1 p2 IL SL VL := decide $
    (((SL = prevote ∧ prevote_locked n p1 IL VL) ∨ (SL = precommit ∧ precommit_locked n p1 IL VL)) ∧
     ∃ (c1 : nodeset), (ctx.member n c1 ∧ participant_context p1 c1) ∧
     tot_view.lt VL v ∧
     (∀ (vl2 : view), tot_view.lt VL vl2 → ¬ ∃ (i2 : interaction), (prevote_locked n p1 i2 vl2 ∨ precommit_locked n p1 i2 vl2)) ∧
     (SL = prevote → ¬ precommit_locked n p1 IL VL)
     )
  -- sent_lock_in_prepare_2: find highest lock for p2
  sent_lock_in_prepare_2 n v p1 p2 IL SL VL := decide $
    (((SL = prevote ∧ prevote_locked n p2 IL VL) ∨ (SL = precommit ∧ precommit_locked n p2 IL VL)) ∧
     ∃ (c2 : nodeset), (ctx.member n c2 ∧ participant_context p2 c2) ∧
     tot_view.lt VL v ∧
     (∀ (vl2 : view), tot_view.lt VL vl2 → ¬ ∃ (i2 : interaction), (prevote_locked n p2 i2 vl2 ∨ precommit_locked n p2 i2 vl2)) ∧
     (SL = prevote → ¬ precommit_locked n p2 IL VL)
     )
  cur_stage n v p1 p2 S := decide $ (S = propose)
}

action operator_propose (op : node) (v : view) (p1 p2 : participant) (c1 c2 : nodeset) (ixn_propose : interaction) {
  require v ≠ tot_view.zero
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require participant_context p1 c1 ∧ participant_context p2 c2
  require ∀ (j : interaction), ¬ parent j ixn_propose
  require ∀ (j : interaction), ¬ parent ixn_propose j
  require height ixn_propose = 0
  require cur_view op v
  require operator op v p1 p2
  require ctx.member op c1 ∨ ctx.member op c2
  require prepared_operator op v p1 p2
  require cur_stage op v p1 p2 propose
  require ixn_propose ≠ genesis;
  require ∀ (ix : interaction), ¬ proposed op v p1 p2 ix
  require ∃ (s1 : nodeset), (
    ctx.supermajority s1 c1 ∧ (
      ∀ (n : node), (
        ctx.member n s1 → (prepared_node n v p1 p2 ∧
        ∃ (vl : view) (ixnl : interaction) (sl : stage) (t1 t2 : nodeset), (
          sent_lock_in_prepare_1 n v p1 p2 ixnl sl vl
          ∧ ((sl = prevote ∧ prevote_locked n p1 ixnl vl) ∨ (sl = precommit ∧ precommit_locked n p1 ixnl vl))
          ∧ tot_view.le vl v
          ∧ ctx.supermajority t1 c1 ∧ ctx.supermajority t2 c2
          ∧ ( sl = prevote → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → prevoted_node nt vl p1 p2 ixnl)) )
          ∧ ( sl = precommit → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → precommitted_node nt vl p1 p2 ixnl)) )
          ∧ interactions ixnl p1 p2
        )
      ))
    )
  )
  require ∃ (s2 : nodeset), (
    ctx.supermajority s2 c2 ∧ (
      ∀ (n : node), (
        ctx.member n s2 → (prepared_node n v p1 p2 ∧
        ∃ (vl : view) (ixnl : interaction) (sl : stage) (t1 t2 : nodeset), (
          sent_lock_in_prepare_2 n v p1 p2 ixnl sl vl
          ∧ ((sl = prevote ∧ prevote_locked n p1 ixnl vl) ∨ (sl = precommit ∧ precommit_locked n p1 ixnl vl))
          ∧ tot_view.le vl v
          ∧ ctx.supermajority t1 c1 ∧ ctx.supermajority t2 c2
          ∧ ( sl = prevote → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → prevoted_node nt vl p1 p2 ixnl)) )
          ∧ ( sl = precommit → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → precommitted_node nt vl p1 p2 ixnl)) )
          ∧ interactions ixnl p1 p2
        )
      ))
    )
  )
  let ixn_max_1 : interaction ← pick
  let s_max_1 : stage ← pick
  let v_max_1 : view ← pick
  require ∃ (n_max_1 : node), (
    ctx.member n_max_1 c1
    ∧ interactions ixn_max_1 p1 p2
    ∧ sent_lock_in_prepare_1 n_max_1 v p1 p2 ixn_max_1 s_max_1 v_max_1
    ∧ ((s_max_1 = prevote ∧ prevote_locked n_max_1 p1 ixn_max_1 v_max_1) ∨ (s_max_1 = precommit ∧ precommit_locked n_max_1 p1 ixn_max_1 v_max_1)) ∧
    ∀ (n_l : node) (ixn_l : interaction) (s_l : stage) (v_l : view), (
      (ctx.member n_l c1  ∧ sent_lock_in_prepare_1 n_l v p1 p2 ixn_l s_l v_l) → (
        interactions ixn_l p1 p2 ∧
        (
          height ixn_l < height ixn_max_1
          ∨ (height ixn_l = height ixn_max_1 ∧ s_l = prevote ∧ s_max_1 = precommit)
          ∨ (height ixn_l = height ixn_max_1 ∧ s_l = s_max_1 ∧ tot_view.le v_l v_max_1)
          ∨ (ixn_l = ixn_max_1 ∧ s_l = s_max_1 ∧ v_l = v_max_1)
        )
      )
    )
  )
  let ixn_max_2 : interaction ← pick
  let s_max_2 : stage ← pick
  let v_max_2 : view ← pick
  require ∃ (n_max_2 : node), (
    ctx.member n_max_2 c2
    ∧ interactions ixn_max_2 p1 p2
    ∧ sent_lock_in_prepare_2 n_max_2 v p1 p2 ixn_max_2 s_max_2 v_max_2
    ∧ ((s_max_2 = prevote ∧ prevote_locked n_max_2 p2 ixn_max_2 v_max_2) ∨ (s_max_2 = precommit ∧ precommit_locked n_max_2 p2 ixn_max_2 v_max_2)) ∧
    ∀ (n_l : node) (ixn_l : interaction) (s_l : stage) (v_l : view), (
      (ctx.member n_l c2  ∧ sent_lock_in_prepare_2 n_l v p1 p2 ixn_l s_l v_l) → (
        interactions ixn_l p1 p2 ∧
        (
          height ixn_l < height ixn_max_2
          ∨ (height ixn_l = height ixn_max_2 ∧ s_l = prevote ∧ s_max_2 = precommit)
          ∨ (height ixn_l = height ixn_max_2 ∧ s_l = s_max_2 ∧ tot_view.le v_l v_max_2)
          ∨ (ixn_l = ixn_max_2 ∧ s_l = s_max_2 ∧ v_l = v_max_2)
        )
      )
    )
  )
  require ixn_max_1 ≠ ixn_propose
  require ¬ (ancestor ixn_max_1 ixn_propose ∨ ancestor ixn_propose ixn_max_1)
  -- Record computed highest locks for respond_propose to read
  highest_lock_in_propose_1 op v p1 p2 ixn_max_1 s_max_1 v_max_1 := true
  highest_lock_in_propose_2 op v p1 p2 ixn_max_2 s_max_2 v_max_2 := true
  if (s_max_1 = prevote ∧ s_max_2 = prevote ∧ ixn_max_1 = ixn_max_2) then
    proposed op v p1 p2 ixn_max_1 := true;
  if (s_max_1 = precommit ∧ s_max_2 = precommit ∧ ixn_max_1 = ixn_max_2) then
    parent ixn_max_1 ixn_propose := decide $ (ixn_max_1 ≠ ixn_propose);
    ancestor A ixn_propose := decide $ ancestor A ixn_max_1 ∨ A = ixn_max_1 ∨ A = ixn_propose;
    proposed op v p1 p2 ixn_propose := true;
    height ixn_propose := height ixn_max_1 + 1;
  if (s_max_1 = prevote ∧ s_max_2 = prevote ∧ ixn_max_1 ≠ ixn_max_2) then
    proposed_nil op v p1 p2 := true;
}

action respond_propose (n : node) (v : view) (p1 p2 : participant) (c1 c2 : nodeset)
    (ixn : interaction) (ixn_max_1 ixn_max_2 : interaction)
    (s_max_1 s_max_2 : stage) (v_max_1 v_max_2 : view) {
  -- Structural checks
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
  -- Quorum verification c1 (QC validity check)
  require ∃ (s1 : nodeset), (
    ctx.supermajority s1 c1 ∧ (
      ∀ (n : node), (
        ctx.member n s1 → (prepared_node n v p1 p2 ∧
        ∃ (vl : view) (ixnl : interaction) (sl : stage) (t1 t2 : nodeset), (
          sent_lock_in_prepare_1 n v p1 p2 ixnl sl vl
          ∧ ((sl = prevote ∧ prevote_locked n p1 ixnl vl) ∨ (sl = precommit ∧ precommit_locked n p1 ixnl vl))
          ∧ tot_view.le vl v
          ∧ ctx.supermajority t1 c1 ∧ ctx.supermajority t2 c2
          ∧ ( sl = prevote → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → prevoted_node nt vl p1 p2 ixnl)) )
          ∧ ( sl = precommit → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → precommitted_node nt vl p1 p2 ixnl)) )
          ∧ interactions ixnl p1 p2
        )
      ))
    )
  )
  -- Quorum verification c2 (QC validity check)
  require ∃ (s2 : nodeset), (
    ctx.supermajority s2 c2 ∧ (
      ∀ (n : node), (
        ctx.member n s2 → (prepared_node n v p1 p2 ∧
        ∃ (vl : view) (ixnl : interaction) (sl : stage) (t1 t2 : nodeset), (
          sent_lock_in_prepare_2 n v p1 p2 ixnl sl vl
          ∧ ((sl = prevote ∧ prevote_locked n p1 ixnl vl) ∨ (sl = precommit ∧ precommit_locked n p1 ixnl vl))
          ∧ tot_view.le vl v
          ∧ ctx.supermajority t1 c1 ∧ ctx.supermajority t2 c2
          ∧ ( sl = prevote → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → prevoted_node nt vl p1 p2 ixnl)) )
          ∧ ( sl = precommit → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → precommitted_node nt vl p1 p2 ixnl)) )
          ∧ interactions ixnl p1 p2
        )
      ))
    )
  )
  -- Read operator's highest lock claims
  require ∃ (op : node), operator op v p1 p2
    ∧ highest_lock_in_propose_1 op v p1 p2 ixn_max_1 s_max_1 v_max_1
    ∧ highest_lock_in_propose_2 op v p1 p2 ixn_max_2 s_max_2 v_max_2
  -- Verify claim 1: backed by real data
  require ∃ (n_max_1 : node), ctx.member n_max_1 c1
    ∧ interactions ixn_max_1 p1 p2
    ∧ sent_lock_in_prepare_1 n_max_1 v p1 p2 ixn_max_1 s_max_1 v_max_1
    ∧ ((s_max_1 = prevote ∧ prevote_locked n_max_1 p1 ixn_max_1 v_max_1) ∨ (s_max_1 = precommit ∧ precommit_locked n_max_1 p1 ixn_max_1 v_max_1))
  -- Verify claim 1: maximal
  require ∀ (n_l : node) (ixn_l : interaction) (s_l : stage) (v_l : view),
    (ctx.member n_l c1 ∧ sent_lock_in_prepare_1 n_l v p1 p2 ixn_l s_l v_l) →
    (interactions ixn_l p1 p2 ∧
      (height ixn_l < height ixn_max_1
       ∨ (height ixn_l = height ixn_max_1 ∧ s_l = prevote ∧ s_max_1 = precommit)
       ∨ (height ixn_l = height ixn_max_1 ∧ s_l = s_max_1 ∧ tot_view.le v_l v_max_1)
       ∨ (ixn_l = ixn_max_1 ∧ s_l = s_max_1 ∧ v_l = v_max_1)))
  -- Verify claim 2: backed by real data
  require ∃ (n_max_2 : node), ctx.member n_max_2 c2
    ∧ interactions ixn_max_2 p1 p2
    ∧ sent_lock_in_prepare_2 n_max_2 v p1 p2 ixn_max_2 s_max_2 v_max_2
    ∧ ((s_max_2 = prevote ∧ prevote_locked n_max_2 p2 ixn_max_2 v_max_2) ∨ (s_max_2 = precommit ∧ precommit_locked n_max_2 p2 ixn_max_2 v_max_2))
  -- Verify claim 2: maximal
  require ∀ (n_l : node) (ixn_l : interaction) (s_l : stage) (v_l : view),
    (ctx.member n_l c2 ∧ sent_lock_in_prepare_2 n_l v p1 p2 ixn_l s_l v_l) →
    (interactions ixn_l p1 p2 ∧
      (height ixn_l < height ixn_max_2
       ∨ (height ixn_l = height ixn_max_2 ∧ s_l = prevote ∧ s_max_2 = precommit)
       ∨ (height ixn_l = height ixn_max_2 ∧ s_l = s_max_2 ∧ tot_view.le v_l v_max_2)
       ∨ (ixn_l = ixn_max_2 ∧ s_l = s_max_2 ∧ v_l = v_max_2)))
  -- Proposal validation: repropose or extend
  require (s_max_1 = prevote ∧ s_max_2 = prevote ∧ ixn_max_1 = ixn_max_2)
        ∨ (s_max_1 = precommit ∧ s_max_2 = precommit ∧ ixn_max_1 = ixn_max_2)
  require (s_max_1 = prevote ∧ s_max_2 = prevote ∧ ixn_max_1 = ixn_max_2) → ixn_max_1 = ixn
  require (s_max_1 = precommit ∧ s_max_2 = precommit ∧ ixn_max_1 = ixn_max_2) →
    (ixn ≠ ixn_max_1 ∧ parent ixn_max_1 ixn
    ∧ height ixn = height ixn_max_1 + 1)
  -- State updates
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
  require ixn_contexts ixn c1 c2
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
  require ixn_contexts ixn c1 c2
  require ctx.member n c1 ∨ ctx.member n c2
  require ∃ (op : node), operator op v p1 p2 ∧ prevoted_operator op v p1 p2 ixn
  require ∃ (s1 s2 : nodeset), ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → prevoted_node nc v p1 p2 ixn
  precommitted_node n v p1 p2 ixn := true
  -- Acquire prevote lock unless already holding a precommit lock
  if ( ctx.member n c1 ∧ ¬ ∃ (u : view), (tot_view.le u v ∧ precommit_locked n p1 ixn u) ) then
    prevote_locked n p1 ixn v := true
  if ( ctx.member n c2 ∧ ¬ ∃ (u : view), (tot_view.le u v ∧ precommit_locked n p2 ixn u) ) then
    prevote_locked n p2 ixn v := true
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
  require ixn_contexts ixn c1 c2
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
  require ixn_contexts ixn c1 c2
  require ctx.member n c1 ∨ ctx.member n c2
  require ∃ (op : node), operator op v p1 p2 ∧ precommitted_operator op v p1 p2 ixn
  require ∃ (s1 s2 : nodeset), ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → precommitted_node nc v p1 p2 ixn
  if (ctx.member n c1) then
    precommit_locked n p1 ixn v := true;
  if (ctx.member n c2) then
    precommit_locked n p2 ixn v := true;
  decided n v p1 p2 ixn := true
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
    ¬ (ctx.is_byz n1 ∨ ctx.is_byz n2) → (( (prevote_locked n1 p1_fixed i1 v ∧ prevote_locked n2 p1_fixed i2 v) ∨ (prevote_locked n1 p2_fixed i1 v ∧ prevote_locked n2 p2_fixed i2 v) ) → i1 = i2)

-- INV3: If an honest node has decided, then a quorum has prevote-locked
invariant [INV3_decided_only_if_quorum_prevote_locked]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ ctx.is_byz n → ( (decided n v p1_fixed p2_fixed ixn ∧ ixn ≠ genesis) →
      (∃ (c1 c2 s1 s2 : nodeset), (ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
        ∧ ∀ (nc : node), (
          (ctx.member nc s1 → ∃ (u : view), (tot_view.le u v ∧ prevoted_node nc v p1_fixed p2_fixed ixn ∧ (prevote_locked nc p1_fixed ixn u ∨ precommit_locked nc p1_fixed ixn u))) ∧
          (ctx.member nc s2 → ∃ (u : view), (tot_view.le u v ∧ prevoted_node nc v p1_fixed p2_fixed ixn ∧ (prevote_locked nc p2_fixed ixn u ∨ precommit_locked nc p2_fixed ixn u))) )) ) )

-- INV4: If a quorum has prevote-locked onto an interaction in view v, then in the Prepare stage of
-- later views, a lock from at least view v and descendant of ixn is discovered
invariant [INV4_quorum_locked_implies_lock_of_descendant_discovered]
  ∀ (p1 p2 : participant) (ixn : interaction) (v vp : view),
  (∃ (c1 c2 s1 s2 : nodeset), (interactions ixn p1 p2 ∧ participant_context p1 c1 ∧ participant_context p2 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
  ∧ ∀ (n : node), ((ctx.member n s1 → prevote_locked n p1 ixn v) ∧ (ctx.member n s2 → prevote_locked n p2 ixn v)))
  ∧ tot_view.lt v vp ) →
  ((∃ (op : node), (∃ (ixn_prop : interaction), proposed op vp p1 p2 ixn_prop) ∨ proposed_nil op vp p1 p2) → (
  ( ∃ (n1 : node) (c1 : nodeset) (ixnl1 : interaction) (sl1 : stage) (vl1 : view), (ctx.member n1 c1 ∧ participant_context p1 c1 ∧ sent_lock_in_prepare_1 n1 vp p1 p2 ixnl1 sl1 vl1 ∧ tot_view.le v vl1 ∧ ancestor ixn ixnl1) )
  ∧ ( ∃ (n2 : node) (c2 : nodeset) (ixnl2 : interaction) (sl2 : stage) (vl2 : view), (ctx.member n2 c2 ∧ participant_context p2 c2 ∧ sent_lock_in_prepare_2 n2 vp p1 p2 ixnl2 sl2 vl2 ∧ tot_view.le v vl2 ∧ ancestor ixn ixnl2) )
  ))

-- Supporting: Prevote lock implies a quorum prevoted for the interaction
invariant [prevote_lock_only_if_quorun_prevoted]
  (¬ ctx.is_byz N ∧ prevote_locked N p1_fixed I V ∨ prevote_locked N p2_fixed I V) → (∃ (c1 c2 s1 s2 : nodeset), ixn_contexts I c1 c2 ∧
    ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧ ∀ (NC : node), (ctx.member NC s1 ∨ ctx.member NC s2) → (prevoted_node NC V p1_fixed p2_fixed I))

-- Supporting (cross-node): precommit + prevote lock consistency
invariant [precommit_node_lock_consistency]
  (¬ ctx.is_byz N ∧ ¬ ctx.is_byz NC ∧ precommitted_node NC V p1_fixed p2_fixed I ∧
   prevote_locked N P J V ∧ (P = p1_fixed ∨ P = p2_fixed) ∧
   I ≠ genesis ∧ J ≠ genesis) → I = J

-- Supporting: A single honest node can only have locks on one interaction per view per participant
invariant [unique_lock_interaction_per_view]
  (¬ ctx.is_byz N ∧ (prevote_locked N P I1 V ∨ precommit_locked N P I1 V) ∧ (prevote_locked N P I2 V ∨ precommit_locked N P I2 V) ∧ (P = p1_fixed ∨ P = p2_fixed)) → I1 = I2

-- Supporting: Precommit lock implies the node prevoted for the interaction
invariant [precommit_lock_implies_prevoted]
  (¬ ctx.is_byz N ∧ (precommit_locked N p1_fixed I V ∨ precommit_locked N p2_fixed I V) ∧ I ≠ genesis) → prevoted_node N V p1_fixed p2_fixed I

-- Supporting: Sent locks in prepare phase correspond to actual locks (p1)
invariant [locks_sent_only_if_locked_1]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare_1 N V p1_fixed p2_fixed IL SL VL) →
    ((SL = prevote ∧ prevote_locked N p1_fixed IL VL) ∨ (SL = precommit ∧ precommit_locked N p1_fixed IL VL))

-- Supporting: Sent locks in prepare phase correspond to actual locks (p2)
invariant [locks_sent_only_if_locked_2]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare_2 N V p1_fixed p2_fixed IL SL VL) →
    ((SL = prevote ∧ prevote_locked N p2_fixed IL VL) ∨ (SL = precommit ∧ precommit_locked N p2_fixed IL VL))

-- Supporting: Genesis locks exist for all context members
invariant [genesis_lock_existence]
  ((participant_context p1_fixed C1 ∧ ctx.member N C1) → precommit_locked N p1_fixed genesis tot_view.zero)
  ∧ ((participant_context p2_fixed C2 ∧ ctx.member N C2) → precommit_locked N p2_fixed genesis tot_view.zero)

invariant [highest_lock_sent]
  (sent_lock_in_prepare_1 N V p1_fixed p2_fixed IL SL VL →
    (((SL = prevote ∧ prevote_locked N p1_fixed IL VL) ∨ (SL = precommit ∧ precommit_locked N p1_fixed IL VL)) ∧
     tot_view.lt VL V ∧
     (∀ i' v', (tot_view.lt VL v' ∧ tot_view.lt v' V) → ¬ (prevote_locked N p1_fixed i' v' ∨ precommit_locked N p1_fixed i' v')) ∧
     (SL = prevote → ¬ precommit_locked N p1_fixed IL VL)))
  ∧
  (sent_lock_in_prepare_2 N V p1_fixed p2_fixed IL SL VL →
    (((SL = prevote ∧ prevote_locked N p2_fixed IL VL) ∨ (SL = precommit ∧ precommit_locked N p2_fixed IL VL)) ∧
     tot_view.lt VL V ∧
     (∀ i' v', (tot_view.lt VL v' ∧ tot_view.lt v' V) → ¬ (prevote_locked N p2_fixed i' v' ∨ precommit_locked N p2_fixed i' v')) ∧
     (SL = prevote → ¬ precommit_locked N p2_fixed IL VL)))

invariant [precommit_next_view_discovery]
  ∀ (v v2 : view) (i : interaction)  (c1 c2: nodeset), (
    (interactions i p1_fixed p2_fixed ∧
     tot_view.next v v2 ∧
     v ≠ v2 ∧
     (∃ (op : node),  (¬ ctx.is_byz op ∧ operator op v2 p1_fixed p2_fixed ∧ prepared_operator op v2 p1_fixed p2_fixed)) ∧
     (∃ (m : node), (¬ ctx.is_byz m ∧ prepared_node m v2 p1_fixed p2_fixed)) ∧
     ixn_contexts i c1 c2 ∧
     i ≠ genesis ∧
     tot_view.zero ≠ v ∧
     (∀ (n : node), (¬ ctx.is_byz n →
      ((ctx.member n c1 → precommit_locked n p1_fixed i v ) ∧
       (ctx.member n c2 → precommit_locked n p2_fixed i v) ∧
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
-- # Supporting Invariants (structural)
-- ####################################################################

invariant [unique_cur_view]
  cur_view N U ∧ cur_view N V → U = V

invariant [node_has_cur_view]
  ∀ (n : node), ∃ (v : view), cur_view n v

invariant [prepared_only_at_cur_or_past_view]
  (prepared_node N V p1_fixed p2_fixed ∧ ¬ ctx.is_byz N ∧ cur_view N V2) → tot_view.le V V2

invariant [unique_stage]
  (¬ ctx.is_byz N ∧ cur_stage N V p1_fixed p2_fixed S1 ∧ cur_stage N V p1_fixed p2_fixed S2) → S1 = S2

invariant [unique_operator]
  (operator N1 V p1_fixed p2_fixed ∧ operator N2 V p1_fixed p2_fixed) → N1 = N2

invariant [proposed_only_by_operator]
  (proposed N V p1_fixed p2_fixed I ∧ ¬ ctx.is_byz N) → operator N V p1_fixed p2_fixed

-- Genesis locks are only precommit at view zero (no prevote genesis locks)
invariant [genesis_lock_only_at_zero]
  prevote_locked N P genesis V → False
  -- Note: precommit_locked genesis is only at tot_view.zero (from init)

invariant [genesis_precommit_lock_only_at_zero]
  precommit_locked N P genesis V → V = tot_view.zero

-- Non-genesis locks require preparation at the same view
invariant [locked_only_if_prepared]
  (¬ ctx.is_byz N ∧ (prevote_locked N p1_fixed I V ∨ prevote_locked N p2_fixed I V ∨ precommit_locked N p1_fixed I V ∨ precommit_locked N p2_fixed I V) ∧ V ≠ tot_view.zero ∧ I ≠ genesis) → prepared_node N V p1_fixed p2_fixed

-- At precommit/prevote/propose/prepare stage: no non-genesis decide or precommit locks at current view
invariant [stage_neg_1]
  ((cur_stage N V p1_fixed p2_fixed precommit ∨ cur_stage N V p1_fixed p2_fixed prevote ∨ cur_stage N V p1_fixed p2_fixed propose
  ∨ cur_stage N V p1_fixed p2_fixed prepare) ∧ I ≠ genesis ∧ ¬ ctx.is_byz N) → ¬ (decided N V p1_fixed p2_fixed I ∨ precommit_locked N p1_fixed I V ∨ precommit_locked N p2_fixed I V)

-- At prevote/propose/prepare stage: no non-genesis locks or precommit state at current view
invariant [stage_neg_2]
  ((cur_stage N V p1_fixed p2_fixed prevote ∨ cur_stage N V p1_fixed p2_fixed propose
  ∨ cur_stage N V p1_fixed p2_fixed prepare) ∧ I ≠ genesis ∧ ¬ ctx.is_byz N) → ¬ (precommitted_node N V p1_fixed p2_fixed I ∨ precommitted_operator N V p1_fixed p2_fixed I ∨ prevote_locked N p1_fixed I V ∨ prevote_locked N p2_fixed I V ∨ precommit_locked N p1_fixed I V ∨ precommit_locked N p2_fixed I V)

-- At propose/prepare stage: no prevotes, prevote-operators, or locks at current view
invariant [stage_neg_3]
  ((cur_stage N V p1_fixed p2_fixed propose ∨ cur_stage N V p1_fixed p2_fixed prepare) ∧ I ≠ genesis ∧ ¬ ctx.is_byz N)
  → ¬ (prevoted_node N V p1_fixed p2_fixed I ∨ prevoted_operator N V p1_fixed p2_fixed I ∨ prevote_locked N p1_fixed I V ∨ prevote_locked N p2_fixed I V ∨ precommit_locked N p1_fixed I V ∨ precommit_locked N p2_fixed I V)

invariant [stage_init_prepare]
  (¬ prepared_node N V p1_fixed p2_fixed ∧ ¬ ctx.is_byz N) → cur_stage N V p1_fixed p2_fixed prepare

invariant [genesis_not_in_pipeline]
  ¬ ( ¬ ctx.is_byz N ∧ (proposed N V p1_fixed p2_fixed genesis ∨ prevoted_node N V p1_fixed p2_fixed genesis
  ∨ prevoted_operator N V p1_fixed p2_fixed genesis ∨ precommitted_node N V p1_fixed p2_fixed genesis
  ∨ precommitted_operator N V p1_fixed p2_fixed genesis))

invariant [prevote_stage_implies_prevoted]
  (cur_stage N V p1_fixed p2_fixed prevote ∧ ¬ ctx.is_byz N) → ∃ I, prevoted_node N V p1_fixed p2_fixed I

invariant [precommit_stage_implies_precommitted]
  (cur_stage N V p1_fixed p2_fixed precommit ∧ ¬ ctx.is_byz N) → ∃ I, precommitted_node N V p1_fixed p2_fixed I

invariant [cross_node_unique_prevote]
  (¬ (ctx.is_byz N1 ∨ ctx.is_byz N2) ∧ prevoted_node N1 V p1_fixed p2_fixed I1 ∧ prevoted_node N2 V p1_fixed p2_fixed I2) → I1 = I2

invariant [precommit_nodes_only_if_prevoted_for_same_ixn]
  (¬ ctx.is_byz N ∧ precommitted_node N V p1_fixed p2_fixed I) → prevoted_node N V p1_fixed p2_fixed I

invariant [precommitted_node_implies_lock]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ ctx.is_byz n → ((precommitted_node n v p1_fixed p2_fixed ixn ∧ ixn ≠ genesis) →
      (∃ (c1 c2 : nodeset),
        ixn_contexts ixn c1 c2 ∧
        (ctx.member n c1 → ∃ (u : view), tot_view.le u v ∧ (prevote_locked n p1_fixed ixn u ∨ precommit_locked n p1_fixed ixn u)) ∧
        (ctx.member n c2 → ∃ (u : view), tot_view.le u v ∧ (prevote_locked n p2_fixed ixn u ∨ precommit_locked n p2_fixed ixn u))))

invariant [ancestor_def_fwd]
  ancestor I J → (I = J ∨ parent I J ∨ ∃ (k : interaction), parent I k ∧ ancestor k J)

invariant [ancestor_def_bwd]
  (I = J ∨ parent I J ∨ ∃ (k : interaction), parent I k ∧ ancestor k J) → ancestor I J

invariant [decide_only_if_precommit_operator]
  (¬ ctx.is_byz N ∧ decided OP V P Q I ∧ I ≠ genesis) → (∃ (op : node), (operator op V P Q ∧ precommitted_operator op V P Q I))

invariant [stage_2]
  (cur_stage N V p1_fixed p2_fixed prevote ∧ ¬ ctx.is_byz N)
  → (∃ (i : interaction), ((∃ (op : node), proposed op V p1_fixed p2_fixed i) ∧ prevoted_node N V p1_fixed p2_fixed i) ∨ (∃ (op : node), proposed_nil op V p1_fixed p2_fixed))

invariant [unique_proposal]
  ¬ (ctx.is_byz N1 ∨ ctx.is_byz N2) → ( (proposed N1 V p1_fixed p2_fixed I1 ∧ proposed N2 V p1_fixed p2_fixed I2) → (I1 = I2 ∧ N1 = N2) )

invariant [unique_proposed_interaction]
  (proposed N V p1_fixed p2_fixed I1 ∧ proposed N V p1_fixed p2_fixed I2) → I1 = I2

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


-- Placeholder safety
safety [main_safety]
  true

#gen_spec

set_option veil.printCounterexamples true

#check_invariants


end IFPProtocolD
