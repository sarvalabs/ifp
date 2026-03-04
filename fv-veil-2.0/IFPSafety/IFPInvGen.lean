import Veil

veil module IFPProtocol


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

-- variable (ctx.ctx.is_byz : node → Bool)
instantiate tot_view : TotalOrderWithMinimum view
instantiate ctx : IFPByzQuorum node nodeset

-- open IFPByzQuorum

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


#gen_state

ghost relation ixn_contexts (I : interaction) (C D : nodeset) :=
∃ (p q : participant), interactions I p q ∧ participant_context p C ∧ participant_context q D

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
  -- height2 I := 0;
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
          ∧ locked n p1 ixnl sl vl
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
          ∧ locked n p1 ixnl sl vl
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
    ∧ locked n_max_1 p1 ixn_max_1 s_max_1 v_max_1 ∧
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
    ∧ locked n_max_2 p2 ixn_max_2 s_max_2 v_max_2 ∧
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
  require ∃ (s1 : nodeset), (
    ctx.supermajority s1 c1 ∧ (
      ∀ (n : node), (
        ctx.member n s1 → (prepared_node n v p1 p2 ∧
        ∃ (vl : view) (ixnl : interaction) (sl : stage) (t1 t2 : nodeset), (
          sent_lock_in_prepare_1 n v p1 p2 ixnl sl vl
          ∧ locked n p1 ixnl sl vl
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
          ∧ locked n p1 ixnl sl vl
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
    ∧ locked n_max_1 p1 ixn_max_1 s_max_1 v_max_1 ∧
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
    ∧ locked n_max_2 p2 ixn_max_2 s_max_2 v_max_2 ∧
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
  -- valid proposal pattern: repropose or extend (otherwise should be nil)
  require (s_max_1 = prevote ∧ s_max_2 = prevote ∧ ixn_max_1 = ixn_max_2)
        ∨ (s_max_1 = precommit ∧ s_max_2 = precommit ∧ ixn_max_1 = ixn_max_2)
  require (s_max_1 = prevote ∧ s_max_2 = prevote ∧ ixn_max_1 = ixn_max_2) → ixn_max_1 = ixn
  require (s_max_1 = precommit ∧ s_max_2 = precommit ∧ ixn_max_1 = ixn_max_2) →
    (ixn ≠ ixn_max_1 ∧ parent ixn_max_1 ixn
    ∧ height ixn = height ixn_max_1 + 1)
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
  if ( ctx.member n c1 ∧ ¬ ∃ (u : view), (tot_view.le u v ∧ locked n p1 ixn precommit u) ) then
    locked n p1 ixn prevote v := true
  if ( ctx.member n c2 ∧ ¬ ∃ (u : view), (tot_view.le u v ∧ locked n p2 ixn precommit u) ) then
    locked n p2 ixn prevote v := true
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
  locked n p1 ixn precommit v := true;
  if (ctx.member n c2) then
  locked n p2 ixn precommit v := true;
  decided n v p1 p2 ixn := true
  cur_stage n v p1 p2 S := decide $ (S = commit)
}


-- ####################################################################
-- # Core Invariants (10 invariants + safety)
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
      (∃ (c1 c2 s1 s2 : nodeset), (ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
        ∧ ∀ (nc : node), (
          (ctx.member nc s1 → ∃ (u : view), (tot_view.le u v ∧ prevoted_node nc v p1_fixed p2_fixed ixn ∧ (locked nc p1_fixed ixn prevote u ∨ locked nc p1_fixed ixn precommit u))) ∧
          (ctx.member nc s2 → ∃ (u : view), (tot_view.le u v ∧ prevoted_node nc v p1_fixed p2_fixed ixn ∧ (locked nc p2_fixed ixn prevote u ∨ locked nc p2_fixed ixn precommit u))) )) ) )

-- INV4: If a quorum has prevote-locked onto an interaction in view v, then in the Prepare stage of
-- later views, a lock from at least view v and descendant of ixn is discovered
-- (commented out: working on supporting invariants first)
invariant [INV4_quorum_locked_implies_lock_of_descendant_discovered]
  ∀ (p1 p2 : participant) (ixn : interaction) (v vp : view),
  (∃ (c1 c2 s1 s2 : nodeset), (interactions ixn p1 p2 ∧ participant_context p1 c1 ∧ participant_context p2 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
  ∧ ∀ (n : node), ((ctx.member n s1 → locked n p1 ixn prevote v) ∧ (ctx.member n s2 → locked n p2 ixn prevote v)))
  ∧ tot_view.lt v vp ) →
  ((∃ (op : node), (∃ (ixn_prop : interaction), proposed op vp p1 p2 ixn_prop) ∨ proposed_nil op vp p1 p2) → (
  ( ∃ (n1 : node) (c1 : nodeset) (ixnl1 : interaction) (sl1 : stage) (vl1 : view), (ctx.member n1 c1 ∧ participant_context p1 c1 ∧ sent_lock_in_prepare_1 n1 vp p1 p2 ixnl1 sl1 vl1 ∧ tot_view.le v vl1 ∧ ancestor ixn ixnl1) )
  ∧ ( ∃ (n2 : node) (c2 : nodeset) (ixnl2 : interaction) (sl2 : stage) (vl2 : view), (ctx.member n2 c2 ∧ participant_context p2 c2 ∧ sent_lock_in_prepare_2 n2 vp p1 p2 ixnl2 sl2 vl2 ∧ tot_view.le v vl2 ∧ ancestor ixn ixnl2) )
  ))

-- Supporting: Prevote lock implies a quorum prevoted for the interaction
invariant [prevote_lock_only_if_quorun_prevoted]
  (¬ ctx.is_byz N ∧ locked N p1_fixed I prevote V ∨ locked N p2_fixed I prevote V) → (∃ (c1 c2 s1 s2 : nodeset), ixn_contexts I c1 c2 ∧
    ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧ ∀ (NC : node), (ctx.member NC s1 ∨ ctx.member NC s2) → (prevoted_node NC V p1_fixed p2_fixed I))

-- Supporting (cross-node): If honest NC has precommitted for I at V, and honest N has a prevote lock
-- for J at V, then I = J. Both imply a quorum prevoted at V (via respond_prevote preconditions and
-- prevote_lock_only_if_quorum_prevoted), and INV1/quorum intersection forces the interactions to match.
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

invariant [precommit_next_view_discovery]
  ∀ (v v2 : view) (i : interaction)  (c1 c2: nodeset), (
    (interactions i p1_fixed p2_fixed ∧
     tot_view.next v v2 ∧
     v ≠ v2 ∧
     (∃ (op : node),  (¬ ctx.is_byz op ∧ operator op v2 p1_fixed p2_fixed ∧ prepared_operator op v2 p1_fixed p2_fixed)) ∧
     (∃ (m : node), (¬ ctx.is_byz m ∧ prepared_node m v2 p1_fixed p2_fixed)) ∧
     ixn_contexts i c1 c2 ∧
     i ≠ genesis ∧
     -- il ≠ genesis ∧
     tot_view.zero ≠ v ∧
     -- tot_view.lt v v2 ∧ -- Enforce v < v2 (next should imply this)
     -- ¬ tot_view.lt v2 v ∧ -- No cycles
     -- ¬ tot_view.lt v2 tot_view.zero ∧ -- v2 cannot be less than zero
     -- ¬ ∃ (v_mid : view), (tot_view.lt v v_mid ∧ tot_view.lt v_mid v2) ∧ -- Rule out views between v and v2 (enforce consecutive)
     -- ¬ tot_view.lt v tot_view.zero ∧ -- Ensure v is not before zero (zero is minimum)
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
-- # Supporting Invariants (added by inference)
-- ####################################################################

-- Tier 3: Structural (leaf nodes, no further dependencies)

-- Each node has exactly one current view (set_view replaces functionally)
invariant [unique_cur_view]
  cur_view N U ∧ cur_view N V → U = V

-- Every node always has some current view
invariant [node_has_cur_view]
  ∀ (n : node), ∃ (v : view), cur_view n v

-- Nodes can only be prepared for views they have reached (current or past)
invariant [prepared_only_at_cur_or_past_view]
  (prepared_node N V p1_fixed p2_fixed ∧ ¬ ctx.is_byz N ∧ cur_view N V2) → tot_view.le V V2

-- One stage per node per view (prevents double-stage allowing double-prevote)
invariant [unique_stage]
  (¬ ctx.is_byz N ∧ cur_stage N V p1_fixed p2_fixed S1 ∧ cur_stage N V p1_fixed p2_fixed S2) → S1 = S2

-- At most one operator per view (from pick_operator requiring no existing operator)
invariant [unique_operator]
  (operator N1 V p1_fixed p2_fixed ∧ operator N2 V p1_fixed p2_fixed) → N1 = N2

-- Only the operator can have proposed (from propose action requiring operator)
invariant [proposed_only_by_operator]
  (proposed N V p1_fixed p2_fixed I ∧ ¬ ctx.is_byz N) → operator N V p1_fixed p2_fixed

-- Genesis locks are only created at init with S=false, V=zero
invariant [genesis_lock_only_at_zero]
  (locked N P genesis S V) → (V = tot_view.zero ∧ S = precommit)

-- Non-genesis locks require preparation at the same view
invariant [locked_only_if_prepared]
  (¬ ctx.is_byz N ∧ (locked N p1_fixed I S V ∨ locked N p2_fixed I S V) ∧ V ≠ tot_view.zero ∧ I ≠ genesis) → prepared_node N V p1_fixed p2_fixed

-- At precommit/prevote/propose/prepare stage: no non-genesis decide or precommit locks at current view
invariant [stage_neg_1]
  ((cur_stage N V p1_fixed p2_fixed precommit ∨ cur_stage N V p1_fixed p2_fixed prevote ∨ cur_stage N V p1_fixed p2_fixed propose
  ∨ cur_stage N V p1_fixed p2_fixed prepare) ∧ I ≠ genesis ∧ ¬ ctx.is_byz N) → ¬ (decided N V p1_fixed p2_fixed I ∨ locked N p1_fixed I precommit V ∨ locked N p2_fixed I precommit V)

-- At prevote/propose/prepare stage: no non-genesis locks or precommit state at current view
invariant [stage_neg_2]
  ((cur_stage N V p1_fixed p2_fixed prevote ∨ cur_stage N V p1_fixed p2_fixed propose
  ∨ cur_stage N V p1_fixed p2_fixed prepare) ∧ I ≠ genesis ∧ ¬ ctx.is_byz N) → ¬ (precommitted_node N V p1_fixed p2_fixed I ∨ precommitted_operator N V p1_fixed p2_fixed I ∨ locked N p1_fixed I S V ∨ locked N p2_fixed I S V)

-- At propose/prepare stage: no prevotes, prevote-operators, or locks at current view
invariant [stage_neg_3]
  ((cur_stage N V p1_fixed p2_fixed propose ∨ cur_stage N V p1_fixed p2_fixed prepare) ∧ I ≠ genesis ∧ ¬ ctx.is_byz N)
  → ¬ (prevoted_node N V p1_fixed p2_fixed I ∨ prevoted_operator N V p1_fixed p2_fixed I ∨ locked N p1_fixed I S V ∨ locked N p2_fixed I S V)

-- If not prepared, must be at prepare stage (contrapositive: past prepare → prepared)
invariant [stage_init_prepare]
  (¬ prepared_node N V p1_fixed p2_fixed ∧ ¬ ctx.is_byz N) → cur_stage N V p1_fixed p2_fixed prepare

-- Genesis never enters the pipeline: never proposed, prevoted, or precommitted
invariant [genesis_not_in_pipeline]
  ¬ ( ¬ ctx.is_byz N ∧ (proposed N V p1_fixed p2_fixed genesis ∨ prevoted_node N V p1_fixed p2_fixed genesis
  ∨ prevoted_operator N V p1_fixed p2_fixed genesis ∨ precommitted_node N V p1_fixed p2_fixed genesis
  ∨ precommitted_operator N V p1_fixed p2_fixed genesis))

-- At prevote stage, node has prevoted for some interaction
-- (respond_propose is the only transition setting cur_stage to prevote, and it also sets prevoted_node)
invariant [prevote_stage_implies_prevoted]
  (cur_stage N V p1_fixed p2_fixed prevote ∧ ¬ ctx.is_byz N) → ∃ I, prevoted_node N V p1_fixed p2_fixed I

-- At precommit stage, node has precommitted for some interaction
-- (respond_prevote is the only transition setting cur_stage to precommit, and it also sets precommitted_node)
invariant [precommit_stage_implies_precommitted]
  (cur_stage N V p1_fixed p2_fixed precommit ∧ ¬ ctx.is_byz N) → ∃ I, precommitted_node N V p1_fixed p2_fixed I

-- Tier 2: Supporting (depends on Tier 3)

-- Cross-node unique prevote: all honest prevotes in a view agree on the interaction
-- Follows from prevote_implies_proposed + unique_operator + unique_proposed_interaction
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
        ixn_contexts ixn c1 c2 ∧
        (ctx.member n c1 → ∃ (u : view), tot_view.le u v ∧ (locked n p1_fixed ixn prevote u ∨ locked n p1_fixed ixn precommit u)) ∧
        (ctx.member n c2 → ∃ (u : view), tot_view.le u v ∧ (locked n p2_fixed ixn prevote u ∨ locked n p2_fixed ixn precommit u))))

-- Ancestor is at most the transitive closure of parent (forward direction)
invariant [ancestor_def_fwd]
  ancestor I J → (I = J ∨ parent I J ∨ ∃ (k : interaction), parent I k ∧ ancestor k J)

-- Ancestor includes the transitive closure of parent (backward direction)
invariant [ancestor_def_bwd]
  (I = J ∨ parent I J ∨ ∃ (k : interaction), parent I k ∧ ancestor k J) → ancestor I J

-- Decision requires a precommit operator (rules out spurious P=Q decisions)
invariant [decide_only_if_precommit_operator]
  (¬ ctx.is_byz N ∧ decided OP V P Q I ∧ I ≠ genesis) → (∃ (op : node), (operator op V P Q ∧ precommitted_operator op V P Q I))

-- At prevote stage, node prevoted for the proposed interaction (or proposed_nil)
invariant [stage_2]
  (cur_stage N V p1_fixed p2_fixed prevote ∧ ¬ ctx.is_byz N)
  → (∃ (i : interaction), ((∃ (op : node), proposed op V p1_fixed p2_fixed i) ∧ prevoted_node N V p1_fixed p2_fixed i) ∨ (∃ (op : node), proposed_nil op V p1_fixed p2_fixed))

-- Only one proposal per view (same interaction and operator)
invariant [unique_proposal]
  ¬ (ctx.is_byz N1 ∨ ctx.is_byz N2) → ( (proposed N1 V p1_fixed p2_fixed I1 ∧ proposed N2 V p1_fixed p2_fixed I2) → (I1 = I2 ∧ N1 = N2) )

-- A single node can propose at most one interaction per view (no honesty guard needed).
-- Follows from propose action's precondition: ∀ ix, ¬ proposed op v p1 p2 ix.
-- Required for manual proof of respond_prevote × precommit_node_lock_consistency,
-- where the operator may be byzantine.
invariant [unique_proposed_interaction]
  (proposed N V p1_fixed p2_fixed I1 ∧ proposed N V p1_fixed p2_fixed I2) → I1 = I2

-- Honest node prevoted → a proposal exists for that interaction
invariant [prevote_implies_proposed]
  (prevoted_node N V p1_fixed p2_fixed I ∧ ¬ ctx.is_byz N) → (∃ (op : node), (operator op V p1_fixed p2_fixed ∧ proposed op V p1_fixed p2_fixed I ))

-- Honest node precommitted → a proposal exists for that interaction
invariant [precommit_only_if_propose]
  (¬ ctx.is_byz N ∧ precommitted_node N V p1_fixed p2_fixed I) → (∃ (op : node), operator op V p1_fixed p2_fixed ∧ proposed op V p1_fixed p2_fixed I)

invariant [prepare_response_only_on_prepare]
  ¬ ctx.is_byz N → (prepared_node N V P Q → ∃ (op : node), operator op V P Q ∧ prepared_operator op V P Q)

invariant [prevote_only_by_operator]
  ¬ ctx.is_byz N → (prevoted_operator OP V P Q I → operator OP V P Q)

invariant [precommit_only_by_operator]
  (¬ ctx.is_byz OP ∧ precommitted_operator OP V P Q I) → operator OP V P Q

-- ####################################################################
-- # Main Safety Property
-- ####################################################################

-- If two nodes decide two ixns, then one is an ancestor of the other
-- (commented out: working on supporting invariants first)
-- safety [main_safety]
--   (¬ ctx.ctx.is_byz N1 ∧ ¬ ctx.ctx.is_byz N2 ∧ decided N1 V1 P1 P2 I1 ∧ decided N2 V2 P1 P2 I2) → (ancestor I1 I2 ∨ ancestor I2 I1)

-- Placeholder safety
safety [main_safety]
  true

#gen_spec

set_option veil.printCounterexamples true
-- set_option veil.smt.model.minimize true
-- set_option veil.smt.translator "SmtTranslator.leanSmt"
-- -- set_option veil.smt.reconstructProofs true
-- -- set_option veil.vc_gen "transition"
-- set_option veil.smt.seed 44
-- set_option veil.smt.timeout 10
-- set_option veil.smt.solver "z3"


  -- @[invProof]
  -- theorem respond_prevote_tr_unique_lock_interaction_per_view :
  --     ∀ (st st' : @State view participant node interaction nodeset stage ctx.ctx.is_byz),
  --       (@System view view_dec view_ne participant participant_dec participant_ne node node_dec
  --               node_ne interaction interaction_dec interaction_ne nodeset nodeset_dec nodeset_ne
  --               stage stage_dec stage_ne ctx.ctx.is_byz tot_view ctx).assumptions
  --           st →
  --         (@System view view_dec view_ne participant participant_dec participant_ne node node_dec
  --                 node_ne interaction interaction_dec interaction_ne nodeset nodeset_dec nodeset_ne
  --                 stage stage_dec stage_ne ctx.ctx.is_byz tot_view ctx).inv
  --             st →
  --           (@IFPProtocol.respond_prevote.tr view view_dec view_ne participant participant_dec
  --                 participant_ne node node_dec node_ne interaction interaction_dec interaction_ne
  --                 nodeset nodeset_dec nodeset_ne stage stage_dec stage_ne ctx.ctx.is_byz tot_view ctx)
  --               st st' →
  --             (@IFPProtocol.unique_lock_interaction_per_view view view_dec view_ne participant
  --                 participant_dec participant_ne node node_dec node_ne interaction interaction_dec
  --                 interaction_ne nodeset nodeset_dec nodeset_ne stage stage_dec stage_ne ctx.ctx.is_byz
  --                 tot_view ctx)
  --               st' :=
  --   by
  --   ((unhygienic intros);
  --     solve_clause[IFPProtocol.respond_prevote.tr]IFPProtocol.unique_lock_interaction_per_view)

#time #check_invariants


  -- Root cause: leanSmt loses the WP substitution for cur_stage.
  -- The SMT query sees pre-state cur_stage instead of ite(N=n∧V=v, S=commit, cur_stage...).
  -- leanAuto encodes function updates correctly; cvc5 can then close the goal.
  -- set_option veil.smt.translator "SmtTranslator.leanAuto" in
  -- @[invProof]
  -- theorem respond_precommit_stage_neg_1 :
  --     ∀ (st : @State view participant node interaction nodeset stage ctx.ctx.is_byz),
  --       ∀ (n : node) (v : view) (p1 : participant) (p2 : participant) (c1 : nodeset) (c2 : nodeset)
  --         (ixn : interaction),
  --         (@System view view_dec view_ne participant participant_dec participant_ne node node_dec
  --                 node_ne interaction interaction_dec interaction_ne nodeset nodeset_dec nodeset_ne
  --                 stage stage_dec stage_ne ctx.ctx.is_byz tot_view ctx).assumptions
  --             st →
  --           (@System view view_dec view_ne participant participant_dec participant_ne node node_dec
  --                   node_ne interaction interaction_dec interaction_ne nodeset nodeset_dec
  --                   nodeset_ne stage stage_dec stage_ne ctx.ctx.is_byz tot_view ctx).inv
  --               st →
  --             (@IFPProtocol.respond_precommit.ext view view_dec view_ne participant participant_dec
  --                 participant_ne node node_dec node_ne interaction interaction_dec interaction_ne
  --                 nodeset nodeset_dec nodeset_ne stage stage_dec stage_ne ctx.ctx.is_byz tot_view ctx n v p1
  --                 p2 c1 c2 ixn)
  --               st fun _ (st' : @State view participant node interaction nodeset stage ctx.ctx.is_byz) =>
  --               @IFPProtocol.stage_neg_1 view view_dec view_ne participant participant_dec
  --                 participant_ne node node_dec node_ne interaction interaction_dec interaction_ne
  --                 nodeset nodeset_dec nodeset_ne stage stage_dec stage_ne ctx.ctx.is_byz tot_view ctx st' :=
  --   by solve_wp_clause IFPProtocol.respond_precommit.ext IFPProtocol.stage_neg_1



--   @[invProof]
--   theorem respond_propose_tr_stage_2 :
--       ∀ (st st' : @State view participant node interaction nodeset stage ctx.ctx.is_byz),
--         (@System view view_dec view_ne participant participant_dec participant_ne node node_dec
--                 node_ne interaction interaction_dec interaction_ne nodeset nodeset_dec nodeset_ne
--                 stage stage_dec stage_ne ctx.ctx.is_byz tot_view ctx).assumptions
--             st →
--           (@System view view_dec view_ne participant participant_dec participant_ne node node_dec
--                   node_ne interaction interaction_dec interaction_ne nodeset nodeset_dec nodeset_ne
--                   stage stage_dec stage_ne ctx.ctx.is_byz tot_view ctx).inv
--               st →
--             (@IFPProtocol.respond_propose.tr view view_dec view_ne participant participant_dec
--                   participant_ne node node_dec node_ne interaction interaction_dec interaction_ne
--                   nodeset nodeset_dec nodeset_ne stage stage_dec stage_ne ctx.ctx.is_byz tot_view ctx)
--                 st st' →
--               (@IFPProtocol.stage_2 view view_dec view_ne participant participant_dec participant_ne
--                   node node_dec node_ne interaction interaction_dec interaction_ne nodeset
--                   nodeset_dec nodeset_ne stage stage_dec stage_ne ctx.ctx.is_byz tot_view ctx)
--                 st' :=
--     by ((unhygienic intros); solve_clause[IFPProtocol.respond_propose.tr]IFPProtocol.stage_2)


end IFPProtocol
