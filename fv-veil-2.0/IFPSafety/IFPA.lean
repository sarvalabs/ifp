-- Approach A: Structure + TSet for locks
-- Bundle (interaction, stage, view) into a LockInfo structure.
-- Each node holds a per-participant lock set: function locks : node → participant → LockSet
-- Uses TSet operations: insert, contains, toList, filter, etc.

import Veil

veil module IFPProtocolA


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

-- APPROACH A: Lock as a structured type
@[veil_decl]
structure LockInfo (interaction stage view : Type) where
  ixn : interaction
  stg : stage
  vw  : view
deriving instance Veil.Enumeration for LockInfo

type LockSet

-- `instantiations`
instantiate tot_view : TotalOrderWithMinimum view
instantiate ctx : IFPByzQuorum node nodeset
instantiate lockTset : TSet (LockInfo interaction stage view) LockSet

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
-- sent_lock_in_prepare still carries the lock triple as a LockInfo
relation sent_lock_in_prepare_1 : node → view → participant → participant → LockInfo interaction stage view → Bool
relation sent_lock_in_prepare_2 : node → view → participant → participant → LockInfo interaction stage view → Bool
relation decided : node → view → participant → participant → interaction → Bool

-- APPROACH A: Locks as a per-node per-participant set of LockInfo
function locks : node → participant → LockSet

-- Operator relations
relation operator: node → view → participant → participant → Bool
relation prepared_operator : node → view → participant → participant → Bool
relation proposed : node → view → participant → participant → interaction → Bool
relation proposed_nil : node → view → participant → participant → Bool
relation prevoted_operator : node → view → participant → participant → interaction → Bool
relation precommitted_operator : node → view → participant → participant → interaction → Bool
-- Highest lock computed by operator during propose (for each participant's context)
relation highest_lock_in_propose_1 : node → view → participant → participant → LockInfo interaction stage view → Bool
relation highest_lock_in_propose_2 : node → view → participant → participant → LockInfo interaction stage view → Bool

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

-- Ghost: check if a node has a lock with given fields
ghost relation has_lock (N : node) (P : participant) (I : interaction) (S : stage) (V : view) :=
  lockTset.contains { ixn := I, stg := S, vw := V } (locks N P)

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
  -- Genesis: precommit lock at view zero for all node/participant pairs
  -- (only p1_fixed/p2_fixed matter per assumptions; extra locks are harmless)
  locks N P := lockTset.insert { ixn := genesis, stg := precommit, vw := tot_view.zero } lockTset.empty;
  decided N V P Q I := decide $ (I = genesis ∧ V = tot_view.zero ∧ (P = p1_fixed ∧ Q = p2_fixed))
  height I := 0;
  cur_stage N V P Q S := decide $ (S = prepare ∧ (P = p1_fixed ∧ Q = p2_fixed));
  operator N V P Q := false;
  cur_view N V := decide $ (V = tot_view.zero);
  prepared_operator N V P Q := false;
  sent_lock_in_prepare_1 N U P Q L := false;
  sent_lock_in_prepare_2 N U P Q L := false;
  proposed N V P Q I := false;
  proposed_nil N V P Q := false;
  prevoted_operator N V P Q I := false;
  precommitted_operator N V P Q I := false;
  prepared_node N V P Q := false;
  prevoted_node N V P Q I := false;
  precommitted_node N V P Q I := false;
  highest_lock_in_propose_1 N V P Q L := false;
  highest_lock_in_propose_2 N V P Q L := false;
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
  -- sent_lock_in_prepare_1: find highest lock for p1, stored as LockInfo
  sent_lock_in_prepare_1 n v p1 p2 L := decide $
    (lockTset.contains L (locks n p1) ∧
     ∃ (c1 : nodeset), (ctx.member n c1 ∧ participant_context p1 c1) ∧
     tot_view.lt L.vw v ∧
     (∀ (l2 : LockInfo interaction stage view), lockTset.contains l2 (locks n p1) → tot_view.lt L.vw l2.vw → False) ∧
     (L.stg = prevote → ¬ lockTset.contains { ixn := L.ixn, stg := precommit, vw := L.vw } (locks n p1))
     )
  -- sent_lock_in_prepare_2: find highest lock for p2
  sent_lock_in_prepare_2 n v p1 p2 L := decide $
    (lockTset.contains L (locks n p2) ∧
     ∃ (c2 : nodeset), (ctx.member n c2 ∧ participant_context p2 c2) ∧
     tot_view.lt L.vw v ∧
     (∀ (l2 : LockInfo interaction stage view), lockTset.contains l2 (locks n p2) → tot_view.lt L.vw l2.vw → False) ∧
     (L.stg = prevote → ¬ lockTset.contains { ixn := L.ixn, stg := precommit, vw := L.vw } (locks n p2))
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
        ∃ (l : LockInfo interaction stage view) (t1 t2 : nodeset), (
          sent_lock_in_prepare_1 n v p1 p2 l
          ∧ lockTset.contains l (locks n p1)
          ∧ tot_view.le l.vw v
          ∧ ctx.supermajority t1 c1 ∧ ctx.supermajority t2 c2
          ∧ ( l.stg = prevote → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → prevoted_node nt l.vw p1 p2 l.ixn)) )
          ∧ ( l.stg = precommit → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → precommitted_node nt l.vw p1 p2 l.ixn)) )
          ∧ interactions l.ixn p1 p2
        )
      ))
    )
  )
  require ∃ (s2 : nodeset), (
    ctx.supermajority s2 c2 ∧ (
      ∀ (n : node), (
        ctx.member n s2 → (prepared_node n v p1 p2 ∧
        ∃ (l : LockInfo interaction stage view) (t1 t2 : nodeset), (
          sent_lock_in_prepare_2 n v p1 p2 l
          ∧ lockTset.contains l (locks n p1)
          ∧ tot_view.le l.vw v
          ∧ ctx.supermajority t1 c1 ∧ ctx.supermajority t2 c2
          ∧ ( l.stg = prevote → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → prevoted_node nt l.vw p1 p2 l.ixn)) )
          ∧ ( l.stg = precommit → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → precommitted_node nt l.vw p1 p2 l.ixn)) )
          ∧ interactions l.ixn p1 p2
        )
      ))
    )
  )
  let l_max_1 : LockInfo interaction stage view ← pick
  require ∃ (n_max_1 : node), (
    ctx.member n_max_1 c1
    ∧ interactions l_max_1.ixn p1 p2
    ∧ sent_lock_in_prepare_1 n_max_1 v p1 p2 l_max_1
    ∧ lockTset.contains l_max_1 (locks n_max_1 p1) ∧
    ∀ (n_l : node) (l_other : LockInfo interaction stage view), (
      (ctx.member n_l c1  ∧ sent_lock_in_prepare_1 n_l v p1 p2 l_other) → (
        interactions l_other.ixn p1 p2 ∧
        (
          height l_other.ixn < height l_max_1.ixn
          ∨ (height l_other.ixn = height l_max_1.ixn ∧ l_other.stg = prevote ∧ l_max_1.stg = precommit)
          ∨ (height l_other.ixn = height l_max_1.ixn ∧ l_other.stg = l_max_1.stg ∧ tot_view.le l_other.vw l_max_1.vw)
          ∨ (l_other = l_max_1)
        )
      )
    )
  )
  let l_max_2 : LockInfo interaction stage view ← pick
  require ∃ (n_max_2 : node), (
    ctx.member n_max_2 c2
    ∧ interactions l_max_2.ixn p1 p2
    ∧ sent_lock_in_prepare_2 n_max_2 v p1 p2 l_max_2
    ∧ lockTset.contains l_max_2 (locks n_max_2 p2) ∧
    ∀ (n_l : node) (l_other : LockInfo interaction stage view), (
      (ctx.member n_l c2  ∧ sent_lock_in_prepare_2 n_l v p1 p2 l_other) → (
        interactions l_other.ixn p1 p2 ∧
        (
          height l_other.ixn < height l_max_2.ixn
          ∨ (height l_other.ixn = height l_max_2.ixn ∧ l_other.stg = prevote ∧ l_max_2.stg = precommit)
          ∨ (height l_other.ixn = height l_max_2.ixn ∧ l_other.stg = l_max_2.stg ∧ tot_view.le l_other.vw l_max_2.vw)
          ∨ (l_other = l_max_2)
        )
      )
    )
  )
  require l_max_1.ixn ≠ ixn_propose
  require ¬ (ancestor l_max_1.ixn ixn_propose ∨ ancestor ixn_propose l_max_1.ixn)
  -- Record computed highest locks for respond_propose to read
  highest_lock_in_propose_1 op v p1 p2 l_max_1 := true
  highest_lock_in_propose_2 op v p1 p2 l_max_2 := true
  if (l_max_1.stg = prevote ∧ l_max_2.stg = prevote ∧ l_max_1.ixn = l_max_2.ixn) then
    proposed op v p1 p2 l_max_1.ixn := true;
  if (l_max_1.stg = precommit ∧ l_max_2.stg = precommit ∧ l_max_1.ixn = l_max_2.ixn) then
    parent l_max_1.ixn ixn_propose := decide $ (l_max_1.ixn ≠ ixn_propose);
    ancestor A ixn_propose := decide $ ancestor A l_max_1.ixn ∨ A = l_max_1.ixn ∨ A = ixn_propose;
    proposed op v p1 p2 ixn_propose := true;
    height ixn_propose := height l_max_1.ixn + 1;
  if (l_max_1.stg = prevote ∧ l_max_2.stg = prevote ∧ l_max_1.ixn ≠ l_max_2.ixn) then
    proposed_nil op v p1 p2 := true;
}

action respond_propose (n : node) (v : view) (p1 p2 : participant) (c1 c2 : nodeset)
    (ixn : interaction) (l_max_1 l_max_2 : LockInfo interaction stage view) {
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
        ∃ (l : LockInfo interaction stage view) (t1 t2 : nodeset), (
          sent_lock_in_prepare_1 n v p1 p2 l
          ∧ lockTset.contains l (locks n p1)
          ∧ tot_view.le l.vw v
          ∧ ctx.supermajority t1 c1 ∧ ctx.supermajority t2 c2
          ∧ ( l.stg = prevote → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → prevoted_node nt l.vw p1 p2 l.ixn)) )
          ∧ ( l.stg = precommit → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → precommitted_node nt l.vw p1 p2 l.ixn)) )
          ∧ interactions l.ixn p1 p2
        )
      ))
    )
  )
  -- Quorum verification c2 (QC validity check)
  require ∃ (s2 : nodeset), (
    ctx.supermajority s2 c2 ∧ (
      ∀ (n : node), (
        ctx.member n s2 → (prepared_node n v p1 p2 ∧
        ∃ (l : LockInfo interaction stage view) (t1 t2 : nodeset), (
          sent_lock_in_prepare_2 n v p1 p2 l
          ∧ lockTset.contains l (locks n p1)
          ∧ tot_view.le l.vw v
          ∧ ctx.supermajority t1 c1 ∧ ctx.supermajority t2 c2
          ∧ ( l.stg = prevote → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → prevoted_node nt l.vw p1 p2 l.ixn)) )
          ∧ ( l.stg = precommit → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → precommitted_node nt l.vw p1 p2 l.ixn)) )
          ∧ interactions l.ixn p1 p2
        )
      ))
    )
  )
  -- Read operator's highest lock claims
  require ∃ (op : node), operator op v p1 p2
    ∧ highest_lock_in_propose_1 op v p1 p2 l_max_1
    ∧ highest_lock_in_propose_2 op v p1 p2 l_max_2
  -- Verify claim 1: backed by real data
  require ∃ (n_max_1 : node), ctx.member n_max_1 c1
    ∧ interactions l_max_1.ixn p1 p2
    ∧ sent_lock_in_prepare_1 n_max_1 v p1 p2 l_max_1
    ∧ lockTset.contains l_max_1 (locks n_max_1 p1)
  -- Verify claim 1: maximal
  require ∀ (n_l : node) (l_other : LockInfo interaction stage view),
    (ctx.member n_l c1 ∧ sent_lock_in_prepare_1 n_l v p1 p2 l_other) →
    (interactions l_other.ixn p1 p2 ∧
      (height l_other.ixn < height l_max_1.ixn
       ∨ (height l_other.ixn = height l_max_1.ixn ∧ l_other.stg = prevote ∧ l_max_1.stg = precommit)
       ∨ (height l_other.ixn = height l_max_1.ixn ∧ l_other.stg = l_max_1.stg ∧ tot_view.le l_other.vw l_max_1.vw)
       ∨ (l_other = l_max_1)))
  -- Verify claim 2: backed by real data
  require ∃ (n_max_2 : node), ctx.member n_max_2 c2
    ∧ interactions l_max_2.ixn p1 p2
    ∧ sent_lock_in_prepare_2 n_max_2 v p1 p2 l_max_2
    ∧ lockTset.contains l_max_2 (locks n_max_2 p2)
  -- Verify claim 2: maximal
  require ∀ (n_l : node) (l_other : LockInfo interaction stage view),
    (ctx.member n_l c2 ∧ sent_lock_in_prepare_2 n_l v p1 p2 l_other) →
    (interactions l_other.ixn p1 p2 ∧
      (height l_other.ixn < height l_max_2.ixn
       ∨ (height l_other.ixn = height l_max_2.ixn ∧ l_other.stg = prevote ∧ l_max_2.stg = precommit)
       ∨ (height l_other.ixn = height l_max_2.ixn ∧ l_other.stg = l_max_2.stg ∧ tot_view.le l_other.vw l_max_2.vw)
       ∨ (l_other = l_max_2)))
  -- Proposal validation: repropose or extend
  require (l_max_1.stg = prevote ∧ l_max_2.stg = prevote ∧ l_max_1.ixn = l_max_2.ixn)
        ∨ (l_max_1.stg = precommit ∧ l_max_2.stg = precommit ∧ l_max_1.ixn = l_max_2.ixn)
  require (l_max_1.stg = prevote ∧ l_max_2.stg = prevote ∧ l_max_1.ixn = l_max_2.ixn) → l_max_1.ixn = ixn
  require (l_max_1.stg = precommit ∧ l_max_2.stg = precommit ∧ l_max_1.ixn = l_max_2.ixn) →
    (ixn ≠ l_max_1.ixn ∧ parent l_max_1.ixn ixn
    ∧ height ixn = height l_max_1.ixn + 1)
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
  if ( ctx.member n c1 ∧ ¬ ∃ (u : view), (tot_view.le u v ∧ lockTset.contains { ixn := ixn, stg := precommit, vw := u } (locks n p1)) ) then
    locks n p1 := lockTset.insert { ixn := ixn, stg := prevote, vw := v } (locks n p1)
  if ( ctx.member n c2 ∧ ¬ ∃ (u : view), (tot_view.le u v ∧ lockTset.contains { ixn := ixn, stg := precommit, vw := u } (locks n p2)) ) then
    locks n p2 := lockTset.insert { ixn := ixn, stg := prevote, vw := v } (locks n p2)
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
    locks n p1 := lockTset.insert { ixn := ixn, stg := precommit, vw := v } (locks n p1);
  if (ctx.member n c2) then
    locks n p2 := lockTset.insert { ixn := ixn, stg := precommit, vw := v } (locks n p2);
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
    ¬ (ctx.is_byz n1 ∨ ctx.is_byz n2) →
    (( (lockTset.contains { ixn := i1, stg := prevote, vw := v } (locks n1 p1_fixed) ∧ lockTset.contains { ixn := i2, stg := prevote, vw := v } (locks n2 p1_fixed))
     ∨ (lockTset.contains { ixn := i1, stg := prevote, vw := v } (locks n1 p2_fixed) ∧ lockTset.contains { ixn := i2, stg := prevote, vw := v } (locks n2 p2_fixed)) ) → i1 = i2)

-- INV3: If an honest node has decided, then a quorum has prevote-locked
invariant [INV3_decided_only_if_quorum_prevote_locked]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ ctx.is_byz n → ( (decided n v p1_fixed p2_fixed ixn ∧ ixn ≠ genesis) →
      (∃ (c1 c2 s1 s2 : nodeset), (ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
        ∧ ∀ (nc : node), (
          (ctx.member nc s1 → ∃ (u : view), (tot_view.le u v ∧ prevoted_node nc v p1_fixed p2_fixed ixn
            ∧ (lockTset.contains { ixn := ixn, stg := prevote, vw := u } (locks nc p1_fixed) ∨ lockTset.contains { ixn := ixn, stg := precommit, vw := u } (locks nc p1_fixed)))) ∧
          (ctx.member nc s2 → ∃ (u : view), (tot_view.le u v ∧ prevoted_node nc v p1_fixed p2_fixed ixn
            ∧ (lockTset.contains { ixn := ixn, stg := prevote, vw := u } (locks nc p2_fixed) ∨ lockTset.contains { ixn := ixn, stg := precommit, vw := u } (locks nc p2_fixed)))) )) ) )

-- INV4: If a quorum has prevote-locked onto an interaction in view v, then lock discovery happens
invariant [INV4_quorum_locked_implies_lock_of_descendant_discovered]
  ∀ (p1 p2 : participant) (ixn : interaction) (v vp : view),
  (∃ (c1 c2 s1 s2 : nodeset), (interactions ixn p1 p2 ∧ participant_context p1 c1 ∧ participant_context p2 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
  ∧ ∀ (n : node), ((ctx.member n s1 → lockTset.contains { ixn := ixn, stg := prevote, vw := v } (locks n p1)) ∧ (ctx.member n s2 → lockTset.contains { ixn := ixn, stg := prevote, vw := v } (locks n p2))))
  ∧ tot_view.lt v vp ) →
  ((∃ (op : node), (∃ (ixn_prop : interaction), proposed op vp p1 p2 ixn_prop) ∨ proposed_nil op vp p1 p2) → (
  ( ∃ (n1 : node) (c1 : nodeset) (l1 : LockInfo interaction stage view), (ctx.member n1 c1 ∧ participant_context p1 c1 ∧ sent_lock_in_prepare_1 n1 vp p1 p2 l1 ∧ tot_view.le v l1.vw ∧ ancestor ixn l1.ixn) )
  ∧ ( ∃ (n2 : node) (c2 : nodeset) (l2 : LockInfo interaction stage view), (ctx.member n2 c2 ∧ participant_context p2 c2 ∧ sent_lock_in_prepare_2 n2 vp p1 p2 l2 ∧ tot_view.le v l2.vw ∧ ancestor ixn l2.ixn) )
  ))

-- Supporting: Prevote lock implies a quorum prevoted
invariant [prevote_lock_only_if_quorun_prevoted]
  (¬ ctx.is_byz N ∧ lockTset.contains { ixn := I, stg := prevote, vw := V } (locks N p1_fixed)
   ∨ lockTset.contains { ixn := I, stg := prevote, vw := V } (locks N p2_fixed))
  → (∃ (c1 c2 s1 s2 : nodeset), ixn_contexts I c1 c2 ∧
    ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧ ∀ (NC : node), (ctx.member NC s1 ∨ ctx.member NC s2) → (prevoted_node NC V p1_fixed p2_fixed I))

-- Supporting (cross-node): precommit + prevote lock consistency
invariant [precommit_node_lock_consistency]
  (¬ ctx.is_byz N ∧ ¬ ctx.is_byz NC ∧ precommitted_node NC V p1_fixed p2_fixed I ∧
   lockTset.contains { ixn := J, stg := prevote, vw := V } (locks N P) ∧ (P = p1_fixed ∨ P = p2_fixed) ∧
   I ≠ genesis ∧ J ≠ genesis) → I = J

-- Supporting: A single honest node can only have locks on one interaction per view per participant
invariant [unique_lock_interaction_per_view]
  ∀ (n : node) (p : participant) (i1 i2 : interaction) (s1 s2 : stage) (v : view),
  (¬ ctx.is_byz n ∧ lockTset.contains { ixn := i1, stg := s1, vw := v } (locks n p) ∧ lockTset.contains { ixn := i2, stg := s2, vw := v } (locks n p) ∧ (p = p1_fixed ∨ p = p2_fixed)) → i1 = i2

-- Supporting: Precommit lock implies the node prevoted
invariant [precommit_lock_implies_prevoted]
  (¬ ctx.is_byz N ∧ (lockTset.contains { ixn := I, stg := precommit, vw := V } (locks N p1_fixed) ∨ lockTset.contains { ixn := I, stg := precommit, vw := V } (locks N p2_fixed)) ∧ I ≠ genesis) → prevoted_node N V p1_fixed p2_fixed I

-- Supporting: Sent locks correspond to actual locks (p1)
invariant [locks_sent_only_if_locked_1]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare_1 N V p1_fixed p2_fixed L) → lockTset.contains L (locks N p1_fixed)

-- Supporting: Sent locks correspond to actual locks (p2)
invariant [locks_sent_only_if_locked_2]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare_2 N V p1_fixed p2_fixed L) → lockTset.contains L (locks N p2_fixed)

-- Supporting: Genesis locks exist for all context members
invariant [genesis_lock_existence]
  ((participant_context p1_fixed C1 ∧ ctx.member N C1) → lockTset.contains { ixn := genesis, stg := precommit, vw := tot_view.zero } (locks N p1_fixed))
  ∧ ((participant_context p2_fixed C2 ∧ ctx.member N C2) → lockTset.contains { ixn := genesis, stg := precommit, vw := tot_view.zero } (locks N p2_fixed))

invariant [highest_lock_sent]
  (sent_lock_in_prepare_1 N V p1_fixed p2_fixed L →
    (lockTset.contains L (locks N p1_fixed) ∧
     tot_view.lt L.vw V ∧
     (∀ (l2 : LockInfo interaction stage view), lockTset.contains l2 (locks N p1_fixed) → (tot_view.lt L.vw l2.vw ∧ tot_view.lt l2.vw V) → False) ∧
     (L.stg = prevote → ¬ lockTset.contains { ixn := L.ixn, stg := precommit, vw := L.vw } (locks N p1_fixed))))
  ∧
  (sent_lock_in_prepare_2 N V p1_fixed p2_fixed L →
    (lockTset.contains L (locks N p2_fixed) ∧
     tot_view.lt L.vw V ∧
     (∀ (l2 : LockInfo interaction stage view), lockTset.contains l2 (locks N p2_fixed) → (tot_view.lt L.vw l2.vw ∧ tot_view.lt l2.vw V) → False) ∧
     (L.stg = prevote → ¬ lockTset.contains { ixn := L.ixn, stg := precommit, vw := L.vw } (locks N p2_fixed))))

invariant [precommit_next_view_discovery]
  ∀ (v v2 : view) (i : interaction) (c1 c2 : nodeset), (
    (interactions i p1_fixed p2_fixed ∧
     tot_view.next v v2 ∧
     v ≠ v2 ∧
     (∃ (op : node), (¬ ctx.is_byz op ∧ operator op v2 p1_fixed p2_fixed ∧ prepared_operator op v2 p1_fixed p2_fixed)) ∧
     (∃ (m : node), (¬ ctx.is_byz m ∧ prepared_node m v2 p1_fixed p2_fixed)) ∧
     ixn_contexts i c1 c2 ∧
     i ≠ genesis ∧
     tot_view.zero ≠ v ∧
     (∀ (n : node), (¬ ctx.is_byz n →
      ((ctx.member n c1 → lockTset.contains { ixn := i, stg := precommit, vw := v } (locks n p1_fixed)) ∧
       (ctx.member n c2 → lockTset.contains { ixn := i, stg := precommit, vw := v } (locks n p2_fixed)) ∧
       cur_stage n v p1_fixed p2_fixed commit ∧
       prepared_node n v2 p1_fixed p2_fixed ∧
       cur_view n v2
      )) )) →
    (∀ (n : node), ¬ ctx.is_byz n → (
      (ctx.member n c1 → (sent_lock_in_prepare_1 n v2 p1_fixed p2_fixed { ixn := i, stg := precommit, vw := v })) ∧
      (ctx.member n c2 → (sent_lock_in_prepare_2 n v2 p1_fixed p2_fixed { ixn := i, stg := precommit, vw := v })))
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

-- Genesis locks: no prevote locks for genesis, precommit only at view zero
invariant [genesis_lock_only_at_zero]
  ∀ (n : node) (p : participant) (s : stage) (v : view),
    lockTset.contains { ixn := genesis, stg := s, vw := v } (locks n p) → (v = tot_view.zero ∧ s = precommit)

-- Non-genesis locks require preparation
invariant [locked_only_if_prepared]
  ∀ (n : node) (i : interaction) (s : stage) (v : view),
  (¬ ctx.is_byz n ∧ (lockTset.contains { ixn := i, stg := s, vw := v } (locks n p1_fixed) ∨ lockTset.contains { ixn := i, stg := s, vw := v } (locks n p2_fixed)) ∧ v ≠ tot_view.zero ∧ i ≠ genesis) → prepared_node n v p1_fixed p2_fixed

-- Stage negativity invariants
invariant [stage_neg_1]
  ∀ (n : node) (v : view) (i : interaction),
  ((cur_stage n v p1_fixed p2_fixed precommit ∨ cur_stage n v p1_fixed p2_fixed prevote ∨ cur_stage n v p1_fixed p2_fixed propose
  ∨ cur_stage n v p1_fixed p2_fixed prepare) ∧ i ≠ genesis ∧ ¬ ctx.is_byz n) →
  ¬ (decided n v p1_fixed p2_fixed i ∨ lockTset.contains { ixn := i, stg := precommit, vw := v } (locks n p1_fixed) ∨ lockTset.contains { ixn := i, stg := precommit, vw := v } (locks n p2_fixed))

invariant [stage_neg_2]
  ∀ (n : node) (v : view) (i : interaction) (s : stage),
  ((cur_stage n v p1_fixed p2_fixed prevote ∨ cur_stage n v p1_fixed p2_fixed propose
  ∨ cur_stage n v p1_fixed p2_fixed prepare) ∧ i ≠ genesis ∧ ¬ ctx.is_byz n) →
  ¬ (precommitted_node n v p1_fixed p2_fixed i ∨ precommitted_operator n v p1_fixed p2_fixed i ∨ lockTset.contains { ixn := i, stg := s, vw := v } (locks n p1_fixed) ∨ lockTset.contains { ixn := i, stg := s, vw := v } (locks n p2_fixed))

invariant [stage_neg_3]
  ∀ (n : node) (v : view) (i : interaction) (s : stage),
  ((cur_stage n v p1_fixed p2_fixed propose ∨ cur_stage n v p1_fixed p2_fixed prepare) ∧ i ≠ genesis ∧ ¬ ctx.is_byz n)
  → ¬ (prevoted_node n v p1_fixed p2_fixed i ∨ prevoted_operator n v p1_fixed p2_fixed i ∨ lockTset.contains { ixn := i, stg := s, vw := v } (locks n p1_fixed) ∨ lockTset.contains { ixn := i, stg := s, vw := v } (locks n p2_fixed))

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
        (ctx.member n c1 → ∃ (u : view), tot_view.le u v ∧
          (lockTset.contains { ixn := ixn, stg := prevote, vw := u } (locks n p1_fixed) ∨ lockTset.contains { ixn := ixn, stg := precommit, vw := u } (locks n p1_fixed))) ∧
        (ctx.member n c2 → ∃ (u : view), tot_view.le u v ∧
          (lockTset.contains { ixn := ixn, stg := prevote, vw := u } (locks n p2_fixed) ∨ lockTset.contains { ixn := ixn, stg := precommit, vw := u } (locks n p2_fixed)))))

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

set_option maxHeartbeats 10000000
#gen_spec

set_option veil.printCounterexamples true

#time #check_invariants


end IFPProtocolA
