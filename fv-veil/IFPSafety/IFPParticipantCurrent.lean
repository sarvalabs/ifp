import Veil

class IFPByzQuorum (node : Type) (is_byz : outParam (node → Prop)) (nset : outParam Type) where
  member (n : node) (s : nset) : Prop
  supermajority (s : nset) (c : nset) : Prop   -- s is a supermajority of context c  -- 2f + 1 nodes

  supermajority_s_belongs_to_c :
    ∀ (s c : nset), supermajority s c → ∀ (n : node), (member n s → member n c)

  supermajorities_intersect_in_honest :
    ∀ (s1 s2 c : nset),
      (supermajority s1 c ∧ supermajority s2 c) → (∃ (n : node), member n s1 ∧ member n s2 ∧ ¬ is_byz n)
  --  supermajority s1 c ∧ supermajority s2 c →


-- class IFPLock (node participant interaction bool view : Type)  (nset : outParam Type) where
--   member (n : node) (s : nset) : Prop
--   supermajority (s : nset) (c : nset) : Prop   -- s is a supermajority of context c  -- 2f + 1 nodes

--   supermajority_s_belongs_to_c :
--     ∀ (s c : nset), supermajority s c → ∀ (n : node), (member n s → member n c)

--   supermajorities_intersect_in_honest :
--     ∀ (s1 s2 c : nset),
--       (supermajority s1 c ∧ supermajority s2 c) → (∃ (n : node), member n s1 ∧ member n s2 ∧ ¬ is_byz n)
--   --  supermajority s1 c ∧ supermajority s2 c →



-- We prove safety of IFP for a single epoch
veil module IFP

type view
instantiate tot_view : TotalOrderWithMinimum view
type participant
immutable individual p1_fixed : participant
immutable individual p2_fixed : participant
type node
type interaction
type nodeset
type stage
individual propose : stage
individual prevote : stage
individual precommit : stage
individual commit : stage


variable (is_byz : node → Prop)

instantiate ctx : IFPByzQuorum node is_byz nodeset

-- interactions between participants, and contexts are fixed
immutable relation interactions : interaction → participant → participant → Prop
immutable relation participant_context: participant → nodeset → Prop
-- immutable relation ixn_contexts : interaction → nodeset → nodeset → Prop

-- instantiate bg : IFPTheory.Background node participant interaction nodeset
-- open IFPTheory.Background
-- open IFPTheory

-- # for all nodes
relation cur_view: node → view → Prop
-- relation prepare_timed_out: node → view → Prop
-- An alternative: relation in_prepare_stage : node → view → Prop
relation sent_lock_in_prepare_1 : node → view → participant → participant → interaction → Bool → view → Prop
relation sent_lock_in_prepare_2 : node → view → participant → participant → interaction → Bool → view → Prop
relation decided : node → view → participant → participant → interaction → Prop
relation locked : node → participant → interaction → Bool → view → Prop
-- node n locked for participant p on interaction ixn stage prevote view v
-- Bool true = Prevote stage, false = Precommit stage
relation cur_stage : node → view → participant → participant → interaction → stage → Prop
-- 0 = Propose, 1 = Prevote, 2 = Precommit

-- Maintain state variable for checking whether a node has voted for a ixn with a participant in a view
-- relation voted_participant : node → participant → view → Prop


-- # For Operators
relation operator: node → view → participant → participant → Prop
relation prepared_operator : node → view → participant → participant → Prop
relation proposed : node → view → participant → participant → interaction → Prop
relation proposed_nil : node → view → participant → participant → Prop
-- ixn (p1 p2) - view 0
relation prevoted_operator : node → view → participant → participant → interaction → Prop
relation precommitted_operator : node → view → participant → participant → interaction → Prop
-- relation broadcasted_decision : node → view → participant → participant → interaction → Prop

-- relation node_action : node → participant → Prop

-- # For Non-Operator Nodes
relation prepared_node : node → view → participant → participant → Prop
relation prevoted_node : node → view → participant → participant → interaction → Prop
relation precommitted_node : node → view → participant → participant → interaction → Prop

-- # For Interactions
-- relation height : interaction → Nat → Nat → Prop
function height1 : interaction → Nat
function height2 : interaction → Nat
-- relation lock_leq : interaction → Bool → interaction → Bool → Prop - Defined in IFPTheory
relation parent : interaction → interaction → Prop -- parent → child → Prop
-- relation parent2 : interaction → interaction → Prop
-- parent i j = true - here, i is parent of j
relation ancestor : interaction → interaction → Prop -- ancestor → descendant → Prop
-- relation ancestor2 : interaction → interaction → Prop
individual genesis : interaction

#gen_state

ghost relation ixn_contexts (I : interaction) (C D : nodeset) :=
∃ (p q : participant), interactions I p q ∧ participant_context p C ∧ participant_context q D

-- ghost relation instance_ixn (V : view) (P Q : participant) (I : interaction) :=
--   ∃ (n : node), proposed n V P Q I

-- ghost relation locked_in_view (N : node) (U : view) (P : participant) (I : interaction) (S : Bool) (V : view) :=


-- # Assumptions

-- Assume that there are exactly two such participants among which all ixns occur
-- assumption ∃ (p1 p2 : participant), ( p1 ≠ p2 ∧
--   ( ∀ (i: interaction),  interactions i p1 p2 ) )

-- assumption interactions I p1_fixed p2_fixed

-- assumption p1_fixed ≠ p2_fixed

assumption ∀ (i : interaction) (p q : participant),
  interactions i p q → (p = p1_fixed ∧ q = p2_fixed)

assumption p1_fixed ≠ p2_fixed

-- Assume that only two given distinct participants are part of an interaction
-- assumption ∀ (ixn : interaction) (p1 p2 p3: participant),
--   ((interactions ixn p1 p2 ∧ interactions ixn p1 p3) → p2 = p3)
--   ∧ ((interactions ixn p2 p1 ∧ interactions ixn p3 p1) → p2 = p3)
--   ∧ (interactions ixn p1 p2 → p1 ≠ p2)


-- -- All protocol activity must use the fixed participant pair
-- assumption ∀ (n : node) (v : view) (q1 q2 : participant),
--   (prepared_operator n v q1 q2 ∨ prepared_node n v q1 q2) →
--   ((q1 = p1_fixed ∧ q2 = p2_fixed))

-- assumption ∀ (n : node) (v : view) (q1 q2 : participant) (i : interaction),
--   (proposed n v q1 q2 i ∨ prevoted_node n v q1 q2 i ∨ precommitted_node n v q1 q2 i) →
--   ((q1 = p1_fixed ∧ q2 = p2_fixed))

-- assumption ∀ (n : node) (v : view) (q1 q2 : participant) (i : interaction),
--   (prevoted_operator n v q1 q2 i ∨ precommitted_operator n v q1 q2 i) →
--   ((q1 = p1_fixed ∧ q2 = p2_fixed))

-- assumption ∀ (n : node) (v : view) (q1 q2 : participant) (i : interaction),
--   decided n v q1 q2 i →
--   ((q1 = p1_fixed ∧ q2 = p2_fixed))

-- assumption ∀ (i : interaction), interactions i p1 p2

-- Assume that each participant has only one context.
assumption (participant_context P C1 ∧ participant_context P C2) → C1 = C2


after_init {
  parent I J := False;-- (I = genesis ∧ J = genesis);
  -- parent2 I J := (I = genesis ∧ J = genesis);
  ancestor I J := (I = J); -- I = genesis ∧ J = genesis
  -- ancestor2 I J := (I = J); -- I = genesis ∧ J = genesis
  locked N P I S V := (I = genesis ∧ S = false ∧ V = tot_view.zero ∧ (P = p1_fixed ∨ P = p2_fixed));
  decided N V P Q I := (I = genesis ∧ V = tot_view.zero ∧ (P = p1_fixed ∧ Q = p2_fixed))
  -- height I M N := (I = genesis ∧ M = 0 ∧ N = 0);
  -- height1 genesis := 0;
  -- height2 genesis := 0;
  height1 I := 0;
  height2 I := 0;
  cur_stage N V P Q I S := (S = propose ∧ (P = p1_fixed ∧ Q = p2_fixed));
  operator N V P Q := False;
  cur_view N V := (V = tot_view.zero);
  prepared_operator N V P Q := False;
  sent_lock_in_prepare_1 N U P Q L S V := False;
  sent_lock_in_prepare_2 N U P Q L S V := False;
  proposed N V P Q I := False;
  prevoted_operator N V P Q I := False;
  precommitted_operator N V P Q I := False;
  prepared_node N V P Q := False;
  prevoted_node N V P Q I := False;
  precommitted_node N V P Q I := False;
}

-- #print initialState?

-- # Actions

-- action set_view (v_cur v_new: view) = {
--   -- require ¬ (∃ (n : node), cur_view n v) -- Why not, `¬ (∀ n, cur_view n v)`
--   require ∃ (n : node), cur_view n v_cur -- Why not, `∀ (n:node), cur_view n v_cur`
--   -- require ∀ (n :  node), ¬ cur_view n v_new -- Maybe this condition not necessary
--   require tot_view.next v_cur v_new
--   cur_view N v_new := True
--   cur_view N v_cur := False
-- }

action set_view (v_cur v_next : view) = {
  require ∀ (n : node), cur_view n v_cur -- Why not, `∀ (n:node), cur_view n v_cur`
  require tot_view.next v_cur v_next
  cur_view N V := (V = v_next)
}

action pick_operator (op : node) (v : view) (p1 p2 : participant) = {
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require cur_view op v
  require ∃ (c1 : nodeset), participant_context p1 c1 ∧ ctx.member op c1
  -- Operator is picked from first participant's context by default
  require ∀ (n : node), ¬ operator n v p1 p2  -- Operator is not chosen yet for ixn and v
  operator op v p1 p2 := True
}

-- The operator sends a prepare message
action prepare (op : node) (v : view) (p1 p2 : participant) = {
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require cur_view op v
  require operator op v p1 p2
  require ∃ (c1 c2 : nodeset), ((ctx.member op c1 ∨ ctx.member op c2) ∧ participant_context p1 c1 ∧ participant_context p2 c2)
  require ¬ prepared_operator op v p1 p2
  require ∃ (i : interaction), interactions i p1 p2
  prepared_operator op v p1 p2 := True
}

-- The nodes respond with a prepare message
action respond_prepare (n : node) (v : view) (p1 p2 : participant) = {
  -- require ¬ prepare_timed_out n v
  -- TODO: incorporate prepare timeout and ordering and responding to one
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require cur_view n v
  require ∀ (p q : participant), ¬ (prepared_node n v p p2 ∨ prepared_node n v p1 q)
  require ∃ (op : node), (operator op v p1 p2 ∧ prepared_operator op v p1 p2)
  require ∃ (c1 c2 : nodeset), ((ctx.member n c1 ∨ ctx.member n c2) ∧ participant_context p1 c1 ∧ participant_context p2 c2)
  -- n is in the interaction's contexts
  -- if ∃ (vl : view) (ixnl : interaction) (sl : Bool), locked n vl sl ixnl then
    -- sent_lock_in_prepare n v sl ixnl := True
  prepared_node n v p1 p2 := True
  sent_lock_in_prepare_1 n v p1 p2 IL SL VL :=
    (locked n p1 IL SL VL ∧
     ∃ (c1 : nodeset), (ctx.member n c1 ∧ participant_context p1 c1) ∧
     tot_view.lt VL v ∧
     (∀ (vl2 : view), tot_view.lt VL vl2 → ¬ ∃ (i2 : interaction) (s2 : Bool), locked n p1 i2 s2 vl2) ∧
     (SL = true → ¬ locked n p1 IL false VL)
     )
  sent_lock_in_prepare_2 n v p1 p2 IL SL VL :=
    (locked n p2 IL SL VL ∧
     ∃ (c2 : nodeset), (ctx.member n c2 ∧ participant_context p2 c2) ∧
     tot_view.lt VL v ∧
     (∀ (vl2 : view), tot_view.lt VL vl2 → ¬ ∃ (i2 : interaction) (s2 : Bool), locked n p2 i2 s2 vl2) ∧
     (SL = true → ¬ locked n p2 IL false VL)
     )
}

-- -- The nodes send their lock in the prepare message
-- action send_lock_in_prepare_p1 (n : node) (v vl : view) (p1 p2 : participant) (ixnl : interaction) (sl : Bool) = {
--   require (p1 = p1_fixed ∧ p2 = p2_fixed)
--   require p1 ≠ p2
--   require cur_view n v
--   require prepared_node n v p1 p2
--   require locked n p1 ixnl sl vl
--   require ∃ (c1 : nodeset), (ctx.member n c1 ∧ participant_context p1 c1)
--   require ∀ (vl2 : view), tot_view.lt vl vl2 → ¬ ∃ (ixnl2 : interaction) (sl2 : Bool), locked n p1 ixnl2 sl2 vl2
--   require sl = true → ¬ locked n p1 ixnl false vl
--   require ∀ (i_lock : interaction) (s_lock : Bool) (v_lock), ¬ sent_lock_in_prepare_1 n v p1 p2 i_lock s_lock v_lock
--   sent_lock_in_prepare_1 n v p1 p2 ixnl sl vl := True
-- }

-- action send_lock_in_prepare_p2 (n : node) ( v vl : view) (p1 p2 : participant) (ixnl : interaction) (sl : Bool) = {
--   require (p1 = p1_fixed ∧ p2 = p2_fixed)
--   require p1 ≠ p2
--   require cur_view n v
--   require prepared_node n v p1 p2
--   require locked n p2 ixnl sl vl
--   require ∃ (c2 : nodeset), ctx.member n c2 ∧ participant_context p2 c2
--   require ∀ (vl2 : view), tot_view.lt vl vl2 → ¬ ∃ (ixnl2 : interaction) (sl2: Bool), locked n p2 ixnl2 sl2 vl2
--   require sl = true → ¬ locked n p2 ixnl false vl
--   require ∀ (i_lock : interaction) (s_lock : Bool) (v_lock), ¬ sent_lock_in_prepare_2 n v p1 p2 i_lock s_lock v_lock
--   sent_lock_in_prepare_2 n v p1 p2 ixnl sl vl := True
-- }

-- The operator makes a proposal
action propose (op : node) (v : view) (p1 p2 : participant) (ixn_propose : interaction) = {
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require ∀ (j : interaction), ¬ parent j ixn_propose
  require height1 ixn_propose = 0 ∧ height2 ixn_propose = 0
  require cur_view op v
  require operator op v p1 p2
  require ∃ (c1 c2 : nodeset), ((ctx.member op c1 ∨ ctx.member op c2) ∧ participant_context p1 c1 ∧ participant_context p2 c2)
  require prepared_operator op v p1 p2
  require cur_stage op v p1 p2 ixn_propose propose -- in propose stage
  require ixn_propose ≠ genesis;     -- Don't extend genesis to itself
  require ∀ (ix : interaction), ¬ proposed op v p1 p2 ix -- operator hasnt proposed any ixns yet
  -- quorum of valid locks send from p1's context
  require ∃ (c1 c2 s1 : nodeset), (
    participant_context p1 c1 ∧ ctx.supermajority s1 c1 ∧ participant_context p2 c2 ∧ (
      ∀ (n : node), (
        ctx.member n s1 → (prepared_node n v p1 p2 ∧
        ∃ (vl : view) (ixnl : interaction) (sl : Bool) (t1 t2 : nodeset), (
          sent_lock_in_prepare_1 n v p1 p2 ixnl sl vl
          ∧ locked n p1 ixnl sl vl
          ∧ tot_view.le vl v
          ∧ ctx.supermajority t1 c1 ∧ ctx.supermajority t2 c2
          ∧ ( sl = True → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → prevoted_node nt vl p1 p2 ixnl)) )
          ∧ ( sl = False → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → precommitted_node nt vl p1 p2 ixnl)) )
          ∧ interactions ixnl p1 p2 -- added to require but is also an assumption
        )
      ))
    )
  )
  -- quorum of valid locks send from p2's context
  require ∃ (c1 c2 s2 : nodeset), (
    participant_context p2 c2 ∧ ctx.supermajority s2 c2 ∧ participant_context p1 c1 ∧ (
      ∀ (n : node), (
        ctx.member n s2 → (prepared_node n v p1 p2 ∧
        ∃ (vl : view) (ixnl : interaction) (sl : Bool) (t1 t2 : nodeset), (
          sent_lock_in_prepare_2 n v p1 p2 ixnl sl vl
          ∧ locked n p1 ixnl sl vl
          ∧ tot_view.le vl v
          ∧ ctx.supermajority t1 c1 ∧ ctx.supermajority t2 c2
          ∧ ( sl = True → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → prevoted_node nt vl p1 p2 ixnl)) )
          ∧ ( sl = False → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → precommitted_node nt vl p1 p2 ixnl)) )
          ∧ interactions ixnl p1 p2 -- added to require but is also an assumption
        )
      ))
    )
  )
  -- highest lock from p1's context
  let ixn_max_1 : interaction ← fresh
  let s_max_1 : Bool ← fresh
  let v_max_1 : view ← fresh
  require ∃ (n_max_1 : node) (c1 : nodeset), (
    participant_context p1 c1
    ∧ ctx.member n_max_1 c1
    ∧ interactions ixn_max_1 p1 p2
    ∧ sent_lock_in_prepare_1 n_max_1 v p1 p2 ixn_max_1 s_max_1 v_max_1 ∧
    ∀ (n_l : node) (ixn_l : interaction) (s_l : Bool) (v_l : view), (
      (ctx.member n_l c1  ∧ sent_lock_in_prepare_1 n_l v p1 p2 ixn_l s_l v_l) → (
        interactions ixn_l p1 p2 ∧ -- added to require but is also an assumption
        (
          height1 ixn_l < height1 ixn_max_1
          ∨ (height1 ixn_l = height1 ixn_max_1 ∧ s_l = true ∧ s_max_1 = false)
          ∨ (height1 ixn_l = height1 ixn_max_1 ∧ s_l = s_max_1 ∧ tot_view.le v_l v_max_1)
          ∨ (ixn_l = ixn_max_1 ∧ s_l = s_max_1 ∧ v_l = v_max_1)
        )
      )
    )
  )
  -- highest lock from p2's context
  let ixn_max_2 : interaction ← fresh
  let s_max_2 : Bool ← fresh
  let v_max_2 : view ← fresh
  require ∃ (n_max_2 : node) (c2 : nodeset), (
    participant_context p2 c2
    ∧ ctx.member n_max_2 c2
    ∧ interactions ixn_max_2 p1 p2
    ∧ sent_lock_in_prepare_2 n_max_2 v p1 p2 ixn_max_2 s_max_2 v_max_2 ∧
    ∀ (n_l : node) (ixn_l : interaction) (s_l : Bool) (v_l : view), (
      (ctx.member n_l c2  ∧ sent_lock_in_prepare_2 n_l v p1 p2 ixn_l s_l v_l) → (
        interactions ixn_l p1 p2 ∧ -- added to require but is also an assumption
        (
          height2 ixn_l < height2 ixn_max_2
          ∨ (height2 ixn_l = height2 ixn_max_2 ∧ s_l = true ∧ s_max_2 = false)
          ∨ (height2 ixn_l = height2 ixn_max_2 ∧ s_l = s_max_2 ∧ tot_view.le v_l v_max_2)
          ∨ (ixn_l = ixn_max_2 ∧ s_l = s_max_2 ∧ v_l = v_max_2)
        )
      )
    )
  )
  require ixn_max_1 ≠ ixn_propose
  require ¬ (ancestor ixn_max_1 ixn_propose ∨ ancestor ixn_propose ixn_max_1)
  -- repropose if both are locks for same ixn
  if (s_max_1 = true ∧ s_max_2 = true ∧ ixn_max_1 = ixn_max_2) then
    proposed op v p1 p2 ixn_max_1 := True;
  -- extend if both are commits and are same ixn
  if (s_max_1 = false ∧ s_max_2 = false ∧ ixn_max_1 = ixn_max_2) then
    parent ixn_max_1 ixn_propose := (ixn_max_1 ≠ ixn_propose);
    ancestor A ixn_propose := ancestor A ixn_max_1 ∨ A = ixn_max_1 ∨ A = ixn_propose;
    proposed op v p1 p2 ixn_propose := True;
    height1 ixn_propose := height1 ixn_max_1 + 1; -- (if ixn_max_1 ≠ ixn_propose then height1 ixn_max_1 + 1 else height1 ixn_propose);
    height2 ixn_propose := height2 ixn_max_2 + 1-- (if ixn_max_1 ≠ ixn_propose then height2 ixn_max_2 + 1 else height2 ixn_propose);
  if (s_max_1 = true ∧ s_max_2 = true ∧ ixn_max_1 ≠ ixn_max_2) then
    proposed_nil op v p1 p2 := True;
  -- cur_stage op v p1 p2 ixn_propose S := (S = prevote) -- move to prevote stage
  -- We need the operator to respond to propose msg he sent in respond_propose as a normal node.
  -- The stage is only changed when as a normal node, the response is made. Otherwise, the operator wont pass the require for stage in respond_propose
}

-- action respond_propose_nil (n : node) (v : view) (p1 p2 : participant) = {

-- }

-- The nodes respond with a prevote
action respond_propose (n : node) (v : view) (p1 p2 : participant) (ixn : interaction) = {
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require cur_view n v
  require cur_stage n v p1 p2 ixn propose -- in propose stage
  require interactions ixn p1 p2
  require ∃ (op : node), operator op v p1 p2 ∧ proposed op v p1 p2 ixn
  require ∀ (i : interaction), ¬ prevoted_node n v p1 p2 i
  require ∃ (c1 c2 : nodeset), (ctx.member n c1 ∨ ctx.member n c2) ∧ ixn_contexts ixn c1 c2
  -- quorum of valid locks send from p1's context
  require ∃ (c1 c2 s1 : nodeset), (
    participant_context p1 c1 ∧ ctx.supermajority s1 c1 ∧ participant_context p2 c2 ∧ (
      ∀ (n : node), (
        ctx.member n s1 → (prepared_node n v p1 p2 ∧
        ∃ (vl : view) (ixnl : interaction) (sl : Bool) (t1 t2 : nodeset), (
          sent_lock_in_prepare_1 n v p1 p2 ixnl sl vl
          ∧ locked n p1 ixnl sl vl
          ∧ tot_view.le vl v
          ∧ ctx.supermajority t1 c1 ∧ ctx.supermajority t2 c2
          ∧ ( sl = True → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → prevoted_node nt vl p1 p2 ixnl)) )
          ∧ ( sl = False → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → precommitted_node nt vl p1 p2 ixnl)) )
          ∧ interactions ixnl p1 p2 -- added to require but is also an assumption
        )
      ))
    )
  )
  -- quorum of valid locks send from p2's context
  require ∃ (c1 c2 s2 : nodeset), (
    participant_context p2 c2 ∧ ctx.supermajority s2 c2 ∧ participant_context p1 c1 ∧ (
      ∀ (n : node), (
        ctx.member n s2 → (prepared_node n v p1 p2 ∧
        ∃ (vl : view) (ixnl : interaction) (sl : Bool) (t1 t2 : nodeset), (
          sent_lock_in_prepare_2 n v p1 p2 ixnl sl vl
          ∧ locked n p1 ixnl sl vl
          ∧ tot_view.le vl v
          ∧ ctx.supermajority t1 c1 ∧ ctx.supermajority t2 c2
          ∧ ( sl = True → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → prevoted_node nt vl p1 p2 ixnl)) )
          ∧ ( sl = False → (∀ (nt : node), ((ctx.member nt t1 ∨ ctx.member nt t2) → precommitted_node nt vl p1 p2 ixnl)) )
          ∧ interactions ixnl p1 p2 -- added to require but is also an assumption
        )
      ))
    )
  )
  -- highest lock from p1's context
  let ixn_max_1 : interaction ← fresh
  let s_max_1 : Bool ← fresh
  let v_max_1 : view ← fresh
  require ∃ (n_max_1 : node) (c1 : nodeset), (
    participant_context p1 c1
    ∧ ctx.member n_max_1 c1
    ∧ interactions ixn_max_1 p1 p2
    ∧ sent_lock_in_prepare_1 n_max_1 v p1 p2 ixn_max_1 s_max_1 v_max_1 ∧
    ∀ (n_l : node) (ixn_l : interaction) (s_l : Bool) (v_l : view), (
      (ctx.member n_l c1  ∧ sent_lock_in_prepare_1 n_l v p1 p2 ixn_l s_l v_l) → (
        interactions ixn_l p1 p2 ∧ -- added to require but is also an assumption
        (
          height1 ixn_l < height1 ixn_max_1
          ∨ (height1 ixn_l = height1 ixn_max_1 ∧ s_l = true ∧ s_max_1 = false)
          ∨ (height1 ixn_l = height1 ixn_max_1 ∧ s_l = s_max_1 ∧ tot_view.le v_l v_max_1)
          ∨ (ixn_l = ixn_max_1 ∧ s_l = s_max_1 ∧ v_l = v_max_1)
        )
      )
    )
  )
  -- highest lock from p2's context
  let ixn_max_2 : interaction ← fresh
  let s_max_2 : Bool ← fresh
  let v_max_2 : view ← fresh
  require ∃ (n_max_2 : node) (c2 : nodeset), (
    participant_context p2 c2
    ∧ ctx.member n_max_2 c2
    ∧ interactions ixn_max_2 p1 p2
    ∧ sent_lock_in_prepare_2 n_max_2 v p1 p2 ixn_max_2 s_max_2 v_max_2 ∧
    ∀ (n_l : node) (ixn_l : interaction) (s_l : Bool) (v_l : view), (
      (ctx.member n_l c2  ∧ sent_lock_in_prepare_2 n_l v p1 p2 ixn_l s_l v_l) → (
        interactions ixn_l p1 p2 ∧ -- added to require but is also an assumption
        (
          height2 ixn_l < height2 ixn_max_2
          ∨ (height2 ixn_l = height2 ixn_max_2 ∧ s_l = true ∧ s_max_2 = false)
          ∨ (height2 ixn_l = height2 ixn_max_2 ∧ s_l = s_max_2 ∧ tot_view.le v_l v_max_2)
          ∨ (ixn_l = ixn_max_2 ∧ s_l = s_max_2 ∧ v_l = v_max_2)
        )
      )
    )
  )
  -- reproposed if both are locks for same ixn
  require (s_max_1 = true ∧ s_max_2 = true ∧ ixn_max_1 = ixn_max_2) → ixn_max_1 = ixn
  -- extended if both are commits and are same ixn
  require (s_max_1 = false ∧ s_max_2 = false ∧ ixn_max_1 = ixn_max_2) →
    (parent ixn_max_1 ixn
    ∧ (ixn_max_1 ≠ ixn → height1 ixn = height1 ixn_max_1 + 1)
    ∧ (ixn_max_1 = ixn → height1 ixn = height1 ixn_max_1)
    ∧ (ixn_max_1 ≠ ixn → height2 ixn = height2 ixn_max_1 + 1)
    ∧ (ixn_max_1 = ixn → height2 ixn = height2 ixn_max_1) )
  prevoted_node n v p1 p2 ixn := True
  cur_stage n v p1 p2 ixn S := (S = prevote) -- move to prevote stage
}


-- The operator responds to a quorum of prevotes with a prevote
action prevote (op : node) (v : view) (p1 p2 : participant) (c1 c2 : nodeset) (ixn : interaction) = {
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require ∀ (i : interaction), ¬ prevoted_operator op v p1 p2 i -- maybe remove?
  require cur_view op v
  require operator op v p1 p2
  require ixn_contexts ixn c1 c2
  require ctx.member op c1 ∨ ctx.member op c2
  require cur_stage op v p1 p2 ixn prevote -- in prevote stage
  require ∃ (s1 s2 : nodeset), ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    (∀ (n: node), (ctx.member n s1 ∨ ctx.member n s2) → prevoted_node n v p1 p2 ixn)
  prevoted_operator op v p1 p2 ixn := True
  if ( ctx.member op c1 ∧ ¬ ∃ (u : view), (tot_view.lt u v ∧ locked op p1 ixn false u) ) then
    locked op p1 ixn true v := True -- (( (ctx.member op c1 ∧ P = p1) ∨ (ctx.member op c2 ∧ P = p2) ) )--∧ I = ixn)
  if ( ctx.member op c2 ∧ ¬ ∃ (u : view), (tot_view.lt u v ∧ locked op p2 ixn false u) ) then
    locked op p2 ixn true v := True --(( (ctx.member op c1 ∧ P = p1) ∨ (ctx.member op c2 ∧ P = p2) ) )--∧ I = ixn)
  -- not updating lock if already holding a higher stage lock for same ixn from earlier views
  -- locked op P I S V := (( (ctx.member op c1 ∧ P = p1) ∨ (ctx.member op c2 ∧ P = p2) ) ∧ I = ixn ∧ S = true ∧ V = v)
  -- cur_stage op v p1 p2 ixn S := (S = precommit) -- move to precommit stage
  -- We need the operator to respond to prevote msg he sent in respond_prevote as a normal node.
  -- The stage is only changed when as a normal node, the response is made. Otherwise, the operator wont pass the require for stage in respond_prevote
}

-- The nodes respond to the prevote with a precommit
action respond_prevote (n : node) (v : view) (p1 p2 : participant) (c1 c2 : nodeset) (ixn : interaction) = {
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require cur_view n v
  require cur_stage n v p1 p2 ixn prevote -- in prevote stage
  require ixn_contexts ixn c1 c2
  require ctx.member n c1 ∨ ctx.member n c2
  require ∃ (op : node), operator op v p1 p2 ∧ prevoted_operator op v p1 p2 ixn
  require ∃ (s1 s2 : nodeset), ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → prevoted_node nc v p1 p2 ixn
  precommitted_node n v p1 p2 ixn := True
  if ( ctx.member n c1 ∧ ¬ ∃ (u : view), (tot_view.le u v ∧ locked n p1 ixn false u) ) then
    locked n p1 ixn true v := True --(( (ctx.member n c1 ∧ P = p1) ∨ (ctx.member n c2 ∧ P = p2) ) )--∧ I = ixn)
  if ( ctx.member n c2 ∧ ¬ ∃ (u : view), (tot_view.le u v ∧ locked n p2 ixn false u) ) then
    locked n p2 ixn true v := True --(( (ctx.member n c1 ∧ P = p1) ∨ (ctx.member n c2 ∧ P = p2) ) )--∧ I = ixn)
  -- not updating lock if already holding a higher stage lock for same ixn from earlier views
  -- locked n P I S V := (( (ctx.member n c1 ∧ P = p1) ∨ (ctx.member n c2 ∧ P = p2) ) ∧ I = ixn ∧ S = true ∧ V = v)
  cur_stage n v p1 p2 ixn S := (S = precommit) -- move to precommit stage
}

-- The operator responds to a quorum of precommits by a precommit and decides on the ixn
action precommit (op : node) (v : view) (p1 p2 : participant) (c1 c2 : nodeset) (ixn : interaction) = {
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require cur_view op v
  require operator op v p1 p2
  require ctx.member op c1 ∨ ctx.member op c2
  require cur_stage op v p1 p2 ixn precommit -- in precommit stage
  require ixn_contexts ixn c1 c2
  require ∃ (s1 s2 : nodeset), ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → precommitted_node nc v p1 p2 ixn
  precommitted_operator op v p1 p2 ixn := True
  if (ctx.member op c1) then
  locked op p1 ixn false v := True;--(( (ctx.member op c1 ∧ P = p1) ∨ (ctx.member op c2 ∧ P = p2) ) )--∧ I = ixn)
  if (ctx.member op c2) then
  locked op p2 ixn false v := True;
  -- decided op v p1 p2 ixn := True

  -- broadcasted_decision op v ixn := True
  -- stage op v p1 p2 ixn S := (S = 3) -- move to commit stage
}

-- The nodes decide on the ixn on receiving a precommit from the operator
action respond_precommit (n : node) (v : view) (p1 p2 : participant) (c1 c2 : nodeset) (ixn : interaction) = {
  require (p1 = p1_fixed ∧ p2 = p2_fixed)
  require p1 ≠ p2
  require cur_view n v
  require cur_stage n v p1 p2 ixn precommit -- in precommit stage
  require ixn_contexts ixn c1 c2
  require ctx.member n c1 ∨ ctx.member n c2
  require ∃ (op : node), operator op v p1 p2 ∧ precommitted_operator op v p1 p2 ixn
  require ∃ (s1 s2 : nodeset), ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → precommitted_node nc v p1 p2 ixn
  if (ctx.member n c1) then
  locked n p1 ixn false v := True; --(( (ctx.member n c1 ∧ P = p1) ∨ (ctx.member n c2 ∧ P = p2) ) )-- ∧ I = ixn)
  if (ctx.member n c2) then
  locked n p2 ixn false v := True;
  decided n v p1 p2 ixn := True
  cur_stage n v p1 p2 ixn S := (S = commit)
}

-- -- Nodes decide on an interaction on receiving it from the operator
-- action respond_decision (n : node) (v : view) (ixn : interaction) = {
--   -- let ixn_prep := prepare_propose_ixns v ixn
--   require ∃ (op : node), operator v (prepare_propose_ixns v ixn) op ∧ broadcasted_decision op v ixn ∧
--     ∃ (c1 c2 s1 s2 : nodeset), ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
--     ∀ (n1 : node), (ctx.member n1 s1 ∨ ctx.member n1 s2) → precommitted_node n1 v ixn
--   decided n v ixn := True
-- }

-- action quorum_check (n : node) (p : participant) (c : nodeset) = {
--   require participant_context p c
--   require ctx.member n c
--   node_action n p := True
-- -- }

-- action sabotage (n : node) = {
--   require is_byz n
--   node_action n P := True
-- }

-- # Byzantine nodes can arbitrarily change their local state and send messages
-- action byz_sabotage (n : node) = {
-- #  ------ The Byzantine Actions Being Used Now -----
--   require is_byz n
--   decided n V I := *
--   locked n := *
--   sent_lock_in_prepare n V I J S := *
--   prepared_operator n V I := *
--   proposed n V I := *
--   sent_lock_in_propose n V I J S := *
--   prevoted_operator n V I := *
--   sent_received_prevote_in_prevote n V I M := *
--   precommitted_operator n V I := *
--   broadcasted_decision n V I := *
--   prepared_node n V I := *
--   prevoted_node n V I := *
--   precommitted_node n V I := *
-- }

-- invariant [quorum_with_actions]
--   ∀ (s1 s2 c : nodeset) (p : participant),
--     ctx.supermajority s1 c ∧ ctx.supermajority s2 c ∧
--     (∀ (n : node), (ctx.member n c) → node_action n p) →
--       ∃ (m : node), ctx.member m s1 ∧ ctx.member m s2 ∧ ¬ is_byz m ∧ node_action m p


-- # Invariants

-- Unique Prevote by Nodes
invariant [unique_prevote_nodes]
  ∀ (v : view) (i1 i2 : interaction) (n : node),
    ¬ is_byz n → ((prevoted_node n v p1_fixed p2_fixed i1 ∧ prevoted_node n v p1_fixed p2_fixed i2) → i1 = i2)

-- Unique prevoteQC in Each View------
invariant [unique_prevote_lock_in_view]
  ∀ (n1 n2 : node) (v : view) (i1 i2 : interaction),
    ¬ (is_byz n1 ∨ is_byz n2) → (( (locked n1 p1_fixed i1 true v ∧ locked n2 p1_fixed i2 true v) ∨ (locked n1 p2_fixed i1 true v ∧ locked n2 p2_fixed i2 true v) ) → i1 = i2)

-- invariant [two_prevote_qcs_implies_diff_view]
  -- ∀ ( (s1 s2 s3 s4 c1 c2 : nodeset) ()
  -- )

-- invariant [two_prevoted_operators_implies_diff_view]
--   ∀ (n1 n2 : node) (ixn: interaction) (v1 v2 : view),
--     ¬ (is_byz n1 ∨ is_byz n2) → ( (prevoted_operator n1 v1 p1_fixed p2_fixed ixn ∧ prevoted_operator n2 v2 p1_fixed p2_fixed ixn ∧ n1 ≠ n2) → v1 ≠ v2 )
-- Unique prevoteQC in Each View------

-- Decided only if Quorum of Nodes Prevote-Locked------
invariant [decided_only_if_quorum_prevote_locked]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → ( (decided n v p1_fixed p2_fixed ixn ∧ ixn ≠ genesis) →
      (∃ (c1 c2 s1 s2 : nodeset), (ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
        ∧ ∀ (nc : node), (
          (ctx.member nc s1 → ∃ (u : view), (tot_view.le u v ∧ (locked nc p1_fixed ixn true u ∨ locked nc p1_fixed ixn false u))) ∧
          (ctx.member nc s2 → ∃ (u : view), (tot_view.le u v ∧ (locked nc p2_fixed ixn true u ∨ locked nc p2_fixed ixn false u))) )) ) )

invariant [precommitted_operator_only_if_quorum_prevote_locked]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → ( (precommitted_operator n v p1_fixed p2_fixed ixn ∧ ixn ≠ genesis) →
      (∃ (c1 c2 s1 s2 : nodeset), (ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
        ∧ ∀ (nc : node), (
          (ctx.member nc s1 → ∃ (u : view), (tot_view.le u v ∧ (locked nc p1_fixed ixn true u ∨ locked nc p1_fixed ixn false u))) ∧
          (ctx.member nc s2 → ∃ (u : view), (tot_view.le u v ∧ (locked nc p2_fixed ixn true u ∨ locked nc p2_fixed ixn false u))) )) ) )

-- Decided only if Quorum of Nodes Prevote-Locked------


-- If a quorum has prevote-locked onto an interaction in view v, then in the Prepare stage of
-- later views, a lock from atleast view v and descendant of ixn is obtained -----------------
-- invariant [quorum_locked_implies_lock_of_descendant_discovered]
--   ∀ (p1 p2 : participant) (ixn : interaction) (v vp : view),
--   (∃ (c1 c2 s1 s2 : nodeset), (interactions ixn p1 p2 ∧ participant_context p1 c1 ∨ participant_context p2 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
--   ∧ ∀ (n : node), ((ctx.member n s1 → locked n p1 ixn true v) ∧ (ctx.member n s2 → locked n p2 ixn true v)))
--   ∧ tot_view.lt v vp ) →
--   ((∃ (op : node), prepared_operator op vp p1 p2) → (
--   ( ∃ (n1 : node) (c1 : nodeset) (ixnl1 : interaction) (sl1 : Bool) (vl1 : view), (ctx.member n1 c1 ∧ participant_context p1 c1 ∧ sent_lock_in_prepare_1 n1 vp p1 p2 ixnl1 sl1 vl1 ∧ tot_view.le v vl1 ∧ ancestor ixn ixnl1) )
--   ∧ ( ∃ (n2 : node) (c2 : nodeset) (ixnl2 : interaction) (sl2 : Bool) (vl2 : view), (ctx.member n2 c2 ∧ participant_context p2 c2 ∧ sent_lock_in_prepare_2 n2 vp p1 p2 ixnl2 sl2 vl2 ∧ tot_view.le v vl2 ∧ ancestor ixn ixnl2) )
--   ))

-- invariant [quorum_locked_implies_future_highqc_]

-- If a quorum has prevote-locked onto an interaction in view v, then in the Prepare stage of
-- later views, the highest lock obtained is not from a view earlier than v -----------------


-- ######## Supporting Invariants ############
invariant [precommitted_node_implies_lock]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → ((precommitted_node n v p1_fixed p2_fixed ixn ∧ ixn ≠ genesis) →
      (∃ (c1 c2 : nodeset),
        ixn_contexts ixn c1 c2 ∧
        (ctx.member n c1 → ∃ (u : view), tot_view.le u v ∧ (locked n p1_fixed ixn true u ∨ locked n p1_fixed ixn false u)) ∧
        (ctx.member n c2 → ∃ (u : view), tot_view.le u v ∧ (locked n p2_fixed ixn true u ∨ locked n p2_fixed ixn false u))))

invariant [quorum_locked_implies_discovered_next_view]
  ∀ (ixn : interaction) (v vp : view),
  (∃ (c1 c2 s1 s2 : nodeset), (interactions ixn p1_fixed p2_fixed ∧ participant_context p1_fixed c1 ∨ participant_context p2_fixed c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
  ∧ ∀ (n : node), ((ctx.member n s1 → locked n p1_fixed ixn true v) ∧ (ctx.member n s2 → locked n p2_fixed ixn true v)))
  ∧ tot_view.next v vp ) →
  ((∃ (op : node), prepared_operator op vp p1_fixed p2_fixed) → (
  ( ∃ (n1 : node) (c1 : nodeset) (sl1 : Bool), (ctx.member n1 c1 ∧ participant_context p1_fixed c1 ∧ sent_lock_in_prepare_1 n1 vp p1_fixed p2_fixed ixn sl1 v) )
  ∧ ( ∃ (n2 : node) (c2 : nodeset) (sl2 : Bool), (ctx.member n2 c2 ∧ participant_context p2_fixed c2 ∧ sent_lock_in_prepare_2 n2 vp p1_fixed p2_fixed ixn sl2 v) )
  ))

invariant [prevote_lock_only_if_quorun_prevoted]
  (¬ is_byz N ∧ locked N p1_fixed I true V ∨ locked N p2_fixed I true V) → (∃ (c1 c2 s1 s2 : nodeset), ixn_contexts I c1 c2 ∧
    ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧ ∀ (NC : node), (ctx.member NC s1 ∨ ctx.member NC s2) → (prevoted_node NC V p1_fixed p2_fixed I))

invariant [prevote_operator_only_if_quorum_prevoted]
  ¬ is_byz N → (prevoted_operator N V p1_fixed p2_fixed I → (∃ (c1 c2 s1 s2 : nodeset), ixn_contexts I c1 c2 ∧
    ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧ ∀ (NC : node), (ctx.member NC s1 ∨ ctx.member NC s2) → (prevoted_node NC V p1_fixed p2_fixed I)))

invariant [locks_sent_only_after_prepare_1]
  (¬ is_byz N ∧ sent_lock_in_prepare_1 N V p1_fixed p2_fixed IL SL VL) → prepared_node N V p1_fixed p2_fixed

invariant [locks_sent_only_if_locked_1]
  (¬ is_byz N ∧ sent_lock_in_prepare_1 N V p1_fixed p2_fixed IL SL VL) → locked N p1_fixed IL SL VL

invariant [locks_sent_only_after_prepare_2]
  (¬ is_byz N ∧ sent_lock_in_prepare_2 N V p1_fixed p2_fixed IL SL VL) → prepared_node N V p1_fixed p2_fixed

invariant [locks_sent_only_if_locked_2]
  (¬ is_byz N ∧ sent_lock_in_prepare_2 N V p1_fixed p2_fixed IL SL VL) → locked N p2_fixed IL SL VL

invariant [parent_only_if_proposed]
  parent I J ∧ J ≠ genesis → ∃ (n : node) (p1 p2 : participant) (v : view), proposed n v p1 p2 J

invariant [unique_lock_sent]
  (¬ is_byz N ∧ sent_lock_in_prepare_1 N V p1_fixed p2_fixed IL1 SL1 VL1 ∧ sent_lock_in_prepare_1 N V p1_fixed p2_fixed IL2 SL2 VL2) → (IL1 = IL2 ∧ SL1 = SL2 ∧ VL1 = VL2)

invariant [unique_stage]
  (¬ is_byz N ∧ cur_stage N V p1_fixed p2_fixed I S1 ∧ cur_stage N V p1_fixed p2_fixed I S2) → S1 = S2

invariant [prepare_only_by_operator]
  ¬ is_byz N → (prepared_operator N V p1_fixed p2_fixed → operator N V p1_fixed p2_fixed)

-- invariant [unique_proposal]
--   ¬ (is_byz N1 ∨ is_byz N2) → ( (proposed N1 V p1_fixed p2_fixed I1 ∧ proposed N2 V p1_fixed p2_fixed I2) → (I1 = I2 ∧ N1 = N2) )

-- invariant [proposal_only_if_quorum_prepare]
--   ¬ is_byz N → ( proposed N V p1_fixed p2_fixed I →
--     (∃ (c1 c2 s1 s2 : nodeset), ixn_contexts I c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
--     ∧ ∀ (nc : node), ((ctx.member nc s1 ∨ ctx.member nc s2) → prepared_node nc V p1_fixed p2_fixed)) )

invariant [node_has_cur_view]
  ∀ (n : node), ∃ (v : view), cur_view n v

invariant [unique_cur_view]
  cur_view N U ∧ cur_view N V → U = V

invariant [ancestor_reflexive]
  ancestor I I

invariant [operator_from_ixn_context]
  ¬ is_byz OP → (operator OP V P Q → ∃ (c : nodeset), participant_context P c ∧ ctx.member OP c)

invariant [unique_operator_for_pset]
  ¬ (is_byz N1 ∨ is_byz N2) → (operator N1 V P Q ∧ operator N2 V P Q → N1 = N2)

invariant [proposal_extends_parent]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → ( proposed n v p1_fixed p2_fixed ixn → (∃ (il : interaction) (nl : node) (vl : view) (c1 c2 : nodeset),
    (parent il ixn ∧ participant_context p1_fixed c1 ∧ participant_context p2_fixed c2 ∧
      ((ctx.member nl c1 ∧ sent_lock_in_prepare_1 nl v p1_fixed p2_fixed il true vl) ∨ (ctx.member nl c2 ∧ sent_lock_in_prepare_1 nl v p1_fixed p2_fixed il false vl)))) )

invariant [parent_antisymmetric]
  parent I J ∧ parent J I → (I = J ∧ J = genesis)

invariant [unique_parent]
  parent J I ∧ parent K I → J = K

invariant [parent_irreflexive]
  ¬ parent I I

-- invariant [ancestor_def]
--   ancestor I J ↔ (I = J ∨ parent I J ∨ ∃ (k : interaction), parent I k ∧ ancestor k J)

invariant [decisions_not_from_higher_views]
  cur_view N V ∧ decided N U p1_fixed p2_fixed I → tot_view.le U V

-- invariant [decided_only_if_proposed]
--   ¬ is_byz N → (decided N V P1 P2 I → ∃ (op : node), operator op V P1 P2 ∧ proposed op V P1 P2 I)

invariant [heights_equal]
  height1 I = height2 I

invariant [committed_implies_parent_committed]
  (decided M V p1_fixed p2_fixed J ∧ parent I J ∧ J ≠ genesis) → (∃ (u : view) (n : node), (tot_view.lt u V ∧ decided n u p1_fixed p2_fixed I))

invariant [latest_commit_is_parent] (∃ (u: view) (n : node),
  (decided M V p1_fixed p2_fixed J ∧ tot_view.le u V ∧ decided n u p1_fixed p2_fixed I  ∧ J ≠ genesis
  ∧ (∀ (i : view) (x : node) (ixn : interaction), (tot_view.le u i ∧ tot_view.lt u V) → ¬ decided x i p1_fixed p2_fixed ixn )) )
  → parent I J

invariant [genesis_decided_first]
  (decided N V p1_fixed p2_fixed J ∧ J ≠ genesis) →
    (∃ (u : view) (m : node), tot_view.lt u V ∧ decided m u p1_fixed p2_fixed genesis)

-- invariant [genesis_height_zero]
--   ((height1 I = 0 ∧ (∃ (v : view) (n : node), decided n v P Q I) ) ↔ I = genesis) ∧
--   ((height2 I = 0 ∧ (∃ (v : view) (n : node), decided n v P Q I) ) ↔ I = genesis)

invariant [genesis_view_zero]
  (¬ is_byz N ∧ decided N V P Q I ∧ tot_view.zero = V) → I = genesis

/-
invariant [max_lock_parent_height]

invariant [parent_height]
  parent I J → (height1 I + 1 = height1 J ∧ height2 I + 1 = height2 J)

invariant [parent_height_2]
  (¬ is_byz N ∧ parent I J ∧ proposed N V P Q I) →
    height1 I = height1 J + 1 ∧ height2 I = height2 J + 1

invariant [parent_height_for_valid_proposals]
  (parent I J ∧
   (∃ (n : node) (v : view) (p q : participant),
     ¬ is_byz n ∧ proposed n v p q I)) →
  height1 I = height1 J + 1 ∧ height2 I = height2 J + 1

invariant [ancestor_height]
  ancestor I J → (height1 I ≤ height1 J ∧ height2 I ≤ height2 J)
-/

invariant [unique_decide_in_height]
  (¬ is_byz N ∧ decided N V p1_fixed p2_fixed I) → ¬ (decided N U p1_fixed p2_fixed J ∧ height1 I ≠ 0 ∧ height2 I ≠ 0 ∧ height1 J ≠ 0 ∧ height2 J ≠ 0
  ∧ (height1 I = height1 J ∨ height2 I = height2 J))

invariant [height_uniqueness_of_decided_1]
  (¬ is_byz M ∧ ¬ is_byz N ∧ height1 I = height1 J ∧ decided M U p1_fixed p2_fixed I ∧ decided N V p1_fixed p2_fixed J) → (I = J)

invariant [height_uniqueness_of_decided_2]
  (¬ is_byz M ∧ ¬ is_byz N ∧ height2 I = height2 J ∧ decided M U p1_fixed p2_fixed I ∧ decided N V p1_fixed p2_fixed J) → (I = J)

invariant [genesis_has_no_parent]
  ∀ (p : interaction), ¬ parent p genesis

-- invariant [same_height_locks_implies_diff_view]
--   locked N

-- invariant [extend_highest_lock_1]
--   ¬ is_byz OP ∧ proposed OP V P Q J ∧ pa

invariant [propose_only_if_parent_locked]
  (¬ is_byz OP ∧ proposed OP V p1_fixed p2_fixed J ∧ parent I J) → (∃ (u : view) (n : node) (s : Bool), tot_view.le u V ∧ (locked n p1_fixed I s u ∨ locked n p2_fixed I s u))

-- invariant [proposal_highest_lock]

invariant [propose_only_if_quorum_locks_sent]
  ¬ is_byz N → ( proposed N V p1_fixed p2_fixed I →
    (∃ (c1 c2 s1 s2 : nodeset), ixn_contexts I c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
    ∧ ∀ (nc : node), ((ctx.member nc s1 → (∃ (ixnl : interaction) (sl : Bool) (vl : view), sent_lock_in_prepare_1 nc V p1_fixed p2_fixed ixnl sl vl ) )
      ∧ (ctx.member nc s2 → (∃ (ixnl : interaction) (sl : Bool) (vl : view), sent_lock_in_prepare_1 nc V p1_fixed p2_fixed ixnl sl vl) )) ))

invariant [interaction_participants]
  ∀ (i : interaction) (r s : participant), interactions i r s → (r = p1_fixed ∧ s = p2_fixed)

invariant [precommit_next_view_discovery_2]
  ∀ (v v2 : view) (i : interaction) (op : node) (c1 c2 : nodeset),
    (interactions i p1_fixed p2_fixed ∧
     tot_view.next v v2 ∧
     operator op v2 p1_fixed p2_fixed ∧
     prepared_operator op v2 p1_fixed p2_fixed ∧
     ixn_contexts i c1 c2 ∧
       ∀ (n : node), (
         ¬ is_byz n →
         ((ctx.member n c1 → locked n p1_fixed i false v) ∧
         (ctx.member n c2 → locked n p2_fixed i false v))
       )
    ) →
    (∀ (n : node),
      ¬ is_byz n → ((ctx.member n c1 → sent_lock_in_prepare_1 n v2 p1_fixed p2_fixed i false v) ∧
      (ctx.member n c2 → sent_lock_in_prepare_2 n v2 p1_fixed p2_fixed i false v)))

-- invariant [precommit_next_view_discovery_sup]
--   ∀ (v v2 : view) (i : interaction) (op : node) (c1 c2 s1 s2 : nodeset),
--     (interactions i p1_fixed p2_fixed ∧
--      tot_view.next v v2 ∧
--      operator op v2 p1_fixed p2_fixed ∧
--      prepared_operator op v2 p1_fixed p2_fixed ∧
--      ixn_contexts i c1 c2 ∧
--      ctx.supermajority s1 c1 ∧
--      ctx.supermajority s2 c2 ∧
--      (∀ (n : node), (
--        (ctx.member n s1 → locked n p1_fixed i false v) ∧
--        (ctx.member n s2 → locked n p2_fixed i false v)
--      ))
--     ) →
--     (∀ (n : node),
--       (ctx.member n s1 → sent_lock_in_prepare_1 n v2 p1_fixed p2_fixed i false v) ∧
--       (ctx.member n s2 → sent_lock_in_prepare_2 n v2 p1_fixed p2_fixed i false v))

-- invariant [prevote_next_view_discovery_sup]
--   ∀ (v v2 : view) (i : interaction) (op : node) (c1 c2 s1 s2 : nodeset),
--     (interactions i p1_fixed p2_fixed ∧
--      tot_view.next v v2 ∧
--      operator op v2 p1_fixed p2_fixed ∧
--      prepared_operator op v2 p1_fixed p2_fixed ∧
--      ixn_contexts i c1 c2 ∧
--      ctx.supermajority s1 c1 ∧
--      ctx.supermajority s2 c2 ∧
--      (∀ (n : node), (
--        (ctx.member n s1 → locked n p1_fixed i true v) ∧
--        (ctx.member n s2 → locked n p2_fixed i true v)
--      ))
--     ) →
--     (∀ (n : node),
--       (ctx.member n s1 → (sent_lock_in_prepare_1 n v2 p1_fixed p2_fixed i true v ∨ sent_lock_in_prepare_1 n v2 p1_fixed p2_fixed i false v)) ∧
--       (ctx.member n s2 → (sent_lock_in_prepare_2 n v2 p1_fixed p2_fixed i true v ∨ sent_lock_in_prepare_2 n v2 p1_fixed p2_fixed i false v)))


-- invariant [unique_lock_in_view]
--   (¬ is_byz N1 ∧ ¬ is_byz N2 ∧ locked N1 P I1 S1 V ∧ locked N2 P I2 S2 V ∧ (P = p1_fixed ∨ P = p2_fixed) ) → (I1 = I2)

/-
invariant [decided_only_if_precommitted_operator]
  ∀ (v : view) (p1 p2 : participant) (ixn : interaction) (n : node),
    ¬ is_byz n → ( (decided n v p1 p2 ixn ∧ ixn ≠ genesis) →
      (∃ (op : node), (operator op v p1 p2 ∧ precommitted_operator op v p1 p2 ixn)) )

invariant [precommit_operator_only_if_quorum_locked]
  ∀ (v : view) (ixn : interaction) (p1 p2 : participant) (n : node),
    ¬ is_byz n → (precommitted_operator n v p1 p2 ixn → (∃ (c1 c2 s1 s2 : nodeset), ixn_contexts ixn c1 c2 ∧
    ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (nc : node), ( (ctx.member nc s1 → ∃ (s : Bool), locked nc p1 ixn s v) ∧ (ctx.member nc s2 → ∃ (s : Bool), locked nc p2 ixn s v) ) ) )

invariant [decision_requires_precommit_lock]
  ∀ (n : node) (v : view) (p1 p2 : participant) (i : interaction),
    ¬ is_byz n → (decided n v p1 p2 i ∧ i ≠ genesis → (locked n p1 i false v ∨ locked n p2 i false v))

-- invariant [precommit_operator_only_if_parent_locked]

invariant [prepare_response_only_on_prepare]
  ¬ is_byz N → (prepared_node N V P Q → ∃ (op : node), operator op V P Q ∧ prepared_operator op V P Q)

invariant [prepare_response_only_by_context_nodes]
¬ is_byz N → (prepared_node N V P Q → ∃ (c1 c2 : nodeset), participant_context P c1 ∧ participant_context Q c2 ∧ (ctx.member N c1 ∨ ctx.member N c2))

invariant [proposal_only_by_operator]
  ¬ is_byz N → (proposed N V P Q I → operator N V P Q)

invariant [single_participant_pair_per_view]
  (¬ is_byz N ∧ operator N V P1 Q1 ∧ operator N V P2 Q2) → (P1 = P2 ∧ Q1 = Q2)

invariant [unique_proposal_each_view]
  ¬ (is_byz N1 ∨ is_byz N2) → ( (proposed N1 V P Q I1 ∧ proposed N2 V P Q I2) → (I1 = I2 ∧ N1 = N2) )

invariant [proposal_only_if_quorum_prepare]
  ¬ is_byz N → ( proposed N V P Q I →
    (∃ (c1 c2 s1 s2 : nodeset), ixn_contexts I c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
    ∧ ∀ (nc : node), ((ctx.member nc s1 ∨ ctx.member nc s2) → prepared_node nc V P Q)) )

invariant [propose_only_if_operator_prepare]
  (¬ is_byz N ∧ proposed N V P Q I ) → prepared_operator N V P Q

invariant [prevote_nodes_only_by_context_nodes]
  (¬ is_byz N ∧ prevoted_node N V P Q I) → (∃ (c1 c2 : nodeset), ixn_contexts I c1 c2 ∧ (ctx.member N c1 ∨ ctx.member N c2))

invariant [prevote_operator_only_if_quorum_prepare]
  ¬ is_byz OP → (prevoted_operator OP V P Q I → (∃ (c1 c2 s1 s2 : nodeset), ixn_contexts I c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
    ∧ ∀ (n : node), ((ctx.member n s1 ∨ ctx.member n s2) → prepared_node n V P Q)) )

invariant [prevote_only_by_operator]
  ¬ is_byz N → (prevoted_operator OP V P Q I → operator OP V P Q)

-- invariant [prevote_by_single_operator]
--   ¬ (is_byz OP1 ∨ is_byz OP2) → ((prevoted_operator OP1 V P Q I ∧ prevoted_operator OP2 V P Q I) → OP1 = OP2)

invariant [unique_prevote_operator]
  ¬ is_byz OP → ((prevoted_operator OP V P Q I ∧ prevoted_operator OP V P Q J) → I = J)

invariant [precommit_nodes_only_if_operator_prevote]
  ¬ is_byz N → (precommitted_node N V P Q I → ∃ (op : node), operator op V P Q ∧ prevoted_operator op V P Q I)

-- invariant [precommit_nodes_only_by_context_nodes]
--   ¬ is_byz N → (precommitted_node N V P Q I → ∃ (c1 c2 : nodeset), ixn_contexts I c1 c2 ∧ (ctx.member N c1 ∨ ctx.member N c2))

invariant [precommit_nodes_only_if_prevoted_for_same_ixn]
  ¬ is_byz N → (precommitted_node N V P Q I → prevoted_node N V P Q I)

invariant [unique_precommit_nodes]
  ¬ is_byz N → ((precommitted_node N V P Q I ∧ precommitted_node N V P Q J) → I = J)

invariant [precommit_operator_only_if_quorum_precommit]
  ¬ is_byz OP → (precommitted_operator OP V P Q I → (∃ (c1 c2 s1 s2 : nodeset), ixn_contexts I c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
    ∧ ∀ (n : node), (ctx.member n s1 ∨ ctx.member n s2) → precommitted_node n V P Q I))

invariant [precommit_only_by_operator]
  (¬ is_byz OP ∧ precommitted_operator OP V P Q I) → operator OP V P Q

invariant [precommit_by_single_operator]
  ¬ (is_byz OP1 ∨ is_byz OP2) → ((precommitted_operator OP1 V P Q I ∧ precommitted_operator OP2 V P Q I) → OP1 = OP2)

invariant [unique_precommit_operator]
  (¬ is_byz OP ∧ precommitted_operator OP V P Q I ∧ precommitted_operator OP V P Q J) → I = J

invariant [decide_only_if_precommit_operator]
  (¬ is_byz N ∧ decided OP V P Q I ∧ I ≠ genesis) → (∃ (op : node), (operator op V P Q ∧ precommitted_operator op V P Q I))

invariant [decide_only_if_quorum_precommit]
  (¬ is_byz OP ∧ decided OP V P Q I ∧ I ≠ genesis) → ( ∃ (c1 c2 s1 s2 : nodeset), (ixn_contexts I c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
    ∧ ∀ (n : node), ((ctx.member n s1 ∨ ctx.member n s2) → precommitted_node n V P Q I)) )

invariant [precommit_only_if_propose]
  (¬ is_byz N ∧ precommitted_node N V P Q I) → (∃ (op : node), operator op V P Q ∧ proposed op V P Q I)

invariant [precommit_only_if_prepare_quorum]
  (¬ is_byz N ∧ precommitted_node N V P Q I) → (∃ (c1 c2 s1 s2 : nodeset), (ixn_contexts I c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2
    ∧ ∀ (nc : node), ((ctx.member nc s1 ∨ ctx.member nc s2) → prepared_node nc V P Q)) )
-/

/-
-- If two nodes decide two ixns, then one is an ancestor of the other
safety [main_safety]
  (¬ is_byz N1 ∧ ¬ is_byz N2 ∧ decided N1 V1 P1 P2 I1 ∧ decided N2 V2 P1 P2 I2) → (ancestor I1 I2 ∨ ancestor I2 I1)
-/



#gen_spec

set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true
set_option veil.vc_gen "transition"
-- set_option veil.showVerificationTime true
set_option veil.smt.seed 44
--set_option veil.smt.timeout 10
-- set_option veil.smt.solver "z3"

#time #check_invariants

end IFP
