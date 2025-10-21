
-- # Old Code with All Except Main Safety
import Veil

class IFPTheory.Background
  (node : Type)
  (participant : Type)
  (interaction : Type)
  (context : Type) where
  -- in_context: node → interaction → (participant → node → Prop) → (interaction → participant → participant → Prop) → Prop
  -- ixn_contexts : interaction → (participant → context → Prop) → (participant → context → Prop)
  -- → (interaction → participant → participant → Prop) → Prop

  -- def lock_le (ixn1 : interaction) (s1 : Bool)  (ixn2 : interaction) (s2 : Bool) (height : interaction → Nat) : Prop :=
  -- -- (v1 : View) (v2 : View) (view_le : View → View → Prop)
  -- if height ixn1 < height ixn2 then
  --   True
  -- else if height ixn1 = height ixn2 ∧ s1 = true ∧ s2 = false then
  --   True
  -- -- else if height ixn1 = height ixn2 ∧ s1 = s2 ∧ view_le v1 v2 then
  -- --   True
  -- else
  --   False

-- class IFPNodeSet (node : Type) (participant : Type) (interaction : Type) (is_byz : outParam (node → Prop)) (nset : outParam Type) (context : outParam (participant → nset))
--   (ixn_contexts : outParam (interaction → nset → nset → Prop)) where
--   member (a : node) (s : nset) : Prop
--   is_empty (s : nset) : Prop


--   /-- f + 1 nodes -/
--   greater_than_third (s : nset) : Prop
--   /-- 2f + 1 nodes -/
--   supermajority (s : nset) : Prop
--   /--2f+1 nodes from each context-/
--   quorum (s : nset) (ixn : interaction) : Prop

--   supermajorities_intersect_in_honest :
--     ∀ (s1 s2 : nset), ∃ (a : node), member a s1 ∧ member a s2 ∧ ¬ is_byz a
--   greater_than_third_one_honest :
--     ∀ (s : nset), greater_than_third s → ∃ (a : node), member a s ∧ ¬ is_byz a
--   supermajority_greater_than_third :
--     ∀ (s : nset), supermajority s → greater_than_third s
--   greater_than_third_nonempty :
--     ∀ (s : nset), greater_than_third s → ¬ is_empty s

/-
class IFPByzQuorum (node : Type) (interaction : Type) (is_byz : outParam (node → Prop)) (nset : outParam Type)
(ixn_contexts : outParam (interaction → nset → nset → Prop)) where
  member (a : node) (s : nset) : Prop
  member_ctx1 (a : node) (i : interaction) : Prop
  member_ctx2 (a : node) (i : interaction) : Prop
  supermajority_ctx1 (i : interaction) : Prop       -- 2f + 1 nodes
  supermajority_ctx2 (i : interaction) : Prop       -- 2f + 1 nodes
  quorum (i : interaction) : Prop -- 2f + 1 nodes from each context of ixn

  member_ctx1_ixn :
  supermajorities_intersect_in_honest_ctx1 :
    ∀ (s1 s2 : nset), supermajority_ctx1∃ (a : node), mea s1 ∧  a s2 ∧ ¬ is_byz a
-/

-- # Old Code with Bug Fixed

class IFPByzQuorum (node : Type) (is_byz : outParam (node → Prop)) (nset : outParam Type) where
  member (n : node) (s : nset) : Prop
  supermajority (s : nset) (c : nset) : Prop       -- 2f + 1 nodes

  supermajority_s_belongs_to_c :
    ∀ (s c : nset), supermajority s c → ∀ (n : node), (member n s → member n c)

  supermajorities_intersect_in_honest :
    ∀ (s1 s2 : nset),
      ∃ (n : node), member n s1 ∧ member n s2 ∧ ¬ is_byz n
  --  supermajority s1 c ∧ supermajority s2 c →



-- We prove safety of IFP for a single epoch
veil module IFP

type view
instantiate tot_view : TotalOrderWithMinimum view

type participant
type node
type interaction
-- type context
type nodeset

variable (is_byz : node → Prop) -- immutable relation?

-- instantiate ctx : ByzQuorum node is_byz context
instantiate ctx : IFPByzQuorum node is_byz nodeset

-- interactions between participants, and contexts are fixed
immutable relation participant_context: participant → nodeset → Prop
immutable relation interactions : interaction → participant → participant → Prop
-- immutable relation ixn_contexts : interaction → nodeset → nodeset → Prop

-- instantiate bg : IFPTheory.Background node participant interaction nodeset
-- open IFPTheory.Background
-- open IFPTheory

-- # for all nodes
relation cur_view: node → view → Prop
-- relation prepare_timed_out: node → view → Prop
-- An alternative: relation in_prepare_stage : node → view → Prop
relation sent_lock_in_prepare : node → view → interaction → interaction → Bool → Prop
relation decided : node → view → interaction → Prop
-- relation lock : interaction → Bool → Prop
relation locked : node → interaction → Bool → view → Prop
-- Bool true = Prevote stage, false = Precommit stage
-- function locked : node → interaction × Bool × view

-- # For Operators
relation operator: view → interaction → node → Prop
relation prepared_operator : node → view → interaction → Prop
relation proposed : node → view → interaction → Prop
relation sent_lock_in_propose : node → view → interaction → interaction → Bool → Prop
relation prevoted_operator : node → view → interaction → Prop
relation sent_received_prevote_in_prevote : node → view → interaction → node → Prop
relation precommitted_operator : node → view → interaction → Prop
relation broadcasted_decision : node → view → interaction → Prop

-- # For Non-Operator Nodes
relation prepared_node : node → view → interaction → Prop
relation prevoted_node : node → view → interaction → Prop
relation precommitted_node : node → view → interaction → Prop

-- # For Interactions
function height : interaction → Nat
-- relation height : interaction → Nat → Nat → Prop
-- function height_p1 : interaction → Nat
-- function height_p2 : interaction → Nat
-- relation lock_leq : interaction → Bool → interaction → Bool → Prop - Defined in IFPTheory
relation parent : interaction → interaction → Prop -- parent → child → Prop
relation ancestor : interaction → interaction → Prop -- ancestor → descendant → Prop
-- immutable relation interacting_participants : interaction → participant → participant → Prop
-- relation prepare_propose_ixns : view → interaction → interaction → Prop -- ixn_proposed → ixn_from_prep
function prepare_propose_ixns : view → interaction → interaction -- view → ixn_proposed → ixn_from_prepare
individual genesis : interaction

#gen_state

ghost relation ixn_contexts (I : interaction) (C D : nodeset) :=
∃ (P Q : participant), interactions I P Q ∧ participant_context P C ∧ participant_context Q D

-- # Assumptions
-- Assume that the relations participant_context and ixn_contexts are related as below
-- assumption ∀ (ixn: interaction) (p1 p2 : participant) (c1 c2 : nodeset),
--   ((ixn_contexts ixn c1 c2 ∧ interactions ixn p1 p2) → (participant_context p1 c1 ∧ participant_context p2 c2))
--   ∧ participant_context p1
-- assumption ( ∀ (ixn : interaction) (c1 c2 : nodeset), ixn_contexts ixn c1 c2 →
--   ∃ (p1 p2 : participant), interactions ixn p1 p2 ∧ participant_context p1 c1 ∧ participant_context p2 c2 ) ∧
--   ( ∀ (ixn : interaction) (p1 p2 : participant) (c1 c2 : nodeset), interactions ixn p1 p2 ∧ participant_context p1 c1
--   ∧ participant_context p2 c2 →  ixn_contexts ixn c1 c2 )


-- Assume that only two given distinct participants are part of an interaction
assumption ∀ (ixn : interaction) (p1 p2 p3: participant),
  ((interactions ixn p1 p2 ∧ interactions ixn p1 p3) → p2 = p3)
  ∧ ((interactions ixn p2 p1 ∧ interactions ixn p3 p1) → p2 = p3)
  ∧ (interactions ixn p1 p2 → p1 ≠ p2)

-- Assume that there are exactly two such participants among which all ixns occur
assumption ∃ (p1 p2 : participant), p1 ≠ p2 ∧ ∀ (i: interaction),
  interactions i p1 p2

-- Assume that each participant has only one context.
assumption ∀ (p : participant) (c1 c2 : nodeset),
  (participant_context p c1 ∧ participant_context p c2) → c1 = c2

after_init {
  parent I J := if I = genesis ∧ J = genesis then True else False;
  ancestor I J := if I = J then True else False; -- I = genesis ∧ J = genesis
  locked N I S V := if I = genesis ∧ S = true ∧ V = tot_view.zero then True else False;
  -- locked N  (genesis, false, tot_view.zero)
  decided N V I := if I = genesis ∧ V = tot_view.zero then True else False;
  operator V I N := False;
  cur_view N V := if V = tot_view.zero then True else False;
  prepared_operator N V B := False;
  sent_lock_in_prepare N V B L S := False;
  proposed N V B := False;
  prevoted_operator N V B := False;
  precommitted_operator N V B := False;
  prepared_node N V B := False;
  prevoted_node N V B := False;
  precommitted_node N V B := False;
}

-- #print initialState?

-- # Actions
action pick_operator (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require ∃ (c1 c2 : nodeset), ixn_contexts ixn c1 c2 ∧ ctx.member n c1
  -- Operator is picked from first participant's context by default
  require ∀ (n1 : node), ¬ operator v ixn n1
  -- Operator is not chosen yet for ixn and v
  operator v ixn n := True
}

-- action set_view (v_cur v_new: view) = {
--   -- require ¬ (∃ (n : node), cur_view n v) -- Why not, `¬ (∀ n, cur_view n v)`
--   require ∃ (n : node), cur_view n v_cur -- Why not, `∀ (n:node), cur_view n v_cur`
--   -- require ∀ (n :  node), ¬ cur_view n v_new -- Maybe this condition not necessary
--   require tot_view.next v_cur v_new
--   cur_view N v_new := True
--   cur_view N v_cur := False
-- }


action set_view (v_cur : view) = {
  require ∀ (n : node), cur_view n v_cur -- Why not, `∀ (n:node), cur_view n v_cur`
  cur_view N V := (tot_view.next v_cur V)
}

-- The operator sends a prepare message
action prepare (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require operator v ixn n
  /-
  require ∀ (i : interaction), ∃ (p1 p2 p3 p4 : participant),
    interactions i p1 p2 ∧ interactions ixn p3 p4 ∧ (p1 = p3 ∨ p2 = p4) → ¬ prepared_operator n v i
  `Not sent prepare msg for any other ixn with any of the same participants during the view`
  -- Not needed for now because we assume only two participants. Simpler alternative below
  -/
  require ∀ (i : interaction), ¬ prepared_operator n v i
  prepared_operator n v ixn := True
}

-- The nodes respond with a prepare message
action respond_prepare (n : node) (v : view) (ixn : interaction) = {
  -- require ¬ prepare_timed_out n v
  -- TODO: incorporate prepare timeout and ordering and responding to one
  require cur_view n v
  require ∃ (op : node), operator v ixn op ∧ prepared_operator op v ixn
  require  ∃ (c1 c2 : nodeset), ixn_contexts ixn c1 c2 ∧ (ctx.member n c1 ∨ ctx.member n c2)
  -- n is in the interaction's contexts
  -- if ∃ (vl : view) (ixnl : interaction) (sl : Bool), locked n vl sl ixnl then
    -- sent_lock_in_prepare n v sl ixnl := True
  prepared_node n v ixn := True
}

-- The nodes send their lock in the prepare message
action send_lock_in_prepare (n : node) (v vl : view) (ixn ixnl : interaction) (sl : Bool) = {
  require cur_view n v
  require prepared_node n v ixn
  /-
  require ∃ (p1 p2 p3 p4 : participant),  interactions ixn p1 p2 ∧ interactions ixnl p3 p4 ∧
    (p1 = p3 ∨ p2 = p4) ∧ locked n vl ixnl sl
  `ixnl sl is lock for a participant in ixn's participants`
  We only have two fixed participants for now so each node has only one such lock.
  So we can use the below simplified requirement.
  -/
  require locked n ixnl sl vl
  require ∀ (i_lock : interaction) (s_lock : Bool), ¬ sent_lock_in_prepare n v ixn i_lock s_lock
  -- Not sent any other lock in prepare
  sent_lock_in_prepare n v ixn ixnl sl := True
}

-- The operator makes a proposal
action propose (n : node) (v : view) (ixn ixn_propose : interaction) = {
  require cur_view n v
  require operator v ixn n
  require ∀ (i : interaction), ¬ operator v i n -- operator can only propose one ixn in a view
  require ∃ (c1 c2 s1 s2 : nodeset), ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (n1 : node), (ctx.member n1 s1 ∨ ctx.member n1 s2) → prepared_node n1 v ixn
  require ∀ (ix : interaction), ¬ proposed n v ix
  /-
  let ixn_max_p1 : interaction ← fresh
  let s_max_p1 : Bool ← fresh
  require ∃ (c1 c2 : context), ixn_contexts ixn c1 c2 ∧
    ( ∃ (n_max : node), ctx.member n_max c1 ∧ sent_lock_in_prepare n_max v ixn ixn_max_p1 s_max_p1 ∧
    ∀ (n1 : node) (ixn_p1 : interaction) (s_p1 : Bool), (ctx.member n1 c1 ∧
      sent_lock_in_prepare n v ixn ixn_p1 s_p1) → lock_le ixn_p1 s_p1 ixn_max_p1 s_max_p1 height_p1)
  let ixn_max_p2 : interaction ← fresh
  let s_max_p2 : Bool ← fresh
  require ∃ (c1 c2 : context), ixn_contexts ixn c1 c2 ∧
    ( ∃ (n_max : node), ctx.member n_max c2 ∧ sent_lock_in_prepare n_max v ixn ixn_max_p2 s_max_p2 ∧
    ∀ (n2 : node) (ixn_p2 : interaction) (s_p2 : Bool), (ctx.member n2 c2 ∧
      sent_lock_in_prepare n v ixn ixn_p2 s_p2) → lock_le ixn_p2 s_p2 ixn_max_p2 s_max_p2 height_p2)
  let ixn_proposal : interaction ← fresh
  require (s_max_p1 ∨ s_max_p2) → ixn_max_p1 = ixn_max_p2 = ixn_proposal
  require ¬ (s_max_p1 ∨ s_max_p2) → mother ixn_max_p1 ixn_proposal ∧ father ixn_max_
  if s_max_p1 = true then
    proposed n v ixn_max_p1
  -/
  let ixn_max : interaction ← fresh
  let s_max : Bool ← fresh
  require ∃ (c1 c2 : nodeset), ixn_contexts ixn c1 c2 ∧
    ( ∃ (n_max : node), (ctx.member n_max c1 ∨ ctx.member n_max c2) ∧
      sent_lock_in_prepare n_max v ixn ixn_max s_max ∧
      ∀ (n_l : node) (ixn_l : interaction) (s_l : Bool),
        ((ctx.member n_l c1 ∨ ctx.member n_l c2) ∧ sent_lock_in_prepare n_l v ixn ixn_l s_l) →
          (height ixn_l < height ixn_max ∨ (height ixn_l = height ixn_max ∧ s_l=true ∧ s_max=false)) )
          -- lock_le ixn_l s_l ixn_max s_max height )
  proposed n v ixn_propose := True
  parent ixn_max ixn_propose := True
  -- let ixn_anc : interaction ← fresh
  -- ancestor ixn_anc ixn_propose := if ancestor ixn_anc ixn_max ∨ parent ixn_anc ixn_propose then True else False
  ancestor A ixn_propose := ancestor A ixn_max ∨ A = ixn_max ∨ A = ixn_propose
  -- prepare_propose_ixns v ixn ixn_propose := True
  prepare_propose_ixns v ixn_propose := ixn
  height ixn_propose := height ixn_max + 1
}

-- The operator sends all received locks to nodes in prepareQC as part of proposal
action sent_received_lock_in_propose (n : node) (v vl : view) (ixn_prepare ixn_propose ixnl : interaction) (sl : Bool) = {
  require cur_view n v
  require operator v ixn_prepare n
  require prepare_propose_ixns v ixn_propose = ixn_prepare
  require proposed n v ixn_propose
  require sent_lock_in_prepare n v ixn_prepare ixnl sl
  sent_lock_in_propose n v ixn_propose ixnl sl := True
}

-- The nodes respond with a prevote
action respond_propose (n : node) (v : view) (ixn ixn_prev : interaction) (s_prev : Bool) = {
  require cur_view n v
  require  ∃ (c1 c2 : nodeset), ixn_contexts ixn c1 c2 ∧ (ctx.member n c1 ∨ ctx.member n c2)
  let ixn_prep := prepare_propose_ixns v ixn
  require ∃ (op : node), proposed op v ixn ∧ operator v ixn_prep op
  /-
  require ∀ (i : interaction) (p1 p2 p3 p4 : participant),
    interactions ixn p1 p2 ∧ interactions i p3 p4 ∧ (p1 = p3 ∨ p2 = p4 ∨ p1 = p4 ∨ p2 = p3)
    → ¬ prevoted_node n v i
  -- Not voted for any other ixn with common participants during view
  `Not needed for now because we assume only two participants. Simpler alternative below`
  -/
  require ∀ (i : interaction), ¬ prevoted_node n v i
  require parent ixn_prev ixn
  -- the proposed ixn extends the max lock among the locks in sent_received_lock_in_propose
  require ∀ (ixnl : interaction) (sl : Bool), sent_lock_in_propose n v ixn ixnl sl →
    (height ixnl < height ixn_prev ∨ (height ixnl = height ixn_prev ∧ sl=true ∧ s_prev=false))
  prevoted_node n v ixn := True
}

-- The operator responds to a quorum of prevotes with a prevote
action prevote (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  -- let ixn_prep := prepare_propose_ixns v ixn
  require operator v (prepare_propose_ixns v ixn) n
  require ∃ (c1 c2 s1 s2 : nodeset), ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    (∀ (n1 : node), (ctx.member n1 s1 ∨ ctx.member n1 s2) → prevoted_node n1 v ixn)
  prevoted_operator n v ixn := True
  /-
  `Old Code`
  -- locked n v ixn true := True
  -- let v1 : view ← fresh
  -- let i : interaction ← fresh
  -- let s : Bool ← fresh
  -- locked n v1 i s := if (v1 = v ∧ i = ixn ∧ s = true) then True else False
  locked n v ixn true := True
  ∀ (v1 : view) (i : interaction) (s : Bool), ¬ (v1 = v ∧ i = ixn ∧ s = true)
    → locked n v1 i s := False
  -- Set all other/previous locks to False
  -/
  -- locked n := (ixn, true, v)
  locked n I S V := (I = ixn ∧ S = true ∧ V = v)
}

-- -- The operator sends the prevote votes obtained as prevoteQC part of prevote msg
-- action send_received_prevote_in_prevote (n np : node) (v : view) (ixn : interaction) = {
--   require cur_view n v
--   let ixn_prep := prepare_propose_ixns v ixn
--   require operator v ixn_prep n
--   require prevoted_node np v ixn
--   sent_received_prevote_in_prevote n v ixn np := True
-- }

-- The nodes respond to the prevote with a precommit
action respond_prevote (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require  ∃ (c1 c2 : nodeset), ixn_contexts ixn c1 c2 ∧ (ctx.member n c1 ∨ ctx.member n c2)
  -- let ixn_prep := prepare_propose_ixns v ixn
  require ∃ (op : node), prevoted_operator op v ixn ∧ operator v ( prepare_propose_ixns v ixn) op
  require ∃ (c1 c2 s1 s2 : nodeset), ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (n1 : node), (ctx.member n1 s1 ∨ ctx.member n1 s2) → prevoted_node n1 v ixn
  require prevoted_node n v ixn
  -- require ∀ (i : interaction), ¬ precommitted_node n v i
  /-
  `Old Code`
  -- locked n v ixn true := True
  let v1 : view ← fresh
  let i : interaction ← fresh
  let s : Bool ← fresh
  locked n v1 i s := if (v1 = v ∧ i = ixn ∧ s = true) then True else False
  -/
  -- locked n := (ixn, true, v)
  locked n I S V := (I = ixn ∧ S = true ∧ V = v)
  precommitted_node n v ixn := True
}

-- The operator responds to a quorum of precommits by a precommit and decides on the ixn
action precommit (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  let ixn_prep := prepare_propose_ixns v ixn
  require operator v ixn_prep n
  require ∃ (c1 c2 s1 s2 : nodeset) , ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (n1 : node), (ctx.member n1 s1 ∨ ctx.member n1 s2) → precommitted_node n1 v ixn
  precommitted_operator n v ixn := True
  /-
  `Old Code`
  -- locked n v ixn false := True
  let v1 : view ← fresh
  let i : interaction ← fresh
  let s : Bool ← fresh
  locked n v1 i s := if (v1 = v ∧ i = ixn ∧ s = false) then True else False
  -/
  -- locked n := (ixn, false, v)
  locked n I S V := (I = ixn ∧ S = false ∧ V = v)
  decided n v ixn := True
  broadcasted_decision n v ixn := True
}

-- The nodes decide on the ixn on receiving a precommit from the operator
action respond_precommit (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require  ∃ (c1 c2 : nodeset), ixn_contexts ixn c1 c2 ∧ (ctx.member n c1 ∨ ctx.member n c2)
  let ixn_prep := prepare_propose_ixns v ixn
  require ∃ (op : node), operator v ixn_prep op ∧ precommitted_operator op v ixn ∧
    ∃ (c1 c2 s1 s2 : nodeset), ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (n1 : node), (ctx.member n1 s1 ∨ ctx.member n1 s2) → precommitted_node n1 v ixn
  /-
  `Old Code`
  -- locked n v ixn false := True
  let v1 : view ← fresh
  let i : interaction ← fresh
  let s : Bool ← fresh
  locked n v1 i s := if (v1 = v ∧ i = ixn ∧ s = false) then True else False;
  -/
  -- locked n := (ixn, false, v)
  locked n I S V := (I = ixn ∧ S = false ∧ V = v)
  decided n v ixn := True
}

-- Nodes decide on an interaction on receiving it from the operator
action respond_decision (n : node) (v : view) (ixn : interaction) = {
  -- let ixn_prep := prepare_propose_ixns v ixn
  require ∃ (op : node), operator v (prepare_propose_ixns v ixn) op ∧ broadcasted_decision op v ixn ∧
    ∃ (c1 c2 s1 s2 : nodeset), ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (n1 : node), (ctx.member n1 s1 ∨ ctx.member n1 s2) → precommitted_node n1 v ixn
  decided n v ixn := True
}


-- -- # Byzantine nodes can send whatever they want but cannot forge identities
-- action byz_send_1 (n : node) (v : view) (ixn ixnl : interaction) (sl : Bool)  = {
--   require is_byz n
--   sent_lock_in_prepare n v ixn ixnl sl := True
-- }

-- action byz_send_2 (n : node) (v : view) (ixn : interaction) = {
--   require is_byz n
--   prepared_operator n v ixn := True
-- }

-- action byz_send_3 (n : node) (v : view) (ixn : interaction) = {
--   require is_byz n
--   proposed n v ixn := True
-- }

-- action byz_send_4 (n : node) (v : view) (ixn : interaction) = {
--   require is_byz n
--   prevoted_operator n v ixn := True
-- }

-- action byz_send_5 (n : node) (v : view) (ixn : interaction) = {
--   require is_byz n
--   precommitted_operator n v ixn := True
-- }

-- action byz_send_6 (n : node) (v : view) (ixn : interaction) = {
--   require is_byz n
--   broadcasted_decision n v ixn := True
-- }

-- action byz_send_7 (n : node) (v : view) (ixn : interaction) = {
--   require is_byz n
--   prepared_node n v ixn := True
-- }

-- action byz_send_8 (n : node) (v : view) (ixn : interaction) = {
--   require is_byz n
--   prevoted_node n v ixn := True
-- }

-- action byz_send_9 (n : node) (v : view) (ixn : interaction) = {
--   require is_byz n
--   precommitted_node n v ixn := True
-- }

-- -- # Byzantine nodes can arbitrarily change their local state and send messages
-- action byz_sabotage (n : node) = {
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

/-
# From Tendermint Ivy Proof:
Byzantine nodes can claim they observed whatever they want about themselves,
 but they cannot remove observations. Note that we use assume because we don't want those
 to be checked; we just want them to be true (that's the model of Byzantine behavior)

action misbehave = {
 Byzantine nodes can claim they observed whatever they want about themselves,
 but they cannot remove observations. Note that we use assume because we don't
 want those to be checked; we just want them to be true (that's the model of
 Byzantine behavior).
        observed_prevoted(N,R,V) := *;
        assume (old observed_prevoted(N,R,V)) -> observed_prevoted(N,R,V);
        assume well_behaved(N) -> old observed_prevoted(N,R,V) = observed_prevoted(N,R,V);
        observed_precommitted(N,R,V) := *;
        assume (old observed_precommitted(N,R,V)) -> observed_precommitted(N,R,V);
        assume well_behaved(N) -> old observed_precommitted(N,R,V) = observed_precommitted(N,R,V);
    }
-/

/-
-- # Byzantine Behaviour
internal transition byz_actions = fun st st' =>
  ( ∀ (n : node) (v : view) (ixn ixnl : interaction) (sl : Bool),
    is_byz n ∧ (st.sent_lock_in_prepare n v ixn ixnl sl → st'.sent_lock_in_prepare n v ixn ixnl sl) ) ∧
  ( ∀ (n : node) (v : view) (ixn : interaction),
    is_byz n ∧ (st.decided n v ixn → st'.decided n v ixn) ) ∧
  ( ∀ (n : node) (v : view) (ixn : interaction) (s : Bool),
    is_byz n ∧ (st.locked n = (ixn, s, v) → st'.locked n = (ixn, s, v)) ) ∧
  ( ∀ (n : node) (v : view) (ixn : interaction),
    is_byz n ∧ (st.prepared_operator n v ixn → st'.prepared_operator n v ixn) ) ∧
  ( ∀ (n : node) (v : view) (ixn : interaction),
    is_byz n ∧ (st.proposed n v ixn → st'.proposed n v ixn) ) ∧
  ( ∀ (n : node) (v : view) (ixn : interaction),
    is_byz n ∧ (st.prevoted_operator n v ixn → st'.prevoted_operator n v ixn) ) ∧
  ( ∀ (n : node) (v : view) (ixn : interaction),
    is_byz n ∧ (st.precommitted_operator n v ixn → st'.precommitted_operator n v ixn) ) ∧
  ( ∀ (n : node) (v : view) (ixn : interaction),
    is_byz n ∧ (st.broadcasted_decision n v ixn → st'.broadcasted_decision n v ixn) ) ∧
  ( ∀ (n : node) (v : view) (ixn : interaction),
    is_byz n ∧ (st.prepared_node n v ixn → st'.prepared_node n v ixn) ) ∧
  ( ∀ (n : node) (v : view) (ixn : interaction),
    is_byz n ∧ (st.prevoted_node n v ixn → st'.prevoted_node n v ixn) ) ∧
  ( ∀ (n : node) (v : view) (ixn : interaction),
    is_byz n ∧ (st.precommitted_node n v ixn → st'.precommitted_node n v ixn) )
-/

-- # Invariants

-- If two nodes decide two ixns, then one is an ancestor of the other
safety [main_safety]
  ∀ (n1 n2 : node) (v1 v2 : view) (i1 i2 : interaction),
    (¬ is_byz n1 ∧ ¬ is_byz n2 ∧ decided n1 v1 i1 ∧ decided n2 v2 i2) → (ancestor i1 i2 ∨ ancestor i2 i1)

invariant [node_has_cur_view]
  ∀ (N : node), ∃ (v : view), cur_view N v

invariant [unique_cur_view]
  cur_view N U ∧ cur_view N V → U = V

invariant [ancestor_reflexive]
  ∀ (i : interaction), ancestor i i

invariant [operator_from_ixn_context]
  ∀ (ixn : interaction) (op : node) (v : view),
    ¬ is_byz op → (operator v ixn op → ∃ (c1 c2 : nodeset), ixn_contexts ixn c1 c2 ∧ ctx.member op c1)

invariant [unique_operator_for_ixn]
  ∀ (v : view) (ixn : interaction) (n1 n2 : node),
    ¬ (is_byz n1 ∨ is_byz n2) → (operator v ixn n1 ∧ operator v ixn n2 → n1 = n2)

invariant [prepare_only_by_operator]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (prepared_operator n v ixn → operator v ixn n)

invariant [unique_prepare]
  ∀ (v : view) (i1 i2 : interaction) (n : node),
    (¬ is_byz n ∧ prepared_operator n v i1 ∧ prepared_operator n v i2) → i1 = i2

invariant [prepare_response_only_on_prepare]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (prepared_node n v ixn → ∃ (op : node), operator v ixn op ∧ prepared_operator op v ixn)

invariant [prepare_response_only_by_context_nodes]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (prepared_node n v ixn → ∃ (c1 c2 : nodeset), ixn_contexts ixn c1 c2 ∧ (ctx.member n c1 ∨ ctx.member n c2))

invariant [proposal_only_by_operator]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (proposed n v ixn → ∃ (ixn_prepare : interaction), prepare_propose_ixns v ixn = ixn_prepare ∧ operator v ixn_prepare n)

invariant [unique_proposal_each_view]
  ∀ (v : view) (i1 i2 : interaction) (n1 n2 : node),
    ¬ (is_byz n1 ∨ is_byz n2) → ( (proposed n1 v i1 ∧ proposed n2 v i2) → (i1 = i2 ∧ n1 = n2) )

invariant [proposal_only_if_quorum_prepare]
  ∀ (v : view) (ixn_propose : interaction) (n : node),
    ¬ is_byz n → (proposed n v ixn_propose → (∃ (ixn_prepare : interaction) (c1 c2 s1 s2 : nodeset),
    prepare_propose_ixns v ixn_propose = ixn_prepare ∧ ixn_contexts ixn_prepare c1 c2 ∧
    ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧ ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → prepared_node nc v ixn_prepare))

invariant [prevote_nodes_only_by_context_nodes]
∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (prevoted_node n v ixn → ∃ (c1 c2 : nodeset), ixn_contexts ixn c1 c2 ∧ (ctx.member n c1 ∨ ctx.member n c2))

invariant [unique_prevote_nodes]
  ∀ (v : view) (i1 i2 : interaction) (n : node),
    ¬ is_byz n → ((prevoted_node n v i1 ∧ prevoted_node n v i2) → i1 = i2)

invariant [prevote_operator_only_if_quorum_prevote]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (prevoted_operator n v ixn → (∃ (c1 c2 s1 s2 : nodeset), ixn_contexts ixn c1 c2 ∧
    ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧ ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → prevoted_node nc v ixn))

invariant [prevote_only_by_operator]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (prevoted_operator n v ixn → ∃ (ixnp : interaction), prepare_propose_ixns v ixn = ixnp ∧ operator v ixnp n)

invariant [prevote_by_single_operator]
  ∀ (v : view) (ixn : interaction) (n1 n2 : node),
    ¬ (is_byz n1 ∨ is_byz n2) → ((prevoted_operator n1 v ixn ∧ prevoted_operator n2 v ixn) → (n1 = n2))

invariant [unique_prevote_operator]
  ∀ (v : view) (i1 i2 : interaction) (n : node),
    ¬ is_byz n → ((prevoted_operator n v i1 ∧ prevoted_operator n v i2) → (i1 = i2))

invariant [precommit_nodes_only_if_operator_prevote]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (precommitted_node n v ixn → ∃ (op : node) (ixnp : interaction), prepare_propose_ixns v ixn = ixnp ∧
    operator v ixnp op ∧ prevoted_operator op v ixn)

invariant [precommit_nodes_only_by_context_nodes]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (precommitted_node n v ixn → ∃ (c1 c2 : nodeset), ixn_contexts ixn c1 c2 ∧ (ctx.member n c1 ∨ ctx.member n c2))

invariant [precommit_nodes_only_if_prevoted_for_same_ixn]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (precommitted_node n v ixn → prevoted_node n v ixn)

invariant [unique_precommit_nodes]
  ∀ (v : view) (i1 i2 : interaction) (n : node),
    ¬ is_byz n → ((precommitted_node n v i1 ∧ precommitted_node n v i2) → i1 = i2)

invariant [precommit_operator_only_if_quorum_precommit]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (precommitted_operator n v ixn → (∃ (c1 c2 s1 s2 : nodeset), ixn_contexts ixn c1 c2 ∧
    ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧ ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → precommitted_node nc v ixn))

invariant [precommit_only_by_operator]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (precommitted_operator n v ixn → ∃ (ixnp : interaction), prepare_propose_ixns v ixn = ixnp ∧ operator v ixnp n)

invariant [precommit_by_single_operator]
  ∀ (v : view) (ixn : interaction) (n1 n2 : node),
    ¬ (is_byz n1 ∨ is_byz n2) → ((precommitted_operator n1 v ixn ∧ precommitted_operator n2 v ixn) → (n1 = n2))

invariant [unique_precommit_operator]
  ∀ (v : view) (i1 i2 : interaction) (n : node),
    ¬ is_byz n → ((precommitted_operator n v i1 ∧ precommitted_operator n v i2) → (i1 = i2))

invariant [decide_only_if_precommit_operator]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (decided n v ixn →(∃ (op : node) (ixnp : interaction),
    prepare_propose_ixns v ixn = ixnp ∧ operator v ixnp op ∧ precommitted_operator op v ixn))

-- invariant [precommitted_only_if_proposed]

-- invariant [parent_implies_ancestor]

-- invariant [not_proposed_implies_not_child_of_any_ixn]

-- invariant [unique_parent]

-- invariant [lock_held_only_if_qc_received]

invariant [proposal_extends_parent]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (proposed n v ixn → (∃ (il : interaction) (vl : view) (nl : node), parent il ixn ∧ (locked nl il true vl ∨ locked nl il false vl)))

invariant [ancestor_def]
  ancestor I J ↔ (I = J ∨ parent I J ∨ ∃ (k : interaction), parent I k ∧ ancestor k J)

-- invariant [precommit_operator_only_if_parent_locked]



/-
# Old invariants
invariant [unique_lock_held_by_each_node] `No need now because locked is a function`
  ∀ (v : view) (i1 i2 : interaction) (n : node) (s1 s2 : Bool),
    (locked n v i1 s1 ∧ locked n v i2 s2) →  (i1 = i2 ∧ s1 = s2)

`not needed because we assume that all ixns have same two participants p1 p2`
invariant [no_two_prevotes_for_same_participant]
  ∀ (v : view) (n : node) (i1 i2 : interaction) (p1 p2 p3 p4 : participant),
    ¬ is_byz n → (( interactions i1 p1 p2 ∧ interactions i2 p3 p4 ∧ prevoted_node n v i1 ∧
    prevoted_node n v i2 ) → (p1 ≠ p3 ∧ p2 ≠ p4 ∧ p1 ≠ p4 ∧ p2 ≠ p3))
-/

#gen_spec

set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true
/- The `transition` VC style gives more readable counter-examples, since
those show both the pre-state and post-state. -/
set_option veil.vc_gen "transition"
set_option veil.showVerificationTime true

#time #check_invariants

end IFP
