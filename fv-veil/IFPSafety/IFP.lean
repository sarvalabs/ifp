import Veil


class IFPTheory.Background
  (node : Type)
  (participant : Type)
  (interaction : Type)
  (context : Type) where
  in_context: node → interaction → (participant → node → Prop) → (interaction → participant → participant → Prop) → Prop
  -- ixn_contexts : interaction → (participant → context → Prop) → (participant → context → Prop)
  -- → (interaction → participant → participant → Prop) → Prop

-- We prove safety of IFP for a single epoch

type view
instantiate tot_view : TotalOrderWithMinimum view

type participant
type node
type interaction
type context

variable (is_byz : node → Prop) -- immutable relation?

instantiate ctx : NodeSet node is_byz context

immutable relation participant_context: participant → context → Prop
-- Interactions between participants are also fixed
immutable relation interactions : interaction → participant → participant → Prop
relation ixn_contexts : interaction → context → context → Prop

instantiate bg: IFPTheory.Background node participant interaction context
open IFPTheory.Background

relation operator: view → interaction → node → Prop

relation cur_view: node → view → Prop

-- for all nodes
relation prepare_timed_out: node → view → Prop
-- An alternative: relation in_prepare_stage : node → view → Prop
relation sent_lock_in_prepare : node → view → interaction → interaction → Bool → Prop
relation decided : node → view → interaction → Prop
relation locked : node → view → interaction → Bool → Prop
-- Bool 1 = Prevote stage, 0 = Precommit stage

-- for operators
relation prepared_operator : node → view → interaction → Prop
relation proposed : node → view → interaction → Prop
relation prevoted_operator : node → view → interaction → Prop
relation precommitted_operator : node → view → interaction → Prop
relation broadcasted_decision : node → view → interaction → Prop

-- for non-operator nodes
relation prepared_node : node → view → interaction → Prop
relation prevoted_node : node → view → interaction → Prop
relation precommitted_node : node → view → interaction → Prop

-- for interaction comparisons
-- function height : interaction → Int → Int -- Assumes only one height param for an ixn
relation height : interaction → Nat → Nat → Prop
relation parent : interaction → interaction → Prop
relation ancestor : interaction → interaction → Prop
immutable relation interacting_participants : interaction → participant → participant → Prop

#gen_state

-- Assume that the two participants in an interaction are distinct.
assumption ∀ (ixn : interaction) (p1 p2 : participant),
  interactions ixn p1 p2 → p1 ≠ p2

-- Assume that only two participants can interact with each other.
assumption ∀ (ixn : interaction) (p1 p2 p3: participant),
  ((interactions ixn p1 p2 ∧ interactions ixn p1 p3) → p2 = p3)
  ∧ ((interactions ixn p2 p1 ∧ interactions ixn p3 p1) → p2 = p3)

-- Assume that each participant has only one context.
assumption ∀ (p : participant) (c1 c2 : context),
  participant_context p c1 ∧ participant_context p c2 → c1 = c2


after_init {
  operator V I N := False;
  cur_view N V := if V = tot_view.zero then True else False;
  ancestor B C := B = C;
  decided N V B := False;
  locked N V B S := False;
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

action pick_operator (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require ∃ (c1 c2 : context), ixn_contexts ixn c1 c2 ∧ ctx.member n c1
  -- Operator is picked from first participant's context by default
  require ∀ (n1 : node), ¬ operator v ixn n1
  -- Operator is not chosen yet for ixn and v
  operator v ixn n := True
}

action set_view (v_cur v_new: view) = {
  -- require ¬ (∃ (n : node), cur_view n v) -- Why not, `¬ (∀ n, cur_view n v)`
  require ∃ (n : node), cur_view n v_cur -- Why not, `∀ (n:node), cur_view n v_cur`
  -- require ∀ (n :  node), ¬ cur_view n v_new -- Maybe this condition not necessary
  require tot_view.next v_cur v_new
  cur_view N v_new := True
  cur_view N v_cur := False
}

-- The operator sends a prepare message
action prepare (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require operator v ixn n
  require ∀ (i : interaction), ∃ (p1 p2 p3 p4 : participant),
    interactions i p1 p2 ∧ interactions ixn p3 p4 ∧ (p1 = p3 ∨ p2 = p4) → ¬ prepared_operator n v i
  -- Not sent prepare msg for any other ixn with any of the same participants during the view
  prepared_operator n v ixn := True
}

-- The nodes respond with a prepare message
action respond_prepare (n : node) (v : view) (ixn : interaction) = {
  -- require ¬ prepare_timed_out n v
  -- TODO: incorporate prepare timeout and ordering and responding to one
  require cur_view n v
  require ∃ (op : node), operator v ixn op ∧ prepared_operator op v ixn
  require  ∃ (c1 c2 : context), ixn_contexts ixn c1 c2 ∧ (ctx.member n c1 ∨ ctx.member n c2)
  -- n is in the interaction's contexts
  -- if ∃ (vl : view) (ixnl : interaction) (sl : Bool), locked n vl sl ixnl then
    -- sent_lock_in_prepare n v sl ixnl := True
  prepared_node n v ixn := True
}

-- The nodes send their lock in the prepare message
action send_lock_in_prepare (n : node) (v : view) (ixn : interaction)
(vl : view) (ixnl : interaction) (sl : Bool) = {
  require cur_view n v
  require prepared_node n v ixn
  require ∃ (p1 p2 p3 p4 : participant),  interactions ixn p1 p2 ∧ interactions ixnl p3 p4 ∧
    (p1 = p3 ∨ p2 = p4) ∧ locked n vl ixnl sl
  -- ixnl sl is lock for a participant in ixn's participants
  require ∀ (i : interaction) (s : Bool), ¬ sent_lock_in_prepare n v ixn i s
  -- Not sent any other lock in prepare
  sent_lock_in_prepare n v ixn ixnl sl := True
}
-- TODO: A lock for each interacting participant has to be sent. Here, only one lock can be sent.


-- The operator makes a proposal
action propose (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require ∃ (c1 c2 : context) , ixn_contexts ixn c1 c2 ∧ ctx.supermajority c1 ∧ ctx.supermajority c2 ∧
    ∀ (n1 : node), (ctx.member n1 c1 ∨ ctx.member n1 c2) → prepared_node n1 v ixn
  -- TODO: RemoveOutdated procedure
}

-- The nodes respond with a prevote
action respond_propose (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require ∃ (op : node), proposed op v ixn ∧ operator v ixn op
  require ∀ (i : interaction) (p1 p2 p3 p4 : participant),
    interactions ixn p1 p2 ∧ interactions i p3 p4 ∧ (p1 = p3 ∨ p2 = p4 ∨ p1 = p4 ∨ p2 = p3)
    → ¬ prevoted_node n v i
  -- Not voted for any other ixn with common participants during view
  prevoted_node n v ixn := True
}

-- The operator responds to a quorum of prevotes with a prevote
action prevote (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require ∃ (c1 c2 : context), ixn_contexts ixn c1 c2 ∧ ctx.supermajority c1 ∧ ctx.supermajority c2 ∧
    ∀ (n1 : node), (ctx.member n1 c1 ∨ ctx.member n1 c2) → prevoted_node n1 v ixn
  prevoted_operator n v ixn := True
  locked n v ixn true := True
}

-- The nodes respond to the prevote with a precommit
action respond_prevote (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require ∃ (op : node), prevoted_operator op v ixn ∧ operator v ixn op
  locked n v ixn true := True
  precommitted_node n v ixn := True
}

-- The operator responds to a quorum of precommits by a precommit and decides on the ixn
action precommit (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require ∃ (c1 c2 : context) , ixn_contexts ixn c1 c2 ∧ ctx.supermajority c1 ∧ ctx.supermajority c2 ∧
    ∀ (n1 : node), (ctx.member n1 c1 ∨ ctx.member n1 c2) → precommitted_node n1 v ixn
  precommitted_operator n v ixn := True
  locked n v ixn false := True
  decided n v ixn := True
  broadcasted_decision n v ixn := True
}

-- The nodes decide on the ixn on receiving a precommit from the operator
action respond_precommit (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require ∃ (op : node), operator v ixn op ∧ precommitted_operator op v ixn
  locked n v ixn false := True
  decided n v ixn := True
}

-- Nodes decide on an interaction on receiving it from the operator
action respond_decision (n : node) (v : view) (ixn : interaction) = {
  require ∃ (op : node), operator v ixn op ∧ broadcasted_decision op v ixn
  decided n v ixn := True
}

invariant [operator_from_ixn_context]
  ∀ (ixn : interaction) (op : node) (v : view),
    operator v ixn op → ∃ (c1 c2 : context), ixn_contexts ixn c1 c2 ∧ ctx.member op c1

invariant [unique_operator_for_ixn]
  ∀ (v : view) (ixn : interaction) (n1 n2 : node),
    operator v ixn n1 ∧ operator v ixn n2 → n1 = n2

invariant [prepare_sent_only_by_ixn_operator]
  ∀ (v : view) (ixn : interaction) (n : node),
    prepared_operator n v ixn → operator v ixn n

invariant [prepare_response_only_on_valid_prepare]
  ∀ (v : view) (ixn : interaction) (n : node),
    prepared_node n v ixn → ∃ (op : node), operator v ixn op ∧ prepared_operator op v ixn

invariant [prepare_response_only_by_context_nodes]
  ∀ (v : view) (ixn : interaction) (n : node),
    prepared_node n v ixn → ∃ (c1 c2 : context), ixn_contexts ixn c1 c2 ∧ (ctx.member n c1 ∨ ctx.member n c2)


/-
invariant [no_two_prevotes_for_same_participant]
  ∀ (v : view) (n : node) (i1 i2 : interaction) (p1 p2 p3 p4 : participant),
    ( interactions i1 p1 p2 ∧ interactions i2 p3 p4 ∧ prevoted_node n v i1 ∧
    prevoted_node n v i2 ) → (p1 ≠ p3 ∧ p2 ≠ p4 ∧ p1 ≠ p4 ∧ p2 ≠ p3)
-/
/-
invariant [quorum_prepared_only_if_operator_prepare]
  ∀ (ixn: interaction) (v : view) (c1 c2 : context),
    (ixn contexts c1 c2 ∧ ctx.supermajority c1 ∧ ctx.supermajority c2 ∧
      ∀ (n : node), (ctx.member n c1 ∨ ctx.member n c2) → prepared_node n v ixn) →
      ( ∃ (op : node), operator v ixn op ∧ prepared_operator op v ixn )

invariant [no_conflicting_prevotes_by_nodes]
  ∀ (v : view) (p1 : participant)
-/

#gen_spec


set_option veil.printCounterexamples true
#time #check_invariants
