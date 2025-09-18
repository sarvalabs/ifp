import Veil


class IFPTheory.Background
  (node : Type)
  (participant : Type)
  (interaction : Type) where
  in_context: node → interaction → (participant → node → Prop) → (interaction → participant → participant → Prop) → Prop

-- We prove safety of IFP for a single epoch

type view
instantiate tot : TotalOrderWithMinimum view

type participant
type node
type interaction


-- Context is a relation for a given node, participant
immutable relation context: participant → node → Prop
-- Interactions between participants are also fixed
immutable relation interactions: interaction → participant → participant → Prop

instantiate bg: IFPTheory.Background node participant interaction
open IFPTheory.Background

relation operator: view → interaction → node → Prop
relation is_byz : node → Prop

relation cur_view: node → view → Prop
relation prepared: node → view → interaction → Prop
relation prepare_responded: node → view → interaction → Prop


-- for all nodes
relation prepare_timed_out: node → view → Prop
-- An alternative: relation in_prepare_stage : node → view → Prop
relation sent_lock_in_prepare : node → view → interaction → Prop
relation decided : node → view → interaction → Prop
relation locked : node → view → interaction → Prop

-- for operators
relation sent_prepare_operator : node → view → interaction → Prop
relation proposed : node → view → interaction → Prop
relation prevoted_operator : node → view → interaction → Prop
relation precommitted_operator : node → view → interaction → Prop

-- for non-operator nodes
relation sent_prepare_node : node → view → interaction → Prop
relation prevoted_node : node → view → interaction → Prop
relation precommitted_node : node → view → interaction → Prop

-- for interaction comparisons
function height : interaction → Int → Int -- Assumes only one height param for an ixn
relation parent : interaction → interaction → Prop
relation ancestor : interaction → interaction → Prop
immutable relation interacting_participants : interaction → participant → participant → Prop

#gen_state

-- Assume that only two participants can interact with each other.
assumption ∀ (ixn : interaction) (p1 p2 p3: participant),
  ((interactions ixn p1 p2 ∧ interactions ixn p1 p3) → p2 = p3)
  ∧ ((interactions ixn p2 p1 ∧ interactions ixn p3 p1) → p2 = p3)

after_init {
  operator V I N := False;
  cur_view N V := False;
  height B := 0;
  ancestor B C := B = C;
  decided N V B := False;
  locked N V B := False;
  sent_prepare_operator N V B := False;
  proposed N V B := False;
  prevoted_operator N V B := False;
  precommitted_operator N V B := False;
  sent_prepare_node N V B := False;
  prevoted_node N V B := False;
  precommitted_node N V B := False;
}

action pick_operator (n : node) (ixn : interaction) (v : view) = {
  require cur_view n v
  require ∃ p1 p2, context p1 n ∧ interactions ixn p1 p2
  operator v ixn n := True
}

action set_view (v: view) = {
  require ¬ (∃ n, cur_view n v)
  cur_view N v := True
}

-- The operator sends a prepare message
action prepare (n : node) (ixn : interaction) (v : view) = {
  require operator v ixn n
  require cur_view n v
  require in_context n ixn context interactions
  prepared n v ixn := True
}

action respond_prepare (n: node) (ixn: interaction) (v: view) = {
  require ¬ operator v ixn n
  require ¬ prepare_timed_out n v
  -- Check that n is in the context of the interaction
  require in_context n ixn context interactions
  if ∃ (vl : view), locked n vl ixnl then
    sent_lock_in_prepare n v ixnl := True
  sent_prepare_node n v ixn := True
}
