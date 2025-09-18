import veil


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
relation prepare_timed_out: node → view → Prop
relation prepare_responded: node → view → interaction → Prop

#gen_state

-- Assume that only two participants can interact with each other.
assumption ∀ (ixn : interaction) (p1 p2 p3: participant),
  ((interactions ixn p1 p2 ∧ interactions ixn p1 p3) → p2 = p3)
  ∧ ((interactions ixn p2 p1 ∧ interactions ixn p3 p1) → p2 = p3)

after_init {
  operator V I N := False;
  cur_view N V := False;
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
}
