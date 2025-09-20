import Veil


class IFPTheory.Background
  (node : Type)
  (participant : Type)
  (interaction : Type)
  (context : Type) where
  -- in_context: node → interaction → (participant → node → Prop) → (interaction → participant → participant → Prop) → Prop
  ixn_context : participant → interaction → (participant → context → Prop) → (interaction → participant → participant → Prop) → Prop
-- We prove safety of IFP for a single epoch

type view
instantiate tot : TotalOrderWithMinimum view

type participant
type node
type interaction
type context

variable (is_byz : node → Prop) -- immutable relation?

instantiate ctx : NodeSet node is_byz context

immutable relation participant_context: participant → context → Prop
-- Interactions between participants are also fixed
immutable relation interactions: interaction → participant → participant → Prop

instantiate bg: IFPTheory.Background node participant interaction
open IFPTheory.Background

relation operator: view → interaction → node → Prop

relation cur_view: node → view → Prop

-- for all nodes
relation prepare_timed_out: node → view → Prop
-- An alternative: relation in_prepare_stage : node → view → Prop
relation sent_lock_in_prepare : node → view → interaction → Bool → Prop
relation decided : node → view → interaction → Prop
relation locked : node → view → interaction → Bool → Prop
-- Bool 1 = Prevote stage, 0 = Precommit stage

-- for operators
relation prepared_operator : node → view → interaction → Prop
relation proposed : node → view → interaction → Prop
relation prevoted_operator : node → view → interaction → Prop
relation precommitted_operator : node → view → interaction → Prop

-- for non-operator nodes
relation prepared_node : node → view → interaction → Prop
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

-- Assume that each participant has only one context.
assumption ∀ (p : participant) (c1 c2 : context),
  participant_context p c1 ∧ participant_context p c2 → c1 = c2

after_init {
  operator V I N := False;
  cur_view N V := False;
  -- height B := 0;
  ancestor B C := B = C;
  decided N V B := False;
  locked N V B S := False;
  prepared_operator N V B := False;
  sent_lock_in_prepare N V B S := False;
  proposed N V B := False;
  prevoted_operator N V B := False;
  precommitted_operator N V B := False;
  prepared_node N V B := False;
  prevoted_node N V B := False;
  precommitted_node N V B := False;
}

action pick_operator (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require ∃ (p1 p2 : participant) (c1 : context), interactions ixn p1 p2 ∧
   participant_context p1 c1 ∧ ctx.member n c1
  -- Operator is picked from first participant's context by default
  require ∀ (n1 : node), ¬ operator v ixn n1 -- Operator is not chosen yet for ixn and v
  operator v ixn n := True
}

action set_view (v: view) = {
  require ¬ (∃ n, cur_view n v) -- Why not, `¬ (∀ n, cur_view n v)`
  cur_view N v := True
  -- update along total order
}

-- The operator sends a prepare message
action prepare (n : node) (v : view) (ixn : interaction) = {
  require operator v ixn n
  require cur_view n v
  require ∃ (p1 p2 : participant) (c1 c2 : context), interactions ixn p1 p2 ∧
   participant_context p1 c1 ∧ participant_context p2 c2 ∧ (ctx.member n c1 ∨ ctx.member n c2)
  require ∀ (i : interaction), ¬ prepared_operator n v i
  prepared_operator n v ixn := True
}

action respond_prepare (n : node) (v : view) (ixn : interaction) = {
  -- require ¬ prepare_timed_out n v
  -- TODO: incorporate prepare timeout and ordering and responding to one
  -- Check that n is in the context of the interaction

  require in_context n ixn context interactions
  -- if ∃ (vl : view) (ixnl : interaction) (sl : Bool), locked n vl sl ixnl then
  --  sent_lock_in_prepare n v sl ixnl := True
  -- sent_prepare_node n v ixn := True
}

action send_lock_in_prepare (n : node) (v : view) (ixn : interaction)
(vl : view) (ixnl : interaction) (sl : Bool) = {
  require in_context n ixn context interactions
  require prepared_node n v ixn
  require locked n vl ixnl sl
  sent_lock_in_prepare n v ixnl sl := True
}

action propose (n : node) (v : view) (ixn : interaction) = {
  require ∃ (p1 p2 : participant), interactions ixn p1 p2 →
   (∃ (c1 c2 : context), participant_context p1 c1 ∧ participant_context p2 c2 ∧
    ctx.supermajority c1 ∧ ctx.supermajority c2 ∧
   ∀ (n1 : node), (ctx.member n1 c1 ∨ ctx.member n1 c2) → prepared_node n1 v ixn)
}

action respond_propose (n : node) (v : view) (ixn : interaction) = {
  require ∃ (op : node), proposed op v ixn ∧ operator op ixn n
  require ∀ (i : interaction), ¬ prevoted_node n v i -- Not voted for any other ixn during view
  -- need to add checks on receiving propose
  prevoted_node n v ixn := True
}

action prevote (n : node) (v : view) (ixn : interaction) = {
  require ∃ (p1 p2 : participant), interactions ixn p1 p2 →
   (∃ (c1 c2 : context), participant_context p1 c1 ∧ participant_context p2 c2 ∧
    ctx.supermajority c1 ∧ ctx.supermajority c2 ∧
   ∀ (n1 : node), (ctx.member n1 c1 ∨ ctx.member n1 c2) → prevoted_node n1 v ixn)
  prevoted_operator n v ixn := True
  locked n v ixn 1 :=True
}

action respond_prevote (n : node) (v : view) (ixn : interaction) = {
  require ∃ (op : node), prevoted_operator op v ixn ∧ operator op ixn n
  locked n v ixn 1 := True
  precommitted_node n v ixn := True
}

action precommit (n : node) (v : view) (ixn : interaction) = {
  require ∃ (p1 p2 : participant), interactions ixn p1 p2 →
   (∃ (c1 c2 : context), participant_context p1 c1 ∧ participant_context p2 c2 ∧
    ctx.supermajority c1 ∧ ctx.supermajority c2 ∧
   ∀ (n1 : node), (ctx.member n1 c1 ∨ ctx.member n1 c2) → precommitted_node n1 v ixn)
  precommitted_operator n v ixn
  locked n v ixn 0 := True
  decided n v ixn := True
}

action respond_precommit (n : node) (v : view) (ixn : interaction) = {
  require ∃ (op : node), precommitted_operator op v ixn ∧ operator op ixn n
  prevoted_operator n v ixn
  locked n v ixn 0 := True
  decided n v ixn := True
}
