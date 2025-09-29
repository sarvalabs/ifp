import Veil


class IFPTheory.Background
  (node : Type)
  (participant : Type)
  (interaction : Type)
  (context : Type) where
  -- in_context: node → interaction → (participant → node → Prop) → (interaction → participant → participant → Prop) → Prop
  -- ixn_contexts : interaction → (participant → context → Prop) → (participant → context → Prop)
  -- → (interaction → participant → participant → Prop) → Prop

  def lock_le (ixn1 : interaction) (s1 : Bool)  (ixn2 : interaction) (s2 : Bool) (height : interaction → Nat) : Prop :=
  -- (v1 : View) (v2 : View) (view_le : View → View → Prop)
  if height ixn1 < height ixn2 then
    True
  else if height ixn1 = height ixn2 ∧ s1 = true ∧ s2 = false then
    True
  -- else if height ixn1 = height ixn2 ∧ s1 = s2 ∧ view_le v1 v2 then
  --   True
  else
    False


-- We prove safety of IFP for a single epoch
veil module IFP

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
immutable relation ixn_contexts : interaction → context → context → Prop

instantiate bg: IFPTheory.Background node participant interaction context
open IFPTheory.Background

open IFPTheory

relation operator: view → interaction → node → Prop

relation cur_view: node → view → Prop

-- for all nodes
relation prepare_timed_out: node → view → Prop
-- An alternative: relation in_prepare_stage : node → view → Prop
relation sent_lock_in_prepare : node → view → interaction → interaction → Bool → Prop
relation decided : node → view → interaction → Prop
-- relation lock : interaction → Bool → Prop
-- function locked : node → view → participant → lock
relation locked : node → view → interaction → Bool → Prop
-- Bool true = Prevote stage, false = Precommit stage

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
function height : interaction → Nat
-- relation height : interaction → Nat → Nat → Prop
-- function height_p1 : interaction → Nat
-- function height_p2 : interaction → Nat
-- relation lock_leq : interaction → Bool → interaction → Bool → Prop - Defined in IFPTheory
relation parent : interaction → interaction → Prop -- parent → child → Prop
relation ancestor : interaction → interaction → Prop -- ancestor → descendant → Prop
immutable relation interacting_participants : interaction → participant → participant → Prop

individual genesis : interaction

#gen_state

-- Assume that the relations participant_context and ixn_contexts are related as below
assumption ∀ (ixn: interaction) (p1 p2 : participant) (c1 c2 : context),
  (ixn_contexts ixn c1 c2 ∧ interactions ixn p1 p2) → (participant_context p1 c1 ∧ participant_context p2 c2)

-- Assume that the two participants in an interaction are distinct.
assumption ∀ (ixn : interaction) (p1 p2 : participant),
  interactions ixn p1 p2 → p1 ≠ p2

-- Assume that only two given distinct participants can interact with each other.
assumption ∀ (ixn : interaction) (p1 p2 p3: participant),
  ((interactions ixn p1 p2 ∧ interactions ixn p1 p3) → p2 = p3)
  ∧ ((interactions ixn p2 p1 ∧ interactions ixn p3 p1) → p2 = p3)
  ∧ (interactions ixn p1 p2 → p1 ≠ p2)

-- Assume that each participant has only one context.
assumption ∀ (p : participant) (c1 c2 : context),
  participant_context p c1 ∧ participant_context p c2 → c1 = c2

after_init {
  parent I J := if I = genesis ∧ J = genesis then True else False;
  ancestor I J := if I = genesis ∧ J = genesis then True else False;
  locked N V I S := if I = genesis ∧ S = true ∧ V = tot_view.zero then True else False;
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
action propose (n : node) (v : view) (ixn ixn_propose : interaction) = {
  require cur_view n v
  require operator v ixn n
  require ∃ (c1 c2 : context), ixn_contexts ixn c1 c2 ∧ ctx.supermajority c1 ∧ ctx.supermajority c2 ∧
    ∀ (n1 : node), (ctx.member n1 c1 ∨ ctx.member n1 c2) → prepared_node n1 v ixn
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
  require ∃ (c1 c2 : context), ixn_contexts ixn c1 c2 ∧
    ( ∃ (n_max : node), (ctx.member n_max c1 ∨ ctx.member n_max c2) ∧
      sent_lock_in_prepare n_max v ixn ixn_max s_max ∧
      ∀ (n_l : node) (ixn_l : interaction) (s_l : Bool),
        ((ctx.member n_l c1  ∨ ctx.member n_l c2) ∧ sent_lock_in_prepare n_l v ixn ixn_l s_l) →
          lock_le ixn_l s_l ixn_max s_max height )
  proposed n v ixn_propose := True
  parent ixn_max ixn_propose := True
  -- ∀ (ixn_anc : interaction), ancestor ixn_anc ixn_max → ancestor ixn_anc ixn_propose
  let ixn_anc : interaction ← fresh
  ancestor ixn_anc ixn_propose := if ancestor ixn_anc ixn_max then True else False
}

-- The nodes respond with a prevote
action respond_propose (n : node) (v : view) (ixn ixn_prev : interaction) = {
  require cur_view n v
  require ∃ (op : node), proposed op v ixn ∧ operator v ixn op
  require ∀ (i : interaction) (p1 p2 p3 p4 : participant),
    interactions ixn p1 p2 ∧ interactions i p3 p4 ∧ (p1 = p3 ∨ p2 = p4 ∨ p1 = p4 ∨ p2 = p3)
    → ¬ prevoted_node n v i
  -- Not voted for any other ixn with common participants during view
  require parent ixn_prev ixn
  prevoted_node n v ixn := True
}

-- The operator responds to a quorum of prevotes with a prevote
action prevote (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require operator v ixn n
  require ∃ (c1 c2 : context), ixn_contexts ixn c1 c2 ∧ ctx.supermajority c1 ∧ ctx.supermajority c2 ∧
    ∀ (n1 : node), (ctx.member n1 c1 ∨ ctx.member n1 c2) → prevoted_node n1 v ixn
  prevoted_operator n v ixn := True
  -- locked n v ixn true := True
  let v1 : view ← fresh
  let i : interaction ← fresh
  let s : Bool ← fresh
  locked n v1 i s := if (v1 = v ∧ i = ixn ∧ s = true) then True else False
  /-∀ (v1 : view) (i : interaction) (s : Bool), ¬ (v1 = v ∧ i = ixn ∧ s = true)
    → locked n v1 i s := False-/
  -- Set all other/previous locks to False
}

-- The nodes respond to the prevote with a precommit
action respond_prevote (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require ∃ (op : node), prevoted_operator op v ixn ∧ operator v ixn op
  -- locked n v ixn true := True
  let v1 : view ← fresh
  let i : interaction ← fresh
  let s : Bool ← fresh
  locked n v1 i s := if (v1 = v ∧ i = ixn ∧ s = true) then True else False
  precommitted_node n v ixn := True
}

-- The operator responds to a quorum of precommits by a precommit and decides on the ixn
action precommit (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require operator v ixn n
  require ∃ (c1 c2 : context) , ixn_contexts ixn c1 c2 ∧ ctx.supermajority c1 ∧ ctx.supermajority c2 ∧
    ∀ (n1 : node), (ctx.member n1 c1 ∨ ctx.member n1 c2) → precommitted_node n1 v ixn
  precommitted_operator n v ixn := True
  -- locked n v ixn false := True
  let v1 : view ← fresh
  let i : interaction ← fresh
  let s : Bool ← fresh
  locked n v1 i s := if (v1 = v ∧ i = ixn ∧ s = false) then True else False
  decided n v ixn := True
  broadcasted_decision n v ixn := True
}

-- The nodes decide on the ixn on receiving a precommit from the operator
action respond_precommit (n : node) (v : view) (ixn : interaction) = {
  require cur_view n v
  require ∃ (op : node), operator v ixn op ∧ precommitted_operator op v ixn
  -- locked n v ixn false := True
  let v1 : view ← fresh
  let i : interaction ← fresh
  let s : Bool ← fresh
  locked n v1 i s := if (v1 = v ∧ i = ixn ∧ s = false) then True else False;
  decided n v ixn := True
}

-- Nodes decide on an interaction on receiving it from the operator
action respond_decision (n : node) (v : view) (ixn : interaction) = {
  require ∃ (op : node), operator v ixn op ∧ broadcasted_decision op v ixn
  decided n v ixn := True
}
/-
-- Byzantine nodes can send whatever they want but cannot forge identities
action byz_send_1 (n : node) (v : view) (ixn ixnl : interaction) (sl : Bool)  = {
  require is_byz n
  sent_lock_in_prepare n v ixn ixnl sl := True
}

action byz_send_2 (n : node) (v : view) (ixn : interaction) = {
  require is_byz n
  prepared_operator n v ixn := True
}

action byz_send_3 (n : node) (v : view) (ixn : interaction) = {
  require is_byz n
  proposed n v ixn := True
}

action byz_send_4 (n : node) (v : view) (ixn : interaction) = {
  require is_byz n
  prevoted_operator n v ixn := True
}

action byz_send_5 (n : node) (v : view) (ixn : interaction) = {
  require is_byz n
  precommitted_operator n v ixn := True
}

action byz_send_6 (n : node) (v : view) (ixn : interaction) = {
  require is_byz n
  broadcasted_decision n v ixn := True
}

action byz_send_7 (n : node) (v : view) (ixn : interaction) = {
  require is_byz n
  prepared_node n v ixn := True
}

action byz_send_8 (n : node) (v : view) (ixn : interaction) = {
  require is_byz n
  prevoted_node n v ixn := True
}

action byz_send_9 (n : node) (v : view) (ixn : interaction) = {
  require is_byz n
  precommitted_node n v ixn := True
}
-/

/-
From Tendermint Ivy Proof:
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

internal transition byz_actions = fun st st' =>
  ( ∀ (n : node) (v : view) (ixn ixnl : interaction) (sl : Bool),
    is_byz n ∧ (st.sent_lock_in_prepare n v ixn ixnl sl → st'.sent_lock_in_prepare n v ixn ixnl sl) ) ∧
  ( ∀ (n : node) (v : view) (ixn : interaction),
    is_byz n ∧ (st.decided n v ixn → st'.decided n v ixn) ) ∧
  ( ∀ (n : node) (v : view) (ixn : interaction) (s : Bool),
    is_byz n ∧ (st.locked n v ixn s → st'.locked n v ixn s) ) ∧
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


invariant [operator_from_ixn_context]
  ∀ (ixn : interaction) (op : node) (v : view),
    ¬ is_byz op → (operator v ixn op → ∃ (c1 c2 : context), ixn_contexts ixn c1 c2 ∧ ctx.member op c1)

invariant [unique_operator_for_ixn]
  ∀ (v : view) (ixn : interaction) (n1 n2 : node),
    ¬ (is_byz n1 ∨ is_byz n2) → (operator v ixn n1 ∧ operator v ixn n2 → n1 = n2)

invariant [prepare_only_by_operator]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (prepared_operator n v ixn → operator v ixn n)

invariant [unique_prepare]
  ∀ (v : view) (i1 i2 : interaction) (n : node),
    (¬ is_byz n ∧ prepared_operator n v i1 ∧ prepared_operator n v i2) → i1 = i2

invariant [prepare_response_only_on_valid_prepare]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (prepared_node n v ixn → ∃ (op : node), operator v ixn op ∧ prepared_operator op v ixn)

invariant [prepare_response_only_by_context_nodes]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (prepared_node n v ixn → ∃ (c1 c2 : context), ixn_contexts ixn c1 c2 ∧ (ctx.member n c1 ∨ ctx.member n c2))

invariant [quorum_prepared_only_if_operator_prepare]
  ∀ (ixn: interaction) (v : view) (c1 c2 : context),
    (ixn contexts c1 c2 ∧ ctx.supermajority c1 ∧ ctx.supermajority c2 ∧
      ∀ (n : node), (ctx.member n c1 ∨ ctx.member n c2) → prepared_node n v ixn) →
      ( ∃ (op : node), operator v ixn op ∧ prepared_operator op v ixn )

invariant [proposal_only_by_operator]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (prepared_operator n v ixn → operator v ixn n)

invariant [unique_proposal]
  ∀ (v : view) (i1 i2 : interaction) (n : node),
    (¬ is_byz n ∧ proposed n v i1 ∧ proposed n v i2) → i1 = i2


/-
 safety [main_safety]
  ∀ (v1 v2 : view) (i1 i2 : interaction) (n : node),
    ¬ is_byz n → ((decided n v1 i1 ∧ decided n v2 i2) → (ancestor i1 i2 ∨ ancestor i2 i1))
-/
/-
`old invariant - not needed because we assume that all ixns have same two participants p1 p2`
invariant [no_two_prevotes_for_same_participant]
  ∀ (v : view) (n : node) (i1 i2 : interaction) (p1 p2 p3 p4 : participant),
    ¬ is_byz n → (( interactions i1 p1 p2 ∧ interactions i2 p3 p4 ∧ prevoted_node n v i1 ∧
    prevoted_node n v i2 ) → (p1 ≠ p3 ∧ p2 ≠ p4 ∧ p1 ≠ p4 ∧ p2 ≠ p3))
-/
/-
invariant [proposal_only_if_quorum_prepare]

invariant [prevote_only_if_proposed]

invariant [prevote_response_only_by_context_nodes]

invariant [unique_prevote_nodes]

invariant [quorum_prevoted_only_if_proposed] `Maybe not needed`

invariant [prevote_operator_only_if_quorum_prevote]

invariant [unique_prevote_operator]

invariant [precommit_only_if_prevote_operator]

invariant [precommit_response_only_by_context_nodes]

invariant [unique_precommit_nodes]

invariant [quorum_precommitted_only_if_prevoted_operator] `Maybe not needed`

invariant [precommit_operator_only_if_quorum_precommit]

invariant [unique_precommit_operator]

invariant [decide_only_if_precommit_operator]

invariant [unique_decision_in_view]

invariant [unique_decision_Main_Safety]

`Old invariants below`
invariant [no_conflicting_prevotes]
  ∀ (v : view) (n : node) (i1 i2 : interaction),
    ¬ is_byz n → ((prevoted_node n v i1 ∧ prevoted_node n v i2) → i1 = i2)

invariant [no_conflicting_precommits]
  ∀ (v : view) (n : node) (i1 i2 : interaction),
    ¬ is_byz n → ((precommitted_node n v i1 ∧ precommitted_node n v i2) → i1 = i2)
-/

#gen_spec

set_option veil.printCounterexamples true
-- set_option veil.smt.model.minimize true
/- The `transition` VC style gives more readable counter-examples, since
those show both the pre-state and post-state. -/
-- set_option veil.vc_gen "transition"

#time #check_invariants

end IFP
