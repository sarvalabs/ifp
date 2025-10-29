import Veil

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
type nodeset
-- inductive stg where
--   | propose
--   | prevote
--   | precommit
--   deriving Repr, DecidableEq
type stg
individual propose : stg
individual prevote : stg
individual precommit : stg

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
relation sent_lock_in_prepare : node → view → participant → participant → interaction → Bool → Prop
relation decided : node → view → participant → participant → interaction → Prop
relation locked : node → view → participant → interaction → Bool → view → Prop
-- Bool true = Prevote stage, false = Precommit stage
relation stage : node → view → participant → participant → interaction → stg → Prop
-- 0 = Propose, 1 = Prevote, 2 = Precommit

-- `Maintain state variable for checking whether a node has voted for a ixn with a participant in a view`
-- relation voted_participant : node → participant → view → Prop


-- # For Operators
relation operator: node → view → participant → participant → Prop
relation prepared_operator : node → view → participant → participant → Prop
relation proposed : node → view → participant → participant → interaction → Prop
relation prevoted_operator : node → view → participant → participant → interaction → Prop
relation precommitted_operator : node → view → participant → participant → interaction → Prop
relation broadcasted_decision : node → view → participant → participant → interaction → Prop

-- # For Non-Operator Nodes
relation prepared_node : node → view → participant → participant → Prop
relation prevoted_node : node → view → participant → participant → interaction → Prop
relation precommitted_node : node → view → participant → participant → interaction → Prop

-- # For Interactions
function height : interaction → Nat -- function is better as we can use < for comparison
-- but function might be causing error resulting in no counterexamples
-- relation height : interaction → Nat → Nat → Prop
-- relation lock_leq : interaction → Bool → interaction → Bool → Prop - Defined in IFPTheory
relation parent : interaction → interaction → Prop -- parent → child → Prop
relation ancestor : interaction → interaction → Prop -- ancestor → descendant → Prop
individual genesis : interaction

#gen_state

ghost relation ixn_contexts (I : interaction) (C D : nodeset) :=
∃ (p q : participant), interactions I p q ∧ participant_context p C ∧ participant_context q D

-- ghost relation instance_ixn (V : view) (P Q : participant) (I : interaction) :=
--   ∃ (n : node), proposed n V P Q I

-- ghost relation locked_in_view (N : node) (U : view) (P : participant) (I : interaction) (S : Bool) (V : view) :=


-- # Assumptions

-- -- Assume that there are precisely two distinct participants
-- assumption
--   (∃ (p1 p2 : participant), p1 ≠ p2) ∧ -- there exist two distinct participants
--   (∀ (p1 p2 p3 : participant), p1 ≠ p2 → (p3 = p1 ∨ p3 = p2)) -- in any three participants, one is equal to the other two

-- Assume that only two given distinct participants are part of an interaction
assumption ∀ (ixn : interaction) (p1 p2 p3 p4: participant),
  ((interactions ixn p1 p2 ∧ interactions ixn p3 p4) → p1 = p3 ∧ p2 = p4 ∧ p1 ≠ p4)

-- Assume that there are exactly two such participants among which all ixns occur
assumption ∃ (p1 p2 : participant), p1 ≠ p2 ∧ ∀ (i: interaction),
  interactions i p1 p2

 -- # Revisit assumptions - can remove one of them perhaps.

-- Assume that each participant has only one context.
assumption (participant_context P C1 ∧ participant_context P C2) → C1 = C2


after_init {
  parent I J := (I = genesis ∧ J = genesis);
  ancestor I J := (I = J); -- I = genesis ∧ J = genesis
  locked N U P I S V := (I = genesis ∧ S = true ∧ U = tot_view.zero ∧ V = tot_view.zero);
  decided N V P Q I := (I = genesis ∧ V = tot_view.zero)
  height genesis := 0;
  stage N V P Q I S := (S = propose);
  operator N V P Q := False;
  cur_view N V := (V = tot_view.zero);
  prepared_operator N V P Q := False;
  sent_lock_in_prepare N V P Q L S := False;
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
  require cur_view op v
  require p1 ≠ p2
  require ∃ (c1 : nodeset), participant_context p1 c1 ∧ ctx.member op c1
  -- Operator is picked from first participant's context by default
  require ∀ (n : node), ¬ operator n v p1 p2  -- Operator is not chosen yet for ixn and v
  operator op v p1 p2 := True
}

-- The operator sends a prepare message
action prepare (op : node) (v : view) (p1 p2 : participant) = {
  require cur_view op v
  require operator op v p1 p2
  /-
  require ∀ (i : interaction), ∃ (p1 p2 p3 p4 : participant),
    interactions i p1 p2 ∧ interactions ixn p3 p4 ∧ (p1 = p3 ∨ p2 = p4) → ¬ prepared_operator n v i
  `Not sent prepare msg for any other ixn with any of the same participants during the view`
  -- Not needed for now because we assume only two participants. Simpler alternative below
  -/
  require ¬ prepared_operator op v p1 p2
  prepared_operator op v p1 p2 := True
}

-- The nodes respond with a prepare message
action respond_prepare (n : node) (v : view) (p1 p2 : participant) = {
  -- require ¬ prepare_timed_out n v
  -- TODO: incorporate prepare timeout and ordering and responding to one
  require cur_view n v
  require ∃ (op : node), operator op v p1 p2 ∧ prepared_operator op v p1 p2
  require ∃ (c1 c2 : nodeset), ctx.member n c1 ∨ ctx.member n c2 ∧ participant_context p1 c1 ∧ participant_context p2 c2
  -- n is in the interaction's contexts
  -- if ∃ (vl : view) (ixnl : interaction) (sl : Bool), locked n vl sl ixnl then
    -- sent_lock_in_prepare n v sl ixnl := True
  prepared_node n v p1 p2 := True
}

-- The nodes send their lock in the prepare message
action send_lock_in_prepare_p1 (n : node) (u1 v vl : view) (p1 p2 : participant) (ixnl : interaction) (sl : Bool) = {
  require cur_view n v
  require prepared_node n v p1 p2
  /-
  require ∃ (p1 p2 p3 p4 : participant),  interactions ixn p1 p2 ∧ interactions ixnl p3 p4 ∧
    (p1 = p3 ∨ p2 = p4) ∧ locked n vl ixnl sl
  `ixnl sl is lock for a participant in ixn's participants`
  We only have two fixed participants for now so each node has only one such lock.
  So we can use the below simplified requirement.
  -/
  require locked n u1 p1 ixnl sl vl
  require ∀ (u2 : view), tot_view.le u1 u2 → ¬ ∃ (ixnl2 : interaction) (sl2: Bool) (vl2 : view), locked n u2 p1 ixnl2 sl2 vl2
  require ∀ (i_lock : interaction) (s_lock : Bool), ¬ sent_lock_in_prepare n v p1 p2 i_lock s_lock
  -- Not sent any other lock in prepare
  sent_lock_in_prepare n v p1 p2 ixnl sl := True
}

action send_lock_in_prepare_p2 (n : node) (u1 v vl : view) (p1 p2 : participant) (ixnl : interaction) (sl : Bool) = {
  require cur_view n v
  require prepared_node n v p1 p2
  /-
  require ∃ (p1 p2 p3 p4 : participant),  interactions ixn p1 p2 ∧ interactions ixnl p3 p4 ∧
    (p1 = p3 ∨ p2 = p4) ∧ locked n vl ixnl sl
  `ixnl sl is lock for a participant in ixn's participants`
  We only have two fixed participants for now so each node has only one such lock.
  So we can use the below simplified requirement.
  -/
  require locked n u1 p2 ixnl sl vl
  require ∀ (u2 : view), tot_view.le u1 u2 → ¬ ∃ (ixnl2 : interaction) (sl2: Bool) (vl2 : view), locked n u2 p2 ixnl2 sl2 vl2
  require ∀ (i_lock : interaction) (s_lock : Bool), ¬ sent_lock_in_prepare n v p1 p2 i_lock s_lock
  -- Not sent any other lock in prepare
  sent_lock_in_prepare n v p1 p2 ixnl sl := True
}

-- The operator makes a proposal
action propose (op : node) (v : view) (p1 p2 : participant) (ixn_propose : interaction) = {
  require cur_view op v
  require operator op v p1 p2
  require stage op v p1 p2 ixn_propose propose -- in propose stage
  require ∀ (ix : interaction), ¬ proposed op v p1 p2 ix -- operator hasnt proposed any ixns yet
  require ∃ (c1 c2 s1 s2 : nodeset), participant_context p1 c1 ∧ participant_context p2 c2 ∧
    ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (n : node), (ctx.member n s1 ∨ ctx.member n s2) → prepared_node n v p1 p2 ∧
      ∃ (ul vl : view) (ixnl : interaction) (sl : Bool), sent_lock_in_prepare n v p1 p2 ixnl sl ∧
         (locked n ul p1 ixnl sl vl ∨ locked n ul p2 ixnl sl vl) ∧ tot_view.le ul v
        -- above line: checking validity of the lock sent
  let ixn_max : interaction ← fresh
  let s_max : Bool ← fresh
  require ∃ (n_max : node) (c1 c2 : nodeset), participant_context p1 c1 ∧ participant_context p2 c2 ∧
    (ctx.member n_max c1 ∨ ctx.member n_max c2) ∧
    sent_lock_in_prepare n_max v p1 p2 ixn_max s_max ∧ interactions ixn_max p1 p2 ∧
    ∀ (n_l : node) (ixn_l : interaction) (s_l : Bool),
      ((ctx.member n_l c1 ∨ ctx.member n_l c2) ∧ sent_lock_in_prepare n_l v p1 p2 ixn_l s_l) →
        (height ixn_l < height ixn_max ∨ (height ixn_l = height ixn_max ∧ s_l=true ∧ s_max=false))
          -- lock_le ixn_l s_l ixn_max s_max height )
  parent ixn_max ixn_propose := True
  ancestor A ixn_propose := ancestor A ixn_max ∨ A = ixn_max ∨ A = ixn_propose
  proposed op v p1 p2 ixn_propose := True
  height ixn_propose := height ixn_max + 1
  stage op v p1 p2 ixn_propose S := (S = prevote) -- move to prevote stage
}

-- The nodes respond with a prevote
action respond_propose (n : node) (v : view) (p1 p2 : participant) (ixn ixn_prev : interaction) (s_prev : Bool) = {
  require cur_view n v
  require stage n v p1 p2 ixn propose -- in propose stage
  require interactions ixn p1 p2
  require ∃ (op : node), operator op v p1 p2 ∧ proposed op v p1 p2 ixn
  require ∀ (i : interaction), ¬ prevoted_node n v p1 p2 i
  require ∃ (c1 c2 : nodeset), ctx.member n c1 ∨ ctx.member n c2 ∧ ixn_contexts ixn c1 c2
  require ∃ (c1 c2 s1 s2 : nodeset), ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    (∀ (n1 : node), (ctx.member n1 s1 ∨ ctx.member n1 s2) → prepared_node n1 v p1 p2)
  /-
  require ∀ (i : interaction) (p1 p2 p3 p4 : participant),
    interactions ixn p1 p2 ∧ interactions i p3 p4 ∧ (p1 = p3 ∨ p2 = p4 ∨ p1 = p4 ∨ p2 = p3)
    → ¬ prevoted_node n v i
  -- Not voted for any other ixn with common participants during view
  `Not needed for now because we assume only two participants. Simpler alternative below`
  -/
  require parent ixn_prev ixn
  -- the proposed ixn extends the max lock among the locks in sent_received_lock_in_propose
  require ∀ (ixnl : interaction) (sl : Bool), sent_lock_in_prepare n v p1 p2 ixnl sl →
    (height ixnl < height ixn_prev ∨ (height ixnl = height ixn_prev ∧ sl=true ∧ s_prev=false))
  prevoted_node n v p1 p2 ixn := True
  stage n v p1 p2 ixn S := (S = prevote) -- move to prevote stage
}


-- The operator responds to a quorum of prevotes with a prevote
action prevote (op : node) (v : view) (p1 p2 : participant) (ixn : interaction) = {
  require cur_view op v
  require operator op v p1 p2
  require stage op v p1 p2 ixn prevote -- in prevote stage
  require ∃ (c1 c2 s1 s2 : nodeset), ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    (∀ (n: node), (ctx.member n s1 ∨ ctx.member n s2) → prevoted_node n v p1 p2 ixn)
  prevoted_operator op v p1 p2 ixn := True
  let c : nodeset ← fresh
  locked op v P I S V := (participant_context P c ∧ ctx.member op c ∧ (P = p1 ∨ P = p2) ∧ I = ixn ∧ S = true ∧ V = v)
  -- ∧ (∀ (U : view), tot_view.le U v → ¬ locked op U P I false V )) -- not updating lock if already holding a higher stage lock for same ixn from earlier views
  stage op v p1 p2 ixn S := (S = precommit) -- move to precommit stage
}

-- The nodes respond to the prevote with a precommit
action respond_prevote (n : node) (v : view) (p1 p2 : participant) (ixn : interaction) = {
  require cur_view n v
  require stage n v p1 p2 ixn prevote -- in prevote stage
  require ∃ (c1 c2 : nodeset), ctx.member n c1 ∨ ctx.member n c2 ∧ ixn_contexts ixn c1 c2
  require ∃ (op : node), operator op v p1 p2 ∧ prevoted_operator op v p1 p2 ixn
  require ∃ (c1 c2 s1 s2 : nodeset), ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → prevoted_node nc v p1 p2 ixn
  precommitted_node n v p1 p2 ixn := True
  let c : nodeset ← fresh
  locked n v P I S V := (participant_context P c ∧ ctx.member n c ∧ (P = p1 ∨ P = p2) ∧ I = ixn ∧ S = true ∧ V = v)
  -- ∧ (∀ (U : view), tot_view.le U v → ¬ locked n U P I false V ))
  stage n v p1 p2 ixn S := (S = precommit) -- move to precommit stage
}

-- The operator responds to a quorum of precommits by a precommit and decides on the ixn
action precommit (op : node) (v : view) (p1 p2 : participant) (ixn : interaction) = {
  require cur_view op v
  require operator op v p1 p2
  require stage op v p1 p2 ixn precommit -- in precommit stage
  require ∃ (c1 c2 s1 s2 : nodeset), ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → precommitted_node nc v p1 p2 ixn
  precommitted_operator op v p1 p2 ixn := True
  let c : nodeset ← fresh
  locked op v P I S V := (participant_context P c ∧ ctx.member op c ∧ (P = p1 ∨ P = p2) ∧ I = ixn ∧ S = false ∧ V = v)
  decided op v p1 p2 ixn := True
  -- broadcasted_decision op v ixn := True
  -- stage op v p1 p2 ixn S := (S = 3) -- move to commit stage
}

-- The nodes decide on the ixn on receiving a precommit from the operator
action respond_precommit (n : node) (v : view) (p1 p2 : participant) (ixn : interaction) = {
  require cur_view n v
  require stage n v p1 p2 ixn precommit -- in precommit stage
  require ∃ (c1 c2 : nodeset), ctx.member n c1 ∨ ctx.member n c2 ∧ ixn_contexts ixn c1 c2
  require ∃ (op : node), operator op v p1 p2 ∧ precommitted_operator op v p1 p2 ixn
  require ∃ (c1 c2 s1 s2 : nodeset), ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
    ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → precommitted_node nc v p1 p2 ixn
  let c : nodeset ← fresh
  locked n v P I S V := (participant_context P c ∧ ctx.member n c ∧ (P = p1 ∨ P = p2) ∧ I = ixn ∧ S = false ∧ V = v)
  decided n v p1 p2 ixn := True
}

-- -- Nodes decide on an interaction on receiving it from the operator
-- action respond_decision (n : node) (v : view) (ixn : interaction) = {
--   -- let ixn_prep := prepare_propose_ixns v ixn
--   require ∃ (op : node), operator v (prepare_propose_ixns v ixn) op ∧ broadcasted_decision op v ixn ∧
--     ∃ (c1 c2 s1 s2 : nodeset), ixn_contexts ixn c1 c2 ∧ ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧
--     ∀ (n1 : node), (ctx.member n1 s1 ∨ ctx.member n1 s2) → precommitted_node n1 v ixn
--   decided n v ixn := True
-- }


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
  (¬ is_byz N1 ∧ ¬ is_byz N2 ∧ decided N1 V1 P1 P2 I1 ∧ decided N2 V2 P1 P2 I2) → (ancestor I1 I2 ∨ ancestor I2 I1)

invariant [node_has_cur_view]
  ∀ (n : node), ∃ (v : view), cur_view n v

invariant [unique_cur_view] ∀ (n : node) (u v : view),
  cur_view n u ∧ cur_view n v → u = v

invariant [ancestor_reflexive]
  ancestor I I

invariant [operator_from_ixn_context]
  ¬ is_byz OP → (operator OP V P Q → ∃ (c1 : nodeset), participant_context P = C1 ∧ ctx.member OP c1)

invariant [unique_operator_for_pset]
  ¬ (is_byz N1 ∨ is_byz N2) → (operator N1 V P Q ∧ operator N2 V P Q → N1 = N2)

invariant [prepare_only_by_operator]
  ¬ is_byz N → (prepared_operator N V P Q → operator N V P Q)

invariant [truee]
  true
/-
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

invariant [propose_only_if_operator_prepare]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (proposed n v ixn → ∃ (ip : interaction), prepare_propose_ixns v ixn = ip ∧ prepared_operator n v ip)

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

invariant [prevote_operator_only_if_quorum_prepare]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (prevoted_operator n v ixn → (∃ (c1 c2 s1 s2 : nodeset) (ip : interaction), prepare_propose_ixns v ixn = ip ∧ ixn_contexts ip c1 c2 ∧
    ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧ ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → prepared_node nc v ip))

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
    ¬ is_byz n → (decided n v ixn ∧ ixn ≠ genesis → (∃ (op : node) (ixnp : interaction),
    prepare_propose_ixns v ixn = ixnp ∧ operator v ixnp op ∧ precommitted_operator op v ixn))

invariant [decide_only_if_quorum_precommit]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (decided n v ixn ∧ ixn ≠ genesis → (∃ (c1 c2 s1 s2 : nodeset), ixn_contexts ixn c1 c2 ∧
    ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧ ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → precommitted_node nc v ixn))

invariant [precommit_only_if_propose]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (precommitted_node n v ixn → ∃ (op : node) (ixnp : interaction), prepare_propose_ixns v ixn = ixnp ∧
    operator v ixnp op ∧ proposed op v ixn)

invariant [precommit_only_if_prepare_quorum]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (precommitted_node n v ixn → (∃ (c1 c2 s1 s2 : nodeset) (ixnp : interaction), prepare_propose_ixns v ixn = ixnp ∧ ixn_contexts ixnp c1 c2 ∧
    ctx.supermajority s1 c1 ∧ ctx.supermajority s2 c2 ∧ ∀ (nc : node), (ctx.member nc s1 ∨ ctx.member nc s2) → prepared_node nc v ixnp))

invariant [proposal_extends_parent]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (proposed n v ixn → (∃ (il : interaction) (nl : node), parent il ixn ∧ (sent_lock_in_prepare nl v ixn il true ∨ sent_lock_in_prepare nl v ixn il false)))

invariant [ancestor_def]
  ancestor I J ↔ (I = J ∨ parent I J ∨ ∃ (k : interaction), parent I k ∧ ancestor k J)

invariant [parent_property]
  parent I J ∧ parent J I → I = J

invariant [unique_parent]
  parent J I ∧ parent K I → J = K

invariant [parent_only_if_proposed]
  parent I J → ∃ (n : node) (v : view), proposed n v J

invariant [decisions_not_from_higher_views]
  cur_view N V ∧ decided N U I → tot_view.le U V

invariant [decided_only_if_proposed]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ is_byz n → (decided n v ixn → ∃ (op : node) (ixnp : interaction), prepare_propose_ixns v ixn = ixnp ∧
    operator v ixnp op ∧ proposed op v ixn)
-/
-- invariant [decided_vzero_only_genesis]
--   ∀ (v : view) (ixn : interaction) (n : node),
--     ¬ is_byz n → (decided n v ixn ∧ tot_view.zero v → ixn = genesis)

-- invariant [safety_vone]
--   ∀ (v1 v2 : view) (ixn : interaction) (n : node),
--     ¬ is_byz n → (decided n v2 ixn ∧ tot_view.zero v1 ∧ tot_view.next v1 v2 → ancestor genesis ixn)

-- invariant [safety_vk_vk1]
--   ∀ (v1 v2 : view) (i1 i2 : interaction) (n1 n2 : node),
--     ¬ is_byz n1 ∧ ¬ is_byz n2 → (decided n1 v1 i1 ∧ decided n2 v2 i2 ∧ tot_view.next v1 v2 → ancestor i1 i2)


-- invariant [precommit_operator_only_if_parent_locked]

-- invariant [unique_lock_held_by_each_node]
--   ∀ (v : view) (i1 i2 : interaction) (n : node) (s1 s2 : Bool),
--     (locked n v i1 s1 ∧ locked n v i2 s2) →  (i1 = i2 ∧ s1 = s2)


#gen_spec

set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true
set_option veil.vc_gen "transition"
-- set_option veil.showVerificationTime true
-- set_option veil.smt.seed 7


#time #check_invariants

end IFP
