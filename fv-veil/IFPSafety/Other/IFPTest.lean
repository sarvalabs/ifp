import Veil

class IFPByzQuorum (node : Type) (is_byz : outParam (node → Prop)) (nset : outParam Type) where
  member (n : node) (s : nset) : Prop
  supermajority (s : nset) (c : nset) : Prop       -- 2f + 1 nodes

  supermajority_s_belongs_to_c :
    ∀ (s c : nset), supermajority s c  → ∀ (n : node), (member n s → member n c)

  supermajorities_intersect_in_honest :
    ∀ (s1 s2 c : nset),
      (supermajority s1 c ∧ supermajority s2 c) → (∃ (n : node), member n s1 ∧ member n s2 ∧ ¬ is_byz n)
    --

-- We prove safety of IFP for a single epoch
veil module IFP

type view
instantiate tot_view : TotalOrderWithMinimum view
type participant
type node
type nodeset


variable (is_byz : node → Prop)

instantiate ctx : IFPByzQuorum node is_byz nodeset

immutable relation participant_context: participant → nodeset → Prop


relation node_action : node → participant → Prop


#gen_state

-- # Assumptions

-- -- Assume that there are exactly two such participants among which all ixns occur
-- assumption ∃ (p1 p2 : participant), p1 ≠ p2 ∧ ∀ (i: interaction),
--   interactions i p1 p2

-- Assume that each participant has only one context.
assumption (participant_context P C1 ∧ participant_context P C2) → C1 = C2


after_init {
  node_action N P := False
}


action quorum_check (n : node) (p : participant) (c : nodeset) = {
  require participant_context p c
  require ctx.member n c
  node_action n p := True
}

action sabotage (n : node) = {
  require is_byz n
  node_action n P := True
}

-- invariant [quorum]
--   ∀ (s1 s2 : nodeset) (n : node),
--    ( (ctx.supermajority s1 ∧ ctx.supermajority s2 ∧ ((ctx.member n s1 ∨ ctx.member n s2) → node_action n )) → (∃ (m : node), ctx.member m s1 ∧ ctx.member m s2 ∧ ¬ is_byz m ∧ node_action m) )

invariant [quorum_with_actions]
  ∀ (s1 s2 c : nodeset) (p : participant),
    ctx.supermajority s1 c ∧ ctx.supermajority s2 c ∧
    (∀ (n : node), (ctx.member n s1 ∨ ctx.member n s2) → node_action n p) →
      ∃ (m : node), ctx.member m s1 ∧ ctx.member m s2 ∧ ¬ is_byz m ∧ node_action m p


#gen_spec

set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true
set_option veil.vc_gen "transition"
-- set_option veil.showVerificationTime true
-- set_option veil.smt.seed 7

#time #check_invariants
