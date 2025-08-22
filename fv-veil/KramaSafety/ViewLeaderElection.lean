import Veil

veil module KramaLeaderElection

type view
type participant
type node
type interaction

instantiate tot_view : TotalOrderWithMinimum view
instantiate tot_node : TotalOrderWithMinimum node


function view_participant_leader: view → participant → node
function participant_set: interaction → List participant
relation interaction_leader: interaction → node → Prop
relation current_view: view → Prop

#gen_state

after_init {
    interaction_leader I N := False
    tot_view.zero V →  current_view V := True
    ¬ tot_view.zero V → current_view V := False
}


action interaction_leader_election (ixn : interaction) = {
  require ∀ N : node, interaction_leader ixn N = False
  let ixn_p := participant_set ixn
  -- let participant_leader_v := participant_view_leader v
  let mut interaction_leaders : List node := ixn_p.map ( fun p => participant_leader p)
  let n_max : node ← fresh
  require (n_max ∈ interaction_leaders ∧
        ( ∃ n :node, (n ∈ interaction_leaders ∧ tot_node.le n_max n) → n_max=n) )
  interaction_leader ixn n_max := True;
}


invariant [unique_interaction_leader] interaction_leader I N1 ∧ interaction_leader I N2 → N1 = N2

-- invariant [valid_interaction_leader]
--   ∀ (ixn: interaction) (v: view),
--     interaction_leader v ixn N → (∃ (p : participant),
--     p ∈ participant_set ixn ∧ participant_view_leader v p N)


#gen_spec

set_option veil.printCounterexamples true
-- set_option veil.smt.model.minimize true
/- The `transition` VC style gives more readable counter-examples, since
those show both the pre-state and post-state. -/
set_option veil.vc_gen "transition"

#time #check_invariants!
