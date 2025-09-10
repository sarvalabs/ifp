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
relation view_interaction_leader: view → interaction → node → Prop
relation current_view: view → Prop

#gen_state

after_init {
    view_interaction_leader V I N := False
    current_view V := True
}

action view_change (v:view){
}

action interaction_leader_election (ixn : interaction) (v : view) = {
  require ∀ N : node, view_interaction_leader v ixn N = False
  let ixn_p := participant_set ixn
  let participant_leader_v := view_participant_leader v
  let mut interaction_leaders : List node := ixn_p.map (fun p => participant_leader_v p)
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

-- #time #check_invariants!
