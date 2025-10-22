def hello := "world"

def x  := 1
#eval x

#eval Nat.succ (Nat.succ x)

def myList := ["a","b"]
#eval "a" ∈ myList

class ByzQuorum (node : Type) (is_byz : outParam (node → Prop)) (nset : outParam Type) where
  member (a : node) (s : nset) : Prop
  supermajority (s : nset) : Prop       -- 2f + 1 nodes

  supermajorities_intersect_in_honest :
    ∀ (s1 s2 : nset), ∃ (a : node), member a s1 ∧ member a s2 ∧ ¬ is_byz a


set_view_tr_node_has_cur_view (could not get readable model; try changing `veil.smt.seed` or increasing `veil.smt.timeout`; if the goal cannot be solved by z3, we cannot show a readable model and instead show the model from cvc5):
(; cardinality of Empty is 1
 ; rep: (as @Empty_0 Empty)
 ; cardinality of _view is 1
 ; rep: (as @_view_0 _view)
 ; cardinality of _nodeset is 1
 ; rep: (as @_nodeset_0 _nodeset)
 ; cardinality of _node is 1
 ; rep: (as @_node_0 _node)
 ; cardinality of _interaction is 1
 ; rep: (as @_interaction_0 _interaction)
 ; cardinality of _participant is 2
 ; rep: (as @_participant_0 _participant)
 ; rep: (as @_participant_1 _participant)
 (|define-fun| |_v_cur| () |_view| (|as| |@_view_0| |_view|)) (|define-fun| |_tot_view.le| ((|$x1| |_view|) (|$x2| |_view|)) |Bool| |true|) (|define-fun| |_tot_view.zero| () |_view| (|as| |@_view_0| |_view|)) (|define-fun| |_ctx.supermajority| ((|$x1| |_nodeset|) (|$x2| |_nodeset|)) |Bool| |true|) (|define-fun| |_ctx.member| ((|$x1| |_node|) (|$x2| |_nodeset|)) |Bool| |true|) (|define-fun| |_sk0_| ((|$x1| |_nodeset|) (|$x2| |_nodeset|)) |_node| (|as| |@_node_0| |_node|)) (|define-fun| |_is_byz| ((|$x1| |_node|)) |Bool| |false|) (|define-fun| |_st.proposed| ((|$x1| |_node|) (|$x2| |_view|) (|$x3| |_interaction|)) |Bool| |false|) (|define-fun| |_st.parent| ((|$x1| |_interaction|) (|$x2| |_interaction|)) |Bool| |true|) (|define-fun| |_st.locked| ((|$x1| |_node|) (|$x2| |_interaction|) (|$x3| |Bool|) (|$x4| |_view|)) |Bool| |true|) (|define-fun| |_st.cur_view| ((|$x1| |_node|) (|$x2| |_view|)) |Bool| |true|) (|define-fun| |_p1_| () |_participant| (|as| |@_participant_0| |_participant|)) (|define-fun| |_p2_| () |_participant| (|as| |@_participant_1| |_participant|)) (|define-fun| |_st.interactions| ((|$x1| |_interaction|) (|$x2| |_participant|) (|$x3| |_participant|)) |Bool| (|and| (|=| (|as| |@_interaction_0| |_interaction|) |$x1|) (|=| (|as| |@_participant_0| |_participant|) |$x2|) (|=| (|as| |@_participant_1| |_participant|) |$x3|))) (|define-fun| |_st.precommitted_operator| ((|$x1| |_node|) (|$x2| |_view|) (|$x3| |_interaction|)) |Bool| |false|) (|define-fun| |_st.participant_context| ((|$x1| |_participant|) (|$x2| |_nodeset|)) |Bool| (|not| (|and| (|=| (|as| |@_participant_0| |_participant|) |$x1|) (|=| (|as| |@_nodeset_0| |_nodeset|) |$x2|)))) (|define-fun| |_st.precommitted_node| ((|$x1| |_node|) (|$x2| |_view|) (|$x3| |_interaction|)) |Bool| |false|) (|define-fun| |_st.prevoted_node| ((|$x1| |_node|) (|$x2| |_view|) (|$x3| |_interaction|)) |Bool| |false|) (|define-fun| |_st.prevoted_operator| ((|$x1| |_node|) (|$x2| |_view|) (|$x3| |_interaction|)) |Bool| |false|) (|define-fun| |_st.prepare_propose_ixns| ((|$x1| |_view|) (|$x2| |_interaction|)) |_interaction| (|as| |@_interaction_0| |_interaction|)) (|define-fun| |_st.prepared_node| ((|$x1| |_node|) (|$x2| |_view|) (|$x3| |_interaction|)) |Bool| |false|) (|define-fun| |_st.operator| ((|$x1| |_view|) (|$x2| |_interaction|) (|$x3| |_node|)) |Bool| |false|) (|define-fun| |_st.prepared_operator| ((|$x1| |_node|) (|$x2| |_view|) (|$x3| |_interaction|)) |Bool| |false|) (|define-fun| |_st.ancestor| ((|$x1| |_interaction|) (|$x2| |_interaction|)) |Bool| |true|) (|define-fun| |_sk1_| ((|$x1| |_node|)) |_view| (|as| |@_view_0| |_view|)) (|define-fun| |_st.decided| ((|$x1| |_node|) (|$x2| |_view|) (|$x3| |_interaction|)) |Bool| |false|))
