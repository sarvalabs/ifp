import Veil

/- In this file, we model a simplified version of IFP
with a single chain (associated with a participant) -/

veil module SingleChain

type node
type block
type view
type quorum


instantiate tot : TotalOrder view
open TotalOrder

-- quorum and honesty
immutable relation member (N : node) (Q: quorum)
immutable relation honest : node → Prop

/- We abstract over a node's current round, instead only tracking
with a relation which rounds the node has left.
This is in order to avoid using a function from
node to round, and it allows us to emit verification conditions that are
efficiently solvable by the SMT Solver.
Source: Formal Verification of Tendermint using IVy, and the
PaxosEPR example given in Veil.
But in those examples, it is a relation involving the nodes as well. -/
relation left_view : view → Prop

-- for blocks
function height : block → Int
relation parent : block → block → Prop
relation ancestor : block → block → Prop

-- for all nodes
inmmutable relation leader : node → view → Prop
relation decided : node → view → block → Prop
relation locked : node → view → block → Prop

-- for leaders
relation sent_prepare_leader : node → view → block → Prop
relation proposed : node → view → block → Prop
relation prevoted_leader : node → view → block → Prop
relation precommitted_leader : node → view → block → Prop

-- for non-leader nodes
relation sent_prepare_node : node → view → block → Prop
relation prevoted_node : node → view → block → Prop
relation precommitted_node : node → view → block → Prop

#gen_state

after init {
    parent B C := False
    -- parent genesis genesis := True
    -- proposed(B) := B = genesis
    height B := 0
    ancestor B C := B = C
    left_view R := True --I guess?
    decided N V B := False
    locked N V B := False
    sent_prepare_leader N V B := False
    proposed N V B := False
    prevoted_leader N V B := False
    precommitted_leader N V B := False
    sent_prepare_node N V B := False
    prevoted_node N V B := False
    precommitted_node N V B := False
}

-- Every view V has a unique leader
assumption leader N1 V ∧ leader N2 V → N1 = N2

-- Quorum intersection property
assumption ∀ (Q1:quorum) (Q2:quorum), ∃ (N:node), honest n ∧ member N Q1 ∧ member N Q2

-- WRITE ACTIONS HERE


invariant [genesis_parent] parent genesis genesis
invariant parent B C → ancestor B C
invariant parent C D ∧ ancestor B C → ancestor B D
        invariant ~proposed(B) -> ~prev(B,C)
        invariant ~proposed(B) -> block_height(B) = 0
        invariant prev(B,C) & prev(B,D) -> C=D
        invariant prev(B,C) & prev(C,B) -> C=tree.genesis
        invariant prev(B,C) & B ~= C -> block_height(C) < block_height(B)
        invariant prev(B,C) -> proposed(C)
        invariant proposed(B) -> ancestor(genesis,B)
        invariant prev(B,C) -> ancestor(C,B)
        invariant ancestor(B,C) & B ~= C -> block_height(B) < block_height(C)
        invariant ancestor(B,C) & ~proposed(B) -> B=C
        invariant ancestor(B,B)
        invariant ancestor(B,C) & ancestor(C,B) -> B=C
        invariant ancestor(B,C) & ancestor(C,D) -> ancestor(B,D)
        invariant ancestor(B,D) & ancestor(C,D) -> ancestor(B,C) | ancestor(C,B)
        invariant ancestor(B,D) & ancestor(C,D) &  ancestor(B,C) & B ~= C & C ~= D -> ~prev(D,B)

        #invariant proposed(B) -> exists D. prev(B,D)
        #invariant prev(B,C) -> exists D. prev(B,D)
        #invariant ancestor(B,C) & B~=C -> exists D. prev(C,D) & ancestor(B,D)
