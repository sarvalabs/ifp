-- IFPNL: IFPL simplified to single-context (no participants).
-- Mirrors the IFPM → IFPN transformation applied to IFPL:
-- 1. Removed participant type and dual contexts
-- 2. Single quorum instead of dual quorum checks
-- 3. Single lock dimension (no per-participant locks)
-- 4. Merged sent_lock_in_prepare_1/2 into single sent_lock_in_prepare
-- 5. Dropped propose_nil (trigger vanishes with single highest lock)
-- Retains IFPL's ghost relations (locked_at_view, locked_for_descendant,
-- proposed_for_descendant, decided_for_descendant), height-based uniqueness
-- (unique_decided_at_height, unique_locked_at_height), and view-height
-- monotonicity (lock_height_monotone, decision_height_monotone).

import Veil

veil module IFPProtocolNL


class IFPByzQuorum (node : Type) (nset : Type) where
  is_byz : node → Prop
  member (n : node) (s : nset) : Prop
  supermajority (s : nset) : Prop   -- 2f + 1 nodes

  supermajorities_intersect_in_honest :
    ∀ (s1 s2 : nset),
      (supermajority s1 ∧ supermajority s2) → (∃ (n : node), member n s1 ∧ member n s2 ∧ ¬ is_byz n)


-- `type declarations`
type view
type node
type interaction
type nodeset
type stage

-- `instantiations`
instantiate tot_view : TotalOrderWithMinimum view
instantiate ctx : IFPByzQuorum node nodeset

-- `individuals`
immutable individual prepare : stage
immutable individual propose : stage
immutable individual prevote : stage
immutable individual precommit : stage
immutable individual commit : stage

individual genesis : interaction


-- `mutable relations and functions`
relation cur_view: node → view → Bool
relation cur_stage : node → view → stage → Bool
relation sent_lock_in_prepare : node → view → interaction → stage → view → Bool
relation decided : node → view → interaction → Bool
relation locked : node → interaction → stage → view → Bool

-- Operator relations
relation operator: node → view → Bool
relation prepared_operator : node → view → Bool
relation proposed_repropose : node → view → interaction → Bool
relation proposed_extend : node → view → interaction → Bool
relation prevoted_operator : node → view → interaction → Bool
relation precommitted_operator : node → view → interaction → Bool

-- Non-operator relations
relation prepared_node : node → view → Bool
relation prevoted_node : node → view → interaction → Bool
relation precommitted_node : node → view → interaction → Bool

-- Interaction relations
relation parent : interaction → interaction → Bool
relation ancestor : interaction → interaction → Bool
function height : interaction → Nat

-- ####################################################################
-- # Ghost Relations (HotStuff-style, maintained in actions)
-- ####################################################################

-- "Node N has some lock at exactly view V"
-- Eliminates ∃ I S, locked N I S V from invariant quantification.
-- Analogous to HotStuff's votedh(N, H).
relation locked_at_view : node → view → Bool

-- "Node N has a lock on some descendant of A at exactly view V"
-- i.e., ∃ I S, locked N I S V ∧ ancestor A I
-- Eliminates the need for the SMT solver to find interaction witnesses
-- and prove ancestry relationships.
-- Analogous to HotStuff's votedb(N, B, H).
relation locked_for_descendant : node → interaction → view → Bool

-- "At view V, the proposed interaction is a descendant of A"
-- i.e., ∃ op I, (proposed_repropose op V I ∨ proposed_extend op V I) ∧ ancestor A I
relation proposed_for_descendant : view → interaction → Bool

-- "Node N decided a descendant of A at view V"
-- i.e., ∃ I, decided N V I ∧ ancestor A I
relation decided_for_descendant : node → interaction → view → Bool


#gen_state

-- `assumptions`

assumption ¬ (prepare = propose ∨ prepare = prevote ∨ prepare = precommit ∨ prepare = commit ∨
  propose = prevote ∨ propose = precommit ∨ propose = commit ∨ prevote = precommit ∨ prevote = commit ∨ precommit = commit)

-- `init`

after_init {
  parent I J := false;
  ancestor I J := decide $ (I = J);
  locked N I S V := decide $ (I = genesis ∧ S = precommit ∧ V = tot_view.zero);
  decided N V I := decide $ (I = genesis ∧ V = tot_view.zero)
  height I := 0;
  cur_stage N V S := decide $ (S = prepare);
  operator N V := false;
  cur_view N V := decide $ (V = tot_view.zero);
  prepared_operator N V := false;
  sent_lock_in_prepare N U L S V := false;
  proposed_repropose N V I := false;
  proposed_extend N V I := false;
  prevoted_operator N V I := false;
  precommitted_operator N V I := false;
  prepared_node N V := false;
  prevoted_node N V I := false;
  precommitted_node N V I := false;
  -- Ghost init (locked): matches initial locked state
  -- Initially: locked N genesis precommit tot_view.zero
  -- Initially: ancestor A genesis iff A = genesis
  locked_at_view N V := decide $ (V = tot_view.zero);
  locked_for_descendant N A V := decide $ (A = genesis ∧ V = tot_view.zero);
  -- Ghost init (proposed/decided)
  proposed_for_descendant V A := false;
  decided_for_descendant N A V := decide $ (A = genesis ∧ V = tot_view.zero);
}

-- ####################################################################
-- # Actions
-- ####################################################################

action set_view (v_cur v_next : view) {
  require ∀ (n : node), cur_view n v_cur
  require tot_view.next v_cur v_next
  cur_view N V := decide $ (V = v_next)
  -- No ghost updates: no locks change during view transition
}

action pick_operator (op : node) (v : view) {
  require v ≠ tot_view.zero
  require cur_view op v
  require ∀ (n : node), ¬ operator n v
  operator op v := true
  -- No ghost updates: no locks change
}

action operator_prepare (op : node) (v : view) {
  require v ≠ tot_view.zero
  require cur_view op v
  require cur_stage op v prepare
  require operator op v
  require ¬ prepared_operator op v
  prepared_operator op v := true
  -- No ghost updates: no locks change
}

action respond_prepare (n : node) (v : view) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v prepare
  require ¬ prepared_node n v
  require ∃ (op : node), (operator op v ∧ prepared_operator op v)
  prepared_node n v := true
  sent_lock_in_prepare n v IL SL VL := decide $
    (locked n IL SL VL ∧
     tot_view.lt VL v ∧
     (∀ (vl2 : view), tot_view.lt VL vl2 → ¬ ∃ (i2 : interaction) (s2 : stage), locked n i2 s2 vl2) ∧
     (SL = prevote → ¬ locked n IL precommit VL))
  cur_stage n v S := decide $ (S = propose)
  -- No ghost updates: no locks change (sent_lock_in_prepare reads locks but doesn't create new ones)
}

-- Repropose: highest lock is a prevote lock
action propose_repropose (op : node) (v : view) {
  require v ≠ tot_view.zero
  require cur_view op v
  require operator op v
  require prepared_operator op v
  require cur_stage op v propose
  require ∀ (ix : interaction), ¬ proposed_repropose op v ix
  require ∀ (ix : interaction), ¬ proposed_extend op v ix
  require ∃ (s : nodeset), (
    ctx.supermajority s ∧ (
      ∀ (n : node), (
        ctx.member n s → (prepared_node n v ∧
        ∃ (vl : view) (ixnl : interaction) (sl : stage) (t : nodeset), (
          sent_lock_in_prepare n v ixnl sl vl
          ∧ locked n ixnl sl vl
          ∧ tot_view.le vl v
          ∧ ctx.supermajority t
          ∧ ( sl = prevote → (∀ (nt : node), (ctx.member nt t → prevoted_node nt vl ixnl)) )
          ∧ ( sl = precommit → (∀ (nt : node), (ctx.member nt t → precommitted_node nt vl ixnl)) )
        )
      ))
    )
  )
  let ixn_max : interaction ← pick
  let s_max : stage ← pick
  let v_max : view ← pick
  require ∃ (n_max : node), (
    sent_lock_in_prepare n_max v ixn_max s_max v_max
    ∧ locked n_max ixn_max s_max v_max ∧
    ∀ (n_l : node) (ixn_l : interaction) (s_l : stage) (v_l : view), (
      sent_lock_in_prepare n_l v ixn_l s_l v_l → (
        height ixn_l < height ixn_max
        ∨ (height ixn_l = height ixn_max ∧ s_l = prevote ∧ s_max = precommit)
        ∨ (height ixn_l = height ixn_max ∧ s_l = s_max ∧ tot_view.le v_l v_max)
        ∨ (ixn_l = ixn_max ∧ s_l = s_max ∧ v_l = v_max)
      )
    )
  )
  require s_max = prevote
  proposed_repropose op v ixn_max := true;
  -- GHOST: proposed interaction is a descendant of A iff A is an ancestor of ixn_max
  proposed_for_descendant v A := decide $ (proposed_for_descendant v A ∨ ancestor A ixn_max);
}

-- Extend: highest lock is a precommit lock
action propose_extend (op : node) (v : view) (ixn_propose : interaction) {
  require v ≠ tot_view.zero
  require ∀ (j : interaction), ¬ (parent j ixn_propose ∨ parent ixn_propose j)
  require ∀ (j : interaction), (ixn_propose ≠ j → ¬ (ancestor j ixn_propose ∨ ancestor ixn_propose j))
  require height ixn_propose = 0
  require cur_view op v
  require operator op v
  require prepared_operator op v
  require cur_stage op v propose
  require ixn_propose ≠ genesis
  require ∀ (ix : interaction), ¬ proposed_repropose op v ix
  require ∀ (ix : interaction), ¬ proposed_extend op v ix
  require ∃ (s : nodeset), (
    ctx.supermajority s ∧ (
      ∀ (n : node), (
        ctx.member n s → (prepared_node n v ∧
        ∃ (vl : view) (ixnl : interaction) (sl : stage) (t : nodeset), (
          sent_lock_in_prepare n v ixnl sl vl
          ∧ locked n ixnl sl vl
          ∧ tot_view.le vl v
          ∧ ctx.supermajority t
          ∧ ( sl = prevote → (∀ (nt : node), (ctx.member nt t → prevoted_node nt vl ixnl)) )
          ∧ ( sl = precommit → (∀ (nt : node), (ctx.member nt t → precommitted_node nt vl ixnl)) )
        )
      ))
    )
  )
  let ixn_max : interaction ← pick
  let s_max : stage ← pick
  let v_max : view ← pick
  require ∃ (n_max : node), (
    sent_lock_in_prepare n_max v ixn_max s_max v_max
    ∧ locked n_max ixn_max s_max v_max ∧
    ∀ (n_l : node) (ixn_l : interaction) (s_l : stage) (v_l : view), (
      sent_lock_in_prepare n_l v ixn_l s_l v_l → (
        height ixn_l < height ixn_max
        ∨ (height ixn_l = height ixn_max ∧ s_l = prevote ∧ s_max = precommit)
        ∨ (height ixn_l = height ixn_max ∧ s_l = s_max ∧ tot_view.le v_l v_max)
        ∨ (ixn_l = ixn_max ∧ s_l = s_max ∧ v_l = v_max)
      )
    )
  )
  require s_max = precommit
  require ixn_max ≠ ixn_propose
  require ¬ (ancestor ixn_max ixn_propose ∨ ancestor ixn_propose ixn_max)
  parent ixn_max ixn_propose := decide $ (ixn_max ≠ ixn_propose);
  ancestor A ixn_propose := decide $ (ancestor A ixn_propose ∨ ancestor A ixn_max ∨ A = ixn_max ∨ A = ixn_propose);
  proposed_extend op v ixn_propose := true;
  height ixn_propose := height ixn_max + 1;
  -- GHOST: parallel-safe version — expand ancestor post-state for ixn_propose
  proposed_for_descendant v A := decide $ (proposed_for_descendant v A
    ∨ ancestor A ixn_propose ∨ ancestor A ixn_max ∨ A = ixn_max ∨ A = ixn_propose);
}

action respond_propose (n : node) (v : view) (ixn : interaction) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v propose
  require ∃ (op : node), operator op v ∧ (proposed_repropose op v ixn ∨ proposed_extend op v ixn)
  require ∀ (i : interaction), ¬ prevoted_node n v i
  require ixn ≠ genesis
  require ∃ (s : nodeset), (
    ctx.supermajority s ∧ (
      ∀ (n : node), (
        ctx.member n s → (prepared_node n v ∧
        ∃ (vl : view) (ixnl : interaction) (sl : stage) (t : nodeset), (
          sent_lock_in_prepare n v ixnl sl vl
          ∧ locked n ixnl sl vl
          ∧ tot_view.le vl v
          ∧ ctx.supermajority t
          ∧ ( sl = prevote → (∀ (nt : node), (ctx.member nt t → prevoted_node nt vl ixnl)) )
          ∧ ( sl = precommit → (∀ (nt : node), (ctx.member nt t → precommitted_node nt vl ixnl)) )
        )
      ))
    )
  )
  let ixn_max : interaction ← pick
  let s_max : stage ← pick
  let v_max : view ← pick
  require ∃ (n_max : node), (
    sent_lock_in_prepare n_max v ixn_max s_max v_max
    ∧ locked n_max ixn_max s_max v_max ∧
    ∀ (n_l : node) (ixn_l : interaction) (s_l : stage) (v_l : view), (
      sent_lock_in_prepare n_l v ixn_l s_l v_l → (
        height ixn_l < height ixn_max
        ∨ (height ixn_l = height ixn_max ∧ s_l = prevote ∧ s_max = precommit)
        ∨ (height ixn_l = height ixn_max ∧ s_l = s_max ∧ tot_view.le v_l v_max)
        ∨ (ixn_l = ixn_max ∧ s_l = s_max ∧ v_l = v_max)
      )
    )
  )
  -- Valid proposal: repropose or extend
  require s_max = prevote ∨ s_max = precommit
  require (s_max = prevote) → ixn_max = ixn
  require (s_max = precommit) →
    (ixn ≠ ixn_max ∧ parent ixn_max ixn
    ∧ height ixn = height ixn_max + 1)
  prevoted_node n v ixn := true
  cur_stage n v S := decide $ (S = prevote)
  -- No ghost updates: no locks change
}

action operator_prevote (op : node) (v : view) (ixn : interaction) {
  require v ≠ tot_view.zero
  require ∀ (i : interaction), ¬ prevoted_operator op v i
  require cur_view op v
  require operator op v
  require cur_stage op v prevote
  require ∃ (s : nodeset), ctx.supermajority s ∧
    (∀ (n: node), ctx.member n s → prevoted_node n v ixn)
  prevoted_operator op v ixn := true
  -- No ghost updates: no locks change
}

action respond_prevote (n : node) (v : view) (ixn : interaction) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v prevote
  require ∃ (op : node), operator op v ∧ prevoted_operator op v ixn
  require ∃ (s : nodeset), ctx.supermajority s ∧
    ∀ (nc : node), ctx.member nc s → prevoted_node nc v ixn
  precommitted_node n v ixn := true
  if ( ¬ ∃ (u : view), (tot_view.le u v ∧ locked n ixn precommit u) ) then
    locked n ixn prevote v := true;
    -- GHOST: new prevote lock at view v
    locked_at_view n v := true;
    locked_for_descendant n A v := decide $ (locked_for_descendant n A v ∨ ancestor A ixn);
  cur_stage n v S := decide $ (S = precommit)
}

action operator_precommit (op : node) (v : view) (ixn : interaction) {
  require v ≠ tot_view.zero
  require cur_view op v
  require operator op v
  require cur_stage op v precommit
  require ∃ (s : nodeset), ctx.supermajority s ∧
    ∀ (nc : node), ctx.member nc s → precommitted_node nc v ixn
  precommitted_operator op v ixn := true
  -- No ghost updates: no locks change
}

action respond_precommit (n : node) (v : view) (ixn : interaction) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v precommit
  require ∃ (op : node), operator op v ∧ precommitted_operator op v ixn
  require ∃ (s : nodeset), ctx.supermajority s ∧
    ∀ (nc : node), ctx.member nc s → precommitted_node nc v ixn
  locked n ixn precommit v := true;
  -- GHOST: new precommit lock at view v
  locked_at_view n v := true;
  locked_for_descendant n A v := decide $ (locked_for_descendant n A v ∨ ancestor A ixn);
  decided n v ixn := true
  -- GHOST: node decided a descendant of A at view v
  decided_for_descendant n A v := decide $ (decided_for_descendant n A v ∨ ancestor A ixn);
  cur_stage n v S := decide $ (S = commit)
}


-- ####################################################################
-- # Core Invariants
-- ####################################################################

-- INV1: Honest nodes cannot prevote on two different interactions in a given view
invariant [INV1_unique_prevote_nodes]
  ∀ (v : view) (i1 i2 : interaction) (n : node),
    ¬ ctx.is_byz n → ((prevoted_node n v i1 ∧ prevoted_node n v i2) → i1 = i2)

-- INV2: Honest nodes cannot be prevote-locked for different interactions in a given view
invariant [INV2_unique_prevote_lock_in_view]
  ∀ (n1 n2 : node) (v : view) (i1 i2 : interaction),
    ¬ (ctx.is_byz n1 ∨ ctx.is_byz n2) → ((locked n1 i1 prevote v ∧ locked n2 i2 prevote v) → i1 = i2)

-- INV3: If an honest node has decided, then a quorum has prevote-locked
invariant [INV3_decided_only_if_quorum_prevote_locked]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ ctx.is_byz n → ( (decided n v ixn ∧ ixn ≠ genesis) →
      (∃ (s : nodeset), (ctx.supermajority s
        ∧ ∀ (nc : node), ctx.member nc s → ∃ (u : view), (tot_view.le u v ∧ prevoted_node nc v ixn ∧ (locked nc ixn prevote u ∨ locked nc ixn precommit u)))) )

-- Supporting: Prevote lock implies a quorum prevoted for the interaction
invariant [prevote_lock_only_if_quorum_prevoted]
  (¬ ctx.is_byz N ∧ locked N I prevote V) → (∃ (s : nodeset), ctx.supermajority s ∧
    ∀ (NC : node), ctx.member NC s → prevoted_node NC V I)

-- Supporting (cross-node): If honest NC has precommitted for I at V, and honest N has a prevote lock
-- for J at V, then I = J.
invariant [precommit_node_lock_consistency]
  (¬ ctx.is_byz N ∧ ¬ ctx.is_byz NC ∧ precommitted_node NC V I ∧
   locked N J prevote V ∧
   I ≠ genesis ∧ J ≠ genesis) → I = J

-- Supporting: A single honest node can only have locks on one interaction per view
invariant [unique_lock_interaction_per_view]
  (¬ ctx.is_byz N ∧ locked N I1 S1 V ∧ locked N I2 S2 V) → I1 = I2

-- Cross-node lock uniqueness: all honest nodes locked at the same view
-- hold locks on the same interaction. Follows from INV-2 + precommit_lock_implies_prevoted.
invariant [cross_node_unique_lock]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   locked N1 I1 S1 V ∧ locked N2 I2 S2 V ∧
   I1 ≠ genesis ∧ I2 ≠ genesis)
  → I1 = I2

-- Supporting: Precommit lock implies the node prevoted for the interaction
invariant [precommit_lock_implies_prevoted]
  (¬ ctx.is_byz N ∧ locked N I precommit V ∧ I ≠ genesis) → prevoted_node N V I

-- Supporting: Sent locks in prepare phase correspond to actual locks
invariant [locks_sent_only_if_locked]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare N V IL SL VL) → locked N IL SL VL

-- Supporting: Genesis locks exist for all nodes
invariant [genesis_lock_existence]
  ∀ (n : node), locked n genesis precommit tot_view.zero

invariant [sent_lock_prepare_implies_cur_view_ge]
  (sent_lock_in_prepare N V IL SL VL ∧ cur_view N VCUR) → tot_view.le V VCUR

invariant [highest_lock_sent]
  sent_lock_in_prepare N V IL SL VL →
    (locked N IL SL VL ∧
     tot_view.lt VL V ∧
     (∀ i' s' v', (tot_view.lt VL v' ∧ tot_view.lt v' V) → ¬ locked N i' s' v') ∧
     (SL = prevote → ¬ locked N IL precommit VL))

-- Stepping stone for INV4: consecutive view case
invariant [precommit_next_view_discovery]
  ∀ (v v2 : view) (i : interaction), (
    (tot_view.next v v2 ∧
     v ≠ v2 ∧
     (∃ (op : node), (¬ ctx.is_byz op ∧ operator op v2 ∧ prepared_operator op v2)) ∧
     (∃ (m : node), (¬ ctx.is_byz m ∧ prepared_node m v2)) ∧
     i ≠ genesis ∧
     tot_view.zero ≠ v ∧
     (∀ (n : node), (¬ ctx.is_byz n →
      (locked n i precommit v ∧
       cur_stage n v commit ∧
       prepared_node n v2 ∧
       cur_view n v2
      )) )) →
    (∀ (n : node), ¬ ctx.is_byz n →
      sent_lock_in_prepare n v2 i precommit v)
  )

-- ####################################################################
-- # Freshness Invariants (no state on unparented interactions)
-- ####################################################################
-- These ensure that a "fresh" interaction (no parent, ≠ genesis) has no
-- pre-existing locks, proposals, or decisions. Required so that when
-- propose_extend expands the ancestor relation for ixn_propose, the
-- _fwd ghost invariants hold vacuously (the antecedent is false).

-- A locked interaction must have a parent (unless it's genesis)
invariant [no_lock_without_parent]
  (locked N I S V ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

-- A proposed interaction must have a parent (unless it's genesis)
invariant [no_proposal_without_parent]
  ((proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

-- A decided interaction must have a parent (unless it's genesis)
invariant [no_decide_without_parent]
  (decided N V I ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

-- ####################################################################
-- # Genesis Ancestry Invariants
-- ####################################################################
-- All proposed/locked non-genesis interactions must descend from genesis.
-- These block spurious models where interaction chains are disconnected
-- from genesis, which would violate proposed_extends_locked_descendant
-- and precommit_next_view_discovery.

-- All proposed non-genesis interactions have genesis as ancestor
invariant [proposed_descends_from_genesis]
  ((proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ I ≠ genesis) → ancestor genesis I

-- All non-genesis locked interactions have genesis as ancestor
invariant [locked_descends_from_genesis]
  (locked N I S V ∧ I ≠ genesis) → ancestor genesis I

-- ####################################################################
-- # Ghost Consistency Invariants (locked)
-- ####################################################################

-- locked_at_view forward: any lock implies the view-level ghost
invariant [locked_at_view_fwd]
  locked N I S V → locked_at_view N V

-- locked_at_view backward (honest only): ghost implies a real lock exists
invariant [locked_at_view_bwd]
  (¬ ctx.is_byz N ∧ locked_at_view N V) →
    ∃ (I : interaction) (S : stage), locked N I S V

-- locked_for_descendant forward: real lock + ancestry implies ghost
invariant [locked_for_descendant_fwd]
  (locked N I S V ∧ ancestor A I) → locked_for_descendant N A V

-- locked_for_descendant backward (honest only): ghost implies a real lock on a descendant
invariant [locked_for_descendant_bwd]
  (¬ ctx.is_byz N ∧ locked_for_descendant N A V) →
    ∃ (I : interaction) (S : stage), locked N I S V ∧ ancestor A I

-- ####################################################################
-- # Ghost Consistency Invariants (proposed/decided)
-- ####################################################################

-- proposed_for_descendant forward: proposed + ancestry → ghost
invariant [proposed_for_descendant_fwd]
  ((proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ ancestor A I) → proposed_for_descendant V A

-- proposed_for_descendant backward: ghost → ∃ proposed descendant
invariant [proposed_for_descendant_bwd]
  proposed_for_descendant V A →
    ∃ (OP : node) (I : interaction), (proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ ancestor A I

-- decided_for_descendant forward: decided + ancestry → ghost
invariant [decided_for_descendant_fwd]
  (decided N V I ∧ ancestor A I) → decided_for_descendant N A V

-- decided_for_descendant backward (honest only): ghost → ∃ decided descendant
invariant [decided_for_descendant_bwd]
  (¬ ctx.is_byz N ∧ decided_for_descendant N A V) →
    ∃ (I : interaction), decided N V I ∧ ancestor A I

-- ####################################################################
-- # Lock Descendant Monotonicity (core ghost invariant)
-- ####################################################################

-- If node N has locked_for_descendant for (A, V) and holds any lock at view U ≥ V,
-- that lock is also for a descendant of A.
-- This is the key invariant enabling INV-4: once locked on a descendant of A,
-- all subsequent locks remain descendants of A.
invariant [lock_descendant_monotone]
  (¬ ctx.is_byz N ∧ locked_for_descendant N A V ∧ locked N I S U ∧
   tot_view.le V U) → ancestor A I

-- ####################################################################
-- # Decision–Proposal Linking Invariant
-- ####################################################################

-- Any decided interaction was proposed at that view
invariant [decided_implies_proposed]
  (¬ ctx.is_byz N ∧ decided N V I ∧ I ≠ genesis) →
    ∃ (op : node), proposed_repropose op V I ∨ proposed_extend op V I

-- ####################################################################
-- # Ancestor Structural Invariants
-- ####################################################################
-- These give SMT direct access to key properties of ancestor without
-- needing to discover witnesses via ancestor_def_fwd/bwd unfolding.

-- Reflexivity
invariant [ancestor_refl]
  ∀ (I : interaction), ancestor I I

-- Parent implies ancestor
invariant [ancestor_from_parent]
  parent I J → ancestor I J

-- Transitivity (avoids SMT needing to find intermediate witness k)
invariant [ancestor_trans]
  (ancestor I J ∧ ancestor J K) → ancestor I K

-- Anti-symmetry (no cycles; follows from height monotonicity)
invariant [ancestor_antisymm]
  (ancestor I J ∧ ancestor J I) → I = J

-- Strict ancestor means strictly lower height
invariant [ancestor_height_strict]
  (ancestor I J ∧ I ≠ J) → height I < height J

-- Contrapositive: equal height + different → no ancestry in either direction
invariant [no_ancestor_equal_height]
  (height I = height J ∧ I ≠ J) → (¬ ancestor I J ∧ ¬ ancestor J I)

-- Parent increases height by exactly 1
invariant [parent_height]
  parent I J → height J = height I + 1

-- Ancestor is at most the transitive closure of parent
invariant [ancestor_def_fwd]
  ancestor I J → (I = J ∨ parent I J ∨ ∃ (k : interaction), parent I k ∧ ancestor k J)

invariant [ancestor_def_bwd]
  (I = J ∨ parent I J ∨ ∃ (k : interaction), parent I k ∧ ancestor k J) → ancestor I J


-- ####################################################################
-- # Supporting Invariants (structural)
-- ####################################################################

-- Each node has exactly one current view
invariant [unique_cur_view]
  cur_view N U ∧ cur_view N V → U = V

-- Every node always has some current view
invariant [node_has_cur_view]
  ∀ (n : node), ∃ (v : view), cur_view n v

-- Nodes can only be prepared for views they have reached
invariant [prepared_only_at_cur_or_past_view]
  (prepared_node N V ∧ ¬ ctx.is_byz N ∧ cur_view N V2) → tot_view.le V V2

-- Non-genesis locks are at views ≤ current view (collapses locked_only_if_prepared + prepared_only_at_cur_or_past_view)
invariant [lock_at_most_cur_view]
  (¬ ctx.is_byz N ∧ locked N I S V ∧ I ≠ genesis ∧ cur_view N VCUR)
  → tot_view.le V VCUR

-- Sent lock entries can only exist for views the node has reached
invariant [sent_lock_only_at_past_view]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare N V IL SL VL ∧ cur_view N VCUR) → tot_view.le V VCUR

-- One stage per node per view
invariant [unique_stage]
  (¬ ctx.is_byz N ∧ cur_stage N V S1 ∧ cur_stage N V S2) → S1 = S2

-- At most one operator per view
invariant [unique_operator]
  (operator N1 V ∧ operator N2 V) → N1 = N2

-- Only the operator can have proposed
invariant [proposed_only_by_operator]
  ((proposed_repropose N V I ∨ proposed_extend N V I) ∧ ¬ ctx.is_byz N) → operator N V

-- Genesis locks are only at view zero with precommit stage
invariant [genesis_lock_only_at_zero]
  locked N genesis S V → (V = tot_view.zero ∧ S = precommit)

invariant [lock_stage_valid]
  locked N I S V → (S = prevote ∨ S = precommit)

-- Non-genesis locks require preparation at the same view
invariant [locked_only_if_prepared]
  (¬ ctx.is_byz N ∧ locked N I S V ∧ V ≠ tot_view.zero ∧ I ≠ genesis) → prepared_node N V

-- Stage negation invariants
invariant [stage_neg_1]
  ((cur_stage N V precommit ∨ cur_stage N V prevote ∨ cur_stage N V propose
  ∨ cur_stage N V prepare) ∧ I ≠ genesis ∧ ¬ ctx.is_byz N) → ¬ (decided N V I ∨ locked N I precommit V)

invariant [stage_neg_2]
  ((cur_stage N V prevote ∨ cur_stage N V propose
  ∨ cur_stage N V prepare) ∧ I ≠ genesis ∧ ¬ ctx.is_byz N) → ¬ (precommitted_node N V I ∨ precommitted_operator N V I ∨ locked N I S V)

invariant [stage_neg_3]
  ((cur_stage N V propose ∨ cur_stage N V prepare) ∧ I ≠ genesis ∧ ¬ ctx.is_byz N)
  → ¬ (prevoted_node N V I ∨ prevoted_operator N V I ∨ locked N I S V)

invariant [stage_init_prepare]
  (¬ prepared_node N V ∧ ¬ ctx.is_byz N) → cur_stage N V prepare

invariant [stage_neg_4]
  (cur_stage N V prepare ∧ ¬ ctx.is_byz N) →
    ¬ (prepared_node N V ∨ sent_lock_in_prepare N V IL SL VL)

-- Genesis never enters the pipeline
invariant [genesis_not_in_pipeline]
  ¬ ( ¬ ctx.is_byz N ∧ (proposed_repropose N V genesis ∨ proposed_extend N V genesis ∨ prevoted_node N V genesis
  ∨ prevoted_operator N V genesis ∨ precommitted_node N V genesis
  ∨ precommitted_operator N V genesis))

invariant [prevote_stage_implies_prevoted]
  (cur_stage N V prevote ∧ ¬ ctx.is_byz N) → ∃ I, prevoted_node N V I

invariant [precommit_stage_implies_precommitted]
  (cur_stage N V precommit ∧ ¬ ctx.is_byz N) → ∃ I, precommitted_node N V I

-- Cross-node unique prevote
invariant [cross_node_unique_prevote]
  (¬ (ctx.is_byz N1 ∨ ctx.is_byz N2) ∧ prevoted_node N1 V I1 ∧ prevoted_node N2 V I2) → I1 = I2

-- Precommitted node implies it prevoted for the same interaction
invariant [precommit_nodes_only_if_prevoted_for_same_ixn]
  (¬ ctx.is_byz N ∧ precommitted_node N V I) → prevoted_node N V I

-- Precommitted node implies a lock exists for it
invariant [precommitted_node_implies_lock]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ ctx.is_byz n → ((precommitted_node n v ixn ∧ ixn ≠ genesis) →
      ∃ (u : view), tot_view.le u v ∧ (locked n ixn prevote u ∨ locked n ixn precommit u))

-- Combined: precommitted node implies prevoted AND locked (flattened).
-- Collapses precommit_nodes_only_if_prevoted_for_same_ixn + precommitted_node_implies_lock
-- into a single inference step for INV3.
invariant [precommit_quorum_prevoted_and_locked]
  (¬ ctx.is_byz NC ∧ precommitted_node NC V IXN ∧ IXN ≠ genesis) →
  (prevoted_node NC V IXN ∧
   ∃ (U : view), tot_view.le U V ∧ (locked NC IXN prevote U ∨ locked NC IXN precommit U))

-- Decision requires a precommit operator
invariant [decide_only_if_precommit_operator]
  (¬ ctx.is_byz N ∧ decided OP V I ∧ I ≠ genesis) → (∃ (op : node), (operator op V ∧ precommitted_operator op V I))

-- At prevote stage, node prevoted for the proposed interaction
invariant [stage_2]
  (cur_stage N V prevote ∧ ¬ ctx.is_byz N)
  → (∃ (i : interaction), (∃ (op : node), proposed_repropose op V i ∨ proposed_extend op V i) ∧ prevoted_node N V i)

-- Only one proposal per view
invariant [unique_proposal]
  ¬ (ctx.is_byz N1 ∨ ctx.is_byz N2) → ( ((proposed_repropose N1 V I1 ∨ proposed_extend N1 V I1) ∧ (proposed_repropose N2 V I2 ∨ proposed_extend N2 V I2)) → (I1 = I2 ∧ N1 = N2) )

invariant [unique_proposed_interaction]
  ((proposed_repropose N V I1 ∨ proposed_extend N V I1) ∧ (proposed_repropose N V I2 ∨ proposed_extend N V I2)) → I1 = I2

-- Honest node prevoted → a proposal exists
invariant [prevote_implies_proposed]
  (prevoted_node N V I ∧ ¬ ctx.is_byz N) → (∃ (op : node), (operator op V ∧ (proposed_repropose op V I ∨ proposed_extend op V I)))

invariant [precommit_only_if_propose]
  (¬ ctx.is_byz N ∧ precommitted_node N V I) → (∃ (op : node), operator op V ∧ (proposed_repropose op V I ∨ proposed_extend op V I))

invariant [prepare_response_only_on_prepare]
  ¬ ctx.is_byz N → (prepared_node N V → ∃ (op : node), operator op V ∧ prepared_operator op V)

invariant [prevote_only_by_operator]
  ¬ ctx.is_byz N → (prevoted_operator OP V I → operator OP V)

invariant [precommit_only_by_operator]
  (¬ ctx.is_byz OP ∧ precommitted_operator OP V I) → operator OP V

invariant [prepared_node_has_lock_sent]
  (¬ ctx.is_byz N ∧ prepared_node N V ∧ V ≠ tot_view.zero ∧
   locked N IL SL VL ∧
   tot_view.lt VL V ∧
   (∀ (vl2 : view), (tot_view.lt VL vl2 ∧ tot_view.lt vl2 V) → ¬ ∃ (i2 : interaction) (s2 : stage), locked N i2 s2 vl2) ∧
   (SL = prevote → ¬ locked N IL precommit VL))
  → sent_lock_in_prepare N V IL SL VL

-- ####################################################################
-- # Decision Invariants
-- ####################################################################

-- If J is decided and has parent I, then I was decided at an earlier view
invariant [committed_implies_parent_committed]
  (decided M V J ∧ parent I J ∧ J ≠ genesis) →
    ∃ (u : view) (n : node), tot_view.lt u V ∧ decided n u I

-- Any non-genesis decision implies genesis was decided earlier
invariant [genesis_decided_first]
  (decided N V J ∧ J ≠ genesis) →
    ∃ (u : view) (m : node), tot_view.lt u V ∧ decided m u genesis

-- A decided non-genesis interaction requires the deciding node to hold a precommit lock
invariant [decision_requires_precommit_lock]
  (¬ ctx.is_byz N ∧ decided N V I ∧ I ≠ genesis) → locked N I precommit V

-- Decisions only at past or current view
invariant [decisions_not_from_higher_views]
  (cur_view N V ∧ decided N U I) → tot_view.le U V

-- Genesis was decided at view zero
invariant [genesis_view_zero]
  (¬ ctx.is_byz N ∧ decided N V I ∧ tot_view.zero = V) → I = genesis

-- Decision implies a quorum precommitted
invariant [decide_only_if_quorum_precommit]
  (¬ ctx.is_byz N ∧ decided N V I ∧ I ≠ genesis) →
    (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (n : node), ctx.member n s → precommitted_node n V I)

-- ####################################################################
-- # Ancestor/Parent Structural Invariants (additional)
-- ####################################################################

-- Each interaction has at most one parent
invariant [unique_parent]
  parent J I ∧ parent K I → J = K

-- No interaction is its own parent
invariant [parent_irreflexive]
  ¬ parent I I

-- Genesis has no parent
invariant [genesis_has_no_parent]
  ¬ parent I genesis

-- Height 0 among decided interactions ↔ genesis
invariant [genesis_height_zero]
  (height I = 0 ∧ (∃ (v : view) (n : node), decided n v I)) ↔ I = genesis

-- Parent edges only exist because of propose_extend
invariant [parent_only_if_proposed]
  parent I J ∧ J ≠ genesis → ∃ (n : node) (v : view), proposed_extend n v J

-- ####################################################################
-- # Operator/Quorum Invariants
-- ####################################################################

-- Operator prevote implies a quorum prevoted
invariant [prevote_operator_only_if_quorum_prevoted]
  ¬ ctx.is_byz N → (prevoted_operator N V I →
    (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (NC : node), ctx.member NC s → prevoted_node NC V I))

-- Precommit operator implies a quorum precommitted
invariant [precommit_operator_only_if_quorum_precommit]
  ¬ ctx.is_byz OP → (precommitted_operator OP V I →
    (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (n : node), ctx.member n s → precommitted_node n V I))

-- ####################################################################
-- # Uniqueness Invariants (additional)
-- ####################################################################

-- At most one sent lock per node per view
invariant [unique_lock_sent]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare N V IL1 SL1 VL1 ∧ sent_lock_in_prepare N V IL2 SL2 VL2) →
    (IL1 = IL2 ∧ SL1 = SL2 ∧ VL1 = VL2)

-- A node can only precommit one interaction per view
invariant [unique_precommit_nodes]
  (¬ ctx.is_byz N ∧ precommitted_node N V I ∧ precommitted_node N V J) → I = J

-- An operator can only prevote one interaction per view
invariant [unique_prevote_operator]
  (¬ ctx.is_byz OP ∧ prevoted_operator OP V I ∧ prevoted_operator OP V J) → I = J

-- An operator can only precommit one interaction per view
invariant [unique_precommit_operator]
  (¬ ctx.is_byz OP ∧ precommitted_operator OP V I ∧ precommitted_operator OP V J) → I = J

-- ####################################################################
-- # Additional Supporting Invariants
-- ####################################################################

-- Sent lock implies prepared
invariant [sent_lock_only_if_prepare]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare N V IL SL VL) → prepared_node N V

-- Propose stage implies a sent lock exists
invariant [stage_1]
  (cur_stage N V propose ∧ ¬ ctx.is_byz N) →
    (∃ (il : interaction) (sl : stage) (vl : view), sent_lock_in_prepare N V il sl vl)

-- Precommit stage implies a prevote lock exists
invariant [stage_3]
  (cur_stage N V precommit ∧ ¬ ctx.is_byz N) →
    (∃ (i : interaction), (prevoted_operator N V i ∨ precommitted_node N V i) ∧ locked N i prevote V)

-- Commit stage implies a precommit lock exists
invariant [stage_4]
  (cur_stage N V commit ∧ ¬ ctx.is_byz N) →
    (∃ (i : interaction), (precommitted_operator N V i ∨ decided N V i) ∧ locked N i precommit V)

-- Prepared operator not at view zero
invariant [prepared_operator_not_at_zero]
  (prepared_operator OP V ∧ ¬ ctx.is_byz OP) → V ≠ tot_view.zero

-- Proposal implies operator prepared
invariant [propose_only_if_operator_prepare]
  (¬ ctx.is_byz N ∧ (proposed_repropose N V I ∨ proposed_extend N V I)) → prepared_operator N V

-- Proposal requires a locked parent (for extend proposals)
invariant [propose_only_if_parent_locked]
  (¬ ctx.is_byz OP ∧ proposed_extend OP V J ∧ parent I J) →
    (∃ (u : view) (n : node) (s : stage), tot_view.le u V ∧ locked n I s u)

-- ####################################################################
-- # Main Safety Property
-- ####################################################################

safety [main_safety]
  ∀ (n1 n2 : node) (v1 v2 : view) (i1 i2 : interaction),
    (¬ ctx.is_byz n1 ∧ ¬ ctx.is_byz n2 ∧
     decided n1 v1 i1 ∧
     decided n2 v2 i2) →
    (ancestor i1 i2 ∨ ancestor i2 i1)

-- ####################################################################
-- # Height-Based Uniqueness Invariants
-- ####################################################################

-- Decided interactions at the same height are identical
-- (corollary of main_safety + no_ancestor_equal_height)
invariant [unique_decided_at_height]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   decided N1 V1 I1 ∧
   decided N2 V2 I2 ∧
   height I1 = height I2)
  → I1 = I2

-- Honest non-genesis locks at the same height are on the same interaction (cross-node)
-- (corollary of cross_node_unique_lock + lock_descendant_monotone + ancestor_height_strict)
invariant [unique_locked_at_height]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   locked N1 I1 S1 V1 ∧ locked N2 I2 S2 V2 ∧
   I1 ≠ genesis ∧ I2 ≠ genesis ∧
   height I1 = height I2)
  → I1 = I2

-- ####################################################################
-- # View-Height Monotonicity Invariants
-- ####################################################################

-- Single-node lock height monotonicity: locks at later views have >= height
-- (corollary of lock_descendant_monotone + ancestor_height_strict)
invariant [lock_height_monotone]
  (¬ ctx.is_byz N ∧
   locked N I1 S1 V1 ∧ locked N I2 S2 V2 ∧
   tot_view.le V1 V2)
  → height I1 ≤ height I2

-- Cross-node decision height monotonicity: decisions at later views have >= height
-- (corollary of main_safety + committed_implies_parent_committed + ancestor_height_strict)
invariant [decision_height_monotone]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   decided N1 V1 I1 ∧
   decided N2 V2 I2 ∧
   tot_view.lt V1 V2)
  → height I1 ≤ height I2

-- set_option maxHeartbeats 10000000
set_option veil.smt.timeout 1300
#gen_spec

set_option veil.printCounterexamples true

-- #model_check interpreted
-- { view := Fin 2,
--   node := Fin 2,
--   interaction := Fin 2,
--   nodeset := Fin 1,
--   stage := Fin 5 }
-- { tot_view := {
--     le := fun x y => x.val ≤ y.val,
--     lt := fun x y => x.val < y.val,
--     le_refl := by intro x; omega,
--     le_trans := by intro x y z h1 h2; omega,
--     le_antisymm := by intro x y h1 h2; ext; omega,
--     le_total := by intro x y; omega,
--     le_lt := by intro x y; simp only; constructor <;> intro h <;> (try ext) <;> omega,
--     next := fun x y => x.val + 1 = y.val,
--     next_def := by intro x y; simp only; sorry,
--     zero := 0,
--     zero_lt := by intro x; omega },
--   ctx := {
--     is_byz := fun _ => False,
--     member := fun _ _ => True,
--     supermajority := fun _ => True,
--     supermajorities_intersect_in_honest := by
--       intro s1 s2 ⟨_, _⟩; exact ⟨0, trivial, trivial, id⟩ },
--   prepare := 0,
--   propose := 1,
--   prevote := 2,
--   precommit := 3,
--   commit := 4 } (maxDepth := 3)

#check_action respond_prevote

-- #check_invariants

end IFPProtocolNL
