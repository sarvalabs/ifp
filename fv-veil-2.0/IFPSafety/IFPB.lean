/-
# Restricted IFP with full Byzantine actions (IFPB).

Target safety property

    safety [main_safety]
      ¬is_byz n1 ∧ ¬is_byz n2 ∧ decided n1 v1 i1 ∧ decided n2 v2 i2
        → ancestor i1 i2 ∨ ancestor i2 i1

The invariant set below is inherited from the proven honest-execution
model (IFP.lean lineage: SMT automation + 18 manual preservation
theorems). Under the Byzantine actions a known subset is EXPECTED RED
(enumerated in the comment block after byz_state) pending the
CTI-driven guard/weakening campaign.

Scope of this restricted IFP model:
- The two fixed participants share a single consensus set (context);
- Within a single epoch
- Synchronous view changes.
- Byzantine adversary (accuracy-first, two capability families): is_byz
  nodes run the full honest protocol PLUS
    message injection — additive injection of arbitrary rows they own in
                the 9 message relations (equivocation; signed messages
                cannot be unsent): byz_prevote, byz_precommit,
                byz_prepare, byz_send_lock, byz_prepare_operator,
                byz_repropose, byz_extend, byz_prevote_operator,
                byz_precommit_operator;
    state havoc — arbitrary set/unset of their own local state:
                byz_lock/byz_unlock, byz_decide/byz_undecide (per-cell,
                with honest-template ghost co-writes on set), and
                byz_state (bulk self-slice `:= *` over committed_ixn,
                cur_stage, and the collection caches). Uncertified
                tree-minting is then reachable through honest
                propose_extend with a faked frontier.
  Unforgeability is structural (byz writes only its own rows); the fault
  bound enters solely via
  IFPByzQuorum.supermajorities_intersect_in_honest (abstract n > 3f).
  Ghosts and interaction structure (parent/ancestor/height) are not
  byz-writable; cur_view (synchrony) and operator (leader schedule)
  remain environment-controlled.
-/

import Veil

veil module IFPProtocolNTDPH


class IFPByzQuorum (node : Type) (nset : Type) where
  is_byz : node → Prop
  member (n : node) (s : nset) : Prop
  supermajority (s : nset) : Prop

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

-- `stages`
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

-- Node relations
relation prepared_node : node → view → Bool
relation prevoted_node : node → view → interaction → Bool
relation precommitted_node : node → view → interaction → Bool

-- Interaction relations
relation parent : interaction → interaction → Bool
relation ancestor : interaction → interaction → Bool
function height : interaction → Nat

-- (Commented out by Claude — references the `height` FUNCTION (above) as a
-- type, which does not elaborate and blocks the whole build. Restore as
-- `node → Nat → Bool` if this relation is actually wanted.)
-- relation height_is_committed : node → height → Bool

-- ####################################################################
-- # Reproposal-run ghosts (extend → repropose* → extend chain)
-- # ----------------------------------------------------------------
-- # The lifecycle sketched as `x I V1 J V5 H`:
-- #   V1: propose_extend mints I (frontier at height h-1 → I at height h)
-- #   ··· I reproposed again and again while its highest lock is a
-- #       PREVOTE-QC at height h (operator frontier still at h-1)
-- #   commit of I discovered in prepare → frontier rises to I
-- #   V5: propose_extend mints I's child J at height h+1
-- # Both relations are WRITE-ONLY, set in lockstep at propose_extend, and
-- # only grow. The contiguity ("the SAME block is reproposed again and
-- # again") is deliberately NOT asserted here: that is cross-view
-- # lock-propagation (locks_analog_precommit), not a preserved-by-
-- # construction leaf — see the probe notes.
-- ####################################################################

-- "Interaction I was extended (born) at view V." Operator-erased projection
-- of proposed_extend, seeded with genesis @ view zero. Needed because the
-- extend_bridge update must look up the parent's birth view DECIDABLY — no
-- ∃ over a sort is allowed inside a `decide` update.
relation born_at : interaction → view → Bool

-- "Interaction C's PARENT was extended (born) at view VP." Together with
-- born_at C VC this is the minimal birth-view linkage — the parent identity P is
-- recoverable via `parent P C` and the height via `height C`, so this 2-ary
-- relation replaces the 5-ary extend_bridge. The half-open span (VP, VC] is the
-- parent's reproposal run plus the view its commit was discovered.
relation parent_born_at : interaction → view → Bool




-- Committed state
relation committed_ixn : node → interaction → Bool

-- ####################################################################
-- # Ghost Relations
-- ####################################################################

-- Height-indexed descendant ghosts (view-free; one accumulating set per node).
-- Write-only ghost state, maintained alongside the real `locked`/`decided`
-- updates. Signatures drop the participant param (cf. IFPJ) and the view index
-- (not needed). Only the descendant-indexed forms are kept; the plain
-- `locked_at_height`/`committed_at_height` were the A = genesis instance of
-- these, and the view-indexed `locked_at_view` / `proposed_for_descendant` /
-- `decided_for_descendant` ghosts were removed as redundant write-only state.
-- "Node N holds a lock on a descendant of A of height H."  ≡ ∃ I S V, locked N I S V ∧ ancestor A I ∧ height I = H
relation locked_descendant_at_height : node → interaction → Nat → Bool
-- "Node N decided a descendant of A of height H."  ≡ ∃ V I, decided N V I ∧ ancestor A I ∧ height I = H
relation committed_descendant_at_height : node → interaction → Nat → Bool

-- Ghost: a precommit-QC has been aggregated at (V, I) AND at least one node
-- has witnessed it via respond_precommit. Set by respond_precommit (whose
-- precondition guarantees a real supermajority of precommitted_node plus an
-- operator-side precommitted_operator witness, regardless of operator honesty).
-- Tied to that quorum by precommit_backed_fwd. No _bwd direction (avoids SMT
-- cost of asserting the ghost flip on every supermajority change in
-- respond_prevote).
relation precommit_backed : view → interaction → Bool

-- Operator's cached argmax over collected prepare responses. Set by
-- collect_prepares; consumed by the propose_* actions. Functional behaviour
-- (uniqueness per (op, v)) enforced by op_argmax_*_unique.
-- Mirrors Tendermint's `validValue`/`validRound` cached during prevote-handler
-- and consumed by `startRound`. Split into three 3-ary relations (rather than
-- one 5-ary) to keep #gen_spec's simp normalization tractable.
relation prepares_collected : node → view → Bool
relation op_argmax_ixn   : node → view → interaction → Bool
relation op_argmax_stage : node → view → stage → Bool
relation op_argmax_view  : node → view → view → Bool

-- Validator's cached argmax over received prepare responses (mirror of
-- op_argmax_*). Set by collect_recvd_locks; consumed by respond_propose_*.
-- Splits respond_propose's bundled quorum + argmax reasoning out of the
-- prevote actions into a single dedicated transition, so per-(invariant ×
-- prevote-action) proofs no longer have to re-derive the argmax.
relation recvd_collected   : node → view → Bool
relation argmax_recvd_ixn   : node → view → interaction → Bool
relation argmax_recvd_stage : node → view → stage → Bool
relation argmax_recvd_view  : node → view → view → Bool



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
  committed_ixn N I := decide $ (I = genesis);
  locked_descendant_at_height N A H := decide $ (A = genesis ∧ H = 0);
  committed_descendant_at_height N A H := decide $ (A = genesis ∧ H = 0);
  born_at I V := decide $ (I = genesis ∧ V = tot_view.zero);
  parent_born_at C VP := false;
  precommit_backed V I := false;
  prepares_collected N V := false;
  op_argmax_ixn   N V I := false;
  op_argmax_stage N V S := false;
  op_argmax_view  N V VL := false;
  recvd_collected   N V := false;
  argmax_recvd_ixn   N V I := false;
  argmax_recvd_stage N V S := false;
  argmax_recvd_view  N V VL := false;
}

-- ####################################################################
-- # Actions
-- ####################################################################

action set_view (v_cur v_next : view) {
  require ∀ (n : node), cur_view n v_cur
  require tot_view.next v_cur v_next
  cur_view N V := decide $ (V = v_next)
}

action pick_operator (op : node) (v : view) {
  require v ≠ tot_view.zero
  require cur_view op v
  require ∀ (n : node), ¬ operator n v
  operator op v := true
}

action operator_prepare (op : node) (v : view) {
  require v ≠ tot_view.zero
  require cur_view op v
  require cur_stage op v prepare
  require operator op v
  require ¬ prepared_operator op v
  prepared_operator op v := true
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
}

-- Operator collects prepare responses, computes the highest-view sent lock,
-- and stores it as `op_argmax`. The propose_* actions then just use `op_argmax`.
action collect_prepares (op : node) (v : view) (s : nodeset) (n_max : node)
    (ixn_max : interaction) (s_max : stage) (v_max : view) {
  -- (0) Sanity checks.
  require v ≠ tot_view.zero
  require cur_view op v
  require operator op v
  require prepared_operator op v
  require prepared_node op v
  require ¬ prepares_collected op v

  -- (1) Prepare-quorum witness: a quorum of nodes each sent a genuine
  -- prepare-response. NO per-member QC check here — only the highest lock's QC
  -- is verified, in the argmax witness below (step 3).
  require ctx.supermajority s
  require ∀ (n : node), ctx.member n s → (prepared_node n v ∧
    ∃ (vl : view) (ixnl : interaction) (sl : stage),
      sent_lock_in_prepare n v ixnl sl vl
      ∧ locked n ixnl sl vl
      ∧ tot_view.le vl v)

  -- (2) Argmax witness: n_max identifies the highest-view sent lock at v.
  require sent_lock_in_prepare n_max v ixn_max s_max v_max
  require locked n_max ixn_max s_max v_max
  require ∀ (n_l : node) (ixn_l : interaction) (s_l : stage) (v_l : view),
    sent_lock_in_prepare n_l v ixn_l s_l v_l → tot_view.le v_l v_max
  require ∀ (vl : view) (n : node) (i' : interaction) (s' : stage),
    (tot_view.lt v_max vl ∧ tot_view.lt vl v) →
      ¬ sent_lock_in_prepare n v i' s' vl

  -- (3) Verify the QC backing the highest lock.
  require ∃ (t_max : nodeset), ctx.supermajority t_max
    ∧ (s_max = prevote   → ∀ (nt : node), ctx.member nt t_max → prevoted_node    nt v_max ixn_max)
    ∧ (s_max = precommit → ∀ (nt : node), ctx.member nt t_max → precommitted_node nt v_max ixn_max)

  -- (4) Store the result.
  prepares_collected op v := true
  op_argmax_ixn   op v I  := decide $ (I = ixn_max)
  op_argmax_stage op v S  := decide $ (S = s_max)
  op_argmax_view  op v VL := decide $ (VL = v_max)
}

-- Repropose: highest lock is at committed_height + 1 and is from prevote stage
action propose_repropose (op : node) (v : view) (ci : interaction) {
  require v ≠ tot_view.zero
  require cur_view op v
  require operator op v
  require prepared_operator op v
  require prepares_collected op v
  require cur_stage op v propose
  require ∀ (ix : interaction), ¬ proposed_repropose op v ix
  require ∀ (ix : interaction), ¬ proposed_extend op v ix
  -- Use operator's argmax from collect_prepares.
  let ixn_max : interaction ← pick
  let s_max : stage ← pick
  let v_max : view ← pick
  require op_argmax_ixn   op v ixn_max
  require op_argmax_stage op v s_max
  require op_argmax_view  op v v_max
  -- heightDiff == 1 && PREVOTE → repropose
  require committed_ixn op ci
  require ancestor genesis ci
  require height ixn_max = height ci + 1
  require s_max = prevote
  proposed_repropose op v ixn_max := true;
}

-- Extend: all locks at committed_height → fresh proposal
action propose_extend (op : node) (v : view) (ixn_propose : interaction) (ci : interaction) {
  require v ≠ tot_view.zero
  require ∀ (j : interaction), ¬ (parent j ixn_propose ∨ parent ixn_propose j)
  require ∀ (j : interaction), (ixn_propose ≠ j → ¬ (ancestor j ixn_propose ∨ ancestor ixn_propose j))
  require height ixn_propose = 0
  require cur_view op v
  require operator op v
  require prepared_operator op v
  require prepares_collected op v
  require cur_stage op v propose
  require ixn_propose ≠ genesis
  require ∀ (ix : interaction), ¬ proposed_repropose op v ix
  require ∀ (ix : interaction), ¬ proposed_extend op v ix
  -- Use operator's argmax from collect_prepares
  let ixn_max : interaction ← pick
  let s_max : stage ← pick
  let v_max : view ← pick
  require op_argmax_ixn   op v ixn_max
  require op_argmax_stage op v s_max
  require op_argmax_view  op v v_max
  -- heightDiff == 0 → extend
  require committed_ixn op ci
  require ancestor genesis ci
  require height ixn_max = height ci
  require ci ≠ ixn_propose
  require ¬ (ancestor ci ixn_propose ∨ ancestor ixn_propose ci)
  parent ci ixn_propose := decide $ (ci ≠ ixn_propose);
  ancestor A ixn_propose := decide $ (ancestor A ixn_propose ∨ ancestor A ci ∨ A = ci ∨ A = ixn_propose);
  proposed_extend op v ixn_propose := true;
  height ixn_propose := height ci + 1;
  -- GHOST (reproposal-run): record I's birth + the parent→child extend bridge.
  -- `born_at ci VP` is a Bool lookup of the parent's birth view, so the bridge
  -- threads it without an existential. ci ≠ ixn_propose (required above), so the
  -- born_at write does not perturb the ci lookup; H = height ci + 1 avoids any
  -- dependence on the height update above.
  born_at I V := decide $ (born_at I V ∨ (I = ixn_propose ∧ V = v));
  -- C's parent is ci; ci was born at the VP for which born_at ci VP holds.
  parent_born_at C VP := decide $ (parent_born_at C VP ∨ (C = ixn_propose ∧ born_at ci VP));
}

-- Validator-side analogue of collect_prepares.
action collect_recvd_locks (n : node) (v : view) (s : nodeset) (n_max : node)
    (ixn_max : interaction) (s_max : stage) (v_max : view) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v propose
  require prepared_node n v
  require ¬ recvd_collected n v

  -- Prepare-quorum witness: a quorum of nodes each sent a genuine (locked)
  -- prepare-response. NO per-member QC check here — only the highest lock's QC
  -- is verified, in the argmax witness below (step 3).
  require ctx.supermajority s
  require ∀ (m : node), ctx.member m s → (prepared_node m v ∧
    ∃ (vl : view) (ixnl : interaction) (sl : stage),
      sent_lock_in_prepare m v ixnl sl vl
      ∧ locked m ixnl sl vl
      ∧ tot_view.le vl v)

  -- Argmax witness: n_max identifies the highest-view sent lock at v, and
  -- (step 3) that highest lock is verified QC-backed (`t_max` supermajority).
  require sent_lock_in_prepare n_max v ixn_max s_max v_max
  require locked n_max ixn_max s_max v_max
  require ∀ (n_l : node) (ixn_l : interaction) (s_l : stage) (v_l : view),
    sent_lock_in_prepare n_l v ixn_l s_l v_l → tot_view.le v_l v_max
  -- No sent_lock at views strictly above v_max (pure ∀ form, EPR).
  require ∀ (vl : view) (n' : node) (i' : interaction) (s' : stage),
    (tot_view.lt v_max vl ∧ tot_view.lt vl v) →
      ¬ sent_lock_in_prepare n' v i' s' vl
  require ∃ (t_max : nodeset), ctx.supermajority t_max
    ∧ (s_max = prevote   → ∀ (nt : node), ctx.member nt t_max → prevoted_node    nt v_max ixn_max)
    ∧ (s_max = precommit → ∀ (nt : node), ctx.member nt t_max → precommitted_node nt v_max ixn_max)

  -- Store the result.
  recvd_collected n v := true
  argmax_recvd_ixn   n v I  := decide $ (I = ixn_max)
  argmax_recvd_stage n v S  := decide $ (S = s_max)
  argmax_recvd_view  n v VL := decide $ (VL = v_max)
}

-- Repropose branch: argmax is a prevote-stage lock at the same interaction
-- the operator is reproposing.
action respond_propose_repropose (n : node) (v : view) (ixn : interaction) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v propose
  require ∃ (op : node), operator op v ∧ proposed_repropose op v ixn
  require ∀ (i : interaction), ¬ prevoted_node n v i
  require ixn ≠ genesis
  require recvd_collected n v
  let ixn_max : interaction ← pick
  let s_max : stage ← pick
  let v_max : view ← pick
  require argmax_recvd_ixn   n v ixn_max
  require argmax_recvd_stage n v s_max
  require argmax_recvd_view  n v v_max
  require s_max = prevote
  require ixn = ixn_max
  require height ixn = height ixn_max
  prevoted_node n v ixn := true
  cur_stage n v S := decide $ (S = prevote)
}

-- Extend branch: argmax is a precommit-stage lock and the operator is
-- proposing a fresh child of the locked interaction.
action respond_propose_extend (n : node) (v : view) (ixn : interaction) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v propose
  require ∃ (op : node), operator op v ∧ proposed_extend op v ixn
  require ∀ (i : interaction), ¬ prevoted_node n v i
  require ixn ≠ genesis
  require recvd_collected n v
  let ixn_max : interaction ← pick
  let s_max : stage ← pick
  let v_max : view ← pick
  require argmax_recvd_ixn   n v ixn_max
  require argmax_recvd_stage n v s_max
  require argmax_recvd_view  n v v_max
  require s_max = precommit
  require ixn ≠ ixn_max
  require parent ixn_max ixn
  require height ixn = height ixn_max + 1
  prevoted_node n v ixn := true
  cur_stage n v S := decide $ (S = prevote)
}

action operator_prevote (op : node) (v : view) (ixn : interaction) (s : nodeset) {
  require v ≠ tot_view.zero
  require ∀ (i : interaction), ¬ prevoted_operator op v i
  require cur_view op v
  require operator op v
  require cur_stage op v prevote
  require ctx.supermajority s
  require ∀ (n : node), ctx.member n s → prevoted_node n v ixn
  prevoted_operator op v ixn := true
}

action respond_prevote (n : node) (v : view) (ixn : interaction) (s : nodeset) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v prevote
  require ∃ (op : node), operator op v ∧ prevoted_operator op v ixn
  require ctx.supermajority s
  require ∀ (nc : node), ctx.member nc s → prevoted_node nc v ixn
  precommitted_node n v ixn := true
  if ( ¬ ∃ (u : view), (tot_view.le u v ∧ locked n ixn precommit u) ) then
    locked n ixn prevote v := true;
    -- GHOST: new prevote lock at height (height ixn), on every ancestor A of ixn.
    locked_descendant_at_height n A H := decide $ (locked_descendant_at_height n A H ∨ (ancestor A ixn ∧ H = height ixn));
  cur_stage n v S := decide $ (S = precommit)
}

action operator_precommit (op : node) (v : view) (ixn : interaction) (s : nodeset) {
  require v ≠ tot_view.zero
  require cur_view op v
  require operator op v
  require cur_stage op v precommit
  require ctx.supermajority s
  require ∀ (nc : node), ctx.member nc s → precommitted_node nc v ixn
  precommitted_operator op v ixn := true
}

action respond_precommit (n : node) (v : view) (ixn : interaction) (s : nodeset) {
  require v ≠ tot_view.zero
  require cur_view n v
  require cur_stage n v precommit
  require ∃ (op : node), operator op v ∧ precommitted_operator op v ixn
  require ctx.supermajority s
  require ∀ (nc : node), ctx.member nc s → precommitted_node nc v ixn
  -- A node decides an interaction at most once across all views.
  require ∀ (v_old : view), ¬ decided n v_old ixn
  -- Ghost set (monotonic): first responding node flips it on; subsequent
  -- responders re-write `true`. The precommitted_operator/supermajority
  -- preconditions above are exactly precommit_backed's witness — equivalent
  -- to operator_precommit's old write, just deferred to the first witnessing.
  precommit_backed v ixn := true
  locked n ixn precommit v := true;
  -- GHOST: new precommit lock at height (height ixn), on every ancestor A of ixn.
  locked_descendant_at_height n A H := decide $ (locked_descendant_at_height n A H ∨ (ancestor A ixn ∧ H = height ixn));
  decided n v ixn := true
  -- GHOST: node decided a descendant of A at height (height ixn), on every ancestor A of ixn.
  committed_descendant_at_height n A H := decide $ (committed_descendant_at_height n A H ∨ (ancestor A ixn ∧ H = height ixn));
  -- Update committed interaction only if this is a newer decision
  if (∃ (ci_old : interaction), committed_ixn n ci_old ∧ height ixn > height ci_old) then
    committed_ixn n I := decide $ (I = ixn);
  cur_stage n v S := decide $ (S = commit)
}

-- ####################################################################
-- # Byzantine actions (accuracy-first model).
-- # A Byzantine node controls exactly its OWN rows (self-row confinement
-- # = unforgeable signatures / no writes to other processes' memory) in
-- # every non-ghost, non-interaction-structure relation, via two actions:
-- #   messages — ADDITIVE only (a signed message in the network cannot
-- #              be unsent): 9 per-relation injector actions; repeated
-- #              firing yields arbitrary finite injection + equivocation.
-- #   state    — set OR unset arbitrarily: per-cell actions for the two
-- #              ghost-shadowed relations (byz_lock/byz_unlock,
-- #              byz_decide/byz_undecide — the set direction co-writes
-- #              the descendant ghost with the verbatim honest template;
-- #              ∃-over-sort inside `decide` does not elaborate, so bulk
-- #              havoc cannot maintain the ghosts), plus one bulk
-- #              self-slice havoc (byz_state) for the ghost-free state
-- #              relations. Repeated firing ≡ arbitrary two-sided havoc.
-- # Encoding note: the canonical `transition` idiom (ReliableBroadcast)
-- # is unusable in this module — #gen_spec extraction executes a
-- # transition by enumerating post-states, and `height : interaction →
-- # Nat` makes the state non-enumerable. Imperative actions extract
-- # compositionally and match the in-CI encoding surface of
-- # veil-2.0-preview (small arities, pinned-slice `:= *`).
-- # Byz nodes ALSO run every honest action (no honest action carries a
-- # ¬is_byz require) — e.g. a byz operator that fakes its own
-- # committed_ixn / argmax cache / cur_stage via byz_state can then pass
-- # propose_extend's gates honestly and mint a fresh child of ANY known
-- # block: uncertified tree extension is reachable without byz ever
-- # writing parent/ancestor/height directly.
-- # NOT byz-writable: ghost relations (precommit_backed, the two
-- # descendant-height ghosts, born_at, parent_born_at) — model-side
-- # bookkeeping, co-updated in lockstep below where byz sets shadowed
-- # state; interaction structure (parent/ancestor/height/genesis) —
-- # hash-chain facts, written only by propose_extend; environment state
-- # (cur_view = synchronous view clock, operator = leader schedule).
-- ####################################################################

action byz_prevote (n : node) (v : view) (ixn : interaction) {
  require ctx.is_byz n
  prevoted_node n v ixn := true
}

action byz_precommit (n : node) (v : view) (ixn : interaction) {
  require ctx.is_byz n
  precommitted_node n v ixn := true
}

action byz_prepare (n : node) (v : view) {
  require ctx.is_byz n
  prepared_node n v := true
}

action byz_send_lock (n : node) (v : view) (il : interaction) (sl : stage) (vl : view) {
  require ctx.is_byz n
  sent_lock_in_prepare n v il sl vl := true
}

action byz_prepare_operator (op : node) (v : view) {
  require ctx.is_byz op
  prepared_operator op v := true
}

action byz_repropose (op : node) (v : view) (ixn : interaction) {
  require ctx.is_byz op
  proposed_repropose op v ixn := true
}

action byz_extend (op : node) (v : view) (ixn : interaction) {
  require ctx.is_byz op
  proposed_extend op v ixn := true
}

action byz_prevote_operator (op : node) (v : view) (ixn : interaction) {
  require ctx.is_byz op
  prevoted_operator op v ixn := true
}

action byz_precommit_operator (op : node) (v : view) (ixn : interaction) {
  require ctx.is_byz op
  precommitted_operator op v ixn := true
}

action byz_lock (n : node) (ixn : interaction) (s : stage) (v : view) {
  require ctx.is_byz n
  locked n ixn s v := true;
  locked_descendant_at_height n A H := decide $ (locked_descendant_at_height n A H ∨ (ancestor A ixn ∧ H = height ixn))
}

action byz_unlock (n : node) (ixn : interaction) (s : stage) (v : view) {
  require ctx.is_byz n
  locked n ixn s v := false
}

/-
3f+1
n - sends highest lock (honest)
nb - sends another lock for invalid interaction of same height stage (byz)

-/






action byz_decide (n : node) (v : view) (ixn : interaction) {
  require ctx.is_byz n
  decided n v ixn := true;
  -- GHOST: verbatim honest template (cf. respond_precommit).
  committed_descendant_at_height n A H := decide $ (committed_descendant_at_height n A H ∨ (ancestor A ixn ∧ H = height ixn))
}

action byz_undecide (n : node) (v : view) (ixn : interaction) {
  require ctx.is_byz n
  decided n v ixn := false
}

-- Bulk self-slice havoc of the ghost-free state relations (committed
-- frontier, stage pointer, collection caches). Two-sided by construction:
-- `:= *` on the n-slice sets and unsets arbitrarily in one step.
-- precommit_backed is NOT byz-writable: it means "a real precommit QC was
-- witnessed" and byz reaches its writer only through honest-shell
-- respond_precommit, whose quorum requires hold for byz executors too.
action byz_state (n : node) {
  require ctx.is_byz n
  committed_ixn n I := *;
  cur_stage n V S := *;
  prepares_collected n V := *;
  op_argmax_ixn n V I := *;
  op_argmax_stage n V S := *;
  op_argmax_view n V VL := *;
  recvd_collected n V := *;
  argmax_recvd_ixn n V I := *;
  argmax_recvd_stage n V S := *;
  argmax_recvd_view n V VL := *
}


safety [main_safety]
  ∀ (n1 n2 : node) (v1 v2 : view) (i1 i2 : interaction),
    (¬ ctx.is_byz n1 ∧ ¬ ctx.is_byz n2 ∧
     decided n1 v1 i1 ∧
     decided n2 v2 i2) →
    (ancestor i1 i2 ∨ ancestor i2 i1)

-- ####################################################################
-- # BYZANTINE REPAIR STATUS
-- #
-- # Triage rule. A `¬is_byz` guard repairs an invariant exactly when the
-- # byz-written atom sits in a POSITIVE HYPOTHESIS: the guard shields the
-- # antecedent from injected rows (byz_prevote/precommit/prepare/send_lock/
-- # *_operator/repropose/extend/lock/decide) and from the two-sided
-- # byz_state slice havoc. A guard does NOT repair a POSITIVE CONCLUSION
-- # that byz_unlock / byz_undecide retracts — there the guard strengthens
-- # the goal and makes matters worse; those need an honest witness named in
-- # the conclusion, or a QC-form weakening.
-- ####################################################################
--
-- REPAIRED by ¬is_byz guard (48 — applied in place; invariant ORDER and
-- COUNT are unchanged, so the positional `hinv` chains in the manual
-- theorems below still address the same conjuncts):
--   [byz_send_lock/byz_prepare] locks_sent_only_if_locked, highest_lock_sent,
--     sent_lock_prepare_implies_cur_view_ge (now literally
--     sent_lock_only_at_past_view — redundant, but NOT deleted: deletion
--     would shift every positional proof), sent_lock_only_if_prepare_unrestricted
--     (now literally sent_lock_only_if_prepare — ditto),
--     recvd_collected_implies_(bounded_)prepare_quorum (double guard: the
--     collector N *and* the quorum member m — an honest member's `locked`
--     row is never retracted and its sent_lock row is written once by
--     respond_prepare's slice-write; this is also the form LAP's proof
--     wants, since quorum intersection hands it an honest member).
--   [byz_lock/byz_unlock] lock_stage_valid, no_lock_without_parent,
--     locked_descends_from_genesis, locked_height_positive,
--     genesis_lock_only_at_zero, lock_at_zero_is_genesis_precommit,
--     genesis_lock_existence, prevote_lock_only_if_quorum_prevoted,
--     precommit_lock_implies_precommit_backed (honest precommit locks are
--     written ONLY by respond_precommit, atomically with precommit_backed).
--   [byz_decide/byz_undecide] no_decide_without_parent, decided_height_positive,
--     genesis_decided_first (conclusion witness m := the now-honest N),
--     genesis_decided_at_zero, decisions_not_from_higher_views,
--     genesis_height_zero (guard pushed inside the ∃-decider; the ↔ had to
--     be split — the ← direction can no longer supply `∃ honest n. decided`
--     because NOTHING in this model asserts an honest node exists, so it
--     now yields only `height genesis = 0`, which is all its consumers used),
--     decide_only_if_precommit_operator (the guard was DANGLING on an unused
--     N while the decider OP ran free — rebound to OP).
--   [byz_state] unique_committed_ixn, node_has_committed_ixn,
--     committed_ixn_implies_precommit_backed, recvd_collected_at_past_view,
--     the 9 op_argmax_* and 9 argmax_recvd_* cache invariants.
--   [byz_repropose/byz_extend] proposed_extend_view_bound,
--     proposed_repropose_view_bound, proposed_height_positive.
--   [byz_decide ghost] committed_descendant_at_height_implies_locked_descendant
--     (byz_decide co-writes ONLY committed_descendant_at_height while
--     respond_precommit writes both ghosts; guarding N sidesteps the
--     asymmetry — the alternative fix is to mirror respond_precommit's
--     locked_descendant_at_height co-write into byz_decide).
--
-- COMMENTED OUT — a guard cannot fix these (10). Each is struck out in place
-- below with a `##### COMMENTED OUT (Byzantine-false) #####` banner giving the
-- counterexample and the intended repair. The invariant conjunction went
-- 182 -> 172. NOTE: the 18 manual theorems all live inside the `/- ... -/`
-- archive block that opens just below #gen_spec, so none of them is live code
-- and nothing here breaks the build. They are still indexed POSITIONALLY
-- (`hinv.2.2...1`), so to keep the archive usable on revival every chain was
-- REMAPPED to the new numbering (12 chains rewritten, 20 `#N` annotations
-- updated). Five were additionally struck out inside the archive: four proved
-- a now-removed invariant, and
-- propose_repropose_proposed_repropose_parent_matches_committed CONSUMED the
-- removed reproposed_argmax_parent_committed — the invariant it proved
-- SURVIVES, so on revival it must be re-derived without that conjunct (or left
-- to SMT).
--
-- Also owed on revival: the guard campaign above changed the STATEMENT of
-- invariants that some archived proofs prove or consume —
--   PROVE a now-guarded invariant, so their goal changed —
--     respond_prevote_committed_descendant_at_height_implies_locked_descendant,
--     collect_recvd_locks_recvd_collected_implies_bounded_prepare_quorum,
--     respond_prevote_recvd_collected_implies_bounded_prepare_quorum.
--   CONSUME a now-guarded invariant, so the extracted `have` carries an extra
--   ¬is_byz premise to discharge —
--     respond_propose_extend_locks_analog_precommit and
--     respond_propose_repropose_locks_analog_precommit (#3, #65, #69),
--     propose_extend_locked_descendant_at_height_bwd (#166).
--
-- The 10, and why a guard is the wrong tool for each:
--   (a) positive conclusion retracted by byz_unlock/byz_undecide, needs an
--       honest witness named in the conclusion:
--         op_argmax_is_highest_lock, argmax_recvd_is_highest_lock,
--         prevote_justified_by_highest_lock  (the argmax holder genuinely
--           CAN be Byzantine, so guarding the witness would be false);
--         propose_only_if_parent_locked  (true, and the honest witness is OP
--           itself via committed_ixn_precommit_locked — restate as
--           `∃ u. locked OP I precommit u`);
--         precommit_backed_implies_decided  (respond_precommit writes
--           `decided` only for its executor; a byz executor then undecides).
--   (b) conclusion asserts the precommit_backed GHOST where only a real
--       vote-QC survives — needs QC-form weakening:
--         extended_argmax_committed, reproposed_argmax_parent_committed,
--         committed_implies_parent_committed (#56),
--         parent_implies_parent_precommit_backed (#180 — via the honest-shell
--         mint: byz_state fakes committed_ixn, then HONEST propose_extend
--         writes `parent` for an uncertified block; note `parent` carries no
--         node argument, so there is nothing to guard).
--   (c) needs an action-level require, not an invariant edit:
--         reproposal_extends_decided_parent — its `VM < V` conjunct dies
--         because byz_send_lock may report a lock at a view ≥ the current
--         one and collect_recvd_locks' argmax witness n_max need not belong
--         to the prepare-quorum s (only members carry `vl ≤ v`). Real
--         validators reject such a report: add `require tot_view.lt v_max v`
--         to collect_prepares and collect_recvd_locks.
--
-- NOT red, but the honest-model proof route is gone — these now need quorum
-- intersection (supermajorities_intersect_in_honest applied to the two
-- quorums, then the node-local uniqueness lemmas unique_prevote_nodes /
-- unique_precommit_nodes): same_view_precommit_prevote_agree,
-- precommit_qc_unique_at_view, unique_prevote_lock_in_view,
-- precommit_node_lock_consistency, cross_node_unique_lock,
-- unique_locked_at_height. Expect manual theorems here.


invariant [locks_analog_precommit]
  ∀ (V V2 : view) (I J : interaction) (NP : node),
    (¬ ctx.is_byz NP ∧
     precommit_backed V I ∧ I ≠ genesis ∧ J ≠ genesis ∧
     prevoted_node NP V2 J ∧
     tot_view.lt V V2) →
    (J = I ∨ ancestor I J)


invariant [argmax_recvd_ixn_descends_from_precommit_backed_at_bounded_view]
  ∀ (U V_act V_max : view) (I IM : interaction) (N : node),
    (¬ ctx.is_byz N ∧
     precommit_backed U I ∧ I ≠ genesis ∧
     argmax_recvd_ixn N V_act IM ∧ argmax_recvd_view N V_act V_max ∧
     tot_view.lt U V_act ∧ tot_view.le U V_max) →
    (I = IM ∨ ancestor I IM)

-- [RISK 1] prepare-quorum members captured by recvd_collected have sent-lock views
-- bounded by the cached argmax view VMAX. Discharged at collect_rx`ecvd_locks (its
-- supermajority s + per-member sent_lock + the argmax-dominance require give
-- VL ≤ VMAX); monotone elsewhere. Feeds the gap case of locks_analog_precommit.
invariant [recvd_collected_implies_bounded_prepare_quorum]
  (¬ ctx.is_byz N ∧ recvd_collected N VACT ∧ argmax_recvd_view N VACT VMAX) →
    ∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (m : node), ¬ ctx.is_byz m → ctx.member m s →
        prepared_node m VACT ∧
        ∃ (IL : interaction) (SL : stage) (VL : view),
          sent_lock_in_prepare m VACT IL SL VL ∧ locked m IL SL VL ∧
          tot_view.le VL VMAX


-- ####################################################################
-- # ===== ACTIVE FRONTIER — VERIFY FIRST (this session) =====
-- # Invariants under active check after restoring RISK1 + dropping the false
-- # reproposal block(B). Front-loaded so #check_invariants reports their status
-- # before the heartbeat/SMT budget is spent on the stable base below. The
-- # qc_descent cluster (reproposed_relock, RISK3, qc_anchored_*, reproposal,
-- # B4/B5) follows immediately, so the whole verify-set is contiguous here.
-- # NOTE: locks_analog_decided stays RED until locks_analog_precommit (LAP,
-- # still commented further down) is restored — that is the next step, expected.
-- ####################################################################


-- -- B3a (repropose carrier): prevote-stage argmax ⇒ J itself prevote-certified at VM.
-- invariant [qc_anchored_repropose]
--   (¬ ctx.is_byz N ∧ prevoted_node N V2 J ∧ J ≠ genesis ∧ V2 ≠ tot_view.zero ∧
--    argmax_recvd_stage N V2 prevote) →
--     ∃ (VM : view), argmax_recvd_view N V2 VM ∧ tot_view.lt VM V2 ∧
--       (∃ (s : nodeset), ctx.supermajority s ∧
--           ∀ (m : node), ctx.member m s → prevoted_node m VM J)

-- -- B3b (extend carrier): precommit-stage argmax ⇒ J's parent P precommit-certified at VM.
-- invariant [qc_anchored_extend]
--   (¬ ctx.is_byz N ∧ prevoted_node N V2 J ∧ J ≠ genesis ∧ V2 ≠ tot_view.zero ∧
--    argmax_recvd_stage N V2 precommit) →
--     ∃ (VM : view), argmax_recvd_view N V2 VM ∧ tot_view.lt VM V2 ∧
--       (∃ (P : interaction) (s : nodeset), ctx.supermajority s ∧ parent P J ∧
--           ∀ (m : node), ctx.member m s → precommitted_node m VM P)


-- ####################################################################
-- # Argmax ↔ committed-frontier anchoring (proposal side)
-- # ----------------------------------------------------------------
-- # The operator's cached argmax, when it drives a proposal, is anchored at the
-- # committed frontier by the height-based decision logic:
-- #   repropose (height argmax = committed+1): argmax I is a CHILD of committed,
-- #     so I's parent J was committed (precommit-QC witnessed). Near-leaf via
-- #     no_proposal_without_parent + parent_height +
-- #     proposed_repropose_parent_matches_committed + decided_implies_precommit_backed.
-- #   extend (height argmax = committed): argmax I IS the committed interaction.
-- #     Guarded to precommit-stage argmax (matches respond_propose_extend's
-- #     `require s_max = precommit`) so it discharges via op_argmax_qc_backed +
-- #     op_argmax_is_highest_lock + precommit_lock_implies_precommit_backed +
-- #     unique_precommit_backed_at_height — WITHOUT entangling LAP (the prevote-
-- #     stage sub-case would restate no-fork).
-- # "committed" = precommit_backed (monotone). committed_ixn OP is deliberately
-- # NOT used: it is overwritten when OP later decides higher, which would break
-- # preservation at respond_precommit.
-- ####################################################################

-- repropose: argmax I (prevote-stage at argmax view U) sits one height above
-- committed ⇒ I's parent J was committed at some W strictly below U.
-- UNGATED (2026-06-30): `proposed_repropose OP V I` hypothesis dropped so this
-- fires from op_argmax on the PRE-state (needed by propose_repropose's
-- proposed_repropose_parent_matches_committed obligation, whose action precondition
-- `∀ ix, ¬ proposed_repropose op v ix` falsified the old gated form). Vestigial:
-- the conclusion is derived from op_argmax_qc_backed + op_argmax_is_highest_lock,
-- not from proposed_repropose. Only weakens hypotheses ⇒ no consumer breaks; its
-- own preservation must be re-checked (now fires whenever op_argmax is prevote-stage).
-- ##### COMMENTED OUT (Byzantine-false) #####
-- FALSE under byz: same QC-vs-ghost gap as extended_argmax_committed,
-- applied to the parent. Repair: QC-form conclusion.
-- invariant [reproposed_argmax_parent_committed]
--   (¬ ctx.is_byz OP ∧
--    op_argmax_ixn OP V I ∧ op_argmax_stage OP V prevote ∧
--    op_argmax_view OP V U ∧ I ≠ genesis) →
--     ∃ (J : interaction) (W : view), parent J I ∧ tot_view.lt W U ∧ precommit_backed W J


-- extend: precommit-stage argmax I sits at committed height ⇒ I itself committed.
-- ##### COMMENTED OUT (Byzantine-false) #####
-- FALSE under byz even with the honest-operator guard: collect_prepares step
-- 3 verifies a real precommit QC, but a QC is strictly weaker than the
-- precommit_backed GHOST (nobody need have run respond_precommit). The
-- honest route died with precommit_lock_implies_precommit_backed, since
-- byz_lock plants precommit locks. Repair: weaken the conclusion to QC form.
-- invariant [extended_argmax_committed]
--   (¬ ctx.is_byz OP ∧ proposed_extend OP V IX ∧
--    op_argmax_ixn OP V I ∧ op_argmax_stage OP V precommit ∧
--    op_argmax_view OP V U ∧ I ≠ genesis) →
--     precommit_backed U I

-- ####################################################################
-- # Single-step lock propagation (IFP analog of paper Lemma 3)
-- # ----------------------------------------------------------------
-- # When I is committed at V (precommit-QC witnessed), the validator M that
-- # collects prepares in the immediately-next view VN = next(V) discovers it as
-- # its cached highest lock. The two branches are NOT symmetric in soundness:
-- #
-- #  extend: I is a FRESH child (propose_extend creates it with height 0 / no
-- #    parent), so it was never committed before V (extended_ixn_not_committed_before).
-- #    Then every honest member of V's precommit-quorum holds its I-lock at exactly
-- #    V (a precommit lock below V is impossible), forcing VM = V EXACTLY.
-- #
-- #  repropose: I is an EXISTING interaction that may already have been committed
-- #    at some U < V (a lagging/Byzantine operator can repropose it). The honest
-- #    quorum members then kept their OLD precommit lock at U and report U, so
-- #    VM = V can FAIL. Conclusion weakened: the argmax discovers I at SOME
-- #    committed view VM ≤ V.  RESIDUAL RISK — even IM = I / precommit_backed VM I
-- #    are only sound if a higher-view QC on a different/descendant interaction at
-- #    an intermediate U<W<V is excluded; that exclusion leans on the honest-N
-- #    prevote-stage-argmax premise via lock-propagation (circular under Veil's
-- #    frame). If the build reds on IM = I, fall back to descent (≈ RISK3).
-- #
-- # DISCHARGE: collect_recvd_locks, via precommit_backed_fwd × the action's
-- # prepare-quorum → honest m*. NOT leaves — expect /manual-prove. Extend also
-- # consumes extended_ixn_not_committed_before to kill the below-V re-precommit.
-- ####################################################################

-- Fresh-child leaf: an extended interaction is brand new at its proposal view, so
-- it was never proposed (hence never committed) at any earlier view. Substantive
-- at propose_extend (fresh preconditions: no parent ⇒ never proposed ⇒ never
-- precommit_backed); preserved at respond_precommit because precommit_backed is
-- only written at cur_view ≥ V (proposed_extend_view_bound).
invariant [extended_ixn_not_committed_before]
  (¬ ctx.is_byz OP ∧ proposed_extend OP V I) → ∀ (U : view), tot_view.lt U V → ¬ precommit_backed U I

-- repropose branch: I (existing) re-proposed at V. VM = V can fail when I was
-- already committed at U < V (re-precommitters report U) ⇒ weakened to VM ≤ V.
-- invariant [reproposed_committed_propagates_to_next_argmax]
--   (¬ ctx.is_byz N ∧ ¬ ctx.is_byz M ∧
--    argmax_recvd_stage N V prevote ∧
--    prevoted_node N V I ∧
--    proposed_repropose OP V I ∧
--    precommit_backed V I ∧ I ≠ genesis ∧
--    tot_view.next V VN ∧
--    argmax_recvd_ixn M VN IM ∧ argmax_recvd_view M VN VM) →
--     (IM = I ∧ VM = V ∧ precommit_backed VM I)


-- -- extend branch: I is a FRESH child ⇒ never committed before V ⇒ VM = V exact.
-- invariant [extended_committed_propagates_to_next_argmax]
--   (¬ ctx.is_byz N ∧ ¬ ctx.is_byz M ∧
--    argmax_recvd_stage N V precommit ∧
--    prevoted_node N V I ∧
--    proposed_extend OP V I ∧
--    precommit_backed V I ∧ I ≠ genesis ∧
--    tot_view.next V VN ∧
--    argmax_recvd_ixn M VN IM ∧ argmax_recvd_view M VN VM) →
--     (IM = I ∧ VM = V)

-- B2: an honest prevote agrees with the prevoter's cached argmax (prevote-stage
-- ⇒ J is the argmax; precommit-stage ⇒ J's parent is the argmax). Descent-free.
invariant [prevote_matches_argmax]
  (¬ ctx.is_byz N ∧ prevoted_node N V2 J ∧ J ≠ genesis ∧ V2 ≠ tot_view.zero) →
    ∃ (IM : interaction), argmax_recvd_ixn N V2 IM ∧
      ((argmax_recvd_stage N V2 prevote ∧ J = IM) ∨
       (argmax_recvd_stage N V2 precommit ∧ parent IM J))

-- Strict-view feeder of main_safety. Expected RED until LAP is restored (no live
-- supplier for the ancestor step at respond_precommit) — kept at top to surface it.
invariant [locks_analog_decided]
  ∀ (V V2 : view) (I I2 : interaction) (N1 N2 : node),
    (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
     I ≠ genesis ∧ I2 ≠ genesis ∧
     decided N1 V I ∧ decided N2 V2 I2 ∧
     tot_view.lt V V2) →
    (I = I2 ∨ ancestor I I2)




-- Companion (relock side): the same reproposed block gets prevote-locked again
-- at the reproposal view V. When I is reproposed at V (proposed_repropose OP V I)
-- and some node N holds a prevote lock on that same I at exactly V, that lock
-- traces back to the operator's repropose decision: I was the cached argmax
-- interaction at prevote stage, with some argmax view VM. propose_repropose set
-- proposed_repropose op v ixn_max only after requiring op_argmax_ixn op v ixn_max,
-- op_argmax_stage op v prevote, op_argmax_view op v v_max; the op_argmax cache is
-- frozen once prepares_collected (collect_prepares requires ¬ prepares_collected),
-- so these argmax facts persist for all later locks acquired at V.
invariant [reproposed_relock_at_view_implies_argmax]
  (¬ ctx.is_byz OP ∧ proposed_repropose OP V I ∧ locked N I prevote V) →
    ∃ (VM : view),
      op_argmax_ixn OP V I ∧ op_argmax_view OP V VM ∧ op_argmax_stage OP V prevote





-- B3a+ (reproposal prevote-QC anchor): when an honest N prevotes J in the repropose
-- branch (cached argmax is prevote-stage), J is prevote-QC'd at an earlier view VM < V.
-- The former block (B) (parent P precommit_backed AND decided) was REMOVED as FALSE:
--   (i) Byzantine operator — pick_operator/propose_repropose carry no ¬is_byz op
--       guard, so a Byzantine op reproposes a real-QC'd ixn whose parent (unique) was
--       never decided/precommit_backed (the ties are all ¬is_byz OP-guarded).
--   (ii) Genesis parent — an honest height-1 repropose has parent = genesis, and
--        precommit_backed VP genesis is unsatisfiable (precommit_backed needs v ≠ zero).
-- What remains is strictly weaker than qc_anchored_repropose (lacks the
-- argmax_recvd_view conjunct), hence REDUNDANT — safe to delete wholesale once green.
-- ##### COMMENTED OUT (Byzantine-false) #####
-- FALSE under byz: the `VM < V` conjunct dies because byz_send_lock may
-- report a lock at a view >= the current one, and collect_recvd_locks'
-- argmax witness n_max need not be in the prepare-quorum s (only members
-- carry `vl <= v`). Repair is at the ACTION level: add `require tot_view.lt
-- v_max v` to collect_prepares and collect_recvd_locks.
-- invariant [reproposal_extends_decided_parent]
--   (¬ ctx.is_byz N ∧ prevoted_node N V J ∧ J ≠ genesis ∧ V ≠ tot_view.zero ∧
--    argmax_recvd_stage N V prevote) →
--     (∃ (VM : view), tot_view.lt VM V ∧
--        ∃ (s : nodeset), ctx.supermajority s ∧
--          ∀ (m : node), ctx.member m s → prevoted_node m VM J)


-- B4: same-view precommit-QC and prevote-QC agree (two honest intersectors).
invariant [same_view_precommit_prevote_agree]
  (precommit_backed V I ∧ I ≠ genesis ∧ J ≠ genesis ∧
   (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (m : node), ctx.member m s → prevoted_node m V J)) →
    I = J

-- B5: two precommit-QCs at one view agree.
invariant [precommit_qc_unique_at_view]
  ((∃ (s1 : nodeset), ctx.supermajority s1 ∧
      ∀ (m : node), ctx.member m s1 → precommitted_node m V I1) ∧
   (∃ (s2 : nodeset), ctx.supermajority s2 ∧
      ∀ (m : node), ctx.member m s2 → precommitted_node m V I2)) →
    I1 = I2

-- -- B6 (the GAP as a descent-FREE leaf): in the gap regime VM < V < V2, an earlier
-- -- precommit for I floats down to a precommit-QC at U ≤ VM on the same I.
-- -- Concentrates the quorum-intersection + lock-trichotomy; expect /manual-prove.
-- invariant [precommit_floats_down_to_argmax]
--   (¬ ctx.is_byz N ∧ prevoted_node N V2 J ∧ J ≠ genesis ∧
--    precommit_backed V I ∧ I ≠ genesis ∧
--    argmax_recvd_view N V2 VM ∧ tot_view.lt VM V ∧ tot_view.lt V V2) →
--     ∃ (U : view), tot_view.le U VM ∧ precommit_backed U I

-- ####################################################################
-- # op_argmax cache invariants (S8 — Tendermint-style aggregation)
-- ####################################################################

-- Functional behaviour: at most one value per (op, v) per dimension.
-- Discharged by collect_prepares' `decide` update templates.
invariant [op_argmax_ixn_unique]
  (¬ ctx.is_byz OP ∧ op_argmax_ixn OP V I1 ∧ op_argmax_ixn OP V I2) → I1 = I2

invariant [op_argmax_stage_unique]
  (¬ ctx.is_byz OP ∧ op_argmax_stage OP V S1 ∧ op_argmax_stage OP V S2) → S1 = S2

invariant [op_argmax_view_unique]
  (¬ ctx.is_byz OP ∧ op_argmax_view OP V VL1 ∧ op_argmax_view OP V VL2) → VL1 = VL2

-- Existence iff prepares collected, per dimension. Split forms (no ↔) for
-- simp tractability.
invariant [op_argmax_ixn_implies_collected]
  (¬ ctx.is_byz OP ∧ op_argmax_ixn OP V I) → prepares_collected OP V

invariant [op_argmax_stage_implies_collected]
  (¬ ctx.is_byz OP ∧ op_argmax_stage OP V S) → prepares_collected OP V

invariant [op_argmax_view_implies_collected]
  (¬ ctx.is_byz OP ∧ op_argmax_view OP V VL) → prepares_collected OP V

invariant [collected_implies_op_argmax_ixn]
  (¬ ctx.is_byz OP ∧ prepares_collected OP V) → ∃ (I : interaction), op_argmax_ixn OP V I

invariant [collected_implies_op_argmax_stage]
  (¬ ctx.is_byz OP ∧ prepares_collected OP V) → ∃ (S : stage), op_argmax_stage OP V S

invariant [collected_implies_op_argmax_view]
  (¬ ctx.is_byz OP ∧ prepares_collected OP V) → ∃ (VL : view), op_argmax_view OP V VL

-- op_argmax_is_highest_lock relocated to the top of the invariant list (sited
-- with main_safety) so its preservation across respond_prepare is discharged
-- early. The OLD universal-dominance clause was dropped for the same reason as
-- argmax_recvd_is_highest_lock — respond_prepare can extend sent_lock_in_prepare
-- with a VL > VM, making the universal structurally unprovable.

-- Argmax interaction is QC-backed at its claimed (view, stage) for honest op.
-- Discharged by the argmax `t_max` QC-backing require (step 3) inside
-- collect_prepares.
invariant [op_argmax_qc_backed]
  (¬ ctx.is_byz OP ∧ op_argmax_ixn OP V IM ∧ op_argmax_stage OP V SM ∧ op_argmax_view OP V VM) →
    (SM = prevote → ∃ (Q : nodeset), ctx.supermajority Q ∧
       ∀ (N : node), ctx.member N Q → prevoted_node N VM IM) ∧
    (SM = precommit → ∃ (Q : nodeset), ctx.supermajority Q ∧
       ∀ (N : node), ctx.member N Q → precommitted_node N VM IM)



-- %%%%%%%%% TESTED ALL BELOW HERE

-- B7 (GOAL, single self-referential invariant): every certificate at V2 > V is
-- I or a descendant of I. cert_qc = prevote_qc ∨ precommit_qc, inlined.
-- invariant [qc_descent]
--   (precommit_backed V I ∧ I ≠ genesis ∧ J ≠ genesis ∧ tot_view.lt V V2 ∧
--    ((∃ (s : nodeset), ctx.supermajority s ∧
--        ∀ (m : node), ctx.member m s → prevoted_node m V2 J) ∨
--     (∃ (s : nodeset), ctx.supermajority s ∧
--        ∀ (m : node), ctx.member m s → precommitted_node m V2 J))) →
--     (J = I ∨ ancestor I J)

-- [RISK 4 — unbounded feeder; should be unchanged but verify]
-- Step 1 — Lift collect_recvd_locks's action quorum into a state invariant.
-- Trivially provable at collect_recvd_locks (the action's `s` parameter is the
-- witness); preserved elsewhere by monotonicity of recvd_collected and
-- sent_lock_in_prepare. Makes the prepare-quorum directly visible to SMT in
-- downstream proofs so they don't have to re-derive it from the action body.
invariant [recvd_collected_implies_prepare_quorum]
  (¬ ctx.is_byz N ∧ recvd_collected N VACT) →
    ∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (m : node), ¬ ctx.is_byz m → ctx.member m s →
        prepared_node m VACT ∧
        ∃ (IL : interaction) (SL : stage) (VL : view),
          sent_lock_in_prepare m VACT IL SL VL ∧ locked m IL SL VL

-- ----- existing top-level invariants (already passing pre-edit) -----

-- Relocated from the freshness section (was failing at propose_repropose,
-- ~60s timeout). At propose_repropose the post-state `proposed_repropose op v
-- ixn_max := true` requires `∃ J. parent J ixn_max` in pre-state. The chain
-- routes through op_argmax_is_highest_lock → locked → no_lock_without_parent;
-- placing it above the cache-existence invariant keeps the chain visible.
invariant [no_proposal_without_parent]
  (¬ ctx.is_byz OP ∧ (proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

-- Relocated from the genesis-ancestry section (was failing at propose_repropose,
-- ~61s timeout). Chain: op_argmax_is_highest_lock → locked →
-- locked_descends_from_genesis → ancestor genesis ixn_max.
invariant [proposed_descends_from_genesis]
  (¬ ctx.is_byz OP ∧ (proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ I ≠ genesis) → ancestor genesis I

-- Existence witness: cached (IM, SM, VM) came from some actual sent_lock at V.
-- Existential-only form (no universal-dominance clause). Preservation at
-- respond_prepare hinges on the unrestricted `sent_lock_only_if_prepare`
-- (no ¬is_byz guard): combined with respond_prepare's `require ¬ prepared_node n v`,
-- the case `N_pre = n_action ∧ V = v_action` becomes unreachable, so the
-- pre-state witness survives in the unchanged slice.
-- ##### COMMENTED OUT (Byzantine-false) #####
-- FALSE under byz: conclusion `∃N. sent_lock ∧ locked N ...` — the argmax
-- holder may be Byzantine and byz_unlock retracts the sole witness. A guard
-- would be WRONG (the holder genuinely can be byz). Live replacement:
-- op_argmax_qc_backed (#... QC form) already carries the usable content.
-- invariant [op_argmax_is_highest_lock]
--   (¬ ctx.is_byz OP ∧ op_argmax_ixn OP V IM ∧ op_argmax_stage OP V SM ∧ op_argmax_view OP V VM) →
--     ∃ (N : node), sent_lock_in_prepare N V IM SM VM ∧ locked N IM SM VM

-- Validator-side mirror of op_argmax_is_highest_lock. Same preservation
-- argument at respond_prepare (unrestricted sent_lock_only_if_prepare + action
-- precondition contradict the substantive case).
-- ##### COMMENTED OUT (Byzantine-false) #####
-- FALSE under byz: validator-side mirror of op_argmax_is_highest_lock — same
-- byz_unlock witness retraction. Live replacement: argmax_recvd_qc_backed.
-- invariant [argmax_recvd_is_highest_lock]
--   (¬ ctx.is_byz N ∧ argmax_recvd_ixn N V IM ∧ argmax_recvd_stage N V SM ∧ argmax_recvd_view N V VM) →
--     ∃ (M : node), sent_lock_in_prepare M V IM SM VM ∧ locked M IM SM VM


-- Fork-location lemma: if two honest decisions are incomparable (main_safety
-- violated), the divergence is witnessed by a concrete fork — a common
-- interaction A with two DISTINCT children c1, c2, one an ancestor of each
-- decided interaction. Structural (tree-only): A := LCA(i1,i2), c1/c2 := the
-- first step off A toward i1 / i2, via ancestor_def_fwd + unique_parent.
-- NOT a safety proof on its own — it only extracts the fork witness. It reduces
-- main_safety to the local "no honest sibling-fork" consensus obligation
-- (no interaction has two distinct children each backing an honest decision).
invariant [safety_violation_locates_fork]
  ∀ (n1 n2 : node) (v1 v2 : view) (i1 i2 : interaction),
    (¬ ctx.is_byz n1 ∧ ¬ ctx.is_byz n2 ∧
     decided n1 v1 i1 ∧ decided n2 v2 i2 ∧
     ¬ ancestor i1 i2 ∧ ¬ ancestor i2 i1) →
    ∃ (A c1 c2 : interaction),
      parent A c1 ∧ parent A c2 ∧ c1 ≠ c2 ∧
      ancestor c1 i1 ∧ ancestor c2 i2

-- ####################################################################
-- # Decoupled qc_descent invariant set (replaces the LAP <-> F1 cycle)
-- # Design: IFPSafety/locks_analog_precommit_decoupling.md
-- # qc_descent (B7) is the single self-referential goal (self-loop on the
-- # J-side certificate view V2); B1-B6 are descent-free leaves. cert_qc /
-- # prevote_qc / precommit_qc are inlined as exists-supermajority predicates.
-- # NB: the design doc's certificate view "W" is written V2 here (a bare `W`
-- # collides with a global identifier in scope, so it does not auto-bind).
-- # NOTE: LAP (locks_analog_precommit) and F1 are intentionally KEPT for now;
-- # delete them + re-route locks_analog_decided only AFTER qc_descent verifies.
-- # qc_descent (B7) and precommit_floats_down_to_argmax (B6) are expected to
-- # need /manual-prove (the gap is this file's documented timeout point).
-- ####################################################################

-- B1: a witnessed precommit-QC sits strictly above the initial view.
invariant [precommit_backed_above_zero]
  precommit_backed V I → V ≠ tot_view.zero

-- [prevote_matches_argmax (B2) relocated to the ACTIVE FRONTIER block at top of invariant list]

-- B3 (carrier, descent-FREE): every honest prevote extends a certificate at the
-- prevoter's cached argmax view VM < V2. Exposes argmax_recvd_view so the gap
-- leaf (B6) reuses the SAME VM. Split by the cached argmax stage (B2's
-- discriminator): prevote-stage ⇒ repropose anchor (J prevote-certified at VM),
-- precommit-stage ⇒ extend anchor (J's parent precommit-certified at VM). The two
-- guards partition realizable states (argmax_recvd_stage is set once at
-- collect_recvd_locks to the single s_max ∈ {prevote, precommit}), so together they
-- reconstitute the original disjunction; a consumer reads the stage off B2.


-- Bridge: any honest non-genesis prevote at non-zero V routes through the cache,
-- so downstream invariants (e.g. locks_analog_prevoted) can lift argmax facts
-- out of the prevote action body and into a cache lookup.
invariant [prevoted_node_implies_recvd_collected]
  (¬ ctx.is_byz N ∧ prevoted_node N V I ∧ I ≠ genesis ∧ V ≠ tot_view.zero) →
    recvd_collected N V

-- recvd_collected at V exists only after global cur_view has reached V.
-- Discharged at collect_recvd_locks via its `require cur_view n v` precondition;
-- combined with cur_view_global this pins V = cur_view at firing. Preserved by
-- set_view (cur_view only advances via tot_view.next) and trivially elsewhere.
-- Closes the trivial-preservation cases of argmax_recvd_ixn_descends_from_precommit_backed
-- on respond_precommit (new precommit_backed view V_pre = cur_view, so V_pre < V_act
-- is ruled out by V_act ≤ cur_view = V_pre) and on set_view (advance).
invariant [recvd_collected_at_past_view]
  (¬ ctx.is_byz N ∧ recvd_collected N V ∧ cur_view N1 VC) → tot_view.le V VC

-- ####################################################################
-- # argmax_recvd cache invariants (validator-side mirror of op_argmax_*)
-- ####################################################################

-- Functional behaviour: at most one value per (n, v) per dimension.
-- Discharged by collect_recvd_locks' `decide` update templates.
invariant [argmax_recvd_ixn_unique]
  (¬ ctx.is_byz N ∧ argmax_recvd_ixn N V I1 ∧ argmax_recvd_ixn N V I2) → I1 = I2

invariant [argmax_recvd_stage_unique]
  (¬ ctx.is_byz N ∧ argmax_recvd_stage N V S1 ∧ argmax_recvd_stage N V S2) → S1 = S2

invariant [argmax_recvd_view_unique]
  (¬ ctx.is_byz N ∧ argmax_recvd_view N V VL1 ∧ argmax_recvd_view N V VL2) → VL1 = VL2

-- Existence iff recvd_collected, per dimension. Split forms for simp tractability.
invariant [argmax_recvd_ixn_implies_collected]
  (¬ ctx.is_byz N ∧ argmax_recvd_ixn N V I) → recvd_collected N V

invariant [argmax_recvd_stage_implies_collected]
  (¬ ctx.is_byz N ∧ argmax_recvd_stage N V S) → recvd_collected N V

invariant [argmax_recvd_view_implies_collected]
  (¬ ctx.is_byz N ∧ argmax_recvd_view N V VL) → recvd_collected N V

invariant [collected_implies_argmax_recvd_ixn]
  (¬ ctx.is_byz N ∧ recvd_collected N V) → ∃ (I : interaction), argmax_recvd_ixn N V I

invariant [collected_implies_argmax_recvd_stage]
  (¬ ctx.is_byz N ∧ recvd_collected N V) → ∃ (S : stage), argmax_recvd_stage N V S

invariant [collected_implies_argmax_recvd_view]
  (¬ ctx.is_byz N ∧ recvd_collected N V) → ∃ (VL : view), argmax_recvd_view N V VL

-- Cache existence witness: the cached (IM, SM, VM) tuple came from some
-- actual sent_lock at V. Preserved monotonically (sent_lock_in_prepare and
-- locked never shrink).
-- The OLD universal-dominance clause
--   ∀ N' IL SL VL, sent_lock_in_prepare N' V IL SL VL → tot_view.le VL VM
-- argmax_recvd_is_highest_lock relocated to the top of the invariant list
-- (sited with main_safety). The OLD universal-dominance clause was structurally
-- unprovable at respond_prepare: late preparers can extend
-- `sent_lock_in_prepare` with a VL > VM (the holder had a lock above VM that
-- wasn't yet a sent_lock at V when collect_recvd_locks fired). Dropped.
-- The substantive use of "argmax dominates" is inlined into Step 3.5's proof
-- at collect_recvd_locks, where the action's prepare-quorum `s` and the
-- action's own argmax-dominance require make the snapshot reasoning local.

-- Cached argmax interaction is QC-backed at its claimed (view, stage) for honest validator.
invariant [argmax_recvd_qc_backed]
  (¬ ctx.is_byz N ∧ argmax_recvd_ixn N V IM ∧ argmax_recvd_stage N V SM ∧ argmax_recvd_view N V VM) →
    (SM = prevote → ∃ (Q : nodeset), ctx.supermajority Q ∧
       ∀ (N' : node), ctx.member N' Q → prevoted_node N' VM IM) ∧
    (SM = precommit → ∃ (Q : nodeset), ctx.supermajority Q ∧
       ∀ (N' : node), ctx.member N' Q → precommitted_node N' VM IM)


-- ####################################################################
-- # Argmax → precommit_backed ancestry bridge (Option 3)
-- ####################################################################
-- Substantive case: collect_prepares. Via intersection of the prepare-quorum
-- with precommit_backed_fwd's supermajority, an honest n* holds both
--   - precommitted_node at (V, I), hence a lock at U ≤ V on I, and
--   - sent_lock_in_prepare at V2 with QC-backed (ixnl, sl, vl), where vl ≤ v_max
-- so lock_height_monotone within n* + ancestor descent gives ancestor I IM.
-- All other actions preserve trivially: op_argmax_ixn, precommit_backed, and
-- ancestor are monotonic on pre-existing data; new ancestor entries from
-- propose_extend involve a fresh ixn_propose not equal to any pre-existing I/IM.
-- invariant [op_argmax_ancestor_of_precommit_backed]
--   ∀ (V V2 : view) (I IM : interaction) (OP : node),
--     (precommit_backed V I ∧ I ≠ genesis ∧
--      op_argmax_ixn OP V2 IM ∧
--      tot_view.lt V V2) →
--     (I = IM ∨ ancestor I IM)






-- Bridge: precommitted_node directly implies a prevote-QC was aggregated
-- (mirrors respond_prevote's `∃ op. operator op v ∧ prevoted_operator op v ixn`
-- precondition lifted into a state invariant, with the operator-role guard).
invariant [precommitted_node_implies_prevote_qc]
  (¬ ctx.is_byz N ∧ precommitted_node N V I) → (∃ (op : node), operator op V ∧ prevoted_operator op V I)


  -- Bridge for main_safety to feed this invariant.
  invariant [decided_implies_precommit_backed]
    (¬ ctx.is_byz N ∧ decided N V I ∧ I ≠ genesis) → precommit_backed V I

-- (IFPNTDP) Removed: precommitted_operator no longer implies precommit_backed.
-- operator_precommit sets precommitted_operator but not precommit_backed; only
-- the subsequent respond_precommit fires precommit_backed. The
-- decided_implies_precommit_backed bridge now holds trivially because both
-- updates happen atomically in respond_precommit, so this intermediate bridge
-- is no longer needed.
-- invariant [precommitted_operator_implies_precommit_backed]
--   precommitted_operator OP V I → precommit_backed V I

-- Honest non-genesis prevote at non-zero view is justified by some pre-existing
-- lock (monotonic witness). The dominance / argmax clause was dropped: it fails
-- preservation on respond_prepare when a late preparer m (honest, different
-- from the prevoter) first prepares at V with a lock view > the prevote's
-- v_max — protocol-allowed, since respond_propose's argmax is a snapshot, not
-- a forward-time-stable property.
-- ##### COMMENTED OUT (Byzantine-false) #####
-- FALSE under byz: `∃ n_max. locked n_max ...` witness may be Byzantine
-- (byz_unlock). Partial recovery via the step-3 QC only supplies the s_max =
-- precommit disjunct; the (prevote, ixn_max = I) branch has no honest
-- witness.
-- invariant [prevote_justified_by_highest_lock]
--   (¬ ctx.is_byz N ∧ prevoted_node N V I ∧ I ≠ genesis ∧ V ≠ tot_view.zero) →
--     ∃ (n_max : node) (ixn_max : interaction) (s_max : stage) (v_max : view),
--       locked n_max ixn_max s_max v_max ∧
--       tot_view.lt v_max V ∧
--       ((s_max = prevote ∧ ixn_max = I) ∨
--        (s_max = precommit ∧ parent ixn_max I))

-- Strengthened: mirrors respond_prevote's exact post-condition. Either the
-- prevote lock is at the same view V (new lock set by respond_prevote), or a
-- pre-existing precommit lock at some U ≤ V. Rules out spurious states where
-- precommitted_node exists without the matching `locked` side-effect.
invariant [precommit_node_locked_at_same_view]
  (¬ ctx.is_byz N ∧ precommitted_node N V I ∧ I ≠ genesis) →
    (locked N I prevote V ∨ ∃ (U : view), tot_view.le U V ∧ locked N I precommit U)



-- Precommit locks are bounded by the holder's committed_ixn height. Established
-- atomically in respond_precommit (sets locked precommit + updates committed_ixn
-- when height ≥ old). Rules out spurious states where a precommit lock exists
-- without the matching committed_ixn bookkeeping.
invariant [precommit_lock_height_le_committed]
  (¬ ctx.is_byz N ∧ locked N I precommit V ∧ committed_ixn N CI) →
    height I ≤ height CI


-- ####################################################################
-- # Core Safety-Routing Invariants
-- ####################################################################

invariant [genesis_decided_only_at_zero]
  (¬ ctx.is_byz N ∧ decided N V genesis) → V = tot_view.zero

invariant [proposed_parent_height_le_committed]
  (¬ ctx.is_byz OP ∧
   (proposed_repropose OP V J ∨ proposed_extend OP V J) ∧
   parent I J ∧ committed_ixn OP CI) →
    height I ≤ height CI

invariant [decision_height_monotone]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   decided N1 V1 I1 ∧
   decided N2 V2 I2 ∧
   tot_view.lt V1 V2)
  → height I1 ≤ height I2

invariant [proposed_extend_parent_matches_committed]
  (¬ ctx.is_byz OP ∧ proposed_extend OP V J ∧ parent I J ∧
   committed_ixn OP CI ∧ height I = height CI) → I = CI

invariant [proposed_repropose_parent_matches_committed]
  (¬ ctx.is_byz OP ∧ proposed_repropose OP V J ∧ parent I J ∧
   committed_ixn OP CI ∧ height I = height CI) → I = CI

invariant [unique_decided_at_height]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   decided N1 V1 I1 ∧
   decided N2 V2 I2 ∧
   height I1 = height I2)
  → I1 = I2

invariant [committed_ixn_height_upper_bound]
  (¬ ctx.is_byz N ∧ decided N V I ∧ committed_ixn N CI) → height I ≤ height CI

invariant [genesis_decided_first]
  (¬ ctx.is_byz N ∧ decided N V J ∧ J ≠ genesis) →
    ∃ (u : view) (m : node), tot_view.lt u V ∧ decided m u genesis

-- ##### COMMENTED OUT (Byzantine-false) #####
-- FALSE under byz: an honest decision on J only forces a precommit QC on J's
-- parent at some VM (via the prevoters' argmax) — NOT that anyone ran
-- respond_precommit on it, so no node need have `decided` the parent.
-- Repair: restate as `→ ∃ W < V. <precommit QC for I at W>`.
-- invariant [committed_implies_parent_committed]
--   (decided M V J ∧ parent I J ∧ J ≠ genesis) →
--     ∃ (u : view) (n : node), tot_view.lt u V ∧ decided n u I


-- All nodes share the same cur_view (by synchronous set_view).
-- Required to rule out spurious split-view pre-states for locks_analog_*.
invariant [cur_view_global]
  (cur_view N1 V1 ∧ cur_view N2 V2) → V1 = V2

-- An honest node's prevote cannot be at a view later than the current global view.
-- Follows from: honest prevote requires cur_view at that view, combined with cur_view_global.
invariant [prevoted_node_view_bound]
  (¬ ctx.is_byz N2 ∧ cur_view N1 V1 ∧ prevoted_node N2 V2 I) →
    tot_view.le V2 V1

-- An honest node's precommit cannot be at a view later than the current global view.
invariant [precommitted_node_view_bound]
  (¬ ctx.is_byz N2 ∧ cur_view N1 V1 ∧ precommitted_node N2 V2 I) →
    tot_view.le V2 V1

-- ####################################################################
-- # precommit_backed support invariants
-- ####################################################################
-- precommit_backed is a stored ghost set in operator_precommit, where the
-- supermajority precondition guarantees a real precommitted_node quorum.
-- Tied to the underlying quorum by precommit_backed_fwd; no _bwd direction
-- (avoids SMT cost on respond_prevote — the ghost lags the supermajority
-- formation but is set as soon as any operator aggregates the QC).

-- Forward: ghost ⇒ supermajority of precommitted_node exists.
-- Established by operator_precommit's precondition; preserved by monotonicity
-- of precommitted_node (no action ever unsets it).
invariant [precommit_backed_fwd]
  precommit_backed V I →
    (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (n : node), ctx.member n s → precommitted_node n V I)

-- Uniqueness at a view: via precommit_backed_fwd + supermajority intersection
-- + unique_precommit_nodes.
invariant [unique_precommit_backed_at_view]
  (precommit_backed V I1 ∧ precommit_backed V I2) → I1 = I2

-- Uniqueness at a height: if two precommit-backed interactions share a height,
-- they're equal. Closes the equal-height case in locks_analog_precommit without
-- chain descent. Provable via precommit_backed_fwd + supermajorities_intersect_in_honest
-- + unique_locked_at_height (the honest intersector holds precommit locks for
-- both at the shared height, so the locks coincide).
invariant [unique_precommit_backed_at_height]
  (precommit_backed V1 I1 ∧ precommit_backed V2 I2 ∧
   I1 ≠ genesis ∧ I2 ≠ genesis ∧
   height I1 = height I2) → I1 = I2

-- ####################################################################
-- # Simple Invariants
-- ####################################################################

-- Honest nodes cannot prevote on two different interactions in a given view
invariant [unique_prevote_nodes]
  ∀ (v : view) (i1 i2 : interaction) (n : node),
    ¬ ctx.is_byz n → ((prevoted_node n v i1 ∧ prevoted_node n v i2) → i1 = i2)

-- Honest nodes cannot be prevote-locked for different interactions in a given view
invariant [unique_prevote_lock_in_view]
  ∀ (n1 n2 : node) (v : view) (i1 i2 : interaction),
    ¬ (ctx.is_byz n1 ∨ ctx.is_byz n2) → ((locked n1 i1 prevote v ∧ locked n2 i2 prevote v) → i1 = i2)

-- If an honest node has decided, then a quorum has prevote-locked
invariant [decided_only_if_quorum_prevote_locked]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ ctx.is_byz n → ( (decided n v ixn ∧ ixn ≠ genesis) →
      (∃ (s : nodeset), (ctx.supermajority s
        ∧ ∀ (nc : node), ¬ ctx.is_byz nc → (
          ctx.member nc s → ∃ (u : view), (tot_view.le u v ∧ prevoted_node nc v ixn ∧ (locked nc ixn prevote u ∨ locked nc ixn precommit u))) )) )

invariant [unique_locked_at_height]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
    locked N1 I1 precommit V1 ∧ locked N2 I2 precommit V2 ∧
    I1 ≠ genesis ∧ I2 ≠ genesis ∧ height I1 = height I2)
    → I1 = I2

-- Prevote lock implies a quorum prevoted for the interaction
invariant [prevote_lock_only_if_quorum_prevoted]
  (¬ ctx.is_byz N ∧ locked N I prevote V) → (∃ (s : nodeset), ctx.supermajority s ∧
    ∀ (NC : node), ctx.member NC s → prevoted_node NC V I)

-- If honest NC has precommitted for I at V, and honest N has a prevote lock for J at V, then I = J.
invariant [precommit_node_lock_consistency]
  (¬ ctx.is_byz N ∧ ¬ ctx.is_byz NC ∧ precommitted_node NC V I ∧
   locked N J prevote V ∧
   I ≠ genesis ∧ J ≠ genesis) → I = J

-- A single honest node can only have locks on one interaction per view
invariant [unique_lock_interaction_per_view]
  (¬ ctx.is_byz N ∧ locked N I1 S1 V ∧ locked N I2 S2 V) → I1 = I2

-- Cross-node lock uniqueness
invariant [cross_node_unique_lock]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   locked N1 I1 S1 V ∧ locked N2 I2 S2 V ∧
   I1 ≠ genesis ∧ I2 ≠ genesis)
  → I1 = I2

-- Precommit lock implies the node prevoted for the interaction
invariant [precommit_lock_implies_prevoted]
  (¬ ctx.is_byz N ∧ locked N I precommit V ∧ I ≠ genesis) → prevoted_node N V I

invariant [precommit_lock_implies_precommit_backed]
  (¬ ctx.is_byz N ∧ locked N I precommit V ∧ I ≠ genesis) → precommit_backed V I

-- Sent locks in prepare phase correspond to actual locks
invariant [locks_sent_only_if_locked]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare N V IL SL VL) → locked N IL SL VL

-- Genesis locks exist for all nodes
invariant [genesis_lock_existence]
  ∀ (n : node), ¬ ctx.is_byz n → locked n genesis precommit tot_view.zero

invariant [sent_lock_prepare_implies_cur_view_ge]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare N V IL SL VL ∧ cur_view N VCUR) → tot_view.le V VCUR

invariant [highest_lock_sent]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare N V IL SL VL) →
    (locked N IL SL VL ∧
     tot_view.lt VL V ∧
     (∀ i' s' v', (tot_view.lt VL v' ∧ tot_view.lt v' V) → ¬ locked N i' s' v') ∧
     (SL = prevote → ¬ locked N IL precommit VL))

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

invariant [decided_implies_proposed]
  (¬ ctx.is_byz N ∧ decided N V I ∧ I ≠ genesis) →
    ∃ (op : node), proposed_repropose op V I ∨ proposed_extend op V I

invariant [no_lock_without_parent]
  (¬ ctx.is_byz N ∧ locked N I S V ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

invariant [no_decide_without_parent]
  (¬ ctx.is_byz N ∧ decided N V I ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

invariant [locked_descends_from_genesis]
  (¬ ctx.is_byz N ∧ locked N I S V ∧ I ≠ genesis) → ancestor genesis I


-- ####################################################################
-- # Height-Indexed Ghost Invariants
-- # ----------------------------------------------------------------
-- # Wires up the two VIEW-FREE, PARTICIPANT-FREE descendant height ghosts
-- # (locked_descendant_at_height, committed_descendant_at_height). Every bit is
-- # set in lockstep with the matching real `locked`/`decided` write (init,
-- # respond_prevote inside the new-prevote-lock `if`, respond_precommit
-- # unconditional) and the sets only ever grow, so all of these are LEAVES —
-- # preserved by construction. The plain locked_at_height/committed_at_height
-- # ghosts (the A = genesis instance of these, via locked_descends_from_genesis
-- # + ancestor_refl) and the view-indexed locked_at_view / proposed_for_descendant
-- # / decided_for_descendant ghosts were removed as redundant write-only state.
-- #
-- # VIEW-ERASURE (cf. IFPJ, whose ghosts carry P and V): dropping the view index
-- # makes IFPJ's per-view family (lock_height_monotone, unique_lock_height,
-- # locked_descendant_height_monotone) UNSTATABLE — a node legitimately
-- # accumulates lock-heights from many views into one set. What survives is:
-- # fwd/bwd consistency, the descendant height-bound, genesis/zero anchors, and
-- # the cross-ghost containment below. The no-fork UNIQUENESS crux is NOT here:
-- # it lives over the real relation in unique_decided_at_height; these ghosts
-- # only carry the ancestry+height bookkeeping a height-descent argument needs.
-- ####################################################################

-- --- Forward: every real lock/decision is recorded in the height ghost ---
invariant [locked_descendant_at_height_fwd]
  (locked N I S V ∧ ancestor A I) → locked_descendant_at_height N A (height I)

invariant [committed_descendant_at_height_fwd]
  (decided N V I ∧ ancestor A I) → committed_descendant_at_height N A (height I)

-- --- Backward: an honest height-ghost bit witnesses a real lock/decision. The
-- view is existentialized (the view-free ghost no longer records which view).
-- ¬is_byz is the conventional guard on _bwd directions; not strictly required.
invariant [locked_descendant_at_height_bwd]
  (¬ ctx.is_byz N ∧ locked_descendant_at_height N A H) →
    ∃ (I : interaction) (S : stage) (V : view),
      locked N I S V ∧ ancestor A I ∧ height I = H

invariant [committed_descendant_at_height_bwd]
  (¬ ctx.is_byz N ∧ committed_descendant_at_height N A H) →
    ∃ (V : view) (I : interaction), decided N V I ∧ ancestor A I ∧ height I = H

-- --- Height bound: a descendant marker sits at or above its ancestor's height.
-- The one safety-relevant height fact that survives view-erasure (Go enforces
-- child.height = parent.height+1, krama_engine.go:987). Each writer sets
-- H = height ixn together with ancestor A ixn, and ancestor_height_strict +
-- ancestor_refl give height A ≤ height ixn = H.
invariant [locked_descendant_height_bound]
  (¬ ctx.is_byz N ∧ locked_descendant_at_height N A H) → height A ≤ H

invariant [committed_descendant_height_bound]
  (¬ ctx.is_byz N ∧ committed_descendant_at_height N A H) → height A ≤ H

-- --- Cross-ghost containment (markers set in lockstep ⇒ subset holds).
-- decision marker ⇒ lock marker (every decide co-fires a precommit lock)
invariant [committed_descendant_at_height_implies_locked_descendant]
  (¬ ctx.is_byz N ∧ committed_descendant_at_height N A H) → locked_descendant_at_height N A H

-- --- Genesis / height-0 anchors (init-persistent; ghosts only grow). The
-- height-0 floor a height-descent argument terminates at.
invariant [genesis_locked_descendant_at_height_zero]
  ∀ (n : node), locked_descendant_at_height n genesis 0

invariant [genesis_committed_descendant_at_height_zero]
  ∀ (n : node), committed_descendant_at_height n genesis 0

-- ####################################################################
-- # Reproposal-run ghost invariants (born_at / extend_bridge)
-- # ----------------------------------------------------------------
-- # All LEAVES, preserved by construction (set in lockstep at propose_extend;
-- # the sets only grow). The contiguity / "same block reproposed" claim is
-- # deliberately ABSENT — it is cross-view lock-propagation, not a leaf.
-- ####################################################################

-- Lockstep (reverse projection): every extend records a birth.
invariant [extended_implies_born_at]
  (¬ ctx.is_byz OP ∧ proposed_extend OP V I) → born_at I V

-- Forward projection (guarded for the genesis seed): a non-genesis birth came
-- from a real extend.
invariant [born_at_implies_extended]
  (born_at I V ∧ I ≠ genesis) → ∃ (op : node), proposed_extend op V I

-- A non-genesis born interaction has a parent (born_at is set in lockstep with
-- parent ci ixn_propose). Mirrors no_lock_without_parent; feeds born_at_unique.
invariant [born_at_implies_parent]
  (born_at I V ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

-- Birth view is unique: propose_extend's freshness precondition forbids
-- re-extending an already-parented interaction, so it is extended at most once.
invariant [born_at_unique]
  (born_at I V1 ∧ born_at I V2) → V1 = V2

-- parent_born_at structural leaves.
-- A non-genesis interaction carrying a parent-birth has a real parent, born at
-- that view (recovers extend_bridge's parent + endpoint-born content). The
-- update only fires for VP with born_at ci VP and writes parent ci C in lockstep,
-- so the witness P = ci.
invariant [parent_born_at_implies_parent]
  (parent_born_at C VP ∧ C ≠ genesis) → ∃ (P : interaction), parent P C ∧ born_at P VP

-- Parent-birth view is unique (C's parent is unique by unique_parent, and that
-- parent's birth is unique by born_at_unique).
invariant [parent_born_at_unique]
  (parent_born_at C VP1 ∧ parent_born_at C VP2) → VP1 = VP2

-- ####################################################################
-- # Ancestor Parent Structural Invariants
-- ####################################################################

invariant [ancestor_refl]
  ∀ (I : interaction), ancestor I I

invariant [ancestor_from_parent]
  parent I J → ancestor I J

invariant [ancestor_trans]
  (ancestor I J ∧ ancestor J K) → ancestor I K

invariant [ancestor_antisymm]
  (ancestor I J ∧ ancestor J I) → I = J

invariant [ancestor_height_strict]
  (ancestor I J ∧ I ≠ J) → height I < height J

invariant [no_ancestor_equal_height]
  (height I = height J ∧ I ≠ J) → (¬ ancestor I J ∧ ¬ ancestor J I)

invariant [parent_height]
  parent I J → height J = height I + 1

invariant [ancestor_def_fwd]
  ancestor I J → (I = J ∨ parent I J ∨ ∃ (k : interaction), parent I k ∧ ancestor k J)

invariant [ancestor_def_bwd]
  (I = J ∨ parent I J ∨ ∃ (k : interaction), parent I k ∧ ancestor k J) → ancestor I J

invariant [unique_parent]
  parent J I ∧ parent K I → J = K

invariant [parent_irreflexive]
  ¬ parent I I

invariant [genesis_has_no_parent]
  ¬ parent I genesis

invariant [genesis_height_zero]
  ((height I = 0 ∧ (∃ (v : view) (n : node), ¬ ctx.is_byz n ∧ decided n v I)) → I = genesis)
  ∧ (I = genesis → height I = 0)

invariant [parent_only_if_proposed]
  parent I J ∧ J ≠ genesis → ∃ (n : node) (v : view), proposed_extend n v J

-- ####################################################################
-- # Supporting Invariants
-- ####################################################################

invariant [unique_cur_view]
  cur_view N U ∧ cur_view N V → U = V

invariant [node_has_cur_view]
  ∀ (n : node), ∃ (v : view), cur_view n v

invariant [prepared_only_at_cur_or_past_view]
  (prepared_node N V ∧ ¬ ctx.is_byz N ∧ cur_view N V2) → tot_view.le V V2

invariant [proposed_extend_view_bound]
  (¬ ctx.is_byz N2 ∧ cur_view N1 V1 ∧ proposed_extend N2 V2 I) →
    tot_view.le V2 V1

invariant [proposed_repropose_view_bound]
  (¬ ctx.is_byz N2 ∧ cur_view N1 V1 ∧ proposed_repropose N2 V2 I) →
    tot_view.le V2 V1

invariant [lock_at_most_cur_view]
  (¬ ctx.is_byz N ∧ locked N I S V ∧ I ≠ genesis ∧ cur_view N VCUR)
  → tot_view.le V VCUR

invariant [sent_lock_only_at_past_view]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare N V IL SL VL ∧ cur_view N VCUR) → tot_view.le V VCUR

invariant [unique_stage]
  (¬ ctx.is_byz N ∧ cur_stage N V S1 ∧ cur_stage N V S2) → S1 = S2

invariant [unique_operator]
  (operator N1 V ∧ operator N2 V) → N1 = N2

invariant [proposed_only_by_operator]
  ((proposed_repropose N V I ∨ proposed_extend N V I) ∧ ¬ ctx.is_byz N) → operator N V

invariant [genesis_lock_only_at_zero]
  (¬ ctx.is_byz N ∧ locked N genesis S V) → (V = tot_view.zero ∧ S = precommit)

-- Dual of genesis_lock_only_at_zero: locks at view zero are only the genesis
-- init locks (every node, precommit stage). Init sets locked to exactly
-- (_, genesis, precommit, zero); respond_prevote and respond_precommit both
-- require v ≠ tot_view.zero, so no non-init lock at zero is reachable.
-- Trivially inductive; rules out SMT-planted phantom Byzantine locks at zero.
invariant [lock_at_zero_is_genesis_precommit]
  (¬ ctx.is_byz N ∧ locked N I S V ∧ V = tot_view.zero) → (I = genesis ∧ S = precommit)

invariant [lock_stage_valid]
  (¬ ctx.is_byz N ∧ locked N I S V) → (S = prevote ∨ S = precommit)

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

invariant [genesis_not_in_pipeline]
  ¬ ( ¬ ctx.is_byz N ∧ (proposed_repropose N V genesis ∨ proposed_extend N V genesis ∨ prevoted_node N V genesis
  ∨ prevoted_operator N V genesis ∨ precommitted_node N V genesis
  ∨ precommitted_operator N V genesis))

invariant [prevote_stage_implies_prevoted]
  (cur_stage N V prevote ∧ ¬ ctx.is_byz N) → ∃ I, prevoted_node N V I

invariant [precommit_stage_implies_precommitted]
  (cur_stage N V precommit ∧ ¬ ctx.is_byz N) → ∃ I, precommitted_node N V I

-- Byzantine weakening: under proposal equivocation (byz_propose fires twice with
-- different ixns) two honest validators can legitimately prevote different
-- interactions at one view, so per-view prevote agreement holds only when the
-- view's operator is honest (unique_operator + prevote_implies_proposed +
-- guarded unique_proposed_interaction then force a single proposed ixn).
invariant [cross_node_unique_prevote]
  (¬ (ctx.is_byz N1 ∨ ctx.is_byz N2) ∧ (∃ (op : node), operator op V ∧ ¬ ctx.is_byz op) ∧
   prevoted_node N1 V I1 ∧ prevoted_node N2 V I2) → I1 = I2

invariant [precommit_nodes_only_if_prevoted_for_same_ixn]
  (¬ ctx.is_byz N ∧ precommitted_node N V I) → prevoted_node N V I

invariant [precommitted_node_implies_lock]
  ∀ (v : view) (ixn : interaction) (n : node),
    ¬ ctx.is_byz n → ((precommitted_node n v ixn ∧ ixn ≠ genesis) →
      ∃ (u : view), tot_view.le u v ∧ (locked n ixn prevote u ∨ locked n ixn precommit u))

invariant [precommit_quorum_prevoted_and_locked]
  (¬ ctx.is_byz NC ∧ precommitted_node NC V IXN ∧ IXN ≠ genesis) →
  (prevoted_node NC V IXN ∧
   ∃ (U : view), tot_view.le U V ∧ (locked NC IXN prevote U ∨ locked NC IXN precommit U))

invariant [decide_only_if_precommit_operator]
  (¬ ctx.is_byz OP ∧ decided OP V I ∧ I ≠ genesis) → (∃ (op : node), (operator op V ∧ precommitted_operator op V I))

invariant [stage_2]
  (cur_stage N V prevote ∧ ¬ ctx.is_byz N)
  → (∃ (i : interaction), ((∃ (op : node), proposed_repropose op V i ∨ proposed_extend op V i) ∧ prevoted_node N V i))

invariant [unique_proposal]
  ¬ (ctx.is_byz N1 ∨ ctx.is_byz N2) → ( ((proposed_repropose N1 V I1 ∨ proposed_extend N1 V I1) ∧ (proposed_repropose N2 V I2 ∨ proposed_extend N2 V I2)) → (I1 = I2 ∧ N1 = N2) )

invariant [unique_proposed_interaction]
  (¬ ctx.is_byz N ∧ (proposed_repropose N V I1 ∨ proposed_extend N V I1) ∧ (proposed_repropose N V I2 ∨ proposed_extend N V I2)) → I1 = I2

invariant [prevote_implies_proposed]
  (prevoted_node N V I ∧ ¬ ctx.is_byz N) → (∃ (op : node), (operator op V ∧ (proposed_repropose op V I ∨ proposed_extend op V I)))

invariant [precommit_only_if_propose]
  (¬ ctx.is_byz N ∧ precommitted_node N V I) → (∃ (op : node), operator op V ∧ (proposed_repropose op V I ∨ proposed_extend op V I))

invariant [prepare_response_only_on_prepare]
  ¬ ctx.is_byz N → (prepared_node N V → ∃ (op : node), operator op V ∧ prepared_operator op V)

invariant [prevote_only_by_operator]
  (¬ ctx.is_byz OP ∧ prevoted_operator OP V I) → operator OP V

invariant [precommit_only_by_operator]
  (¬ ctx.is_byz OP ∧ precommitted_operator OP V I) → operator OP V

invariant [prepared_node_has_lock_sent]
  (¬ ctx.is_byz N ∧ prepared_node N V ∧ V ≠ tot_view.zero ∧
   locked N IL SL VL ∧
   tot_view.lt VL V ∧
   (∀ (vl2 : view), (tot_view.lt VL vl2 ∧ tot_view.lt vl2 V) → ¬ ∃ (i2 : interaction) (s2 : stage), locked N i2 s2 vl2) ∧
   (SL = prevote → ¬ locked N IL precommit VL))
  → sent_lock_in_prepare N V IL SL VL

invariant [decision_requires_precommit_lock]
  (¬ ctx.is_byz N ∧ decided N V I ∧ I ≠ genesis) → locked N I precommit V

invariant [decisions_not_from_higher_views]
  (¬ ctx.is_byz N ∧ cur_view N V ∧ decided N U I) → tot_view.le U V

invariant [genesis_view_zero]
  (¬ ctx.is_byz N ∧ decided N V I ∧ tot_view.zero = V) → I = genesis

invariant [genesis_decided_at_zero]
  ∀ (n : node), ¬ ctx.is_byz n → decided n tot_view.zero genesis

invariant [decide_only_if_quorum_precommit]
  (¬ ctx.is_byz N ∧ decided N V I ∧ I ≠ genesis) →
    (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (n : node), ctx.member n s → precommitted_node n V I)

invariant [prevote_operator_only_if_quorum_prevoted]
  ¬ ctx.is_byz N → (prevoted_operator N V I →
    (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (NC : node), ctx.member NC s → prevoted_node NC V I))

invariant [precommit_operator_only_if_quorum_precommit]
  ¬ ctx.is_byz OP → (precommitted_operator OP V I →
    (∃ (s : nodeset), ctx.supermajority s ∧
      ∀ (n : node), ctx.member n s → precommitted_node n V I))

invariant [unique_lock_sent]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare N V IL1 SL1 VL1 ∧ sent_lock_in_prepare N V IL2 SL2 VL2) →
    (IL1 = IL2 ∧ SL1 = SL2 ∧ VL1 = VL2)

invariant [unique_precommit_nodes]
  (¬ ctx.is_byz N ∧ precommitted_node N V I ∧ precommitted_node N V J) → I = J

invariant [unique_prevote_operator]
  (¬ ctx.is_byz OP ∧ prevoted_operator OP V I ∧ prevoted_operator OP V J) → I = J

invariant [unique_precommit_operator]
  (¬ ctx.is_byz OP ∧ precommitted_operator OP V I ∧ precommitted_operator OP V J) → I = J

invariant [sent_lock_only_if_prepare]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare N V IL SL VL) → prepared_node N V

invariant [sent_lock_only_if_prepare_unrestricted]
  (¬ ctx.is_byz N ∧ sent_lock_in_prepare N V IL SL VL) → prepared_node N V

-- invariant [stage_1]
--   (cur_stage N V propose ∧ ¬ ctx.is_byz N) →
--     (∃ (il : interaction) (sl : stage) (vl : view), sent_lock_in_prepare N V il sl vl)

invariant [stage_3]
  (cur_stage N V precommit ∧ ¬ ctx.is_byz N) →
    (∃ (i : interaction), (prevoted_operator N V i ∨ precommitted_node N V i) ∧
     (locked N i prevote V ∨ (∃ (u : view), tot_view.le u V ∧ locked N i precommit u)))

invariant [stage_4]
  (cur_stage N V commit ∧ ¬ ctx.is_byz N) →
    (∃ (i : interaction), (precommitted_operator N V i ∨ decided N V i) ∧ locked N i precommit V)

invariant [prepared_operator_not_at_zero]
  (prepared_operator OP V ∧ ¬ ctx.is_byz OP) → V ≠ tot_view.zero

invariant [propose_only_if_operator_prepare]
  (¬ ctx.is_byz N ∧ (proposed_repropose N V I ∨ proposed_extend N V I)) → prepared_operator N V

-- ##### COMMENTED OUT (Byzantine-false) #####
-- FALSE as stated under byz (witness `n` may be Byzantine, byz_unlock). TRUE
-- with an honest witness named: restate as `→ ∃ u. locked OP I precommit u`,
-- justified by committed_ixn_precommit_locked at the proposal step.
-- invariant [propose_only_if_parent_locked]
--   (¬ ctx.is_byz OP ∧ proposed_extend OP V J ∧ parent I J) →
--     (∃ (u : view) (n : node) (s : stage), tot_view.le u V ∧ locked n I s u)

-- ####################################################################
-- # Committed State Invariants
-- ####################################################################

invariant [unique_committed_ixn]
  (¬ ctx.is_byz N ∧ committed_ixn N I1 ∧ committed_ixn N I2) → I1 = I2

invariant [node_has_committed_ixn]
  ∀ (n : node), ¬ ctx.is_byz n → ∃ (i : interaction), committed_ixn n i

invariant [committed_ixn_decided]
  (¬ ctx.is_byz N ∧ committed_ixn N I) →
    ∃ (V : view), decided N V I

invariant [committed_ixn_is_genesis_or_has_parent]
  (¬ ctx.is_byz N ∧ committed_ixn N I ∧ I ≠ genesis) → ∃ (J : interaction), parent J I

invariant [committed_ixn_descends_from_genesis]
  (¬ ctx.is_byz N ∧ committed_ixn N I) → ancestor genesis I

invariant [committed_ixn_precommit_locked]
  (¬ ctx.is_byz N ∧ committed_ixn N I ∧ I ≠ genesis) →
    ∃ (V : view), locked N I precommit V

invariant [committed_ixn_unique_at_height]
  (¬ ctx.is_byz N1 ∧ ¬ ctx.is_byz N2 ∧
   committed_ixn N1 I1 ∧ committed_ixn N2 I2 ∧
   height I1 = height I2) → I1 = I2

invariant [committed_ixn_height_positive]
  (¬ ctx.is_byz N ∧ committed_ixn N I ∧ I ≠ genesis) → height I ≥ 1

-- Genesis frontier: a precommit-backed interaction is real (precommit-QC'd), so
-- height 0 forces it to be genesis. Needed to close the `ci = genesis` (height-0
-- parent) subcase of proposed_repropose_parent_matches_committed at propose_repropose.
-- Near-leaf: at the precommit-setting action the backed interaction has height ≥ 1
-- (it was proposed) or is genesis; via precommit_backed_fwd → honest precommitter →
-- locked_height_positive.  Preserved elsewhere by precommit_backed monotonicity.
invariant [precommit_backed_height_zero_is_genesis]
  (precommit_backed V I ∧ height I = 0) → I = genesis

-- ####################################################################
-- # Height Positivity Invariants
-- ####################################################################

invariant [locked_height_positive]
  (¬ ctx.is_byz N ∧ locked N I S V ∧ I ≠ genesis) → height I ≥ 1

invariant [proposed_height_positive]
  (¬ ctx.is_byz OP ∧ (proposed_repropose OP V I ∨ proposed_extend OP V I) ∧ I ≠ genesis) →
    height I ≥ 1

invariant [decided_height_positive]
  (¬ ctx.is_byz N ∧ decided N V I ∧ I ≠ genesis) → height I ≥ 1

invariant [prevoted_height_positive]
  (¬ ctx.is_byz N ∧ prevoted_node N V I ∧ I ≠ genesis) → height I ≥ 1


-- RED under Byzantine actions — NOT guard-fixable. The honest rationale was:
-- precommit_backed is written ONLY by respond_precommit, which co-fires
-- `decided n v ixn`, so both sets grow in lockstep. That fails here:
-- respond_precommit writes `decided` only for its EXECUTOR, and byz nodes run
-- the honest shell, so a byz executor can fire respond_precommit (setting the
-- precommit_backed ghost, which byz cannot write directly) and then retract its
-- own row with byz_undecide, leaving the ghost with no decision witness.
-- A ¬is_byz guard cannot help: `decided` here is a positive CONCLUSION, so a
-- guard strengthens the goal. Repair options: name an honest witness (requires
-- respond_precommit to record one), or drop this leaf and reroute its consumer
-- (committed_implies_parent_committed) onto precommit_backed_fwd's QC instead.
-- ##### COMMENTED OUT (Byzantine-false) #####
-- FALSE under byz: respond_precommit sets the precommit_backed ghost but
-- writes `decided` only for its EXECUTOR; byz nodes run the honest shell, so
-- a byz executor fires it and then retracts with byz_undecide. Consumers
-- should route through precommit_backed_fwd (QC form) instead.
-- invariant [precommit_backed_implies_decided]
--   precommit_backed V I → ∃ (n : node), decided n V I

-- REPAIRED with ¬is_byz N. The old rationale ("Byzantine-robust — no honesty
-- guard needed: committed_ixn rows are rewritten ONLY in respond_precommit's
-- if-branch") predates byz_state, which havocs `committed_ixn n I := *` over a
-- byz node's whole slice. For an HONEST N the original argument stands: the
-- only writer is respond_precommit's if-branch, atomically with the
-- unconditional `precommit_backed v ixn := true`; init rows are {genesis},
-- exempted by the guard; precommit_backed is monotone.
invariant [committed_ixn_implies_precommit_backed]
  (¬ ctx.is_byz N ∧ committed_ixn N I ∧ I ≠ genesis) → ∃ (W : view), precommit_backed W I

-- RED under Byzantine actions — NOT guard-fixable (`parent` carries no node
-- argument, so there is no owner to guard). The honest rationale was: `parent`
-- is written ONLY at propose_extend, with parent = ci where `require
-- committed_ixn op ci` binds even Byzantine operators, so
-- committed_ixn_implies_precommit_backed (pre-state) supplies the witness.
-- That step is exactly what breaks — the HONEST-SHELL MINT. Byz nodes run
-- every honest action, so a byz operator fakes `committed_ixn op ci` via
-- byz_state for an arbitrary genesis-descendant ci, then passes
-- propose_extend's gates honestly and writes `parent ci ixn_propose` for an
-- uncertified ci. Guarding committed_ixn_implies_precommit_backed with
-- ¬is_byz N (done above) is what removes the pre-state witness here.
-- Repair: weaken the conclusion to the vote-QC form that actually survives
-- (a precommit QC at some W for I), mirroring op_argmax_qc_backed.
-- Consumer: committed_implies_parent_committed at respond_precommit, which is
-- itself RED for the same reason and needs the same QC-form restatement.
-- ##### COMMENTED OUT (Byzantine-false) #####
-- FALSE under byz via the HONEST-SHELL MINT: a byz operator fakes
-- committed_ixn with byz_state, then passes propose_extend's gates honestly
-- and writes `parent ci ixn` for an uncertified ci. `parent` has no node
-- argument, so there is nothing to guard. Repair: QC-form conclusion.
-- invariant [parent_implies_parent_precommit_backed]
--   (parent I J ∧ I ≠ genesis) → ∃ (W : view), precommit_backed W I


-- Bridge leaf (#181, keep LAST — active positional proofs reference ≤ #88; the
-- commented respond_precommit drafts' #180 chains need a trailing `.1` if revived):
-- a reproposal row carries the operator's frozen argmax cache. By construction
-- at propose_repropose — its requires are literally this conclusion
-- (prepares_collected, op_argmax_ixn op v ixn_max, op_argmax_stage op v s_max
-- with s_max = prevote, op_argmax_view op v v_max). Preserved everywhere else:
-- op_argmax_* is written only by collect_prepares under `require
-- ¬ prepares_collected op v`, and the prepares_collected conjunct here rules
-- that out at any reproposal row (prepares_collected is monotone and
-- proposed_repropose has no other writer).
invariant [reproposed_implies_argmax]
  (¬ ctx.is_byz OP ∧ proposed_repropose OP V I) →
    (prepares_collected OP V ∧ op_argmax_ixn OP V I ∧
     op_argmax_stage OP V prevote ∧ ∃ (VM : view), op_argmax_view OP V VM)

-- Byzantine-robust bridge (#182): an HONEST precommit vote directly witnesses
-- the prevote supermajority that caused it (respond_prevote's quorum require,
-- lifted into a state invariant). Replaces the operator route
-- (precommitted_node_implies_prevote_qc → prevote_operator_only_if_quorum_prevoted),
-- which dies when the view's operator is Byzantine. Established verbatim at
-- respond_prevote; preserved monotonically everywhere else (prevoted_node and
-- the quorum witness only grow; byz_precommit rows are excluded by the guard).
invariant [precommitted_node_implies_prevote_quorum]
  (¬ ctx.is_byz N ∧ precommitted_node N V I) →
    ∃ (s : nodeset), ctx.supermajority s ∧ ∀ (m : node), ctx.member m s → prevoted_node m V I


set_option veil.smt.timeout 15000
set_option maxHeartbeats 4000000
-- The Byzantine action set makes spec extraction recurse deeper than the
-- veil-module default of 1024 (Veil.veilDefaultOptions).
set_option maxRecDepth 8192
-- Spec extraction's simp normalization exceeds 4M heartbeats on the Byzantine
-- action set, so the cap has to be lifted for #gen_spec.
--
-- This MUST be a plain `set_option`, never `set_option maxHeartbeats 0 in #gen_spec`:
-- the `... in` form macro-expands to `section ... end` (Lean's expandInCmd), and the
-- closing `end` runs `popScope`, which drops the top frame of every scoped env
-- extension's state stack. Veil keeps the current module in exactly such an
-- extension (`localEnv`), so #gen_spec's finalization is elaborated and then
-- immediately discarded — every later command reports "The specification of module
-- IFPProtocolNTDPH has not been finalized. Please call #gen_spec first!"
set_option maxHeartbeats 0
#gen_spec
-- Restore the cap for the manual theorems below.
set_option maxHeartbeats 4000000

set_option veil.printCounterexamples true

-- #check_action respond_propose_repropose


theorem respond_propose_repropose_locks_analog_precommit (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_propose_repropose_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1292099 view interaction χ node nodeset stage χ_rep]
    [respond_propose_repropose_dec_1 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1292170 node view χ interaction nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_propose_repropose.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_propose_repropose_dec_0
          respond_propose_repropose_dec_1 n v ixn)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@locks_analog_precommit ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs op_w hop hpr h_no_prev hixn_ng hrc t t_1 t_2
    hari has hav h_stage_eq h_ixn_eq h_height_eq V V2 I J NP hnbyz hpb hI_ng hJ_ng h_prev_post hlt
  -- Ported from the archived IFPNTDP proof (in the comment block below), with the
  -- Byzantine adaptation the header owes at L740-756: the consumed invariants #4, #65
  -- and #69 are now ¬is_byz-guarded, so each application carries the matching honesty
  -- witness -- `hnbyz` for the executor n (available after `subst NP`), `hm_honest` for
  -- the quorum intersector mstar.
  --
  -- hinv conjunct positions for IFPB's CURRENT declaration order. `Invariants` is the
  -- right-nested conjunction of `Module.invariants`, which includes `safety` in source
  -- order, so main_safety = #1. NOTE: decided_implies_precommit_backed (L1325) is
  -- INDENTED -- a `^invariant` grep silently drops it and shifts everything from #40 on
  -- by one. 172 conjuncts total; the pattern below is a 70-slot prefix whose final slot
  -- absorbs #70..#172, so only the prefix positions have to be right.
  --   #2  locks_analog_precommit                         (h_lap)
  --   #3  argmax_recvd_ixn_descends_..._at_bounded_view  (h_step3)
  --   #4  recvd_collected_implies_bounded_prepare_quorum (h_rcibpq)
  --   #40 precommit_node_locked_at_same_view             (h_pcnlsv)
  --   #53 precommit_backed_fwd                           (h_pbf)
  --   #65 precommit_lock_implies_precommit_backed        (h_plipb)
  --   #69 highest_lock_sent                              (h_hls)
  obtain ⟨_,
          h_lap,
          h_step3,
          h_rcibpq,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          h_pcnlsv,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _,
          h_pbf,
          _, _, _, _, _,
          _, _, _, _, _,
          _,
          h_plipb,
          _, _, _,
          h_hls,
          _⟩ := hinv
  subst h_ixn_eq
  by_cases h_match : NP = n ∧ V2 = v ∧ J = ixn
  · obtain ⟨hNPeq, hV2eq, hJeq⟩ := h_match
    subst NP; subst V2; subst J
    by_cases h_le : TotalOrderWithMinimum.le V t_2
    · have h := h_step3 V v t_2 I ixn n hnbyz hpb hI_ng hari hav hlt h_le
      cases h with
      | inl heq => exact Or.inl heq.symm
      | inr hanc => exact Or.inr hanc
    · have le_lt_trans : ∀ {a b c : view},
          TotalOrderWithMinimum.le a b → TotalOrderWithMinimum.lt b c →
          TotalOrderWithMinimum.lt a c := by
        intros a b c hab hbc
        have ⟨hbc_le, hbc_ne⟩ := (tot_view.le_lt _ _).mp hbc
        refine (tot_view.le_lt _ _).mpr ⟨tot_view.le_trans _ _ _ hab hbc_le, ?_⟩
        rintro rfl
        exact hbc_ne (tot_view.le_antisymm _ _ hab hbc_le).symm
      have h_t2_lt_V : TotalOrderWithMinimum.lt t_2 V := by
        rcases tot_view.le_total V t_2 with hVT | hTV
        · exact absurd hVT h_le
        · refine (tot_view.le_lt _ _).mpr ⟨hTV, ?_⟩
          rintro rfl
          exact h_le (tot_view.le_refl _)
      obtain ⟨t_set, ht_sm, ht_mem⟩ := h_pbf V I hpb
      -- #4 is now guarded: `(¬is_byz N ∧ recvd_collected N VACT ∧ argmax_recvd_view ...)`.
      obtain ⟨s_set, hs_sm, hs_mem⟩ := h_rcibpq n v t_2 hnbyz hrc hav
      obtain ⟨mstar, hm_s, hm_t, hm_honest⟩ :=
        ctx.supermajorities_intersect_in_honest s_set t_set ⟨hs_sm, ht_sm⟩
      have hpc_m : st.precommitted_node mstar V I = true := ht_mem mstar hm_t
      -- #4's conclusion now reads `∀ m, ¬is_byz m → member m s → ...`.
      obtain ⟨_, IL, SL, VL, h_slip, _, h_VL_le⟩ := hs_mem mstar hm_honest hm_s
      obtain ⟨_, _, h_no_lock_btw, _⟩ := h_hls mstar v IL SL VL hm_honest h_slip
      have h_VL_lt_V : TotalOrderWithMinimum.lt VL V := le_lt_trans h_VL_le h_t2_lt_V
      have h_lock_choice := h_pcnlsv mstar V I hm_honest hpc_m hI_ng
      cases h_lock_choice with
      | inl h_prev_V =>
        have h_no := h_no_lock_btw I th.prevote V h_VL_lt_V hlt
        exact absurd h_prev_V (fun h => by rw [h] at h_no; exact Bool.noConfusion h_no)
      | inr h_pre_exists =>
        obtain ⟨U, h_U_le_V, h_loc_U⟩ := h_pre_exists
        by_cases h_U_le_t2 : TotalOrderWithMinimum.le U t_2
        · have h_pb_U : st.precommit_backed U I = true :=
            h_plipb mstar I U hm_honest h_loc_U hI_ng
          have h_U_lt_v : TotalOrderWithMinimum.lt U v := le_lt_trans h_U_le_V hlt
          have h := h_step3 U v t_2 I ixn n hnbyz h_pb_U hI_ng hari hav h_U_lt_v h_U_le_t2
          cases h with
          | inl heq => exact Or.inl heq.symm
          | inr hanc => exact Or.inr hanc
        · have h_t2_lt_U : TotalOrderWithMinimum.lt t_2 U := by
            rcases tot_view.le_total U t_2 with hUT | hTU
            · exact absurd hUT h_U_le_t2
            · refine (tot_view.le_lt _ _).mpr ⟨hTU, ?_⟩
              rintro rfl
              exact h_U_le_t2 (tot_view.le_refl _)
          have h_VL_lt_U : TotalOrderWithMinimum.lt VL U := le_lt_trans h_VL_le h_t2_lt_U
          have h_U_lt_v : TotalOrderWithMinimum.lt U v := le_lt_trans h_U_le_V hlt
          have h_no := h_no_lock_btw I th.precommit U h_VL_lt_U h_U_lt_v
          exact absurd h_loc_U (fun h => by rw [h] at h_no; exact Bool.noConfusion h_no)
  · have h_neq : n = NP → v = V2 → ¬ixn = J := by
      intro hnNP hvV2 hixnJ
      exact h_match ⟨hnNP.symm, hvV2.symm, hixnJ.symm⟩
    exact h_lap V V2 I J NP hnbyz hpb hI_ng hJ_ng (h_prev_post h_neq) hlt

/-
-- ##### COMMENTED OUT (Byzantine-false) #####
-- proves op_argmax_is_highest_lock, now commented out.
-- theorem respond_prevote_op_argmax_is_highest_lock (ρ : Type) (σ : Type) (view : Type)
--     [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
--     [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
--     [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
--     (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
--     (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
--     [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
--     [χ_rep :
--       ∀ __veil_f,
--         Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
--           (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
--     [χ_rep_lawful :
--       ∀ __veil_f,
--         Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
--           (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
--     [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
--     [respond_prevote_dec_0 :
--       delta% @IFPProtocolNTDPH._veil_dec_type_1532375 view interaction χ node nodeset stage χ_rep]
--     [respond_prevote_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1532428 nodeset node ctx]
--     [respond_prevote_dec_2 :
--       delta% @IFPProtocolNTDPH._veil_dec_type_1532505 view interaction nodeset χ node ctx stage χ_rep]
--     [respond_prevote_dec_3 :
--       delta% @IFPProtocolNTDPH._veil_dec_type_1532590 node view interaction χ nodeset stage tot_view χ_rep] :
--     ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
--       Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
--         (@respond_prevote.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
--           interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
--           stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_prevote_dec_0 respond_prevote_dec_1
--           respond_prevote_dec_2 respond_prevote_dec_3 n v ixn s)
--         (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
--           interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
--           ρ_sub)
--         (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
--           interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
--           χ χ_rep χ_rep_lawful σ_sub ρ_sub)
--         (@op_argmax_is_highest_lock ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
--           interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
--           stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
--   by
--   veil_human
--   -- Operator-side mirror of respond_prevote_argmax_recvd_is_highest_lock.
--   -- op_argmax_* and sent_lock_in_prepare are frame-unchanged at respond_prevote;
--   -- only `locked` grows (guarded prevote-lock add), so the pre-state instance of
--   -- THIS invariant (hinv position 26) closes both `split_ifs` branches:
--   --   then (no lock written): `exact h_self`.
--   --   else (new lock added): witness lock discharges the new-tuple guard via `fun _ => h_lock`.
--   intro hv_nz hcv hcs x hop hpr hsm hmem
--   obtain ⟨_, _, _, _, _,
--           _, _, _, _, _,
--           _, _, _, _, _,
--           _, _, _, _, _,
--           _, _, _, _, _,
--           h_self, _⟩ := hinv
--   split_ifs
--   · exact h_self
--   · intro OP V IM SM VM h_byz h_ai h_as h_av
--     obtain ⟨M, h_sent, h_lock⟩ := h_self OP V IM SM VM h_byz h_ai h_as h_av
--     exact ⟨M, h_sent, fun _ => h_lock⟩



-- ##### COMMENTED OUT (Byzantine-false) #####
-- proves argmax_recvd_is_highest_lock, now commented out.
-- theorem respond_prevote_argmax_recvd_is_highest_lock (ρ : Type) (σ : Type) (view : Type)
--     [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
--     [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
--     [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
--     (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
--     (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
--     [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
--     [χ_rep :
--       ∀ __veil_f,
--         Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
--           (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
--     [χ_rep_lawful :
--       ∀ __veil_f,
--         Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
--           (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
--     [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
--     [respond_prevote_dec_0 :
--       delta% @IFPProtocolNTDPH._veil_dec_type_1532375 view interaction χ node nodeset stage χ_rep]
--     [respond_prevote_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1532428 nodeset node ctx]
--     [respond_prevote_dec_2 :
--       delta% @IFPProtocolNTDPH._veil_dec_type_1532505 view interaction nodeset χ node ctx stage χ_rep]
--     [respond_prevote_dec_3 :
--       delta% @IFPProtocolNTDPH._veil_dec_type_1532590 node view interaction χ nodeset stage tot_view χ_rep] :
--     ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
--       Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
--         (@respond_prevote.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
--           interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
--           stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_prevote_dec_0 respond_prevote_dec_1
--           respond_prevote_dec_2 respond_prevote_dec_3 n v ixn s)
--         (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
--           interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
--           ρ_sub)
--         (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
--           interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
--           χ χ_rep χ_rep_lawful σ_sub ρ_sub)
--         (@argmax_recvd_is_highest_lock ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
--           interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
--           stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
--   by
--   veil_human
--   -- veil_wp presents respond_prevote's guarded prevote-lock add as an `if ∃u… then A else
--   -- B` in the GOAL, with the invariant's ∀-binders INSIDE each branch. argmax_recvd_* and
--   -- sent_lock_in_prepare are frame-unchanged, so the pre-state instance of THIS invariant
--   -- (hinv position 27) closes both branches:
--   --   then (∃u holds ⇒ ¬(∃u) is false ⇒ no lock written ⇒ st.locked unchanged): `exact h_self`.
--   --   else (new lock added): witness lock discharges the new-tuple guard via `fun _ => h_lock`.
--   intro hv_nz hcv hcs x hop hpr hsm hmem
--   obtain ⟨_, _, _, _, _,
--           _, _, _, _, _,
--           _, _, _, _, _,
--           _, _, _, _, _,
--           _, _, _, _, _,
--           _, h_self, _⟩ := hinv
--   split_ifs
--   · exact h_self
--   · intro N V IM SM VM h_byz h_ai h_as h_av
--     obtain ⟨M, h_sent, h_lock⟩ := h_self N V IM SM VM h_byz h_ai h_as h_av
--     exact ⟨M, h_sent, fun _ => h_lock⟩

theorem respond_prevote_committed_descendant_at_height_implies_locked_descendant (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_prevote_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532375 view interaction χ node nodeset stage χ_rep]
    [respond_prevote_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1532428 nodeset node ctx]
    [respond_prevote_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532505 view interaction nodeset χ node ctx stage χ_rep]
    [respond_prevote_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532590 node view interaction χ nodeset stage tot_view χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_prevote.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_prevote_dec_0 respond_prevote_dec_1
          respond_prevote_dec_2 respond_prevote_dec_3 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@committed_descendant_at_height_implies_locked_descendant ρ σ view view_dec_eq view_inhabited node node_dec_eq
          node_inhabited interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited
          stage stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  -- committed_descendant_at_height is frame-unchanged at respond_prevote; the
  -- locked_descendant_at_height ghost only GROWS (row-rewrite
  -- `decide (old ∨ (ancestor A ixn ∧ H = height ixn))` under the relock guard), so
  -- the pre-state instance (hinv position 88) supplies the old bit in both branches.
  intro hv_nz hcv hcs x hop hpr hsm hmem
  have h_self := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  split_ifs
  · exact h_self
  · intro N A H h_cd
    have h_pre := h_self N A H h_cd
    by_cases hN : n = N
    · rw [if_pos hN, hN]
      exact Or.inl h_pre
    · rw [if_neg hN]
      exact h_pre

theorem respond_prevote_reproposed_relock_at_view_implies_argmax (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_prevote_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532375 view interaction χ node nodeset stage χ_rep]
    [respond_prevote_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1532428 nodeset node ctx]
    [respond_prevote_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532505 view interaction nodeset χ node ctx stage χ_rep]
    [respond_prevote_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532590 node view interaction χ nodeset stage tot_view χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_prevote.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_prevote_dec_0 respond_prevote_dec_1
          respond_prevote_dec_2 respond_prevote_dec_3 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@reproposed_relock_at_view_implies_argmax ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited
          interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage
          stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  -- The bridge leaf (reproposed_implies_argmax, #171; trailing .1 skips the
  -- appended #172) closes both split_ifs branches from the ¬is_byz OP +
  -- proposed_repropose antecedents alone: proposed_repropose and the
  -- op_argmax_* cache are frame-unchanged at respond_prevote, so the (possibly
  -- new) prevote-lock hypothesis is never consulted. Goal conclusion is the
  -- exists_and_left-narrowed form
  -- `op_argmax_ixn ∧ (∃ x, op_argmax_view x) ∧ op_argmax_stage`.
  intro hv_nz hcv hcs x hop hpr hsm hmem
  have h_bridge := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  split_ifs
  · intro OP V I N h_byz h_pr _h_lk
    obtain ⟨_h_pc, h_ai, h_as, VM, h_av⟩ := h_bridge OP V I h_byz h_pr
    exact ⟨h_ai, ⟨VM, h_av⟩, h_as⟩
  · intro OP V I N h_byz h_pr _h_lk
    obtain ⟨_h_pc, h_ai, h_as, VM, h_av⟩ := h_bridge OP V I h_byz h_pr
    exact ⟨h_ai, ⟨VM, h_av⟩, h_as⟩


-- ##### COMMENTED OUT (Byzantine-false) #####
-- CONSUMED reproposed_argmax_parent_committed (removed), so its proof no
-- longer elaborates. The invariant it proves
-- (proposed_repropose_parent_matches_committed) SURVIVES and now falls back
-- to SMT — re-derive this proof without the removed conjunct.
-- theorem propose_repropose_proposed_repropose_parent_matches_committed (ρ : Type) (σ : Type) (view : Type)
--     [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
--     [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
--     [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
--     (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
--     (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
--     [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
--     [χ_rep :
--       ∀ __veil_f,
--         Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
--           (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
--     [χ_rep_lawful :
--       ∀ __veil_f,
--         Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
--           (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
--     [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
--     [propose_repropose_dec_0 :
--       delta% @IFPProtocolNTDPH._veil_dec_type_908506 node view χ interaction nodeset stage χ_rep]
--     [propose_repropose_dec_1 :
--       delta% @IFPProtocolNTDPH._veil_dec_type_908583 node view χ interaction nodeset stage χ_rep] :
--     ∀ (op : node) (v : view) (ci : interaction),
--       Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
--         (@propose_repropose.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
--           interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
--           stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub propose_repropose_dec_0 propose_repropose_dec_1
--           op v ci)
--         (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
--           interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
--           ρ_sub)
--         (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
--           interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
--           χ χ_rep χ_rep_lawful σ_sub ρ_sub)
--         (@proposed_repropose_parent_matches_committed ρ σ view view_dec_eq view_inhabited node node_dec_eq
--           node_inhabited interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited
--           stage stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
--   by
--   veil_human
--   intro hv_nz hcv hop hpo hpc hcs hnr hne t t_1 t_2 ham_i ham_s ham_v hci hgen hht hpv
--     OP V J I CI hbyz hpp hpar hcom hheq
--   subst hpv
--   -- Extract needed invariants from hinv (positions = source declaration order).
--   have h_rapc := hinv.2.2.2.1
--   have h_prpmc := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   have h_upbh := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   have h_plipb := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   have h_ph := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   have h_up := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   have h_ghz := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   have h_cipl := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   have h_ciuah := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   have h_cihp := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   have h_pbhzg := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   by_cases h_match : op = OP ∧ v = V ∧ t = J
--   · -- New tuple (OP,V,J) = (op,v,t): `t` is the freshly-reproposed interaction.
--     obtain ⟨rfl, rfl, rfl⟩ := h_match
--     -- t ≠ genesis: height t = height ci + 1 ≥ 1.
--     have ht_ng : ¬ t = st.genesis := by
--       intro hc
--       obtain ⟨hh0, _⟩ := (h_ghz t).mpr hc
--       omega
--     -- Ungated reproposed_argmax_parent_committed: t's parent P is precommit-backed.
--     obtain ⟨P, hP_par, W, hW_lt, hP_pb⟩ := h_rapc op v t t_2 hbyz ham_i ham_s ham_v ht_ng
--     -- unique_parent ⇒ P = I; carry the precommit-backing to I.
--     have hPI : P = I := h_up P t I hP_par hpar
--     rw [hPI] at hP_pb
--     -- height I = height ci (parent_height) and height CI = height ci.
--     have hht_tI : st.height t = st.height I + 1 := h_ph I t hpar
--     have hhIci : st.height I = st.height ci := by omega
--     have hhCIci : st.height CI = st.height ci := by omega
--     -- CI = ci (committed_ixn_unique_at_height); reduce the goal to I = ci.
--     have hCIci : CI = ci := h_ciuah op op CI ci hbyz hbyz hcom hci hhCIci
--     rw [hCIci]
--     -- Genesis frontier split.
--     by_cases hcig : ci = st.genesis
--     · have hci0 : st.height ci = 0 := ((h_ghz ci).mpr hcig).1
--       have hI0 : st.height I = 0 := by omega
--       exact (h_pbhzg W I hP_pb hI0).trans hcig.symm
--     · have hci_pos : st.height ci ≥ 1 := h_cihp op ci hbyz hci hcig
--       have hI_ng : ¬ I = st.genesis := by
--         intro hc
--         obtain ⟨hh0, _⟩ := (h_ghz I).mpr hc
--         omega
--       obtain ⟨Vc, hlock⟩ := h_cipl op ci hbyz hci hcig
--       have hci_pb : st.precommit_backed Vc ci = true := h_plipb op ci Vc hlock hcig
--       exact h_upbh W I Vc ci hP_pb hci_pb hI_ng hcig hhIci
--   · -- Pre-existing repropose: (OP,V,J) ≠ (op,v,t); pre-state invariant discharges it.
--     have hpre : st.proposed_repropose OP V J = true := by
--       apply hpp
--       intro hoOP hvV htJ
--       exact h_match ⟨hoOP, hvV, htJ⟩
--     exact h_prpmc OP V J I CI hbyz hpre hpar hcom hheq


theorem propose_extend_locked_descendant_at_height_bwd (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [propose_extend_dec_0 : delta% @IFPProtocolNTDPH._veil_dec_type_1012722 interaction χ view node nodeset stage χ_rep]
    [propose_extend_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1012797 interaction χ view node nodeset stage χ_rep]
    [propose_extend_dec_2 : delta% @IFPProtocolNTDPH._veil_dec_type_1012881 node view χ interaction nodeset stage χ_rep]
    [propose_extend_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1012968 node view χ interaction nodeset stage χ_rep] :
    ∀ (op : node) (v : view) (ixn_propose : interaction) (ci : interaction),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@propose_extend.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub propose_extend_dec_0 propose_extend_dec_1
          propose_extend_dec_2 propose_extend_dec_3 op v ixn_propose ci)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@locked_descendant_at_height_bwd ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited
          interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage
          stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz h_nopar h_noanc h_h0 hcv hop hpo hpc hcs h_ng h_nrepr h_next
    t t_1 t_2 hari hstg hav hci hgen_ci hht_max hci_ne hanc1 hanc2
    N A H h_byz h_ldah
  -- `locked_descendant_at_height N A H` is on a relation propose_extend never
  -- touches, so it is the pre-state fact: conjunct #77 of hinv gives a witness.
  -- (Bundle order here differs from IFPNTDPH2: locked_descendant_at_height_bwd is
  -- #77, not #3 — there are 76 conjuncts ahead of it, incl the indented
  -- decided_implies_precommit_backed at #39 and safety[main_safety] at #23.)
  obtain ⟨I, ⟨S, V, h_locked⟩, h_anc, h_ht⟩ :=
    hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      N A H h_byz h_ldah
  -- Freshness: the witness I cannot be the brand-new ixn_propose. I is locked
  -- (h_locked); locked_height_positive (hinv conjunct #166) gives height I ≥ 1,
  -- contradicting ixn_propose's height 0 (h_h0). With I ≠ ixn_propose, both
  -- `if ixn_propose = I` guards take the else-branch.
  have h_lhp := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h_ne : ¬ ixn_propose = I := by
    intro h_eq
    rw [← h_eq] at h_locked
    have h_pos := h_lhp N ixn_propose S V h_locked h_ng
    omega
  exact ⟨I, ⟨S, V, h_locked⟩,
    by rw [if_neg h_ne]; exact h_anc,
    by rw [if_neg h_ne]; exact h_ht⟩

theorem collect_recvd_locks_argmax_recvd_qc_backed (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [collect_recvd_locks_dec_0 : delta% @IFPProtocolNTDPH._veil_dec_type_1167942 nodeset node ctx]
    [collect_recvd_locks_dec_1 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1168068 view nodeset χ node ctx interaction stage χ_rep tot_view]
    [collect_recvd_locks_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1168172 view χ node interaction stage nodeset χ_rep tot_view]
    [collect_recvd_locks_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1168284 view χ node interaction stage tot_view nodeset χ_rep]
    [collect_recvd_locks_dec_4 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1168414 interaction stage view χ node nodeset ctx χ_rep] :
    ∀ (n : node) (v : view) (s : nodeset) (n_max : node) (ixn_max : interaction) (s_max : stage) (v_max : view),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@collect_recvd_locks.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub collect_recvd_locks_dec_0
          collect_recvd_locks_dec_1 collect_recvd_locks_dec_2 collect_recvd_locks_dec_3 collect_recvd_locks_dec_4 n v s
          n_max ixn_max s_max v_max)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@argmax_recvd_qc_backed ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs hpn hnrc hsm hmem hsl_max hlk_max hdom hgap tmax htmax_sm htmax_pv
    htmax_pc N V IM SM VM h_byz h_ixn h_stage h_view
  by_cases h_match : n = N ∧ v = V
  · -- New write at (n, v): the argmax_recvd_* updates decode to (ixn_max, s_max, v_max),
    -- and the action's step-3 precondition (tmax) is exactly the QC-backing witness.
    rw [if_pos h_match] at h_ixn h_stage h_view
    subst IM SM VM
    exact ⟨fun he => ⟨tmax, htmax_sm, htmax_pv he⟩, fun he => ⟨tmax, htmax_sm, htmax_pc he⟩⟩
  · -- Pre-state: (N, V) ≠ (n, v). collect_recvd_locks leaves argmax_recvd_* and
    -- prevoted_node / precommitted_node at (N, V) untouched, so the pre-state instance
    -- of argmax_recvd_qc_backed (hinv conjunct 42) applies.
    rw [if_neg h_match] at h_ixn h_stage h_view
    exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      N V IM SM VM h_byz h_ixn h_stage h_view



-- ##### COMMENTED OUT (Byzantine-false) #####
-- proves reproposal_extends_decided_parent, now commented out.
-- theorem respond_propose_repropose_reproposal_extends_decided_parent (ρ : Type) (σ : Type) (view : Type)
--     [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
--     [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
--     [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
--     (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
--     (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
--     [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
--     [χ_rep :
--       ∀ __veil_f,
--         Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
--           (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
--     [χ_rep_lawful :
--       ∀ __veil_f,
--         Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
--           (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
--     [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
--     [respond_propose_repropose_dec_0 :
--       delta% @IFPProtocolNTDPH._veil_dec_type_1292099 view interaction χ node nodeset stage χ_rep]
--     [respond_propose_repropose_dec_1 :
--       delta% @IFPProtocolNTDPH._veil_dec_type_1292170 node view χ interaction nodeset stage χ_rep] :
--     ∀ (n : node) (v : view) (ixn : interaction),
--       Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
--         (@respond_propose_repropose.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
--           interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
--           stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_propose_repropose_dec_0
--           respond_propose_repropose_dec_1 n v ixn)
--         (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
--           interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
--           ρ_sub)
--         (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
--           interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
--           χ χ_rep χ_rep_lawful σ_sub ρ_sub)
--         (@reproposal_extends_decided_parent ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited
--           interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage
--           stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
--   by
--   veil_human
--   intro hv_nz hcv hcs op_w hop hpr h_no_prev hixn_ng hrc t t_1 t_2
--     hari has hav h_stage_eq h_ixn_eq h_height_eq N V J hnbyz h_prev_post hJ_ng hV_nz h_argstage
--   -- hinv positions (same declaration order as the locks_analog_precommit proof below):
--   -- reproposal_extends_decided_parent=10, argmax_recvd_is_highest_lock=27,
--   -- argmax_recvd_qc_backed=42, highest_lock_sent=76 (main_safety counted at 28).
--   obtain ⟨_, _, _, _, _,
--           _, _, _, _, h_repr,
--           _, _, _, _, _,
--           _, _, _, _, _,
--           _, _, _, _, _,
--           _, h_arihl, _, _, _,
--           _, _, _, _, _,
--           _, _, _, _, _,
--           _, h_qcb, _, _, _,
--           _, _, _, _, _,
--           _, _, _, _, _,
--           _, _, _, _, _,
--           _, _, _, _, _,
--           _, _, _, _, _,
--           _, _, _, _, _,
--           h_hls,
--           _⟩ := hinv
--   subst h_ixn_eq
--   by_cases h_match : N = n ∧ V = v ∧ J = ixn
--   · -- New prevote at (n, v, ixn): the cached argmax is prevote-stage, hence QC-backed
--     -- at v_max (argmax_recvd_qc_backed), and v_max < v via highest_lock_sent applied to
--     -- the argmax witness (argmax_recvd_is_highest_lock).
--     obtain ⟨hNeq, hVeq, hJeq⟩ := h_match
--     subst N; subst V; subst J
--     obtain ⟨Q, hQ_sm, hQ_mem⟩ := (h_qcb n v ixn t_1 t_2 hnbyz hari has hav).1 h_stage_eq
--     obtain ⟨M, h_sent, _⟩ := h_arihl n v ixn t_1 t_2 hnbyz hari has hav
--     have h_vmax_lt : tot_view.lt t_2 v := (h_hls M v ixn t_1 t_2 h_sent).2.1
--     exact ⟨t_2, h_vmax_lt, Q, hQ_sm, fun m hm => by simp [hQ_mem m hm]⟩
--   · -- Pre-existing prevote: (N, V, J) ≠ (n, v, ixn), so the pre-state invariant applies
--     -- and its witnesses survive (prevoted_node only grows under this action).
--     have h_neq : n = N → v = V → ¬ ixn = J := by
--       intro hnN hvV hixnJ
--       exact h_match ⟨hnN.symm, hvV.symm, hixnJ.symm⟩
--     obtain ⟨VM, hVM_lt, s, hs_sm, hs_mem⟩ :=
--       h_repr N V J hnbyz (h_prev_post h_neq) hJ_ng hV_nz h_argstage
--     exact ⟨VM, hVM_lt, s, hs_sm, fun m hm => by simp [hs_mem m hm]⟩

theorem respond_propose_extend_locks_analog_precommit (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_propose_extend_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1376353 view interaction χ node nodeset stage χ_rep]
    [respond_propose_extend_dec_1 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1376424 node view χ interaction nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_propose_extend.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_propose_extend_dec_0
          respond_propose_extend_dec_1 n v ixn)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@locks_analog_precommit ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs op_w hop hpr h_no_prev hixn_ng hrc t t_1 t_2
    hari has hav h_stage_eq h_ixn_neq h_parent h_height_eq V V2 I J NP hnbyz hpb hI_ng hJ_ng h_prev_post hlt
  -- Mirrors respond_propose_repropose_locks_analog_precommit. The ONLY structural
  -- difference: the new prevote J = ixn is the FRESH CHILD of the argmax interaction
  -- t (= ixn_max) — `require parent ixn_max ixn` — rather than ixn = ixn_max. So Step 3
  -- (h_step3) yields `I = t ∨ ancestor I t`; h_lift raises both branches to the goal
  -- `ixn = I ∨ ancestor I ixn` via h_anc_par (parent t ixn ⇒ ancestor t ixn) and
  -- h_anc_trans (transitivity). hinv positions for IFPNTDPH's CURRENT declaration order
  -- (main_safety + indented invariants counted):
  -- locks_analog_precommit=1, argmax_recvd_ixn_descends...=2,
  -- recvd_collected_implies_bounded_prepare_quorum=3, precommit_node_locked_at_same_view=40,
  -- precommit_backed_fwd=53, precommit_lock_implies_precommit_backed=65, highest_lock_sent=69,
  -- ancestor_from_parent=91, ancestor_trans=92.
  obtain ⟨h_lap,
          h_step3,
          h_rcibpq,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _,
          h_pcnlsv,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _,
          h_pbf,
          _, _, _, _, _,
          _, _, _, _, _,
          _,
          h_plipb,
          _, _, _,
          h_hls,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _,
          h_anc_par,
          h_anc_trans,
          _⟩ := hinv
  by_cases h_match : NP = n ∧ V2 = v ∧ J = ixn
  · obtain ⟨hNPeq, hV2eq, hJeq⟩ := h_match
    subst NP; subst V2; subst J
    -- Raise Step 3's `W = t ∨ ancestor W t` (t = ixn_max) to `ixn = W ∨ ancestor W ixn`,
    -- the goal with J = ixn, using parent t ixn (h_parent) + ancestor_from_parent + trans.
    have h_lift : ∀ (W : interaction),
        (W = t ∨ st.ancestor W t) → (ixn = W ∨ st.ancestor W ixn) := by
      intro W hW
      cases hW with
      | inl heq => exact Or.inr (by rw [heq]; exact h_anc_par t ixn h_parent)
      | inr hanc => exact Or.inr (h_anc_trans W t ixn hanc (h_anc_par t ixn h_parent))
    by_cases h_le : TotalOrderWithMinimum.le V t_2
    · exact h_lift I (h_step3 V v t_2 I t n hnbyz hpb hI_ng hari hav hlt h_le)
    · have le_lt_trans : ∀ {a b c : view},
          TotalOrderWithMinimum.le a b → TotalOrderWithMinimum.lt b c →
          TotalOrderWithMinimum.lt a c := by
        intros a b c hab hbc
        have ⟨hbc_le, hbc_ne⟩ := (tot_view.le_lt _ _).mp hbc
        refine (tot_view.le_lt _ _).mpr ⟨tot_view.le_trans _ _ _ hab hbc_le, ?_⟩
        rintro rfl
        exact hbc_ne (tot_view.le_antisymm _ _ hab hbc_le).symm
      have h_t2_lt_V : TotalOrderWithMinimum.lt t_2 V := by
        rcases tot_view.le_total V t_2 with hVT | hTV
        · exact absurd hVT h_le
        · refine (tot_view.le_lt _ _).mpr ⟨hTV, ?_⟩
          rintro rfl
          exact h_le (tot_view.le_refl _)
      obtain ⟨t_set, ht_sm, ht_mem⟩ := h_pbf V I hpb
      obtain ⟨s_set, hs_sm, hs_mem⟩ := h_rcibpq n v t_2 hrc hav
      obtain ⟨mstar, hm_s, hm_t, hm_honest⟩ :=
        ctx.supermajorities_intersect_in_honest s_set t_set ⟨hs_sm, ht_sm⟩
      have hpc_m : st.precommitted_node mstar V I = true := ht_mem mstar hm_t
      obtain ⟨_, IL, SL, VL, h_slip, _, h_VL_le⟩ := hs_mem mstar hm_s
      obtain ⟨_, _, h_no_lock_btw, _⟩ := h_hls mstar v IL SL VL h_slip
      have h_VL_lt_V : TotalOrderWithMinimum.lt VL V := le_lt_trans h_VL_le h_t2_lt_V
      have h_lock_choice := h_pcnlsv mstar V I hm_honest hpc_m hI_ng
      cases h_lock_choice with
      | inl h_prev_V =>
        have h_no := h_no_lock_btw I th.prevote V h_VL_lt_V hlt
        exact absurd h_prev_V (fun h => by rw [h] at h_no; exact Bool.noConfusion h_no)
      | inr h_pre_exists =>
        obtain ⟨U, h_U_le_V, h_loc_U⟩ := h_pre_exists
        by_cases h_U_le_t2 : TotalOrderWithMinimum.le U t_2
        · have h_pb_U : st.precommit_backed U I = true := h_plipb mstar I U h_loc_U hI_ng
          have h_U_lt_v : TotalOrderWithMinimum.lt U v := le_lt_trans h_U_le_V hlt
          exact h_lift I (h_step3 U v t_2 I t n hnbyz h_pb_U hI_ng hari hav h_U_lt_v h_U_le_t2)
        · have h_t2_lt_U : TotalOrderWithMinimum.lt t_2 U := by
            rcases tot_view.le_total U t_2 with hUT | hTU
            · exact absurd hUT h_U_le_t2
            · refine (tot_view.le_lt _ _).mpr ⟨hTU, ?_⟩
              rintro rfl
              exact h_U_le_t2 (tot_view.le_refl _)
          have h_VL_lt_U : TotalOrderWithMinimum.lt VL U := le_lt_trans h_VL_le h_t2_lt_U
          have h_U_lt_v : TotalOrderWithMinimum.lt U v := le_lt_trans h_U_le_V hlt
          have h_no := h_no_lock_btw I th.precommit U h_VL_lt_U h_U_lt_v
          exact absurd h_loc_U (fun h => by rw [h] at h_no; exact Bool.noConfusion h_no)
  · have h_neq : n = NP → v = V2 → ¬ixn = J := by
      intro hnNP hvV2 hixnJ
      exact h_match ⟨hnNP.symm, hvV2.symm, hixnJ.symm⟩
    exact h_lap V V2 I J NP hnbyz hpb hI_ng hJ_ng (h_prev_post h_neq) hlt


-- Successfully Proven.
theorem collect_recvd_locks_recvd_collected_implies_bounded_prepare_quorum (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [collect_recvd_locks_dec_0 : delta% @IFPProtocolNTDPH._veil_dec_type_1167942 nodeset node ctx]
    [collect_recvd_locks_dec_1 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1168068 view nodeset χ node ctx interaction stage χ_rep tot_view]
    [collect_recvd_locks_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1168172 view χ node interaction stage nodeset χ_rep tot_view]
    [collect_recvd_locks_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1168284 view χ node interaction stage tot_view nodeset χ_rep]
    [collect_recvd_locks_dec_4 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1168414 interaction stage view χ node nodeset ctx χ_rep] :
    ∀ (n : node) (v : view) (s : nodeset) (n_max : node) (ixn_max : interaction) (s_max : stage) (v_max : view),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@collect_recvd_locks.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub collect_recvd_locks_dec_0
          collect_recvd_locks_dec_1 collect_recvd_locks_dec_2 collect_recvd_locks_dec_3 collect_recvd_locks_dec_4 n v s
          n_max ixn_max s_max v_max)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@recvd_collected_implies_bounded_prepare_quorum ρ σ view view_dec_eq view_inhabited node node_dec_eq
          node_inhabited interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited
          stage stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs hpn hnrc hsm hmem hsl_max hlk_max hdom hgap tmax htmax_sm htmax_pv
    htmax_pc N VACT VMAX h_rc h_av
  by_cases h_match : N = n ∧ VACT = v
  · -- New write at (n, v): the action's own prepare-quorum `s` witnesses RISK1, and
    -- VMAX = v_max via the argmax_recvd_view decide-update. VL ≤ VMAX comes from the
    -- argmax-dominance precondition `hdom`, NOT the per-member `vl ≤ v`.
    obtain ⟨hN, hV⟩ := h_match
    subst N
    subst VACT
    refine ⟨s, hsm, fun m hm => ?_⟩
    obtain ⟨h_prep, vl, ixnl, sl, h_sent, h_lock, _⟩ := hmem m hm
    refine ⟨h_prep, ixnl, sl, vl, h_sent, h_lock, ?_⟩
    have h_dom : tot_view.le vl v_max := hdom m ixnl sl vl h_sent
    rw [if_pos (And.intro rfl rfl)] at h_av
    rw [h_av]
    exact h_dom
  · -- Pre-state: (N, VACT) ≠ (n, v). collect_recvd_locks only writes recvd_collected /
    -- argmax_recvd_*, leaving sent_lock_in_prepare / locked / prepared_node untouched, so
    -- RISK1's pre-state instance (h_risk1 from hinv, declaration position 3) applies.
    obtain ⟨_, _, h_risk1, _⟩ := hinv
    have h_rc_pre : st.recvd_collected N VACT = true :=
      h_rc (fun hn hv => h_match ⟨hn.symm, hv.symm⟩)
    have h_match' : ¬(n = N ∧ v = VACT) := fun h => h_match ⟨h.1.symm, h.2.symm⟩
    rw [if_neg h_match'] at h_av
    exact h_risk1 N VACT VMAX h_rc_pre h_av

theorem respond_propose_repropose_locks_analog_precommit (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_propose_repropose_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1292099 view interaction χ node nodeset stage χ_rep]
    [respond_propose_repropose_dec_1 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1292170 node view χ interaction nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_propose_repropose.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_propose_repropose_dec_0
          respond_propose_repropose_dec_1 n v ixn)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@locks_analog_precommit ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs op_w hop hpr h_no_prev hixn_ng hrc t t_1 t_2
    hari has hav h_stage_eq h_ixn_eq h_height_eq V V2 I J NP hnbyz hpb hI_ng hJ_ng h_prev_post hlt
  -- PORTED from IFPNTDP.lean L2004-2159 (working). hinv positions for IFPNTDPH's
  -- CURRENT declaration order (main_safety + indented invariants counted):
  -- locks_analog_precommit=1, argmax_recvd_ixn_descends...=2,
  -- recvd_collected_implies_bounded_prepare_quorum=3, precommit_node_locked_at_same_view=40,
  -- precommit_backed_fwd=53, precommit_lock_implies_precommit_backed=65, highest_lock_sent=69.
  obtain ⟨h_lap,
          h_step3,
          h_rcibpq,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _,
          h_pcnlsv,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _,
          h_pbf,
          _, _, _, _, _,
          _, _, _, _, _,
          _,
          h_plipb,
          _, _, _,
          h_hls,
          _⟩ := hinv
  subst h_ixn_eq
  by_cases h_match : NP = n ∧ V2 = v ∧ J = ixn
  · obtain ⟨hNPeq, hV2eq, hJeq⟩ := h_match
    subst NP; subst V2; subst J
    by_cases h_le : TotalOrderWithMinimum.le V t_2
    · have h := h_step3 V v t_2 I ixn n hnbyz hpb hI_ng hari hav hlt h_le
      cases h with
      | inl heq => exact Or.inl heq.symm
      | inr hanc => exact Or.inr hanc
    · have le_lt_trans : ∀ {a b c : view},
          TotalOrderWithMinimum.le a b → TotalOrderWithMinimum.lt b c →
          TotalOrderWithMinimum.lt a c := by
        intros a b c hab hbc
        have ⟨hbc_le, hbc_ne⟩ := (tot_view.le_lt _ _).mp hbc
        refine (tot_view.le_lt _ _).mpr ⟨tot_view.le_trans _ _ _ hab hbc_le, ?_⟩
        rintro rfl
        exact hbc_ne (tot_view.le_antisymm _ _ hab hbc_le).symm
      have h_t2_lt_V : TotalOrderWithMinimum.lt t_2 V := by
        rcases tot_view.le_total V t_2 with hVT | hTV
        · exact absurd hVT h_le
        · refine (tot_view.le_lt _ _).mpr ⟨hTV, ?_⟩
          rintro rfl
          exact h_le (tot_view.le_refl _)
      obtain ⟨t_set, ht_sm, ht_mem⟩ := h_pbf V I hpb
      obtain ⟨s_set, hs_sm, hs_mem⟩ := h_rcibpq n v t_2 hrc hav
      obtain ⟨mstar, hm_s, hm_t, hm_honest⟩ :=
        ctx.supermajorities_intersect_in_honest s_set t_set ⟨hs_sm, ht_sm⟩
      have hpc_m : st.precommitted_node mstar V I = true := ht_mem mstar hm_t
      obtain ⟨_, IL, SL, VL, h_slip, _, h_VL_le⟩ := hs_mem mstar hm_s
      obtain ⟨_, _, h_no_lock_btw, _⟩ := h_hls mstar v IL SL VL h_slip
      have h_VL_lt_V : TotalOrderWithMinimum.lt VL V := le_lt_trans h_VL_le h_t2_lt_V
      have h_lock_choice := h_pcnlsv mstar V I hm_honest hpc_m hI_ng
      cases h_lock_choice with
      | inl h_prev_V =>
        have h_no := h_no_lock_btw I th.prevote V h_VL_lt_V hlt
        exact absurd h_prev_V (fun h => by rw [h] at h_no; exact Bool.noConfusion h_no)
      | inr h_pre_exists =>
        obtain ⟨U, h_U_le_V, h_loc_U⟩ := h_pre_exists
        by_cases h_U_le_t2 : TotalOrderWithMinimum.le U t_2
        · have h_pb_U : st.precommit_backed U I = true := h_plipb mstar I U h_loc_U hI_ng
          have h_U_lt_v : TotalOrderWithMinimum.lt U v := le_lt_trans h_U_le_V hlt
          have h := h_step3 U v t_2 I ixn n hnbyz h_pb_U hI_ng hari hav h_U_lt_v h_U_le_t2
          cases h with
          | inl heq => exact Or.inl heq.symm
          | inr hanc => exact Or.inr hanc
        · have h_t2_lt_U : TotalOrderWithMinimum.lt t_2 U := by
            rcases tot_view.le_total U t_2 with hUT | hTU
            · exact absurd hUT h_U_le_t2
            · refine (tot_view.le_lt _ _).mpr ⟨hTU, ?_⟩
              rintro rfl
              exact h_U_le_t2 (tot_view.le_refl _)
          have h_VL_lt_U : TotalOrderWithMinimum.lt VL U := le_lt_trans h_VL_le h_t2_lt_U
          have h_U_lt_v : TotalOrderWithMinimum.lt U v := le_lt_trans h_U_le_V hlt
          have h_no := h_no_lock_btw I th.precommit U h_VL_lt_U h_U_lt_v
          exact absurd h_loc_U (fun h => by rw [h] at h_no; exact Bool.noConfusion h_no)
  · have h_neq : n = NP → v = V2 → ¬ixn = J := by
      intro hnNP hvV2 hixnJ
      exact h_match ⟨hnNP.symm, hvV2.symm, hixnJ.symm⟩
    exact h_lap V V2 I J NP hnbyz hpb hI_ng hJ_ng (h_prev_post h_neq) hlt


theorem respond_prevote_recvd_collected_implies_bounded_prepare_quorum (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_prevote_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532375 view interaction χ node nodeset stage χ_rep]
    [respond_prevote_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1532428 nodeset node ctx]
    [respond_prevote_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532505 view interaction nodeset χ node ctx stage χ_rep]
    [respond_prevote_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1532590 node view interaction χ nodeset stage tot_view χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_prevote.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_prevote_dec_0 respond_prevote_dec_1
          respond_prevote_dec_2 respond_prevote_dec_3 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@recvd_collected_implies_bounded_prepare_quorum ρ σ view view_dec_eq view_inhabited node node_dec_eq
          node_inhabited interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited
          stage stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  -- Same shape as respond_prevote_argmax_recvd_is_highest_lock: veil_wp yields
  -- `if ∃u… then A else B` with the invariant's ∀-binders inside each branch.
  -- recvd_collected / argmax_recvd_view / prepared_node / sent_lock_in_prepare are all
  -- frame-unchanged, so the pre-state instance (hinv position 3) closes the then-branch
  -- verbatim; in the else-branch each member's witness lock discharges the tuple guard.
  intro hv_nz hcv hcs x hop hpr hsm hmem
  obtain ⟨_, _, h_self, _⟩ := hinv
  split_ifs
  · exact h_self
  · intro N VACT VMAX h_rc h_av
    obtain ⟨s_w, hsm_w, hmem_w⟩ := h_self N VACT VMAX h_rc h_av
    refine ⟨s_w, hsm_w, fun m hm => ?_⟩
    obtain ⟨h_prep, IL, SL, VL, h_sent, h_lock, h_le⟩ := hmem_w m hm
    exact ⟨h_prep, IL, SL, VL, h_sent, fun _ => h_lock, h_le⟩


theorem respond_precommit_committed_ixn_height_upper_bound (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_precommit_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693057 view interaction χ node nodeset stage χ_rep]
    [respond_precommit_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1693110 nodeset node ctx]
    [respond_precommit_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693187 view interaction nodeset χ node ctx stage χ_rep]
    [respond_precommit_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693266 node interaction χ view nodeset stage χ_rep]
    [respond_precommit_dec_4 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693359 node interaction χ view nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_precommit.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_precommit_dec_0 respond_precommit_dec_1
          respond_precommit_dec_2 respond_precommit_dec_3 respond_precommit_dec_4 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@committed_ixn_height_upper_bound ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited
          interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage
          stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs x hop hpo hsm hmem hdec1
  -- Pre-state committed_ixn_height_upper_bound is hinv conjunct #48.
  have h_ub := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  split_ifs with h_guard
  · -- Guard fired: some ci_old was committed strictly below height ixn, so
    -- committed_ixn n is rewritten to {ixn}. New decision closes by refl;
    -- old decisions are ≤ height ci_old < height ixn by the pre-state bound.
    obtain ⟨ci_old, h_ci_old, h_lt⟩ := h_guard
    intro N V I CI h_byz hdec h_ci
    by_cases h_new : n = N ∧ v = V ∧ ixn = I
    · obtain ⟨hN, -, hI⟩ := h_new
      rw [if_pos hN] at h_ci
      rw [← hI, h_ci]
    · have h_old : st.decided N V I = true := hdec fun h1 h2 h3 => h_new ⟨h1, h2, h3⟩
      by_cases hN : n = N
      · rw [if_pos hN] at h_ci
        rw [hN] at h_ci_old
        have h54 := h_ub N V I ci_old h_byz h_old h_ci_old
        rw [h_ci]
        omega
      · rw [if_neg hN] at h_ci
        exact h_ub N V I CI h_byz h_old h_ci
  · -- Guard did not fire: committed_ixn is unchanged and every committed ci
    -- already sits at height ≥ height ixn, bounding the new decision too.
    intro N V I CI h_byz hdec h_ci
    by_cases h_new : n = N ∧ v = V ∧ ixn = I
    · obtain ⟨hN, -, hI⟩ := h_new
      rw [← hN] at h_ci
      rw [← hI]
      rcases Nat.lt_or_ge (st.height CI) (st.height ixn) with h | h
      · exact absurd ⟨CI, h_ci, h⟩ h_guard
      · omega
    · have h_old : st.decided N V I = true := hdec fun h1 h2 h3 => h_new ⟨h1, h2, h3⟩
      exact h_ub N V I CI h_byz h_old h_ci

theorem respond_precommit_committed_descendant_height_bound (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_precommit_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693057 view interaction χ node nodeset stage χ_rep]
    [respond_precommit_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1693110 nodeset node ctx]
    [respond_precommit_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693187 view interaction nodeset χ node ctx stage χ_rep]
    [respond_precommit_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693266 node interaction χ view nodeset stage χ_rep]
    [respond_precommit_dec_4 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693359 node interaction χ view nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_precommit.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_precommit_dec_0 respond_precommit_dec_1
          respond_precommit_dec_2 respond_precommit_dec_3 respond_precommit_dec_4 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@committed_descendant_height_bound ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited
          interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage
          stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs x hop hpo hsm hmem hdec1 N A H h_byz h_cdah
  -- pre-state committed_descendant_height_bound (conjunct #80)
  have h_cb := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- ancestor_height_strict (conjunct #94)
  have h_ahs := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases hN : n = N
  · -- ghost marker for N is the just-written set: pre-existing or the new (ancestor A ixn, H = height ixn)
    rw [if_pos hN] at h_cdah
    rcases h_cdah with h_old | ⟨h_anc, h_H⟩
    · rw [hN] at h_old
      exact h_cb N A H h_byz h_old
    · by_cases h_eq : A = ixn
      · rw [h_eq]; omega
      · have := h_ahs A ixn h_anc h_eq; omega
  · rw [if_neg hN] at h_cdah
    exact h_cb N A H h_byz h_cdah

theorem respond_precommit_locked_descendant_height_bound (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_precommit_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693057 view interaction χ node nodeset stage χ_rep]
    [respond_precommit_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1693110 nodeset node ctx]
    [respond_precommit_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693187 view interaction nodeset χ node ctx stage χ_rep]
    [respond_precommit_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693266 node interaction χ view nodeset stage χ_rep]
    [respond_precommit_dec_4 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693359 node interaction χ view nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_precommit.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_precommit_dec_0 respond_precommit_dec_1
          respond_precommit_dec_2 respond_precommit_dec_3 respond_precommit_dec_4 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@locked_descendant_height_bound ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs x hop hpo hsm hmem hdec1 N A H h_byz h_ldah
  -- pre-state locked_descendant_height_bound (conjunct #79)
  have h_lb := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- ancestor_height_strict (conjunct #94)
  have h_ahs := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases hN : n = N
  · rw [if_pos hN] at h_ldah
    rcases h_ldah with h_old | ⟨h_anc, h_H⟩
    · rw [hN] at h_old
      exact h_lb N A H h_byz h_old
    · by_cases h_eq : A = ixn
      · rw [h_eq]; omega
      · have := h_ahs A ixn h_anc h_eq; omega
  · rw [if_neg hN] at h_ldah
    exact h_lb N A H h_byz h_ldah

theorem respond_precommit_committed_descendant_at_height_bwd (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_precommit_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693057 view interaction χ node nodeset stage χ_rep]
    [respond_precommit_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1693110 nodeset node ctx]
    [respond_precommit_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693187 view interaction nodeset χ node ctx stage χ_rep]
    [respond_precommit_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693266 node interaction χ view nodeset stage χ_rep]
    [respond_precommit_dec_4 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693359 node interaction χ view nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_precommit.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_precommit_dec_0 respond_precommit_dec_1
          respond_precommit_dec_2 respond_precommit_dec_3 respond_precommit_dec_4 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@committed_descendant_at_height_bwd ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited
          interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage
          stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs x hop hpo hsm hmem hdec1 N A H h_byz h_cdah
  -- pre-state committed_descendant_at_height_bwd (conjunct #78)
  have h_bwd := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases hN : n = N
  · rw [if_pos hN] at h_cdah
    rcases h_cdah with h_old | ⟨h_anc, h_H⟩
    · -- pre-existing ghost bit ⇒ pre-state witness, decided survives (monotone)
      rw [hN] at h_old
      obtain ⟨V, I, h_dec, h_anc2, h_ht⟩ := h_bwd N A H h_byz h_old
      exact ⟨V, I, fun _ => h_dec, h_anc2, h_ht⟩
    · -- new marker: the just-decided ixn is the witness (N = n, decided n v ixn)
      exact ⟨v, ixn, fun hguard => absurd rfl (hguard hN rfl), h_anc, h_H.symm⟩
  · rw [if_neg hN] at h_cdah
    obtain ⟨V, I, h_dec, h_anc2, h_ht⟩ := h_bwd N A H h_byz h_cdah
    exact ⟨V, I, fun _ => h_dec, h_anc2, h_ht⟩

theorem respond_precommit_locked_descendant_at_height_bwd (ρ : Type) (σ : Type) (view : Type)
    [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
    [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
    [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
    (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
    (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
    [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
          (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
    [respond_precommit_dec_0 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693057 view interaction χ node nodeset stage χ_rep]
    [respond_precommit_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1693110 nodeset node ctx]
    [respond_precommit_dec_2 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693187 view interaction nodeset χ node ctx stage χ_rep]
    [respond_precommit_dec_3 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693266 node interaction χ view nodeset stage χ_rep]
    [respond_precommit_dec_4 :
      delta% @IFPProtocolNTDPH._veil_dec_type_1693359 node interaction χ view nodeset stage χ_rep] :
    ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@respond_precommit.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
          interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
          stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_precommit_dec_0 respond_precommit_dec_1
          respond_precommit_dec_2 respond_precommit_dec_3 respond_precommit_dec_4 n v ixn s)
        (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          ρ_sub)
        (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
          interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
          χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@locked_descendant_at_height_bwd ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited
          interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage
          stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hv_nz hcv hcs x hop hpo hsm hmem hdec1 N A H h_byz h_ldah
  -- pre-state locked_descendant_at_height_bwd (conjunct #77)
  have h_bwd := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases hN : n = N
  · rw [if_pos hN] at h_ldah
    rcases h_ldah with h_old | ⟨h_anc, h_H⟩
    · rw [hN] at h_old
      obtain ⟨I, ⟨S, V, h_lock⟩, h_anc2, h_ht⟩ := h_bwd N A H h_byz h_old
      exact ⟨I, ⟨S, V, fun _ => h_lock⟩, h_anc2, h_ht⟩
    · -- new marker: the just-created precommit lock on ixn at v is the witness
      exact ⟨ixn, ⟨th.precommit, v, fun hguard => absurd rfl (hguard hN rfl rfl)⟩, h_anc, h_H.symm⟩
  · rw [if_neg hN] at h_ldah
    obtain ⟨I, ⟨S, V, h_lock⟩, h_anc2, h_ht⟩ := h_bwd N A H h_byz h_ldah
    exact ⟨I, ⟨S, V, fun _ => h_lock⟩, h_anc2, h_ht⟩

-- ##### COMMENTED OUT (Byzantine-false) #####
-- proves committed_implies_parent_committed, now commented out (it also
-- consumed #178 and #180, both removed).
-- theorem respond_precommit_committed_implies_parent_committed (ρ : Type) (σ : Type) (view : Type)
--     [view_dec_eq : DecidableEq.{1} view] [view_inhabited : Inhabited.{1} view] (node : Type)
--     [node_dec_eq : DecidableEq.{1} node] [node_inhabited : Inhabited.{1} node] (interaction : Type)
--     [interaction_dec_eq : DecidableEq.{1} interaction] [interaction_inhabited : Inhabited.{1} interaction]
--     (nodeset : Type) [nodeset_dec_eq : DecidableEq.{1} nodeset] [nodeset_inhabited : Inhabited.{1} nodeset]
--     (stage : Type) [stage_dec_eq : DecidableEq.{1} stage] [stage_inhabited : Inhabited.{1} stage]
--     [tot_view : TotalOrderWithMinimum view] [ctx : IFPByzQuorum node nodeset] (χ : State.Label → Type)
--     [χ_rep :
--       ∀ __veil_f,
--         Veil.FieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
--           (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f)]
--     [χ_rep_lawful :
--       ∀ __veil_f,
--         Veil.LawfulFieldRepresentation (State.Label.toDomain view node interaction nodeset stage __veil_f)
--           (State.Label.toCodomain view node interaction nodeset stage __veil_f) (χ __veil_f) (χ_rep __veil_f)]
--     [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory view node interaction nodeset stage) ρ]
--     [respond_precommit_dec_0 :
--       delta% @IFPProtocolNTDPH._veil_dec_type_1693057 view interaction χ node nodeset stage χ_rep]
--     [respond_precommit_dec_1 : delta% @IFPProtocolNTDPH._veil_dec_type_1693110 nodeset node ctx]
--     [respond_precommit_dec_2 :
--       delta% @IFPProtocolNTDPH._veil_dec_type_1693187 view interaction nodeset χ node ctx stage χ_rep]
--     [respond_precommit_dec_3 :
--       delta% @IFPProtocolNTDPH._veil_dec_type_1693266 node interaction χ view nodeset stage χ_rep]
--     [respond_precommit_dec_4 :
--       delta% @IFPProtocolNTDPH._veil_dec_type_1693359 node interaction χ view nodeset stage χ_rep] :
--     ∀ (n : node) (v : view) (ixn : interaction) (s : nodeset),
--       Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
--         (@respond_precommit.ext ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction
--           interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq
--           stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub respond_precommit_dec_0 respond_precommit_dec_1
--           respond_precommit_dec_2 respond_precommit_dec_3 respond_precommit_dec_4 n v ixn s)
--         (@Assumptions ρ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
--           interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
--           ρ_sub)
--         (@Invariants ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited interaction interaction_dec_eq
--           interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage stage_dec_eq stage_inhabited tot_view ctx
--           χ χ_rep χ_rep_lawful σ_sub ρ_sub)
--         (@committed_implies_parent_committed ρ σ view view_dec_eq view_inhabited node node_dec_eq node_inhabited
--           interaction interaction_dec_eq interaction_inhabited nodeset nodeset_dec_eq nodeset_inhabited stage
--           stage_dec_eq stage_inhabited tot_view ctx χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
--   by
--   veil_human
--   intro hv_nz hcv hcs x hop hpo hsm hmem hdec1 M V J I hdec h_par h_Jg
--   -- precommit_qc_unique_at_view (#12)
--   have h_qcu := hinv.2.2.2.2.2.2.2.2.2.2.2.1
--   -- committed_implies_parent_committed pre-state (#56)
--   have h_cipc := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   -- precommitted_node_view_bound (#59)
--   have h_pvb := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   -- precommit_backed_fwd (#60)
--   have h_pbf := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   -- parent_irreflexive (#107)
--   have h_pirr := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   -- genesis_decided_at_zero (#150)
--   have h_gz := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   -- precommit_backed_implies_decided bridge (#178)
--   have h_pbd := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   -- parent_implies_parent_precommit_backed (#180; #181 reproposed_implies_argmax follows, hence trailing .1)
--   have h_pipb := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
--   by_cases h_new : n = M ∧ v = V ∧ ixn = J
--   · -- CASE B: the tuple (M, V, J) is the new decision (n, v, ixn).
--     obtain ⟨hM, hV, hJ⟩ := h_new
--     subst hM; subst hV; subst hJ
--     by_cases h_Ig : I = st.genesis
--     · -- parent is genesis: decided by every node at view zero < v
--       rw [h_Ig]
--       exact ⟨tot_view.zero,
--         (tot_view.le_lt tot_view.zero v).mpr ⟨tot_view.zero_lt v, fun h => hv_nz h.symm⟩,
--         n, fun _ => h_gz n⟩
--     · -- Non-genesis parent: by construction, `parent I ixn` was written at ixn's
--       -- propose_extend birth with I = the proposer's committed_ixn (an action
--       -- require, binding Byzantine operators too), so I is precommit-backed at
--       -- some W (#180) and hence decided at W by some node (#178). W ≠ v: the
--       -- W-quorum from precommit_backed_fwd (#60) against this action's (v, ixn)
--       -- precommit quorum forces I = ixn via precommit_qc_unique_at_view (#12),
--       -- killed by parent_irreflexive (#107). W ≤ v: an honest member of the
--       -- W-quorum precommitted at W while cur_view is v (#59). Hence W < v.
--       obtain ⟨W, h_pb⟩ := h_pipb I ixn h_par h_Ig
--       obtain ⟨n', h_dec'⟩ := h_pbd W I h_pb
--       obtain ⟨s1, hs1_sm, hs1_mem⟩ := h_pbf W I h_pb
--       obtain ⟨m1, hm1_mem, -, hm1_hon⟩ :=
--         ctx.supermajorities_intersect_in_honest s1 s1 ⟨hs1_sm, hs1_sm⟩
--       have h_le : tot_view.le W v := h_pvb m1 n v W I hm1_hon hcv (hs1_mem m1 hm1_mem)
--       have h_ne : W ≠ v := by
--         intro h_eq
--         rw [h_eq] at hs1_mem
--         have h_I : I = ixn := h_qcu v I ixn s1 hs1_sm hs1_mem s hsm hmem
--         rw [h_I, h_pirr] at h_par
--         exact Bool.noConfusion h_par
--       exact ⟨W, (tot_view.le_lt W v).mpr ⟨h_le, h_ne⟩, n', fun _ => h_dec'⟩
--   · -- CASE A: pre-existing decision — pre-state invariant + decided monotone.
--     have h_dJ : st.decided M V J = true := hdec fun h1 h2 h3 => h_new ⟨h1, h2, h3⟩
--     obtain ⟨u, h_lt, x₀, h_dI⟩ := h_cipc M V J I h_dJ h_par h_Jg
--     exact ⟨u, h_lt, x₀, fun _ => h_dI⟩
-/

end IFPProtocolNTDPH
