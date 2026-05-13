# IFPSafety — Per-File Summary

Formal verification of the restricted IFP protocol in Lean 4 / Veil. Each
`IFP*.lean` file in `IFPSafety/` is a *self-contained* model variant: they
share a skeleton (per-view stages `prepare → propose → prevote → precommit →
decide`, 2-fixed-participant or single-context simplification, supermajority
quorum reasoning) but differ in which artifacts of the protocol are reified
as **state**, **ghost relations**, or **invariants** — i.e., which proof-
engineering trick is being tried to make the SMT solver discharge
inductiveness.

There is **no shared `IFPTheory.lean`** in this tree; the `IFPByzQuorum`
class is redeclared in every file, and `TotalOrderWithMinimum` comes from the
Veil library.

---

## Common substrate (shared by all variants)

- **Type class** `IFPByzQuorum` (redeclared per file): `is_byz`, `member`,
  `supermajority`, plus axiomatic facts
  `supermajority_s_belongs_to_c` and `supermajorities_intersect_in_honest`.
  IFPJ enriches this with `greater_than_third` (f+1) and related axioms.
- **Library instance** `TotalOrderWithMinimum view` with `tot_view.zero`,
  `tot_view.next`, `tot_view.lt/le`.
- **Immutable individuals**: `p1_fixed`, `p2_fixed` (in participant-based
  variants), the five stages `prepare/propose/prevote/precommit/commit`,
  `genesis`.
- **Assumptions**: `interactions i p q → p = p1_fixed ∧ q = p2_fixed`;
  `p1_fixed ≠ p2_fixed`; the five stages are pairwise distinct;
  `participant_context` is functional. Single-context variants drop the
  participant assumptions.
- **Five canonical node-side relations**: `prepared_node`, `prevoted_node`,
  `precommitted_node`, `decided`, `locked`. Plus operator-side mirrors:
  `prepared_operator`, `prevoted_operator`, `precommitted_operator`,
  `proposed*`, `proposed_nil`, `operator`.
- **`after_init`**: genesis decided at `tot_view.zero`; all context
  members hold a precommit lock on genesis at view 0; `cur_stage = prepare`;
  all view-0 nodes have `cur_view = zero`; ancestor initialised to identity;
  parent to false; height to 0.
- **Canonical actions**: `set_view`, `pick_operator`, `operator_prepare`,
  `respond_prepare`, `operator_propose` (or split `propose_repropose/extend/nil`),
  `respond_propose`, `operator_prevote`, `respond_prevote`,
  `operator_precommit`, `respond_precommit`. `set_view` is **synchronous**
  (`require ∀ n, cur_view n v_cur`).
- **Three "core" invariants** (variants of):
  - **INV1** `unique_prevote_nodes` — honest node prevotes ≤ once per view
  - **INV2** `unique_prevote_lock_in_view` — at most one prevote-locked
    interaction per view across honest nodes
  - **INV3** `decided_only_if_quorum_prevote_locked` — decision implies a
    prevote-quorum locked it
- **`safety [main_safety]`** (when present):
  `decided n1 v1 i1 ∧ decided n2 v2 i2 → ancestor i1 i2 ∨ ancestor i2 i1`
  (any two decided interactions are comparable on the chain).

---

# Live files (currently in `IFPSafety/`)

## 1. `IFP.lean` — original, monolithic propose (`IFPProtocol`, 762 lines)

Genesis variant. First serious formulation, descended from the initial
`IFPInvGen.lean` drop (`3d169d8`, renamed to `IFP.lean` at `da3b06e`).

- **State shape**: participant-based (every relation indexed by
  `p1 p2 : participant`). `locked : node → participant → interaction → stage
  → view → Bool` (5-arity, stage-tagged). Two `sent_lock_in_prepare_1/2`
  (one per context). Single `proposed`, `proposed_nil`.
- **Distinguishing idea**: the propose-stage logic is encoded *inside one
  giant `operator_propose` action* with several `pick`-bound variables
  (`ixn_max_1`, `s_max_1`, `v_max_1`, …) and argmax preconditions
  (height-then-stage-then-view ordering), then an `if/if/if` cascade for
  repropose-vs-extend-vs-nil. `respond_propose` re-runs the same argmax check.
- **Invariants**: INV1–INV4. INV4 (`quorum_locked_implies_lock_of_descendant_
  discovered`) is the lock-propagation lemma. ~30 supporting invariants
  (`stage_neg_*`, `genesis_lock_existence`, `locks_sent_only_if_locked`,
  `highest_lock_sent`, `precommit_next_view_discovery`, …). The file carries
  an unfinished manual proof of `respond_prepare × precommit_next_view_
  discovery` and a comment explaining why automation breaks (Decidable
  instances inside the `decide` expressions in `sent_lock_in_prepare_*`).
- **Safety**: `safety [main_safety] true` — placeholder; safety is not yet
  routed.

## 2. `IFPD.lean` — split-locks experiment, partial (`IFPProtocolD`, 688 lines)

Sibling experiment to IFP, added in `43a1fab` ("new lock implementations
considered").

- **Distinguishing idea**: drops the `stage` argument from `locked`.
  Replaces it with two relations
  `prevote_locked : node → participant → interaction → view → Bool` and
  `precommit_locked : ...`. A ghost `locked_any` recovers the old union.
  `sent_lock_in_prepare_*` and a new `highest_lock_in_propose_1/2` retain a
  stage parameter to record *which kind* of lock was sent.
- **State of file**: all actions except `respond_propose` are commented
  out — the file is a stub. Only INV1 is declared; INV2/INV3/INV4 and
  supporting invariants present only as commented templates.
- **Why it stalled**: the split duplicates the lock relation across stages,
  which doesn't shrink the SMT search, and `locked_any` reintroduces
  quantifier alternation. Abandoned in favour of the ghost-relation approach
  in IFPH.

## 3. `IFPH.lean` — HotStuff-style ghosts (`IFPProtocolH`, 980 lines)

Originally `IFPInvGen2.lean` → `IFPInvGenH.lean` → `IFPH.lean`
(`bc3089d`, `93fd5dd`, `da3b06e`).

- **Distinguishing idea**: introduces two *stored* (mutable but
  ghost-semantics) relations maintained by every action:
  - `locked_at_view : node → participant → view → Bool` ≡
    `∃ I S, locked N P I S V` (HotStuff's `votedh`).
  - `locked_for_descendant : node → participant → interaction → view → Bool`
    ≡ `∃ I S, locked N P I S V ∧ ancestor A I` (HotStuff's `votedb`).

  These eliminate existential quantification over interactions inside
  INV-4-style invariants; SMT no longer needs witnesses for `∃ I S`.
- **Action change**: the monolithic `operator_propose` is split into
  three actions — `propose_repropose`, `propose_extend`, `propose_nil` —
  each with its own preconditions, removing the `if` cascade.
- **Invariants**: retains INV1–INV3 and `precommit_next_view_discovery`.
  Adds `locked_at_view_fwd/bwd`, `locked_for_descendant_fwd/bwd`,
  `lock_descendant_monotone`, plus the IFP supporting suite. INV4 itself is
  dropped (replaced by the ghost-driven chain).

## 4. `IFPT.lean` — EPR-friendly `highest_lock` relations (`IFPProtocolT`, 860 lines)

Forks IFPH (`4d8304d`, "propose collect and extract new action").

- **Distinguishing idea**: splits the *operator's argmax computation* out
  of the propose actions into a dedicated `collect_and_extract` action that
  writes into two new relations:
  - `highest_lock_1 : node → view → participant → participant → interaction
    → stage → view → Bool`
  - `highest_lock_2 : ...`

  Subsequent `propose_repropose/extend/nil` and `respond_propose` simply
  *read* `highest_lock_1/2` instead of re-running the argmax-over-
  `sent_lock_in_prepare_*` quorum, eliminating the ∃∀∃∀ alternation that
  plagued IFPH's propose.
- Adds explicit ancestor structural invariants: `ancestor_refl`,
  `ancestor_from_parent`, `ancestor_trans`, `ancestor_antisymm`,
  `ancestor_height_strict`, `no_ancestor_equal_height`, `parent_height` — so
  SMT does not need to rediscover transitive closure properties on every
  query. Plus `unique_highest_lock_1/2`, `highest_lock_*_dominates`,
  `highest_lock_*_is_sent_lock` to relate the new ghosts to underlying
  state.

## 5. `IFPU.lean` — proposal/decision descendant ghosts (`IFPProtocolU`, 1069 lines)

Forks IFPT (`da3b06e`, `b6d04fc`).

- **Distinguishing idea**: adds two more ghost relations targeting the
  two remaining gaps in the safety chain:
  - `proposed_for_descendant : view → interaction → Bool` — "at view V,
    the proposed interaction is a descendant of A". Closes **Gap 1**
    (proposal extends locked descendants).
  - `decided_for_descendant : node → interaction → view → Bool` — "node N
    decided a descendant of A at view V". Closes **Gap 2** (decision
    inherits proposal ancestry).
- **First non-trivial `safety [main_safety]`**:
  `decided n1 v1 i1 ∧ decided n2 v2 i2 → ancestor i1 i2 ∨ ancestor i2 i1`.
  Keeps IFPT's full invariant suite plus `propose_only_if_parent_locked`,
  `propose_only_if_operator_prepare`, `prepared_operator_not_at_zero`,
  `stage_4`.

## 6. `IFPJ.lean` — height-as-first-class ghost (`IFPProtocolJ`, 1266 lines)

Forks the (now-deleted) IFPI fork. Added at `44700a5`, evolved through
`1f4dafc`, `5d2050b`.

- **Distinguishing idea**: adds *height-indexed* ghost relations
  (HotStuff brings height in as a first-class parameter; IFPJ matches that):
  - `locked_at_height : node → participant → Nat → view → Bool` ≡ "lock
    for some interaction of height H at view V"
  - `locked_descendant_at_height : node → participant → interaction → Nat
    → view → Bool`
  - `proposed_at_height : view → Nat → Bool`
- **`IFPByzQuorum` class is enriched** with
  `greater_than_third (s c : nset) : Prop` (f+1 nodes, "ICS" reasoning),
  plus axioms `greater_than_third_one_honest`,
  `supermajority_intersect_greater_than_third`,
  `supermajority_honest_subset_gt_third`, etc. `is_byz` and `member` move
  from `Prop` to `Bool` (`5d2050b` fixes the Bool issue).
- All four propose actions plus `respond_propose` maintain the new ghosts.
  Safety property identical to IFPU.

## 7. `IFPL.lean` — height-uniqueness + monotonicity (`IFPProtocolL`, 1379 lines)

Forks the IFPI experimental fork at `bb59280`.

- **Distinguishing idea**: introduces height-based shortcuts to bypass
  ancestor reasoning:
  - `unique_decided_at_height` — at most one interaction decided per height.
  - `unique_locked_at_height` — at most one interaction locked per height.
  - `lock_height_monotone`, `decision_height_monotone` — view increases ⇒
    height (weakly) increases.
- **First file to split `proposed` permanently into `proposed_repropose`
  and `proposed_extend`** as separate state relations (rather than just
  split actions); all downstream variants inherit this.
- Keeps IFPU's ghost relations
  (`locked_at_view`, `locked_for_descendant`, `proposed_for_descendant`,
  `decided_for_descendant`) but not IFPJ's height-indexed ghosts. Same
  `main_safety` as IFPU.

## 8. `IFPM.lean` — Go-implementation-faithful (`IFPProtocolM`, 1209 lines)

Forks IFPL at `060abff`.

- **Distinguishing idea**: rewrites proposal logic to match the reference
  Go implementation. Concrete changes documented in the file header:
  1. Adds `committed_ixn : node → interaction → Bool` — each node's *latest
     decided interaction* (committed_height is `height(committed_ixn)`; no
     separate relation).
  2. Proposal preconditions compare *heights* rather than interaction
     identities (`height ixn_max_1 + 1 = height ixn_propose`).
  3. Highest-lock comparison simplified to *view-only*
     (`tot_view.le v_l v_max`) — matching the Go `LastView` field.
  4. `respond_propose` no longer re-verifies the operator's lock claim;
     accepts on the operator's witnessed proposal (mirroring Go
     `enterPrevote`).
  5. `respond_prevote` removes the precommit-lock guard on prevote-lock
     acquisition.
- Drops IFPL's `locked_for_descendant` / `proposed_for_descendant` /
  `decided_for_descendant`; the only retained ghost is `locked_at_view`.
- Churn commits: `dc1c1cb` (modeling fixes), `990a0f2` (function→relation),
  `9a8febb` (pick synthesis), `a61ab41` (committed_height removed),
  `2206ace` (stage_3 fix for earlier-view precommit locks), `3fe8353`
  (INV3 weakened).

## 9. `IFPO.lean` — QC artifacts as state (`IFPProtocolO`, 1277 lines)

Branched from IFPM at `88dcacb`.

- **Distinguishing idea**: lifts Quorum Certificates into first-class
  state relations:
  - `quorum_prevoted : view → participant → participant → interaction →
    Bool` (prevoteQC artifact)
  - `quorum_precommitted : view → participant → participant → interaction →
    Bool` (precommitQC artifact)

  No node parameter — the QC is a *protocol-level artifact*, not per-node.
  `operator_prevote`/`operator_precommit` set the QC; `respond_prevote`/
  `respond_precommit` consume it instead of re-checking the quorum
  existential. The expensive ∃-over-nodeset moves into a small set of
  "linking" invariants (`qc_prevote_implies_quorum`, …).
- Inherits IFPM's `committed_ixn` and Go-faithful proposal logic. Sibling,
  not descendant, of IFPN.

## 10. `IFPN.lean` — single-context simplification of IFPM (`IFPProtocolN`, 915 lines)

Branched from IFPM at `58669d4` ("ifp without participant, context").

- **Distinguishing idea**: drops the `participant` type entirely. Per the
  file header:
  1. No participant type, no dual contexts.
  2. Single quorum check instead of two.
  3. Single lock dimension —
     `locked : node → interaction → stage → view → Bool` (no `participant`
     index).
  4. `sent_lock_in_prepare_1/2` merged into one `sent_lock_in_prepare`.
- Retains IFPM's `committed_ixn`, height-based proposal, simplified
  `respond_propose`. This is the model the
  `reference_ifpn_dependency_tree` memory entry catalogues. Substrate for
  IFPNT.

## 11. `IFPNL.lean` — single-context simplification of IFPL (`IFPProtocolNL`, 980 lines)

Sibling branch from IFPL at `29f0e2f` ("ifpl without participant and
context").

- **Distinguishing idea**: same single-context simplification applied to
  **IFPL** instead of IFPM. Retains IFPL's descendant-ghost stack
  (`locked_for_descendant`, `proposed_for_descendant`,
  `decided_for_descendant`) and height-uniqueness/monotonicity invariants.
  Drops `propose_nil` ("trigger vanishes with single highest lock").
- A what-if branch: "what would the single-context model look like if we
  had stayed with IFPL's descendant-ghost approach instead of IFPM's
  Go-faithful approach?"

## 12. `IFPNT.lean` — Tendermint-style `locks_analog` (`IFPProtocolNT`, 1378 lines)

Builds on IFPN at `fc60073` ("ifpn + precommit_backed rel and locks inv");
current head at `35b62c9`.

- **Distinguishing idea** (per the file header): routes safety through a
  **lock-propagation bundle mirroring Tendermint's `locks` invariant**
  (from `tendermint/spec/ivy-proofs/classic_safety.ivy`).
  - New ghost relation `precommit_backed : view → interaction → Bool` set
    inside `operator_precommit` whose precondition guarantees a real
    prevote-supermajority of `precommitted_node` — independent of operator
    honesty. Only the *forward* direction (ghost ⇒ quorum witness) is
    asserted; deliberately no `_bwd`, so SMT does not have to flip the
    ghost on `respond_prevote`'s state changes.
  - Headline invariant `locks_analog_precommit`:

    ```
    precommit_backed V I ∧ precommit_backed V2 I2 ∧ tot_view.lt V V2
      → I = I2 ∨ ancestor I I2
    ```

  - Bridge invariants: `decided_implies_precommit_backed`,
    `precommitted_operator_implies_precommit_backed`,
    `precommitted_node_implies_prevote_qc`.
- Also reifies the operator's argmax over prepare responses as state
  (matching Tendermint's `validValue`/`validRound` cached during
  prevote-handler):
  - `prepares_collected : node → view → Bool`
  - `op_argmax : node → view → interaction → stage → view → Bool`
  - With invariants `op_argmax_unique`, `op_argmax_implies_collected`,
    `collected_implies_op_argmax`, `op_argmax_is_highest_lock`,
    `op_argmax_qc_backed`.
- Recent activity (most recent first):
  - `35b62c9` — quorum nodesets are now action *parameters* (`s : nodeset`),
    removing existentials in `require`.
  - `f24a2a8` — restricted decide so a single interaction can't be decided
    across multiple views by the same node.
  - `7168446` — added `precommit_backed_repropose_link`,
    `precommit_backed_extend_link`,
    `op_committed_descends_from_precommit_backed`.
  - `701b051` — `locks_analog_precommit` discharged via *manual proof*
    (Veil's `veil_smt` failed; the workaround is `veil_solve_wp`, per
    `feedback_veil_smt_preprocessing` memory).
  - `415608b` — moved `precommit_backed` ghost into `operator_precommit`;
    added bridge invariants.

---

# Deleted variants (recovered from git HEAD)

## 13. `IFPA.lean` — Structure + TSet for locks (`IFPProtocolA`, 700 lines)

Added in `43a1fab` ("new lock implementations considered") as
`IFPInvGenA.lean`; renamed to `IFPA.lean` at `da3b06e`; deleted (still `D`
in working tree).

- **Distinguishing idea**: bundles `(interaction, stage, view)` into a
  Lean `structure LockInfo` and stores each node's per-participant locks as
  a *TSet*:
  - `function locks : node → participant → LockSet`
  - `instantiate lockTset : TSet (LockInfo interaction stage view) LockSet`
  Lock manipulation uses TSet operations: `insert`, `contains`, `toList`,
  `filter`, etc. A ghost `has_lock N P I S V` recovers point-queries via
  `lockTset.contains { ixn := I, stg := S, vw := V } (locks N P)`.
- All canonical actions are implemented; `sent_lock_in_prepare_*` carries
  `LockInfo` records, and locks are written via `lockTset.insert` in
  `respond_prevote`/`respond_precommit`.
- **Why it was abandoned**: TSet membership creates higher-order obligations
  the Veil/SMT pipeline doesn't discharge efficiently; the abstraction
  bought no simpler SMT queries than the flat relation. Superseded by the
  IFPH ghost-relation approach.

## 14. `IFPI.lean` — IFPH + descendant relations (`IFPProtocolI`)

Created at `73b6b99` ("ifph + proposed and decided descendant relations =
ifpi.lean"); deleted at `214d051`.

- **Distinguishing idea**: an intermediate stepping stone — IFPH plus the
  two descendant-ghost relations later promoted into IFPU:
  - `proposed_for_descendant : view → interaction → Bool`
  - `decided_for_descendant : node → interaction → view → Bool`
  Plus the `proposed_repropose` / `proposed_extend` action split (later
  inherited by IFPL).
- Multiple sub-commits added invariants: `ddc7dca` (more supporting invs),
  `6ab125a` (descendant bwd invs without `_wo_parent` form), `bfccf85`
  (prop/lock genesis descendant), `126e7fe` (more invs added from other
  files), `ea73438` (propose relation split).
- **Why it was deleted**: superseded by IFPU (which kept the descendant
  ghosts) and IFPL (which kept the propose-action split + height work).
  The single-file artifact was no longer needed.

## 15. `IFPK.lean` — IFPJ minus the type-class enlargement (`IFPProtocolK`, 1274 lines)

Created at `dcbcf3f` ("ifpk - greaterthanthird immutable rel + assumption");
deleted later.

- **Distinguishing idea**: identical to IFPJ in modelling intent
  (height-indexed ghosts, f+1 quorum reasoning), but **avoids enlarging the
  `IFPByzQuorum` type class**. `greater_than_third` is instead an immutable
  relation `ifp_greater_than_third : nodeset → nodeset → Bool` with five
  free-standing `assumption`s:
  1. membership containment;
  2. f+1 contains at least one honest node;
  3. monotonicity (supermajority ⇒ greater_than_third);
  4. supermajority ∩ f+1 non-empty;
  5. supermajority contains an f+1 honest subset.
- Per the file header, the motivation is mechanical: *"avoids the `#gen_spec`
  compiler IR error caused by enlarging the IFPByzQuorum type class"* — i.e.,
  a Veil-tooling workaround rather than a modelling change.
- All actions, ghost relations, and the propose action split are inherited
  from IFPJ.

## 16. `IFPNTE.lean` — IFPNT without reproposals (`IFPProtocolNTE`, 1057 lines)

Created at `7168446`; deleted soon after.

- **Distinguishing idea** (per the file header): IFPNT with `propose_repropose`
  fully excised:
  - `relation proposed_repropose` removed (state, init, all references);
  - `action propose_repropose` removed;
  - `respond_propose` voter check restricted to extend-only (`s_max =
    precommit`);
  - invariant `proposed_repropose_parent_matches_committed` removed;
  - all `(proposed_repropose ∨ proposed_extend)` disjuncts collapse to
    `proposed_extend`.
- **Caveat acknowledged in the file**: this is a deliberate deviation from
  `IFP.go`. Without `propose_repropose`, and with `propose_nil` already
  commented out in IFPNT, any state where the operator's highest lock is a
  prevote-stage lock at `committed_height + 1` becomes a stuck-operator
  state. Acceptable as a safety experiment; flagged for fidelity.

---

# Lineage diagram

```
IFP.lean
├── IFPA.lean        [DELETED]  — TSet-based locks, abandoned
├── IFPD.lean        [stub]     — split locked into prevote_locked / precommit_locked
└── IFPH.lean                   — HotStuff ghosts: locked_at_view, locked_for_descendant
    ├── IFPI.lean    [DELETED]  — descendant relations + propose split (intermediate)
    │   ├── IFPT.lean           — collect_and_extract action; highest_lock_1/2 (kills ∃∀∃∀)
    │   │   └── IFPU.lean       — proposed_for_descendant, decided_for_descendant ghosts
    │   ├── IFPJ.lean           — height-as-ghost: locked_at_height, etc.; greater_than_third in ByzQuorum
    │   │   └── IFPK.lean [DEL] — greater_than_third as immutable rel + assumption (avoid IR error)
    │   └── IFPL.lean           — height-uniqueness, height-monotonicity; proposed_repropose/extend split as state
    │       ├── IFPM.lean       — Go-faithful: committed_ixn, height-based proposals, view-only argmax
    │       │   ├── IFPO.lean   — QC relations: quorum_prevoted/precommitted (artifact-as-state)
    │       │   └── IFPN.lean   — single-context: drop participant, dual contexts, dual locks
    │       │       └── IFPNT.lean — Tendermint locks_analog: precommit_backed ghost, op_argmax, prepares_collected
    │       │           └── IFPNTE.lean [DELETED] — IFPNT minus reproposals (short-lived)
    │       └── IFPNL.lean      — single-context: same simplification applied to IFPL (descendant-ghost branch)
```

---

# How the variants relate — five orthogonal axes

Each variant picks a combination along these axes:

| Axis | Choices observed |
|------|-------------------|
| **Lock representation** | Flat 5-arity `locked` (IFP, IFPH, IFPT, IFPU, IFPJ, IFPL, IFPM, IFPO, IFPN, IFPNL, IFPNT) · split into `prevote_locked` + `precommit_locked` (IFPD) · TSet of `LockInfo` records (IFPA) |
| **Argmax / propose decomposition** | Inline pick-and-cascade (IFP) · split into three propose actions (IFPH and downstream) · externalise argmax into a `collect_and_extract` action with `highest_lock_1/2` (IFPT, IFPU) · externalise as `op_argmax` + `prepares_collected` (IFPNT) |
| **Ghost relations** | None (IFP, IFPD) · HotStuff `locked_at_view` / `locked_for_descendant` (IFPH and most downstream) · descendant ghosts for proposals/decisions (IFPU, IFPI, IFPL, IFPNL) · height-indexed ghosts (IFPJ, IFPK) · QC artifacts as state (IFPO) · precommit-QC à la Tendermint (IFPNT, IFPNTE) |
| **`IFPByzQuorum` class** | Just `supermajority` (most variants) · also `greater_than_third` as class field (IFPJ) · `greater_than_third` as immutable relation + axiom (IFPK) |
| **Participant / context structure** | Two-participant + dual-context (IFP, IFPD, IFPH, IFPT, IFPU, IFPI, IFPJ, IFPK, IFPL, IFPM, IFPO, IFPA) · single-context (IFPN, IFPNL, IFPNT, IFPNTE) |

The convergent direction visible in the most recent commits is **single-
context + Go-faithful proposal logic + Tendermint-style precommit-backed
ghost** (the IFPNT line), with IFPO retaining the participant-based
formulation as a QC-first alternative and IFPL/IFPM/IFPU still serving as
reference points for invariant patterns.
