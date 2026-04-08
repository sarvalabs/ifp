# Infer Invariants for IFP Safety Proof

You are helping iteratively infer the supporting invariants necessary for `#check_invariants` to succeed in `IFPSafety/IFPInvGen.lean`. The user provides the InfoView output showing failing invariant×transition pairs and counterexamples from z3/cvc5.

## Context

`IFPInvGen.lean` contains a minimal core of ~10 invariants for the IFP safety proof. The SMT-based verifier (`#check_invariants`) checks that each invariant is preserved by each protocol transition. When it fails, it produces a counterexample showing a spurious state that violates the invariant after the transition. Your job is to analyze these counterexamples and add the **minimum** supporting invariants needed to rule them out.

The reference file `IFPSafety/IFP.lean` contains the full set of invariants (both active and commented out) that the user has previously developed. Prefer reusing invariants from there when applicable.

## Input

The user provides the InfoView output from `#check_invariants`, which contains:
- Which invariant×transition pairs failed (e.g., `respond_prevote × INV2_unique_prevote_lock_in_view`)
- SMT counterexamples showing the spurious states

$ARGUMENTS

## Workflow

### Step 1: Read the current state

Read `IFPSafety/IFPInvGen.lean` to understand which invariants are currently present. Also read the **Invariant Dependency Tree** section in `CLAUDE.md` for the full dependency structure and impact rankings.

### Step 2: Collect all failures

Parse ALL failing invariant×transition pairs from the user's output. For each, extract:
1. **Transition name** (e.g., `respond_prevote`)
2. **Invariant name** (e.g., `INV2_unique_prevote_lock_in_view`)
3. **Counterexample** (key state assignments, spurious properties)

### Step 3: Prioritize by impact-to-effort ratio

**CRITICAL**: When multiple invariants are failing, do NOT fix them one at a time. Instead:

1. **Group failures by root cause**: Multiple failures often share the same root cause (a missing invariant). For example, if `unique_lock_interaction_per_view` fails on 3 transitions AND `INV2` fails on 2 transitions, the root cause may be a single missing `stage_neg_2`.

2. **Focus on core invariants in order**: Always prioritize making INV1 pass first, then INV2, then INV3, then INV4. If failures span multiple core invariants, fix the lowest-numbered one first — its supporting invariants often help the others too. Only address failures of supporting invariants insofar as they block the current target INV.

3. **Compute impact-to-effort dynamically** for each candidate fix invariant:
   - **Impact** = how many of the current failures would this invariant fix (directly or by unblocking a dependency chain)?
   - **Effort** = how many additional invariants must also be added as dependencies? Use the dependency tree in CLAUDE.md to count. Leaf nodes (Tier 3) have effort 0. A Tier 2 invariant that needs 2 Tier 3 deps has effort 2.
   - **Priority** = impact / (1 + effort). Highest priority first.

4. **Always add leaf-node (Tier 3) invariants before their dependents**: They have no dependencies themselves and unblock higher-tier invariants. If a Tier 2 invariant is needed, first add all its Tier 3 dependencies.

5. **Batch additions**: In each iteration, add ALL invariants whose need is clear from the current failures. Do not add just one and wait. The goal is to minimize round-trips.

### Step 4: Determine which invariants to add

For each root cause identified in Step 3, determine the fix:

#### Strategy A: Reuse from IFP.lean (preferred)
Check if an invariant already exists in `IFPSafety/IFP.lean` (active or commented out). Copy its exact definition. Common categories:

**Structural (Tier 3 — always safe to add, no dependencies):**
- `unique_stage` — one stage per view per node
- `stage_neg_1` through `stage_neg_4` — prevent state at wrong stages
- `stage_init_prepare` — unprepared → prepare stage
- `genesis_lock_only_at_zero` — genesis locks at view 0
- `locked_only_if_prepared` — non-genesis locks need prepare
- `unique_cur_view` — one current view per node
- `node_has_cur_view` — every node has a view
- `cur_stage_exists` — always one of 5 stages

**Supporting (Tier 2 — check dependencies before adding):**
- `precommitted_node_implies_lock` (needs stage_neg_2)
- `highest_lock_sent` (needs locked_only_if_prepared, genesis_lock_only_at_zero)
- `prevote_operator_only_if_quorum_prevoted` (self-contained)
- `prepare_only_by_operator`, `operator_from_ixn_context`
- `unique_operator_for_pset`
- Chain/height: `parent_only_if_proposed`, `heights_equal`, `genesis_height_zero`, etc.
- Decision: `genesis_decided_first`, `genesis_view_zero`, `decisions_not_from_higher_views`

#### Strategy B: Formulate a new invariant
Only if no existing invariant from IFP.lean fits. Must be genuinely true and minimal.

### Step 5: Resolve dependency chains

Before finalizing the addition list, walk the dependency tree (from CLAUDE.md) for each invariant you plan to add:

```
Want to add X?
  → Does X depend on Y?
    → Is Y already in IFPInvGen.lean?
      → Yes: done
      → No: Add Y too, and recursively check Y's dependencies
```

Example: Want `precommitted_node_implies_lock`?
  → Depends on `stage_neg_2` → not present → add it
  → `stage_neg_2` depends on `unique_stage` → not present → add it
  → `unique_stage` is a leaf → done
  → Final addition: `unique_stage` + `stage_neg_2` + `precommitted_node_implies_lock`

### Step 6: Apply the changes

Add the new invariants to `IFPInvGen.lean` in the section between the core invariants and the safety property. Group them with comments:

```lean
-- ####################################################################
-- # Supporting Invariants (added by inference)
-- ####################################################################

-- Tier 3: Structural
...

-- Tier 2: Supporting
...
```

### Step 7: Report to the user

Provide a summary table:

```
| Added Invariant | Tier | Fixes Failures | Source |
|-----------------|------|----------------|--------|
| unique_stage    | 3    | (dependency)   | IFP.lean:613 |
| stage_neg_2     | 3    | unique_lock×respond_prevote, ... | IFP.lean:816 |
| ...             |      |                |        |
```

Then ask the user to re-run `#check_invariants` in InfoView and provide the new output.

## Model Defects

Sometimes a counterexample reveals a genuine gap in the protocol model — not a missing invariant, but a missing or incorrect `require` in an action. Signs of a model defect:

- The counterexample is **reachable** (no invariant can rule it out because the model actually allows it)
- An action is missing a precondition that the real protocol enforces (e.g., a node acts without being in the right context, or an action fires at view zero when it shouldn't)
- The state update is wrong (e.g., a lock is set for the wrong participant, or ancestor isn't updated transitively)

When you suspect a model defect:
1. **Flag it explicitly** to the user with the specific counterexample and which action/require is at fault
2. **Explain why** no invariant can fix it (the state is genuinely reachable in the current model)
3. **Propose the minimal model fix** — the smallest `require` addition or state update correction that is faithful to the protocol (reference `CLAUDE.md` protocol description and `IFPSafety/IFP.go` if needed)
4. **Do NOT apply the fix yourself** — wait for user approval since model changes affect protocol faithfulness

## Important Rules

- **NEVER run `lake build` or `lake lean`**. The user checks via Lean InfoView.
- **Model changes require user approval** — flag potential model defects but do not modify actions without explicit confirmation.
- **NEVER modify the existing core invariants** — only add new supporting ones.
- **Prefer fewer, stronger invariants** over many weak ones to minimize the invariant set.
- **Predict cascading needs** — if you know X needs Y, add both.
- **Keep the invariant set minimal** — only add what's needed, not everything from IFP.lean.
- The main file for reference is `IFPSafety/IFP.lean`. The working file is `IFPSafety/IFPInvGen.lean`.

## Common Counterexample Patterns

| Pattern | Likely Fix |
|---------|-----------|
| Node has lock + precommit but is in prepare stage | `stage_neg_2` or `stage_neg_1` |
| Node has two different stages in same view | `unique_stage` |
| Genesis lock at non-zero view | `genesis_lock_only_at_zero` |
| Lock exists but node never prepared | `locked_only_if_prepared` |
| Two operators in same view | `unique_operator_for_pset` |
| Decision at future view | `decisions_not_from_higher_views` |
| Sent lock doesn't match actual lock | `locks_sent_only_if_locked_1/2` (already in core) |
| Precommitted node has no lock | `precommitted_node_implies_lock` |
| Node prevoted but has no proposal | Trace back through stage invariants |
| Height mismatch between h1 and h2 | `heights_equal` |
