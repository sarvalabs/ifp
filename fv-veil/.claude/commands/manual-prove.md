# Manual Prove: IFP invProof Theorem

You are helping manually prove a failing `@[invProof]` theorem in the IFP formal verification project (`IFPSafety/IFP.lean`). The user will provide the theorem name and the InfoView output (counterexample from z3/cvc5).

## Input

The user provides:
1. The theorem name (e.g., `respond_prepare_tr_stage_1`)
2. The InfoView output showing the failing proof state and/or SMT counterexample

$ARGUMENTS

## Workflow

### Step 1: Understand the theorem

Read the theorem in `IFPSafety/IFP.lean`. An `@[invProof]` theorem proves that a specific **transition** preserves a specific **invariant**. Identify:
- **Transition**: The protocol action (e.g., `respond_prepare`, `propose`, `prevote`). Read the action definition to understand what state changes it makes.
- **Invariant**: The safety property being preserved (e.g., `stage_1`, `unique_prevote_nodes`). Read the invariant definition.

### Step 2: Analyze the counterexample

Parse the SMT counterexample to understand WHY the proof fails. Key things to extract:
- **Universe sizes**: How many nodes, views, interactions, etc.
- **Key assignments**: Which node is acting, what view, which participants
- **The spurious state**: What makes this counterexample unreachable in the real protocol
- **Missing facts**: What invariant or precondition would rule out this counterexample

Common patterns in IFP counterexamples:
- **Genesis locks at non-zero views**: The model has `locked N P genesis S V` where `V ≠ tot_view.zero`. Fix: need `genesis_lock_only_at_zero` invariant.
- **Actions firing at view zero**: An action fires at `tot_view.zero` when it shouldn't. Fix: add `require v ≠ tot_view.zero` to the action (faithful if `prepare` already requires it).
- **Byzantine operator exploits**: The operator is byzantine, bypassing `¬ is_byz` guards on invariants. Fix: strengthen invariant to remove `¬ is_byz` guard (if the property holds for all nodes), or add action precondition.
- **Missing stage constraints**: A node has state (locks, votes, etc.) inconsistent with its stage. Fix: check `stage_neg_*` invariants cover the case.
- **Locks at future views**: A node has locks at views beyond its current view. Fix: may need a `locks_not_from_higher_views` invariant.

### Step 3: Determine the fix strategy

Choose the minimal fix:

1. **Model refinement** (preferred if faithful): Add a `require` precondition to the action that is clearly true in the protocol. Example: `require v ≠ tot_view.zero` when `prepare` already requires it.

2. **New supporting invariant** (if genuinely needed): Add a new `invariant` that captures a real protocol property not yet expressed. Example: `genesis_lock_only_at_zero`. Place it near related invariants. Add a comment explaining why it's true.

3. **Manual proof tactics** (if the SMT solver needs guidance): Write intermediate `have` statements, case splits, or witness provisions to help the solver. Use after strategy 1/2 if `solve_clause` still fails.

**Rules**:
- NEVER strengthen an existing invariant (e.g., removing `¬ is_byz` guards) without explicit user approval
- NEVER add invariants that aren't genuinely true of the protocol
- Any model change must faithfully represent the protocol (see CLAUDE.md)
- Prefer the smallest change that fixes the proof

### Step 4: Apply fixes and write the proof

1. If adding a model fix or new invariant, make the edit.
2. Write/update the theorem proof body. Start with:
   ```lean
   by
   unhygienic intros
   solve_clause[IFPProtocol.<transition>.tr] IFPProtocol.<invariant>
   ```
3. If `solve_clause` alone doesn't work after fixes, try manual tactics before it:
   ```lean
   by
   unhygienic intros
   -- manual reasoning here (have statements, case splits, simp)
   solve_clause[IFPProtocol.<transition>.tr] IFPProtocol.<invariant>
   ```

### Step 5: Report to user

Tell the user:
- What counterexample(s) you analyzed
- What fix(es) you applied and why
- Ask them to check InfoView for:
  - The theorem itself (does the proof go through?)
  - Any new invariants (are they verified across all transitions?)

## Important Notes

- NEVER run `lake build` or `lake lean`. The user checks via Lean InfoView.
- The main file is `IFPSafety/IFP.lean` (~1760+ lines).
- Protocol flow: `set_view → pick_operator → prepare → respond_prepare → propose → respond_propose → prevote → respond_prevote → precommit → respond_precommit`
- Lock encoding: `locked N P I true V` = prevote lock, `locked N P I false V` = precommit lock
- Genesis is special: decided at `tot_view.zero`, all nodes start with precommit lock on genesis at zero
- `stage_neg_*` invariants constrain what state can exist at each stage (for non-genesis interactions)
