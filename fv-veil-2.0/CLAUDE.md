# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Formal verification of a **restricted version of the IFP (Interaction Finality Protocol)** — a Byzantine fault-tolerant distributed consensus protocol from the Krama blockchain — using the **Veil framework** in **Lean 4**. Safety properties (consensus agreement) are proved through invariant-based verification with SMT solver automation.

## Protocol Context (from paper.pdf)

IFP (also called Krama) is a participant-centric consensus protocol where each participant has a separate chain, and interactions (analogous to transactions) between participants are finalized by an Interaction Consensus Set (ICS) of validators. The full protocol has: participant contexts (fixed validator committees), stochastic sets (randomly sampled validators), multi-linked DAG storage, epoch-based reconfiguration, and parallel consensus instances for disjoint participant sets.

### Restrictions Applied in This Formalization

We verify a **restricted IFP** that eliminates cross-chain complexity:

1. **Two fixed participants only** (`p1_fixed`, `p2_fixed`) — all interactions occur between them. This removes complications from multiple overlapping consensus instances.
2. **No stochastic set** — not needed for safety (only strengthens bribery resistance).
3. **Single epoch** — epoch reconfiguration is not modeled.
4. **No Tesseracts** — interactions suffice; the Tesseract wrapper is unnecessary with two fixed participants.

This restricted protocol is structurally similar to **Basic Fast-HotStuff** or **Jolteon**. Safety analysis from those protocols guides our invariant formulation.

### Naming Convention (Paper → Model)

| Paper term | Model term |
|------------|------------|
| Vote | Prevote |
| Commit | Precommit |
| Committing a Tesseract | Deciding an interaction |

### Protocol Stages (per view)

Each consensus instance proceeds through 5 stages per node per view:
1. **Prepare** — Operator broadcasts prepare; context nodes respond with their highest locks.
2. **Propose** — Operator collects locks, determines highest, proposes interaction (repropose locked interaction, extend committed parent, or nil).
3. **Prevote** (= paper's "Vote") — Nodes vote on proposal; operator aggregates into prevoteQC. Nodes acquire a **prevote lock** (`locked ... true v`).
4. **Precommit** (= paper's "Commit") — Nodes precommit; operator aggregates into precommitQC. Nodes acquire a **precommit lock** (`locked ... false v`).
5. **Decide** (= paper's "Committing a Tesseract") — Nodes commit the interaction to their history.

### Lock Semantics

Locks are encoded as `locked : node → participant → interaction → Bool → view → Prop` where:
- `Bool = true` → **prevote lock** (acquired during respond_prevote)
- `Bool = false` → **precommit lock** (acquired during respond_precommit, also triggers decision)

A precommit lock is stronger than a prevote lock. The `sent_lock_in_prepare_1/2` relations capture the highest lock each node sends during the prepare phase, encoding the `IsHighestLock` predicate.

### Key Safety Insight

The paper's safety analysis (Section 5) is **inaccurate in details** but provides the general picture. The core argument:
- **Lemma 2** (same-view uniqueness): Conflicting interactions cannot both get commitQCs in the same view (by quorum intersection, an honest node would have voted for both — contradiction).
- **Lemma 3** (lock propagation): If a precommitQC exists for interaction T, its prevoteQC will be discovered by the operator in subsequent views via prepare responses.
- **Theorem 3** (safety): Combining the above — any future proposal must extend (be a child of) previously committed interactions, not conflict with them.

### Proposal Logic (Critical for Invariants)

The operator's proposal decision after collecting locks from both contexts:
- If both highest locks are **prevote** locks for the **same** interaction → **repropose** that interaction
- If both highest locks are **precommit** locks for the **same** interaction → **extend** (propose new interaction with that as parent)
- If both highest locks are **prevote** locks for **different** interactions → **propose nil** (no progress)

### Additional Modeling Decisions

- **Synchronous view changes**: `set_view` requires all nodes to be in `v_cur` before transitioning to `v_next`. This is an intentional simplification.
- **Byzantine actions**: Currently not modeled (`byz_sabotage` is commented out). Will be added later. For now, Byzantine behavior is only implicit through the `is_byz` predicate on quorum axioms.
- **Genesis interaction**: Special initial interaction decided at `tot_view.zero`. All nodes start with a precommit lock on genesis for both participants. Genesis has height 0 and no parent.
- **Chain growth**: New interactions are created via `propose` by setting `parent ixn_max ixn_propose` and updating `ancestor` transitively. Heights increment by 1 from parent.

### Safety Proof Strategy (Restricted IFP with 2 Participants)

The restricted IFP is a 2-chain protocol (like Jolteon/Basic Fast-HotStuff). Safety is established through the following key invariants:

**SAFETY-1 (main_safety):** If two honest nodes have decided two interactions I1 and I2, then one is an ancestor of the other.
- Dependencies: INV-1, INV-2, INV-3

**INV-1 (unique_prevote):** Honest nodes cannot prevote on two different interactions in a given view.
- Dependencies: None
- Follows from: nodes can only prevote on at most one interaction per view. Key procedures are those related to prevote stage.
- Model: `unique_prevote_nodes`

**INV-2 (unique_prevote_lock):** Honest nodes cannot be prevote-locked for different interactions in a given view.
- Dependencies: INV-1
- Follows from: INV-1 + quorum intersection (two supermajorities share an honest node, who only prevoted for one interaction).
- Model: `unique_prevote_lock_in_view`

**INV-3 (commit_only_if_quorum_locked):** If an honest node has decided an interaction in a view, then a quorum of nodes has prevote-locked on it during that view.
- Dependencies: None
- Follows from: precommitQC is required for decide, which requires prevoteQC, which means a supermajority from each context prevoted → prevote-locked.
- Model: `decided_only_if_quorum_prevote_locked`

### Protocol Stage Details (Precise)

**Prepare:**
- Operator sends Prepare to each participant's context.
- Validators collect Prepare messages for interactions involving their participant until PrepareTimeout, then choose one to respond to (others get PrepareNil).
- Prepare response contains the **highest lockedQC** for the participant.

**Propose:**
- Operator collects quorum of Prepare/PrepareNil from contexts.
- Participant set = those from whose contexts a supermajority of Prepare responses were received.
- Extracts highest lockedQCs for each participant. Ordering: height first, then stage (precommit > prevote), then view.
- Removes lockedQCs if there is a participant p in it with a higher QC for p than the lockedQC.
- Decision logic:
  - Unique prevoteQC left → **repropose** that interaction
  - All precommitQCs → **extend** (new interaction with parent)
  - Otherwise → **no proposal** (nil)
- Validators check: valid operator, belongs to ICS, didn't prevote on another interaction with any of the participants, interaction correctly extends latest states per the proposal approach.

**Prevote:**
- Operator collects quorum of Prevote messages, broadcasts prevoteQC to ICS.
- Validators on receiving valid prevoteQC: respond with Precommit, and set lockedQC to prevoteQC **unless** already holding a precommitQC for the same interaction from an earlier view.

**Precommit:**
- Operator collects quorum of Precommit messages, broadcasts precommitQC to ICS.
- Validators on receiving valid precommitQC: **decide** the interaction and set lockedQC to precommitQC.

### Reference Protocols

- **Fast-HotStuff** (`fasthotstuff-jnfg20.pdf`): 2-chain basic BFT. Safety: Lemma 1 (same-view uniqueness), Lemma 2 (lock propagation via highQC discovery), Lemma 3 (no conflicting commits). Operator must include AggQC (proof of highQC from n-f replicas).
- **Jolteon** (`jolteonditto-gkss21.pdf`): 2-chain HotStuff variant. Safety: Observation 1 (one QC per round), Lemma 2 (lock propagation), Lemma 3 (certified blocks extend globally direct-committed blocks), Theorem 2 (total order). Voting rule: extend previous round's QC (happy path) or highest QC in TC (view-change).

### Modeling Constraints

- **Any change to the model must faithfully represent the protocol.** Do not add artificial constraints or simplifications beyond the stated restrictions.
- Invariants should be guided by Fast-HotStuff/Jolteon safety analysis patterns extended to the IFP setting.

## Proof Status

*To be documented — will track which invariant×transition pairs have manual `@[invProof]` theorems vs. auto-verified vs. pending.*

## Important Workflow Rules

- **NEVER run `lake build` or `lake lean`**. The user checks results via the Lean InfoView in their IDE. If you need output (e.g., error messages, counterexamples, proof states), ask the user to provide it from InfoView.

## Working Principles (Veil Verification)

These principles bias toward caution over speed. Verification here is indirect (each round-trip costs a user `lake build` + InfoView relay), counterexamples are ground truth, and the IFP model is fragile — fifty-plus invariants whose interactions are easily broken. For trivial edits, use judgment.

### 1. Think Before Asserting

**Don't assume. Don't hide confusion. Decode the counterexample first.**

Before proposing any invariant, lemma, or model edit:
- **Read the counterexample before theorizing.** If no InfoView output has been shared, ask for it rather than guessing from the dependency tree.
- **State the candidate invariant's shape explicitly**: what it asserts, which transitions could violate it, which existing invariants it leans on for preservation.
- **Flag the three common traps**:
  - *Circularity* — does the invariant presuppose what it's trying to prove? (ancestor/lock-propagation framings are the usual offenders)
  - *Byzantine holes* — quorum-quantified conclusions without `¬is_byz` guards on the member
  - *Protocol fidelity loss* — the fix requires weakening an action's preconditions or adding an artificial guard
- If multiple invariant formulations are plausible, present them — don't pick silently.

### 2. Minimal Invariant Strength

**State the weakest invariant that closes the counterexample. Nothing speculative.**

- No "just in case" invariants. Each one must be traceable to a specific counterexample or a direct dependency from the tree.
- Prefer height-indexed or view-guarded forms over universally quantified ones when they suffice.
- Prefer preserved-by-construction forms (init-persistence, monotonic predicates) over forms that need their own supporting chain.
- No over-quantification: if a guard isn't needed for preservation, leave it out.
- Senior-engineer test: *"Does this invariant reflect a real protocol property, or am I just patching the SMT solver?"* If the latter, rethink.

### 3. Surgical Model Edits

**One invariant, one edit. Every changed line traces to a specific counterexample.**

- Don't touch adjacent invariants, action preconditions, or state signatures while adding a lemma — each unrelated change risks invalidating prior verification.
- Don't reformat or "clean up" existing `@[invProof]` theorems even if verbose; they're load-bearing for specific transitions.
- **Never weaken an action's preconditions to make an invariant go through.** That breaks protocol fidelity. Surface the tradeoff instead.
- *Orphan rule*: if an edit makes a helper lemma unused, mention it — don't silently delete it; it may be invoked by name in `@[invProof]` attributes elsewhere.
- If unrelated dead code or a stale invariant is spotted, mention it; don't remove it unless asked.

### 4. Counterexample-Driven Loop

**Define success criteria per (invariant × transition) pair. Loop until all transitions verify.**

Structure each verification round as:
```
1. Get failing (invariant × transition) from InfoView
   → verify: concrete counterexample in hand
2. Decode counterexample to a protocol-level scenario
   → verify: user confirms the scenario is real / matches protocol intent
3. Propose minimal invariant or lemma change
   → verify: user re-runs and reports pass/fail per transition
4. If a new transition fails, loop to step 1 on the new pair
   → verify: all transitions green, no regressions in other invariants
```

Weak goals ("make INV-3 work") are especially expensive here because each iteration costs a user round-trip. Strong goals ("INV-3 verifies on `respond_precommit` without regressing INV-2") let the loop close. Always discharge cheap structural (leaf) invariants first — they're low-effort and unblock many higher-tier invariants, so the loop doesn't stall on leaf failures.

### 5. Paper- and Implementation-Grounded Model Edits

**Model changes answer to the protocol, not to the SMT solver.**

When a counterexample suggests that an action, state relation, or precondition is itself wrong (not just missing an invariant), the fix must be grounded in an external source of truth:
- **Primary source: `paper.pdf`** — the IFP paper. Section 5 (safety argument) and the protocol stage descriptions define correctness. Quote or paraphrase the relevant passage when justifying a model change.
- **Secondary source: `IFPSafety/IFP.go`** — the reference Go implementation. Use it to resolve ambiguities the paper leaves open (ordering of updates within a stage, how a field is used in practice, concrete predicate definitions).
- **Tertiary sources: `fasthotstuff-jnfg20.pdf` and `jolteonditto-gkss21.pdf`** — the restricted IFP is structurally a 2-chain BFT; when the IFP paper is silent or inaccurate (CLAUDE.md already notes Section 5 is "inaccurate in details"), safety patterns from Fast-HotStuff and Jolteon are the next-best guide.
- **Never patch the model with a constraint that has no counterpart in paper, Go reference, or a cited sibling protocol.** Per the Modeling Constraints section: "Any change to the model must faithfully represent the protocol. Do not add artificial constraints or simplifications beyond the stated restrictions."
- When citing a source, be specific: *"paper.pdf §3.4: validators check 'did not prevote on another interaction with any of the participants' — so the `respond_propose` precondition must include..."*. Vague appeals ("this is standard in BFT") are not acceptable justification.
- If paper and Go diverge, flag the divergence and ask — don't pick silently.

**Failure mode guarded against**: silently strengthening the model to make proofs go through, producing a theorem about a protocol that is no longer IFP.

---

**These principles are working if**: counterexamples are decoded before invariants are proposed, each InfoView round-trip carries a precise question or a minimal edit, the protocol spec stays faithful to `paper.pdf`, and diffs shrink rather than grow across iterations.

## Build Commands

```bash
lake build              # Build the IFPSafety library (default target)
lake clean              # Remove build outputs
lake update             # Update dependencies (pulls latest Veil, mathlib, etc.)
lake lean <file>        # Elaborate/typecheck a single Lean file
```

Lean toolchain version: `leanprover/lean4:v4.22.0` (specified in `lean-toolchain`).

Build configuration is in `lakefile.toml`. The primary dependency is the [Veil](https://github.com/verse-lab/veil) formal verification framework.

## Architecture

### Core Modules

- **`IFPSafety.lean`** — Root module entry point, imports all submodules.
- **`IFPSafety/IFP.lean`** — Main protocol specification (~1,760 lines). Contains the full state machine: types, state relations, 10 protocol actions (`set_view`, `pick_operator`, `prepare`, `respond_prepare`, `propose`, `respond_propose`, `prevote`, `respond_prevote`, `precommit`, `respond_precommit`), 50+ safety invariants, and the main safety theorem. Also contains manual `@[invProof]` theorems for cases where Veil's automation needs help.
- **`IFPSafety/IFPTheory.lean`** — Foundational type classes: `TotalOrderWithMinimum` (view ordering), `ByzQuorum` (Byzantine quorum semantics with supermajority properties), `IsHighestLock` (lock tracking for consensus).
- **`IFPSafety/Test.lean`** — For Testing simple functionalities of Lean. Can ignore. 
- **`IFPSafety/IFP.go`** — Reference Go implementation of the protocol.

### Examples Directory (`IFPSafety/Examples/`)

Protocol implementations for comparison/reference: PaxosEPR, Blockchain, ReliableBroadcast, Ring election, SCP (Stellar Consensus), SuzukiKasami, Rabia, VerticalPaxos.

### Veil DSL Patterns

The protocol uses Veil's embedded DSL within Lean 4:

- **`type`** — Declares uninterpreted sorts (e.g., `view`, `node`, `participant`)
- **`relation`** / **`function`** — Declares mutable state components
- **`instantiate`** — Binds type class instances (e.g., `TotalOrderWithMinimum`, `ByzQuorum`)
- **`action`** — Protocol transitions with `require` preconditions and state updates
- **`safety`** — Top-level safety properties to prove
- **`@[invProof]`** — Attribute marking lemmas as invariant proofs
- **`#gen_state`** / **`#gen_spec`** — Macros generating state datatype and verification spec

### Verification Approach

Safety properties are proved by showing invariants are preserved across all protocol transitions. Key proof tactics:
- `solve_clause` — Veil's automated invariant discharge
- `unhygienic intros` — Introduction of hypotheses
- `simp_all` — Simplification
- SMT backend (Z3/CVC5) handles first-order logic goals

### Important `set_option` flags

```lean
set_option veil.printCounterexamples true   -- Show counterexamples on proof failure
set_option veil.smt.model.minimize true     -- Minimize SMT models
set_option veil.smt.seed 44                 -- Reproducible SMT results
set_option veil.vc_gen "transition"         -- VC generation strategy
set_option synthInstance.maxSize 8192       -- Required for large proof search
```

### Main Safety Theorem

The core property proven: if two honest (non-Byzantine) nodes decide on interactions for the same participants, those interactions must be ancestrally related (consensus agreement).

## Invariant Dependency Tree

File-specific dependency trees live in memory (see `MEMORY.md`). They rot as invariants are added/removed, so they're maintained alongside the proof state rather than inline here.

- For `IFPSafety/IFPN.lean`, see the `ifpn_dependency_tree` memory entry.

## Key Dependencies

| Package | Purpose |
|---------|---------|
| **veil** | Verification framework for transition systems |
| **mathlib4** | Mathematical library |
| **Aesop** | Automated proof search |
| **lean-smt** | SMT solver integration (Z3/CVC5) |
