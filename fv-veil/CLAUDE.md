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

### Safety Proof Strategy (from Fast-HotStuff & Jolteon)

The restricted IFP is a 2-chain protocol (like Jolteon/Basic Fast-HotStuff). The safety argument follows this structure:

**Key lemmas (mapped from Fast-HotStuff/Jolteon to IFP):**

1. **Same-view uniqueness** (Fast-HotStuff Lemma 1, Jolteon Observation 1): At most one interaction can get a prevoteQC (quorum of prevotes) in a given view. Honest nodes only prevote once per view. By quorum intersection, two conflicting prevoteQCs in the same view are impossible.
   - Model invariant: `unique_prevote_nodes`, `unique_prevote_lock_in_view`

2. **Lock propagation** (Fast-HotStuff Lemma 2, Jolteon Lemma 2): If an honest node has a precommit lock (= decided) for interaction I at view v, then in any subsequent view's prepare phase, the operator will discover a lock at least as high as v. This is because a supermajority locked onto I's prevoteQC, and by quorum intersection any future supermajority of prepare responses includes at least one honest node carrying that lock.
   - Model invariant: `decided_only_if_quorum_prevote_locked`, `highest_lock_sent`

3. **No conflicting commits** (Fast-HotStuff Lemma 3/5, Jolteon Lemma 3 + Theorem 2): If interaction I is decided at view v, then any interaction decided at view v' > v must be a descendant of I. The operator at v' discovers the lock for I, and the proposal rules force extending I (not conflicting).
   - Model safety: `main_safety` — `(decided N1 V1 P1 P2 I1 ∧ decided N2 V2 P1 P2 I2) → (ancestor I1 I2 ∨ ancestor I2 I1)`

**Jolteon's 2-chain commit rule** (directly applicable to IFP):
- A block/interaction is committed when there are two adjacent certified rounds: B ← QC_B ← B' with consecutive rounds. In IFP terms: prevoteQC (vote lock) in view v, followed by precommitQC (commit lock) in view v → decide.

**Jolteon's voting rule** (maps to IFP's respond_propose):
- A node votes for a proposal if EITHER:
  1. The proposal directly extends the previous round's QC (happy path), OR
  2. The proposal extends the highest QC found in the TC (timeout/view-change case), AND that QC is at least as high as the max QC in the TC.
- In IFP: this maps to the `respond_propose` action checking that the proposed interaction is consistent with the highest locks from both contexts.

**Fast-HotStuff's AggQC / proof-of-highQC**:
- The operator must prove it is extending the highest known lock. In IFP, this is modeled by requiring supermajority prepare responses from both contexts, extracting the highest lock (`ixn_max_1/2`), and proposing accordingly.

### Modeling Constraints

- **Any change to the model must faithfully represent the protocol.** Do not add artificial constraints or simplifications beyond the stated restrictions.
- Invariants should be guided by Fast-HotStuff/Jolteon safety analysis patterns extended to the IFP setting.

## Proof Status

*To be documented — will track which invariant×transition pairs have manual `@[invProof]` theorems vs. auto-verified vs. pending.*

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

## Key Dependencies

| Package | Purpose |
|---------|---------|
| **veil** | Verification framework for transition systems |
| **mathlib4** | Mathematical library |
| **Aesop** | Automated proof search |
| **lean-smt** | SMT solver integration (Z3/CVC5) |
