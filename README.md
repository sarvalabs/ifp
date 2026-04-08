**Protocol:** Interaction Finality Protocol (IFP)  
**Verification Framework:** Veil (Lean 4)  
**Last Updated:** April 8, 2026

---

## 1. Summary

This repository (fv-veil & fv-veil-2.0) contains the ongoing project on formally verifying the safety of Interaction Finality Protocol (IFP) for Byzantine fault tolerant consensus.

We are proving the core safety property:

> **No two honest nodes can decide on conflicting interactions, even if up to one-third of nodes are malicious in each context set.**

This work produces a **formal proof** — a machine-checked mathematical argument that the safety property holds across every possible execution of the protocol.

The proofs are written in **[Lean 4](https://lean-lang.org/)**, a programming language and proof assistant that allows mathematical statements and their proofs to be expressed as code and machine-checked for correctness. We use **[Veil](https://github.com/verse-lab/veil)**, a domain-specific framework built on top of Lean 4 by researchers at the National University of Singapore, designed specifically for verifying distributed protocols. Veil allows the protocol to be modeled as a state-transition system and uses SMT solvers to automatically discharge most proof obligations, with manual proofs provided where automation is insufficient.

Work began in **October 2025**. The project has progressed through multiple phases — from initial protocol modeling in Veil 1.0, to a more comprehensive formalization currently in progress using Veil 2.0. To date, **103 safety invariants** have been defined, of which **93 are fully machine-verified**, and the remaining 10 are under active verification.

---

## 2. At a Glance

- 103 invariants defined in addition to the main safety property
- 93 invariants verified (✅), 10 pending (⏳)
- ~1,200 lines of specification
- Active development: Oct 2025 — present

**Status definitions:**
- ✅ **Success** — Machine-checked using Veil with zero proof gaps
- ⏳ **Pending** — Invariant formally stated; verification success pending and is in progress

---

## 3. What Is Being Verified

### The Protocol

IFP is a **Byzantine Fault Tolerant (BFT)** consensus protocol — it guarantees safety when up to one-third of the nodes are malicious. Each consensus view proceeds through five stages:

```
  Prepare ──> Propose ──> Prevote ──> Precommit ──> Decide
     │           │           │            │            │
  Operator     Operator    Nodes        Nodes       Nodes
  collects    proposes    prevote on  precommit    decide
  lock info   next ixn    proposal                 the ixn
```

The verification models this entire protocol — every action a participant can take and every message exchanged — then proves that no sequence of actions, including malicious ones, can lead to conflicting decisions.

### Scope of the Proof

The verification follows a phased approach, progressively expanding the scope of the proof:

**Phase 1 — Restricted IFP** *(current)*  
Two fixed participants, single epoch, deterministic node sets. This restricted instance captures all quorum-intersection reasoning essential to safety while isolating consensus logic.

**Phase 2 — Multiple Participants**  
Extend to an arbitrary number of participants with overlapping consensus instances.

**Phase 3 — Full IFP**  
Incorporate read locks and safety under epoch reconfiguration.

---

## 4. Invariants

The safety proof requires identifying invariants that collectively support proving the main safety property. Each invariant must be shown to hold in the initial state and be preserved by every protocol action.

The record below is organized chronologically. Further, they are grouped by the theme of that batch of additions.

---

### 4.1 — October, 2025 — Core Safety & Lock Foundations (12 invariants)

The first invariants, establishing the core safety properties and the foundational lock invariants they depend on.

**1. Unique Prevote** — ✅ Success  
An honest node cannot prevote on two conflicting interactions in the same view.

**2. Unique Prevote Lock** — ✅ Success  
Two honest nodes cannot hold conflicting prevote-locks in the same view.

**3. Decision Requires Quorum Lock** — ⏳ Pending  
A decision can only happen if a supermajority locked on that interaction.

**4. Prevote Lock Requires Quorum** — ✅ Success  
A node's prevote-lock exists only if a valid supermajority actually prevoted.

**5. Unique Lock Per View** — ✅ Success  
A node can hold locks on only one interaction per view.

**6. Precommit Lock Implies Prevoted** — ✅ Success  
A precommit-lock can only exist if the node previously prevoted.

**7. Genesis Lock Existence** — ✅ Success  
All nodes hold a precommit-lock on the genesis interaction at view zero.

**8. Unique Operator** — ✅ Success  
At most one operator exists per view.

**9. Proposed Only By Operator** — ✅ Success  
Only the operator can propose interactions.

**10. Prevote Only By Operator** — ✅ Success  
Only the operator aggregates prevotes.

**11. Precommit Only By Operator** — ✅ Success  
Only the operator aggregates precommits.

**12. Unique Proposed Interaction** — ✅ Success  
An operator proposes at most one interaction per view.

---

### 4.2 — October, 2025 — Lock & Decision Structure (9 invariants)

Links between lock state, precommit behavior, and decision requirements.

**13. Genesis Lock Only At Zero** — ✅ Success  
Genesis locks exist only at view zero.

**14. Locked Only If Prepared** — ✅ Success  
Non-genesis locks can only exist after the prepare phase.

**15. Locks Sent Only If Locked (p1)** — ✅ Success  
Lock messages for participant 1 reflect actual locks held.

**16. Locks Sent Only If Locked (p2)** — ✅ Success  
Lock messages for participant 2 reflect actual locks held.

**17. Precommit Node Only If Prevoted** — ✅ Success  
A precommit can only follow a prevote for the same interaction.

**18. Precommitted Node Implies Lock** — ✅ Success  
A precommitted node holds the corresponding lock.

**19. Decide Only If Precommit Operator** — ✅ Success  
A decision requires the operator to have precommitted.

**20. Prevote Operator Requires Quorum** — ✅ Success  
The operator's aggregated prevote certificate reflects a valid supermajority.

**21. Precommit Operator Requires Quorum** — ✅ Success  
The operator's precommit certificate reflects a valid supermajority.

---

### 4.3 — October, 2025 — Ancestry & Proposal Rules (7 invariants)

The ancestor relation is formalized (split into forward and backward definitions), and proposal-voting links are established.

**22. Ancestor Definition (Forward)** — ✅ Success  
Ancestry equals the transitive closure of the parent relation.

**23. Ancestor Definition (Backward)** — ✅ Success  
Converse of the forward definition.

**24. Genesis Not In Pipeline** — ✅ Success  
Genesis is never proposed, prevoted on, or precommitted beyond initialization.

**25. Unique Proposal** — ✅ Success  
Two proposals in the same view must be identical and from the same operator.

**26. Prevote Implies Proposed** — ✅ Success  
A prevote can only be cast for an interaction that was proposed.

**27. Precommit Only If Proposed** — ✅ Success  
A precommit can only reference a proposed interaction.

**28. Precommit Node Lock Consistency** — ✅ Success  
If one node precommitted and another prevote-locked in the same view, they must agree.

---

### 4.4 — November, 2025 — Ancestry, Decision Properties, Prepare Stage Lock Sending (10 invariants)

**29. Ancestor Reflexive** — ✅ Success  
Every interaction is its own ancestor.

**30. Ancestor From Parent** — ✅ Success  
A parent is an ancestor.

**31. Ancestor Transitive** — ✅ Success  
Ancestry is transitive.

**32. Ancestor Antisymmetric** — ✅ Success  
Ancestry is antisymmetric.

**33. Ancestor Height Strict** — ✅ Success  
Strict ancestors have strictly lower height.

**34. No Ancestor At Equal Height** — ✅ Success  
Distinct interactions at the same height cannot be ancestors.

**35. Parent Height** — ✅ Success  
A child's height equals its parent's height plus one.

**36. Decided Implies Proposed** — ✅ Success  
Decided interactions must have been proposed.

**37. Prepared Node Has Lock Sent (p1)** — ✅ Success  
Prepared nodes with qualifying locks must have sent them (participant 1).

**38. Prepared Node Has Lock Sent (p2)** — ✅ Success  
Prepared nodes with qualifying locks must have sent them (participant 2).

---

### 4.5 — December, 2025 — Lock Discovery, View Management & Roles (7 invariants)

The lock-discovery bridge invariant (precommit next view discovery) is added, along with view management and operator role constraints.

**39. Highest Lock Sent** — ✅ Success  
Lock messages in the prepare phase report the node's actual highest lock.

**40. Precommit Next View Discovery** — ⏳ Pending  
In consecutive views, the operator discovers precommit-locks from the prior view.

**41. Unique Current View** — ✅ Success  
Each node has exactly one current view at any time.

**42. Node Has Current View** — ✅ Success  
Every node always has an assigned view.

**43. Prepared Only At Current Or Past** — ✅ Success  
A node can only be prepared for views it has reached.

**44. Cross-Node Unique Prevote** — ✅ Success  
All honest nodes' prevotes in a view agree on the same interaction.

**45. Prepare Response Only On Prepare** — ✅ Success  
Prepare responses require a prepared operator.

---

### 4.6 — January, 2026 — Prepare Phase & Ghost Relations (3 invariants)

**46. Locked At View (Forward)** — ✅ Success  
Ghost lock-tracking relation reflects actual locks.

**47. Locked At View (Backward)** — ✅ Success  
Actual locks are reflected in the ghost relation.

**48. Sent Lock At Past View** — ✅ Success  
Nodes send locks only from views they have completed.

---

### 4.7 — January, 2026 — Stage Progression (13 invariants)

The protocol enforces a strict ordering of phases within each view. These invariants capture that ordering, the exclusion properties at each stage, and the state implications of being in a given stage.

**49. Unique Stage** — ✅ Success  
A node is in exactly one phase per view.

**50. Stage Init Is Prepare** — ✅ Success  
A node that hasn't started a view must be in the prepare phase.

**51. Stage 1** — ✅ Success  
In the propose phase, lock messages from prepare have been sent.

**52. Stage 2** — ✅ Success  
In the prevote phase, the node prevoted for the proposed interaction (or nil).

**53. Stage 3** — ✅ Success  
In the precommit phase, the node either prevoted for the operator's proposal or holds locks.

**54. Stage 4** — ✅ Success  
In the decide phase, the node holds precommit-locks.

**55. Stage Neg 1** — ✅ Success  
Before the decide phase, no precommit-locks or decisions exist.

**56. Stage Neg 2** — ✅ Success  
Before the precommit phase, no locks or precommits exist.

**57. Stage Neg 3** — ✅ Success  
Before the prevote phase, no prevotes or locks exist.

**58. Stage Neg 4** — ✅ Success  
During the prepare phase, no lock messages have been sent.

**59. Prevote Stage Implies Prevoted** — ✅ Success  
Being in the prevote phase means the node has prevoted.

**60. Precommit Stage Implies Precommitted** — ✅ Success  
Being in the precommit phase means the node has precommitted.

**61. Lock Stage Valid** — ✅ Success  
Locks only occur at valid stages (prevote or precommit).

---

> **February, 2026 — Migration to Veil 2.0.** All invariants from this point onward are formalized using the Veil 2.0 framework, which offers improved automation and a more expressive specification language.

---

### 4.8 — February, 2026 — Chain Structure & Parent Constraints (5 invariants)

Parent-existence constraints and cross-node lock uniqueness.

**62. No Lock Without Parent** — ✅ Success  
Non-genesis locked interactions must have a parent.

**63. No Proposal Without Parent** — ✅ Success  
Non-genesis proposed interactions must have a parent.

**64. No Decision Without Parent** — ✅ Success  
Non-genesis decided interactions must have a parent.

**65. Cross-Node Unique Lock** — ✅ Success  
Two honest nodes cannot hold conflicting locks on the same participant in the same view.

**66. Lock At Most Current View** — ✅ Success  
Locks exist only at views the node has reached.

---

### 4.9 — March, 2026 — Genesis Descendant Properties (2 invariants)

All proposed and locked interactions are anchored to the genesis chain.

**67. Proposed Descends From Genesis** — ✅ Success  
All proposed interactions descend from genesis.

**68. Locked Descends From Genesis** — ✅ Success  
All locked interactions descend from genesis.

---

### 4.10 — March, 2026 — Operator & Uniqueness Constraints (13 invariants)

Operator constraints and uniqueness guarantees for prevotes, precommits, locks, and parent relationships.

**69. Operator From Context** — ✅ Success  
The operator belongs to one of the participant contexts.

**70. Prepared Operator Not At Zero** — ✅ Success  
A prepared operator is not at view zero.

**71. Propose Only If Operator Prepared** — ✅ Success  
Only a prepared operator can propose.

**72. Propose Only If Parent Locked** — ✅ Success  
When extending a chain, some node must hold a lock on the parent interaction.

**73. Sent Lock Only If Prepared** — ✅ Success  
Lock messages are sent only by prepared nodes.

**74. Unique Precommit Nodes** — ✅ Success  
An honest node precommits at most one interaction per view.

**75. Unique Prevote Operator** — ✅ Success  
The operator aggregates at most one prevote certificate per view.

**76. Unique Precommit Operator** — ✅ Success  
The operator aggregates at most one precommit certificate per view.

**77. Unique Lock Sent (p1)** — ✅ Success  
At most one lock message per view per node for participant 1.

**78. Unique Lock Sent (p2)** — ✅ Success  
At most one lock message per view per node for participant 2.

**79. Unique Parent** — ✅ Success  
Each interaction has at most one parent.

**80. Parent Irreflexive** — ✅ Success  
No interaction is its own parent.

**81. Parent Only If Proposed** — ✅ Success  
A parent relationship only exists if the child was proposed.

---

### 4.11 — March, 2026 — Genesis Properties (5 invariants)

Additional genesis invariants ensuring it is correctly decided at initialization and anchors the chain.

**82. Genesis Decided At Zero** — ✅ Success  
All nodes decide genesis at view zero.

**83. Genesis View Zero** — ✅ Success  
Only genesis can be decided at view zero.

**84. Genesis Height Zero** — ✅ Success  
Genesis is the unique interaction at height zero.

**85. Genesis Has No Parent** — ✅ Success  
Genesis has no parent interaction.

**86. Genesis Decided First** — ✅ Success  
Genesis must be decided before any other interaction.

---

### 4.12 — March, 2026 — Decision Completeness (3 invariants)

Decision prerequisites linking the decide action to precommit-locks and quorum precommits.

**87. Decision Requires Precommit Lock** — ✅ Success  
Decided interactions must have a precommit-lock.

**88. Decisions Not From Higher Views** — ✅ Success  
Nodes decide only in views they have reached.

**89. Decide Only If Quorum Precommit** — ✅ Success  
A decision requires a valid supermajority of precommits.

---

### 4.13 — March, 2026 — Height Monotonicity & Uniqueness (4 invariants)

Height-based reasoning is introduced: lock and decision heights grow monotonically, and distinct honest nodes cannot decide or lock conflicting interactions at the same chain height.

**90. Unique Decided At Height** — ⏳ Pending  
Two honest nodes cannot decide different interactions at the same chain height.

**91. Unique Locked At Height** — ⏳ Pending  
Two honest nodes cannot hold locks for different interactions at the same height.

**92. Lock Height Monotone** — ⏳ Pending  
A node's lock heights never decrease across views.

**93. Decision Height Monotone** — ⏳ Pending  
A node's decision heights never decrease across views.

---

### 4.14 — March – April, 2026 — Height-Based Modeling & Decided State (10 invariants)

Decided-state tracking is introduced (each node tracks its latest decided interaction), along with height-based prevote ordering.

*Decided state tracking:*

**94. Unique Decided Interaction** — ✅ Success  
Each node tracks exactly one latest decided interaction.

**95. Node Has Decided Interaction** — ✅ Success  
Every node always has a latest decided interaction.

**96. Decided Interaction Is Valid** — ✅ Success  
The tracked latest decided interaction has actually been decided.

**97. Decided Height Upper Bound** — ⏳ Pending  
The latest decided interaction's height is at least as high as any decided interaction.

**98. Decided Has Parent** — ✅ Success  
Non-genesis latest decided interactions have a parent.

**99. Decided Descends From Genesis** — ✅ Success  
Decided interactions descend from genesis.

**100. Decided Has Precommit Lock** — ✅ Success  
Nodes hold precommit-locks for their decided interactions.

**101. Decided Unique At Height** — ⏳ Pending  
Two nodes' decided interactions at the same height must be identical.

*Decision & chain integrity:*

**102. Decided Implies Parent Decided** — ⏳ Pending  
If an interaction is decided, its parent was decided in an earlier view.

*Height ordering:*

**103. Prevoted Height Ge Locks** — ⏳ Pending  
A prevote target's height is at least as high as all prior locks.

---

### Summary

**October, 2025** — Core Safety & Lock Foundations — 12 invariants (11 ✅, 1 ⏳)  
**October, 2025** — Lock & Decision Structure — 9 invariants (9 ✅)  
**October, 2025** — Ancestry & Proposal Rules — 7 invariants (7 ✅)  
**November, 2025** — Ancestry, Decision Properties, Prepare Stage Lock Sending — 10 invariants (10 ✅)  
**December, 2025** — Lock Discovery, View Management & Roles — 7 invariants (6 ✅, 1 ⏳)  
**January, 2026** — Prepare Phase & Ghost Relations — 3 invariants (3 ✅)  
**January, 2026** — Stage Progression — 13 invariants (13 ✅)  
**February, 2026** — Chain Structure & Parent Constraints — 5 invariants (5 ✅)  
**March, 2026** — Genesis Descendant Properties — 2 invariants (2 ✅)  
**March, 2026** — Operator & Uniqueness Constraints — 13 invariants (13 ✅)  
**March, 2026** — Genesis Properties — 5 invariants (5 ✅)  
**March, 2026** — Decision Completeness — 3 invariants (3 ✅)  
**March, 2026** — Height Monotonicity & Uniqueness — 4 invariants (0 ✅, 4 ⏳)  
**March – April, 2026** — Height-Based Modeling & Decided State — 10 invariants (6 ✅, 4 ⏳)

**Total** — 103 invariants defined. 93 verified, 10 pending.

---

## 5. Roadmap

### In Progress

- Complete the formal safety proof of IFP within a single epoch. This will require verifying the 10 pending invariants and expanding the current set of 103 with additional supporting properties, potentially reaching 150+.

### Upcoming

- Publish proof artifact and accompanying technical report
- Extend to safety of IFP under epoch reconfiguration and in the presence of read locks
- Explore liveness verification

---

## 6. Contributors

Rishal S P, Rahul Lenkala

**External Contributor:**  
Srinidhi Nagendra (Max Planck Institute)

We thank the Veil team at the National University of Singapore for their Veil-related support and bug fixes.
