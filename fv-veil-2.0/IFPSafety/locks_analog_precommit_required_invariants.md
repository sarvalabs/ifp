# Required invariants for `locks_analog_precommit`

> Derived **from first principles** — the IFP protocol, the IFPNTDP model state, and
> the IFPNTDP actions — *not* from the invariant list currently in `IFPNTDP.lean`.
> Each entry: one-sentence English + logical pseudocode (model relation names).
> Names are my own; any overlap with names already in the file is incidental
> confirmation, not the source.

---

## Main invariant to prove: `locks_analog_precommit`

**English.** Once a precommit-QC for interaction `I` has been witnessed at view `V`,
every later honest prevote (at any view `V2 > V`) is on `I` itself or on a
descendant of `I` — a witnessed precommit "locks the chain" against all future
honest prevotes.

```
∀ V V2 I J NP.
  ¬is_byz NP ∧ precommit_backed V I ∧ I ≠ genesis ∧ J ≠ genesis
  ∧ prevoted_node NP V2 J ∧ tot_view.lt V V2
  → (J = I ∨ ancestor I J)
```

### Why these invariants (proof-obligation skeleton)

Only three kinds of transition can falsify it:

| Threatening action(s) | What changes | Discharge route |
|---|---|---|
| `respond_precommit` | new `precommit_backed V I` at current view `v` | **(G)** view-synchrony ⇒ no prevote exists at `V2 > v`, hypothesis vacuous |
| `respond_propose_repropose` / `respond_propose_extend` | new `prevoted_node NP v J`, with `J = ixn_max` (repropose) or `J = child(ixn_max)` (extend) | **(F)** "argmax descends from every earlier precommit", split into bounded + gap cases |
| `propose_extend` | new `ancestor`/`parent` edges to a *fresh* interaction | **(E)** DAG structure ⇒ a fresh interaction is never already-prevoted, ancestry of existing `J` unchanged |

The substantive case is the prevote actions. The prevoted `J` is the operator's
**argmax** `ixn_max` (repropose: `J = ixn_max`; extend: `parent ixn_max J`). So the
whole proof reduces to: *the argmax `ixn_max` descends from every earlier
`precommit_backed I`*, which is invariant **F1**. F1 in turn splits on the argmax
view `v_max`:

- **bounded** (`V ≤ v_max`): the argmax sits at or above the precommit view ⇒ same-view uniqueness (`V = v_max`) or induction on `locks_analog_precommit` itself (`V < v_max`).
- **gap** (`V > v_max`): cross the precommit-quorum at `V` with the prepare-quorum (whose every member's highest lock is `≤ v_max`); the honest intersection node would have to hold a lock strictly between `v_max` and `v` — impossible by the highest-lock-sent property — *unless* its surviving lock is a precommit-lock at `U′ ≤ v_max`, which re-enters the bounded case.

---

## Tier 1 — The inductive heart (mutual with the target)

### F1. `argmax_descends_from_precommit_backed_bounded`
**English.** When a node's cached argmax view `Vmax` already dominates a precommit
view `U` (`U ≤ Vmax`), the cached argmax interaction `IM` is `I` or a descendant of
every interaction `I` that was precommit-backed at `U`.

```
∀ U Vact Vmax I IM N.
  ¬is_byz N ∧ precommit_backed U I ∧ I ≠ genesis
  ∧ argmax_recvd_ixn N Vact IM ∧ argmax_recvd_view N Vact Vmax
  ∧ tot_view.lt U Vact ∧ tot_view.le U Vmax
  → (I = IM ∨ ancestor I IM)
```
*Proved at `collect_recvd_locks` (the only writer of `argmax_recvd_*`). Uses A1, A3,
D2′, INV2, D1, the honest-member axiom, and — for `U < Vmax` — `locks_analog_precommit`
itself at the smaller gap `(U, Vmax)`. F1 and the target are mutually inductive: the
target consumes F1 at the prevote actions; F1 consumes the target at `collect_recvd_locks`.*

---

## Tier 2 — Quorum backing of ghost / cache relations

These turn the "a QC exists" ghosts (`precommit_backed`, `recvd_collected`,
`argmax_recvd_*`) back into the concrete supermajorities that justified them, so the
quorum-intersection axiom can be applied.

### A1. `precommit_backed_implies_precommit_quorum`
**English.** A witnessed precommit-QC for `I` at `V` is backed by a real
supermajority of nodes that each precommit-voted `I` at `V`.
```
∀ V I. precommit_backed V I →
  ∃ t. ctx.supermajority t ∧ ∀ n. ctx.member n t → precommitted_node n V I
```
*Provable at `respond_precommit`: its `s`/`precommitted_node` preconditions are the
witness. Preserved by monotonicity of `precommitted_node`.*

### A2. `recvd_collected_implies_bounded_prepare_quorum`
**English.** A node that has collected prepare responses (argmax view `Vmax`)
witnessed a full supermajority, each member having prepared and sent a real highest
lock at a view `≤ Vmax`.
```
∀ N Vact Vmax. recvd_collected N Vact ∧ argmax_recvd_view N Vact Vmax →
  ∃ s. ctx.supermajority s ∧ ∀ m. ctx.member m s →
    prepared_node m Vact ∧
    ∃ IL SL VL. sent_lock_in_prepare m Vact IL SL VL ∧ locked m IL SL VL
              ∧ tot_view.le VL Vmax
```
*Provable at `collect_recvd_locks` (its `s` parameter + the "all sent locks ≤ v_max"
precondition are the witness). The `VL ≤ Vmax` clause is exactly what powers the
gap-case elimination.*

### A3. `argmax_recvd_qc_backed`
**English.** A node's cached argmax interaction `IM` is itself certified by a
supermajority that voted (prevote- or precommit-, per `SM`) for `IM` at the argmax
view `VM`.
```
∀ N V IM SM VM.
  argmax_recvd_ixn N V IM ∧ argmax_recvd_stage N V SM ∧ argmax_recvd_view N V VM →
  ∃ t. ctx.supermajority t ∧
    (SM = prevote   → ∀ nt. ctx.member nt t → prevoted_node    nt VM IM) ∧
    (SM = precommit → ∀ nt. ctx.member nt t → precommitted_node nt VM IM)
```
*Provable at `collect_recvd_locks` (the action's argmax witness precondition).*

### D2′. `precommit_node_implies_prevote_qc`
**English.** A node's precommit-vote on `I` at `V` is backed by a prevote-QC for `I`
at `V` (it precommitted only after seeing a prevote-QC).
```
∀ N V I. precommitted_node N V I →
  ∃ s. ctx.supermajority s ∧ ∀ nc. ctx.member nc s → prevoted_node nc V I
```
*Provable at `respond_prevote`: its `s`/`prevoted_node` preconditions are the witness.
This is the lever that lets every precommit-QC be turned into a prevote-QC, so
same-view uniqueness needs only INV2 (prevote-QC uniqueness), never a per-node
"precommit ⇒ same prevote" bridge.*

---

## Tier 3 — Lock ⇄ vote ⇄ backing bridges

### C1. `precommit_node_locked_at_same_view`
**English.** An honest node that precommit-voted `I` at `V` is, as a result, locked
on `I` — either a fresh prevote-lock at `V`, or a pre-existing precommit-lock at some
view `U ≤ V`.
```
∀ N V I. ¬is_byz N ∧ precommitted_node N V I →
  (locked N I prevote V ∨ ∃ U. tot_view.le U V ∧ locked N I precommit U)
```
*Directly from the `if`/`else` in `respond_prevote` (the else-branch fires exactly
when the node already holds the precommit-lock).*

### C2. `precommit_lock_implies_precommit_backed`
**English.** If an honest node holds a (non-genesis) precommit-lock on `I` at view
`U`, then a precommit-QC for `I` was witnessed at `U`.
```
∀ N I U. ¬is_byz N ∧ locked N I precommit U ∧ I ≠ genesis →
  precommit_backed U I
```
*`respond_precommit` sets `locked … precommit v` and `precommit_backed v` together;
the genesis precommit-lock from `after_init` (view zero, unbacked) is excluded by
`I ≠ genesis`.*

### B1. `sent_lock_is_highest`
**English.** The lock a node reports in prepare at view `Vp` is its highest-view lock
below `Vp` — it holds no lock at any view strictly between the reported view `VL` and
`Vp`.
```
∀ N Vp IL SL VL I2 S2 V2.
  ¬is_byz N ∧ sent_lock_in_prepare N Vp IL SL VL ∧ locked N I2 S2 V2
  ∧ tot_view.lt VL V2 ∧ tot_view.lt V2 Vp
  → False
```
*From the `decide` body of `respond_prepare` (the "no lock at any `vl2 > VL`" clause).
Preservation leans on view-synchrony (G3): later locks are only ever acquired at the
current view `≥ Vp`, never inside the open gap `(VL, Vp)`. This is the invariant that
kills the gap case's prevote-lock-at-`V` and precommit-lock-at-`U′>Vmax` branches.*

---

## Tier 4 — Same-view uniqueness

### D1. `unique_prevote`
**English.** An honest node cannot prevote two different interactions in the same view.
```
∀ N V I J. ¬is_byz N ∧ prevoted_node N V I ∧ prevoted_node N V J → I = J
```
*From the `require ∀ i. ¬ prevoted_node n v i` guard in both `respond_propose_*`
actions. Leaf invariant.*

### INV2. `unique_prevote_qc_in_view`
**English.** Two prevote-QCs in the same view must certify the same interaction.
```
∀ V I J s1 s2.
  ctx.supermajority s1 ∧ (∀ n. ctx.member n s1 → prevoted_node n V I)
  ∧ ctx.supermajority s2 ∧ (∀ n. ctx.member n s2 → prevoted_node n V J)
  → I = J
```
*Derived from D1 via `supermajorities_intersect_in_honest`: the shared honest node
prevoted both `I` and `J`, so `I = J`. Used in F1's `U = Vmax` same-view sub-case.*

---

## Tier 5 — View synchrony (handles the `respond_precommit` case)

### G0. `single_global_view`
**English.** All nodes are always at one and the same current view (synchronous view
change).
```
∀ N1 N2 V1 V2. cur_view N1 V1 ∧ cur_view N2 V2 → V1 = V2
```
*`set_view` rewrites `cur_view` for **all** nodes simultaneously; `after_init` puts
everyone at `tot_view.zero`. Leaf invariant.*

### G1. `prevote_view_le_current`
**English.** Any prevote occurred at a view at or below the current global view (no
honest node has run ahead).
```
∀ N V J M VM. prevoted_node N V J ∧ cur_view M VM → tot_view.le V VM
```
*`prevoted_node` is set only at `respond_propose_*`, each gated on `cur_view n v`
(= the global view at that time); the global view is monotone (`set_view` uses
`tot_view.next`). This makes the `respond_precommit` case vacuous: the new
`precommit_backed v I` sits at the current view `v`, and G1 forbids any
`prevoted_node NP V2 J` with `V2 > v`, so the `V < V2` hypothesis can never fire.*

### G3. `lock_view_le_current`
**English.** Every (non-genesis) lock was acquired at a view at or below the current
global view.
```
∀ N I S U M VM. locked N I S U ∧ I ≠ genesis ∧ cur_view M VM → tot_view.le U VM
```
*`locked` is written only by `respond_prevote` / `respond_precommit`, both at the
current view. Underwrites B1's preservation (no lock ever lands inside a past gap).*

---

## Tier 6 — Interaction-DAG structure (handles `propose_extend`)

### E1. `ancestor_reflexive`
**English.** Every interaction is its own ancestor.
```
∀ I. ancestor I I
```
*`after_init` sets `ancestor I J := (I = J)`; `propose_extend` keeps the `A = ixn_propose` clause.*

### E2. `ancestor_transitive`
**English.** Ancestry composes.
```
∀ A B C. ancestor A B ∧ ancestor B C → ancestor A C
```
*Needed to chain `ancestor I ixn_max` (from F1) with `ancestor ixn_max J` (extend) into `ancestor I J`.*

### E3. `parent_implies_ancestor`
**English.** A direct parent is an ancestor.
```
∀ A B. parent A B → ancestor A B
```
*Turns `respond_propose_extend`'s `parent ixn_max J` into `ancestor ixn_max J`,
the link that converts F1's conclusion about `ixn_max` into one about the extended `J`.*

### E6. `prevoted_implies_has_parent`
**English.** Every prevoted interaction has a parent in the DAG.
```
∀ N V J. prevoted_node N V J → ∃ P. parent P J
```
*Via E9 + "proposed interactions have parents". Lets SMT see that the *fresh*
interaction created by `propose_extend` (required to have no parent) is never an
already-prevoted `J`, so `propose_extend`'s ancestor-edge update can't perturb the
ancestry of any `J` in the invariant's hypothesis.*

### E9. `prevoted_implies_non_genesis`
**English.** Genesis is never prevoted.
```
∀ N V J. prevoted_node N V J → J ≠ genesis
```
*Both `respond_propose_*` actions `require ixn ≠ genesis`. Gives `ixn_max ≠ genesis`
(through A3 + the precommit analog) so the IH application inside F1 meets its
`J ≠ genesis` side-condition.*

---

## Relied-upon class axiom (not a state invariant)

`ctx.supermajorities_intersect_in_honest`: any two supermajorities share an honest
member; instantiated at `(s, s)` it also yields *every supermajority has an honest
member*. Used in INV2 and in F1's IH-witness selection.

---

## Dependency tree

```
locks_analog_precommit                         [TARGET]
├─ (respond_precommit case)
│   └─ G1  prevote_view_le_current
│       └─ G0  single_global_view
├─ (respond_propose_repropose / _extend case)
│   ├─ F1  argmax_descends_from_precommit_backed_bounded     [mutual induction ↑]
│   │   ├─ A1   precommit_backed_implies_precommit_quorum
│   │   ├─ A3   argmax_recvd_qc_backed
│   │   ├─ D2′  precommit_node_implies_prevote_qc
│   │   ├─ INV2 unique_prevote_qc_in_view
│   │   │   └─ D1  unique_prevote
│   │   ├─ E9   prevoted_implies_non_genesis
│   │   ├─ axiom: supermajority has an honest member
│   │   └─ locks_analog_precommit   (IH at smaller view gap)
│   ├─ (gap case  V > Vmax)
│   │   ├─ A1   precommit_backed_implies_precommit_quorum
│   │   ├─ A2   recvd_collected_implies_bounded_prepare_quorum
│   │   ├─ B1   sent_lock_is_highest
│   │   │   └─ G3  lock_view_le_current  (preservation)
│   │   ├─ C1   precommit_node_locked_at_same_view
│   │   ├─ C2   precommit_lock_implies_precommit_backed
│   │   ├─ axiom: supermajorities_intersect_in_honest
│   │   └─ F1   (re-enters the bounded case at U′ ≤ Vmax)
│   └─ (extend conclusion shaping)
│       ├─ E3  parent_implies_ancestor
│       └─ E2  ancestor_transitive
└─ (propose_extend ancestor-edge case)
    ├─ E6  prevoted_implies_has_parent  (└─ E9)
    ├─ E1  ancestor_reflexive
    └─ E2  ancestor_transitive
```

### Leaves (preserved by construction / single action, no further deps)
`G0`, `D1`, `E1`, `E2`, `E3`, `E9`, `A1`, `A3`, `D2′`, `C1` — discharge these first;
they unblock everything above without round-trips.

### The one genuine cycle
`locks_analog_precommit ⇄ F1` is **mutual induction over the view gap**: F1's
`U < Vmax` branch invokes the target at strictly-smaller `(U, Vmax)`, and the target's
prevote-action proof invokes F1 at the current view. Sound in Veil's conjoined-invariant
framework because each side consumes the *pre-state* (inductive hypothesis) of the
other; well-founded because every appeal strictly shrinks `V2`.
```
