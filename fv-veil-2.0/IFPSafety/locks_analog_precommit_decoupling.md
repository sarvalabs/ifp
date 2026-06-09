# Decoupling LAP ⇄ F1: a non-cyclic safety invariant for restricted-IFP

> Goal: replace the **mutually-inductive** pair `locks_analog_precommit` (LAP, @615) ⇄
> `argmax_recvd_ixn_descends_from_precommit_backed_at_bounded_view` (F1, @631) with a set whose
> dependency graph is a **DAG plus exactly one self-loop**. From the protocol + first principles;
> every load-bearing helper was read in `IFPNTDPH.lean` and is cited with its current line and
> verified guard.
>
> **Revision history (two adversarial passes baked in).**
> - *Pass 1 (red-team)* found the naive QC-level goal BROKEN: it recursed by shrinking the
>   *hypothesis-side* view `V` at fixed witness view — a non-decreasing self-edge. **Fix:** the
>   well-founded measure is the **J-side certificate view `W`**.
> - *Pass 2 (statement-level pressure test)* found the carrier's anchor view was **not provably
>   the same** as the prepare-quorum bound view (the "`v_max` linchpin"): anchoring via
>   `prevote_justified_by_highest_lock` (914) gives an *existential* lock view with no tie to
>   `argmax_recvd_view`. **Fix:** anchor the carrier through the **cache** (`argmax_recvd_qc_backed`
>   @834) so `v_max ≡ argmax_recvd_view h W` by construction. This also removes the design's
>   dependence on `prevote_lock_only_if_quorum_prevoted`/`precommit_lock_implies_precommit_backed`
>   staying Byzantine-unguarded.

---

## 1. Why LAP and F1 form a cycle

Both invariants **assert descent** (`X = I ∨ ancestor I X`), and each is the other's only source
of descent, routed **through the argmax cache**: LAP (at the prevote actions) reads the prevoting
node's `argmax_recvd_ixn` and consumes **F1 at the same view**; F1 (at `collect_recvd_locks`)
crosses the cache's QC at `V_max` with `precommit_backed`'s quorum and consumes **LAP at the
strictly smaller view `V_max`**. Two distinct descent-asserters, mutually dependent ⇒ a real 2-cycle.

---

## 2. The decoupling principle

**Separate the descent-CARRIER from the descent-ASSERTER.** The cache is a message snapshot, already
QC-backed (`argmax_recvd_qc_backed` @834) and prepare-quorum-bounded (`recvd_collected_implies_bounded_prepare_quorum`
@578) by *non-recursive* construction invariants. F1 exists only to thread *descent* through it. Kill that by:

1. **A descent-FREE carrier** that says a prevote merely *extends some certificate at a strictly
   lower view* — asserting **no ancestry**, hence provable from action facts alone.
2. **One descent-asserting invariant** (the goal), whose only edge into a descent-bearing node is
   **to itself**, carrying a **strict decrease of the J-side certificate view `W`**. A self-loop at
   a smaller view is the normal Veil step-induction pattern — not a 2-cycle. Well-founded by `<` on
   `TotalOrderWithMinimum view`, bottoming at `tot_view.zero`.

---

## 3. The reformulated goal

A **certificate** for `J` at `W` is a prevote-QC or a precommit-QC (both *raw quorums*):

```
prevote_qc   W J :≡ ∃ (s:nodeset), ctx.supermajority s ∧ ∀ m, ctx.member m s → prevoted_node    m W J
precommit_qc W J :≡ ∃ (s:nodeset), ctx.supermajority s ∧ ∀ m, ctx.member m s → precommitted_node m W J
cert_qc      W J :≡ prevote_qc W J ∨ precommit_qc W J
```

> **Why raw `precommit_qc`, not the ghost `precommit_backed`:** the carrier's precommit anchor comes
> from `argmax_recvd_qc_backed` (834), whose precommit case yields a `precommitted_node` *quorum*, not
> the ghost; and the model has **no quorum⇒ghost** direction. The downstream feeder `decided J →
> precommit_backed W J` (@897) reaches `cert_qc` via `precommit_backed_fwd` (@1016, ghost⇒quorum), so
> the J-side never needs a prevote-QC conversion — which would route through the Byzantine-operator-
> unsound `prevote_operator_only_if_quorum_prevoted` (@1353).

**`qc_descent` (new GOAL — the single self-referential invariant):**

> *English.* If an honest-witnessed precommit-QC exists for non-genesis `I` at `V`, then every
> certificate for non-genesis `J` at any strictly later view `W` is `I` or a descendant of `I`.

```
qc_descent : ∀ (V W : view) (I J : interaction),
  ( precommit_backed V I ∧ I ≠ genesis ∧ J ≠ genesis ∧ cert_qc W J ∧ tot_view.lt V W )
  → ( J = I ∨ ancestor I J )
```

### 3.1 Same downstream impact as LAP (route to `main_safety` @687)

For two honest decisions `decided n1 v1 i1`, `decided n2 v2 i2`:

- **Both non-genesis:** `decided _ V I → precommit_backed V I` (@897); `decided _ W J →
  precommit_backed W J → precommit_qc W J` (@897 then @1016) `→ cert_qc W J`. `V<W ⇒
  qc_descent(V,W,I,J)`; `W<V` symmetric; `V=W ⇒ unique_precommit_backed_at_view` (@1023) `⇒ I=J`.
  ⇒ `ancestor i1 i2 ∨ ancestor i2 i1` (`ancestor_refl` @1157 for equality). **No operator bridge.**
- **One side genesis:** genesis ancestors everything — `committed_ixn_descends_from_genesis` (@1422)
  + `ancestor_refl`, **independent of `qc_descent`** (which guards `I,J≠genesis`).

Feeds the existing `locks_analog_decided` (@728) → `main_safety`, otherwise unchanged. LAP itself is a
one-liner: honest `prevoted_node NP V2 J ⇒ prevote_qc V2 J` (via `prevote_lock_only_if_quorum_prevoted`
on its lock, or its own quorum) `= cert_qc V2 J ⇒ qc_descent`.

---

## 4. The decoupled invariant set

### Tier A — non-recursive leaves (ALL present, statements/guards verified)

| Invariant | @ | Gives | Guard |
|---|---|---|---|
| `argmax_recvd_qc_backed` | 834 | honest cache `(IM,SM,VM)` ⇒ `prevote_qc VM IM` (prevote) / `precommit_qc VM IM` (precommit) | honest on cache-holder ✓ |
| `argmax_recvd_is_highest_lock` | 682 | honest cache ⇒ `∃M. sent_lock_in_prepare M W IM SM VM ∧ locked …` | honest ✓ |
| `highest_lock_sent` | 1104 | `sent_lock … VL` ⇒ `VL < V` **and** no lock in open `(VL,V)` | **unguarded** ✓ |
| `recvd_collected_implies_bounded_prepare_quorum` | 578 | cache view `VMAX` ⇒ prepare-quorum, member locks `≤ VMAX` | ✓ |
| `prevoted_node_implies_recvd_collected` | 714 | honest prevote ⇒ `recvd_collected` (∴ cache exists, @810/813/816) | honest ✓ |
| `precommit_backed_fwd` | 1016 | `precommit_backed ⇒ precommit_qc` | **unguarded** ✓ |
| `precommit_node_locked_at_same_view` | 926 | honest precommit-vote ⇒ prevote-lock@V or precommit-lock@`u≤V` | honest ✓ |
| `precommit_lock_implies_precommit_backed` | 1090 | precommit-lock ⇒ `precommit_backed` (used only on honest `m*`) | unguarded (honest suffices) ✓ |
| `precommit_nodes_only_if_prevoted_for_same_ixn` | 1287 | honest precommit ⇒ own prevote, same ixn | honest ✓ |
| `cross_node_unique_prevote` | 1284 | two honest prevoters@V agree | two-honest ✓ |
| `unique_precommit_nodes` | 1367 | honest precommits ≤ 1 / view | honest ✓ |
| `unique_precommit_backed_at_view` | 1023 | two `precommit_backed`@V agree | unguarded ✓ |
| `cur_view_global`/`prevoted_node_view_bound`/`precommitted_node_view_bound` | 990/995/1000 | single global view; vote view `≤ cur_view` | honest (used via intersector) |
| `genesis_not_in_pipeline` | 1273 | honest never prevotes/precommits genesis | honest ✓ |
| `committed_ixn_descends_from_genesis` | 1422 | committed ⇒ descends genesis | honest ✓ |
| `ancestor_refl`/`ancestor_from_parent`/`ancestor_trans` | 1157/1160/1163 | tree algebra | — |
| `decided_implies_precommit_backed`/`decide_only_if_quorum_precommit` | 897/1348 | decided ⇒ ghost / quorum | honest ✓ |
| `supermajorities_intersect_in_honest` | class @32 | two supermajorities share an honest member (`s,s` ⇒ each has one) | — |

> **Sub-fact (free, no new invariant): `argmax_recvd_view h W = VM < W`.** From `argmax_recvd_is_highest_lock`
> (682) ⇒ `sent_lock_in_prepare M W IM SM VM`, then `highest_lock_sent` (1104) ⇒ `VM < W`.

### Tier B — new invariants to ADD (5; only the goal is recursive)

**B1. `precommit_backed_above_zero`** *(leaf, base grounding)*
```
∀ V I. precommit_backed V I → V ≠ tot_view.zero
```
*Trivial at `respond_precommit` (`require v ≠ tot_view.zero` @517); init `false`.*

**B2. `prevote_matches_argmax`** *(NEW structural prevote→cache link — the piece confirmed ABSENT by grep)*
> An honest prevote for non-genesis `J` agrees with the prevoter's cached argmax: either `J` *is* the
> argmax (prevote-stage, repropose) or `J`'s parent is the argmax (precommit-stage, extend).
```
∀ N W J.
  ( ¬ ctx.is_byz N ∧ prevoted_node N W J ∧ J ≠ genesis ∧ W ≠ tot_view.zero ) →
    ∃ (IM : interaction), argmax_recvd_ixn N W IM ∧
      ( (argmax_recvd_stage N W prevote   ∧ J = IM)
      ∨ (argmax_recvd_stage N W precommit ∧ parent IM J) )
```
*Trivial at `respond_propose_repropose` (`require ixn = ixn_max ∧ s_max = prevote`) and
`respond_propose_extend` (`require parent ixn_max ixn ∧ s_max = precommit`); the cache is set once at
`collect_recvd_locks` and is functional/stable, so it persists. **Descent-free.***

**B3. `qc_anchored`** *(the descent-FREE carrier — derived, exposes the cache view so the gap can reuse it)*
> Every honest prevote for non-genesis `J` at a non-initial view extends a certificate at the
> prevoter's cached argmax view `v_max < W`: `J` itself prevote-certified there (repropose), or `J`'s
> parent precommit-certified there (extend).
```
∀ N W J.
  ( ¬ ctx.is_byz N ∧ prevoted_node N W J ∧ J ≠ genesis ∧ W ≠ tot_view.zero ) →
    ∃ (v_max : view), argmax_recvd_view N W v_max ∧ tot_view.lt v_max W ∧
      ( prevote_qc v_max J ∨ (∃ P, precommit_qc v_max P ∧ parent P J) )
```
*Derivation (descent-free): `prevote_matches_argmax`(B2) gives `IM` at `argmax_recvd_view N W v_max`
matching `J`; `argmax_recvd_qc_backed`(@834) on the honest `N` gives `prevote_qc v_max IM` (repropose,
`IM=J`) or `precommit_qc v_max IM` (extend, set `P:=IM`, `parent IM J` from B2); `v_max<W` from 682+1104.
**No `prevote_justified_by_highest_lock`/1065/1090 — the cache route makes `v_max ≡ argmax_recvd_view N W`
by construction**, the same view 578 bounds against.*

**B4. `same_view_precommit_prevote_agree`** *(Byzantine-clean same-view repropose base)*
```
∀ V I J. ( precommit_backed V I ∧ I ≠ genesis ∧ J ≠ genesis ∧ prevote_qc V J ) → I = J
```
*`precommit_backed_fwd`(1016)⇒ honest `m*` (`precommit_nodes_only_if_prevoted_for_same_ixn` @1287 ⇒
`prevoted m* V I`); honest `h` of `prevote_qc V J` ⇒ `prevoted h V J`; `cross_node_unique_prevote`(@1284)
⇒ `I=J`. **Never touches the operator.***

**B5. `precommit_qc_unique_at_view`** *(same-view extend base)*
```
∀ V I1 I2. ( precommit_qc V I1 ∧ precommit_qc V I2 ) → I1 = I2
```
*Intersect the two quorums ⇒ honest `m`; `unique_precommit_nodes`(@1367) ⇒ `I1=I2`. Non-recursive.*

**B6. `precommit_floats_down_to_argmax`** *(the GAP packaged as a descent-FREE leaf — isolates the codebase's documented timeout point, see §8)*
> In the gap regime (an earlier precommit at `V` strictly above the prevoter's argmax view `v_max`), the
> precommit "floats down" to a precommit-QC at or below `v_max` on the **same** interaction `I`.
```
∀ N W J V I v_max.
  ( ¬ ctx.is_byz N ∧ prevoted_node N W J ∧ J ≠ genesis ∧
    precommit_backed V I ∧ I ≠ genesis ∧
    argmax_recvd_view N W v_max ∧ tot_view.lt v_max V ∧ tot_view.lt V W ) →
    ∃ (u : view), tot_view.le u v_max ∧ precommit_backed u I
```
> *The entire §6-case-(C) quorum-intersection + lock-trichotomy, packaged as a leaf that asserts a lower
> **precommit**, not ancestry — hence descent-free and non-recursive. Derivation: `precommit_backed_fwd`(@1016)
> ⇒ precommit-quorum `t` for `I`@`V`; `recvd_collected_implies_bounded_prepare_quorum`(@578) on `N`'s cache
> ⇒ prepare-quorum `s`, member locks `≤ v_max`; `supermajorities_intersect_in_honest`(@32) ⇒ honest `m*∈s∩t`;
> `precommit_node_locked_at_same_view`(@926) + `highest_lock_sent`(@1104, open-zone `(VL,W)`) kill the `>v_max`
> lock branches; survivor `locked m* I precommit u`, `u ≤ VL ≤ v_max`; `precommit_lock_implies_precommit_backed`(@1090,
> honest `m*`) ⇒ `precommit_backed u I`. **Discharge this leaf in ISOLATION (commit to `/manual-prove` —
> it relocates the RISK-1a chain from lines 568–576); `qc_descent` consumes it as a one-line premise so the
> trichotomy never re-enters `qc_descent`'s WP.***

**B7. `qc_descent` (the GOAL — §3)** — the only recursive invariant; self-loop at strictly smaller `W`.

### Retire (orphan-rule: re-route, then delete)
`locks_analog_precommit` (@615) → corollary of `qc_descent` (§3); F1 (@631) → unreferenced. Re-route
`locks_analog_decided` (@728) through `qc_descent` + `committed_ixn_descends_from_genesis`; `grep`
`@[invProof]`/manual references to 615/631 first.

---

## 5. Acyclic dependency DAG

```
Tier A leaves (present, non-recursive)
  argmax_recvd_qc_backed(834) / argmax_recvd_is_highest_lock(682) / highest_lock_sent(1104)
  recvd_collected_implies_bounded_prepare_quorum(578) / prevoted_node_implies_recvd_collected(714)
  precommit_backed_fwd(1016) / precommit_node_locked_at_same_view(926) / precommit_lock_⇒_backed(1090)
  cross_node_unique_prevote(1284) / unique_precommit_nodes(1367) / 1287 / unique_precommit_backed_at_view(1023)
  view-sync(990/995/1000) / genesis(1273/1422) / ancestor(1157/60/63) / decided(897/1348)
        │            │              │                 │
        ▼            ▼              ▼                 ▼
Tier B leaves (new, descent-FREE):  precommit_backed_above_zero   prevote_matches_argmax──►qc_anchored
                                    same_view_precommit_prevote_agree   precommit_qc_unique_at_view
                                    precommit_floats_down_to_argmax  (the gap, B6 — heavy but descent-free)
        └───────────────────────────────────┬───────────────────────────────────┘
                                            ▼
                                 ┌────────────────────┐
                                 │     qc_descent      │◄──┐ SELF-LOOP: strict decrease of W
                                 └────────────────────┘   │  (J-side certificate view)
                                            │   └──────────┘
                                            ▼
                                 locks_analog_decided ──► main_safety
                                            ▲
                                            └─ genesis branch: committed_ixn_descends_from_genesis(1422)+ancestor_refl
```

**No 2-cycle exists.** The only edge between two descent-bearing nodes is `qc_descent → qc_descent`,
carrying a strict `W`-decrease. Every other edge enters a **descent-free** node with no path back to a
descent node. LAP/F1 are deleted ⇒ a second descent-asserter is not even expressible.

---

## 6. Preservation case analysis (measure = J-side view `W`)

Fix `precommit_backed V I` (`I≠genesis`), `cert_qc W J` (`J≠genesis`), `V<W`. `cert_qc W J` newly holds
only via a new `prevoted_node` (`respond_propose_*`) or new `precommit_backed`/`precommitted_node`
(`respond_precommit`); all other actions frame the antecedent unchanged. From `cert_qc W J` extract one
**honest** prevoter `h` of `J` at `W` (`prevote_qc`: honest member; `precommit_qc`: honest member +
@1287). Apply `qc_anchored`(B3) ⇒ `v_max = argmax_recvd_view h W < W` and an anchor for `J`.

**B-0 base / view-sync.** New `precommit_backed W_now I` on the I-side: any `cert_qc W J` with `W>W_now`
is impossible — extract the certificate's honest member **first** (`s,s` intersection), *then* `*_view_bound`
(@995/1000) give `W ≤ cur_view = W_now`. **Vacuous.** `V=0` excluded by `precommit_backed_above_zero`;
`J=genesis` ⇒ honest member contradicts `genesis_not_in_pipeline`(1273); `W=0` is the recursion floor.

**(A) `V = v_max` — NON-recursive base (equal view ≠ progress):**
- repropose anchor (`prevote_qc V J`): `same_view_precommit_prevote_agree`(B4) ⇒ `J=I`. **Done.**
- extend anchor (`precommit_qc V P ∧ parent P J`): `precommit_backed V I →(1016) precommit_qc V I`;
  `precommit_qc_unique_at_view`(B5) ⇒ `P=I`; `ancestor_from_parent` ⇒ `ancestor I J`. **Done.**

**(B) `V < v_max` — the SELF-LOOP at certificate view `v_max < W` (STRICT):**
- repropose: `qc_descent(V, v_max, I, J)` on `prevote_qc v_max J`. **[self, W↓]**
- extend: `qc_descent(V, v_max, I, P)` on `precommit_qc v_max P` (= `cert_qc`); `parent P J`+`ancestor_trans`
  ⇒ `ancestor I J`. **[self, W↓]**

**(C) `V > v_max` — the GAP, now a ONE-LINE premise (all quorum work lives in the B6 leaf):**
Apply `precommit_floats_down_to_argmax`(B6) with `(N:=h, W, J, V, I, v_max)` ⇒ `∃ u ≤ v_max, precommit_backed u I`.
Replace the I-side view `V` by `u ≤ v_max`, then **re-enter (A)/(B):** `u=v_max` ⇒ (A) [non-recursive];
`u<v_max` ⇒ (B) `qc_descent(u, v_max, I, anchor)` **[self, certificate view `v_max < W`, STRICT]**. **Done.**
The Pass-2 linchpin (anchor view = bound view, both `argmax_recvd_view h W`) is now *internal to B6*.

So `qc_descent`'s proof at the trigger collapses to a 4-line skeleton: **extract honest `h` → `qc_anchored`(h)
→ if `V>v_max`, B6 lowers the I-side → same-view base (A) or one self-call (B).** Everything heavy is a leaf.

**Byzantine discipline.** Every descent conclusion is drawn at an honest intersector; only honest-guarded
invariants are applied to it. The carrier (B3) is anchored via the honest cache-holder `h` and the
honest-guarded `argmax_recvd_qc_backed`(834) — **no reliance on any lemma being Byzantine-unguarded.**

---

## 7. Edge cases & guards

| Scenario | Discharge | Recursive? |
|---|---|---|
| genesis as `I` | guard | — |
| genesis as `J` | `cert_qc W genesis`,`W≠0` ⇒ honest member ⊥ `genesis_not_in_pipeline`(1273); `J≠genesis` kept | No |
| view-0 base | `precommit_backed_above_zero`(B1); `W=0` recursion floor | No |
| same-view repropose | `same_view_precommit_prevote_agree`(B4), two honest intersectors — never the operator | No |
| same-view extend | `precommit_backed_fwd`(1016)+`precommit_qc_unique_at_view`(B5)+`ancestor_from_parent` | No |
| `V<v_max` | self-loop at `v_max<W` | goal@W↓ |
| gap `V>v_max` | `highest_lock_sent`+`@926`, drop I-side to `u≤v_max`, re-enter (A)/(B); self-call at `v_max<W` | goal@W↓ |
| Byzantine member | always honest intersector; no per-Byzantine conclusion | No |
| Byzantine operator/proposer | carrier anchored on honest cache-holder `h` via `argmax_recvd_qc_backed`(834); same-view base via B4 — never `prevote_operator_only_if_quorum_prevoted`(1353) | No |
| new precommit (sync) | I-side vacuous via honest-extracted view bound; J-side already covered via `prevote_qc` | No |
| `propose_nil` | no certifiable proposal; frame | No |
| double-prevote | `respond_propose_*` `require ∀i ¬prevoted_node n v i` (unguarded) ⇒ one prevote/view even for Byzantine | No |
| main_safety genesis side | `committed_ixn_descends_from_genesis`(1422)+`ancestor_refl`, independent of `qc_descent` | No |

---

## 8. Residual risks / proof checkpoints

1. **`v_max` linchpin — RESOLVED (Pass 2).** `qc_anchored`(B3) exposes `argmax_recvd_view N W v_max`,
   and the gap's 578 consumes the same `v_max`. The earlier "two distinct `v_max`'s" hole is gone *provided
   B3 is stated with the `argmax_recvd_view N W v_max` conjunct* — do not drop it.
2. **★ MAJOR (debate-confirmed): the gap is this codebase's documented timeout point.** §6-case-(C),
   now the B6 leaf, relocates the exact cross-quorum-intersection + lock-trichotomy that lines 568–576 of
   `IFPNTDPH.lean` record as having ALREADY timed out (the pruned RISK-1a /
   `precommit_backed_drops_below_argmax_view`). **Mitigation (mandatory):** discharge **B6 in ISOLATION**,
   committing to `/manual-prove` (`veil_solve_wp`) from the outset; `qc_descent` then consumes it as a
   one-line premise so the trichotomy never re-enters `qc_descent`'s WP. Plan manual proofs for
   `(qc_descent × respond_propose_repropose)` and `(qc_descent × respond_prevote)` too. *Whether even the
   isolated B6 discharges under the WP/simp budget is empirical — settle it with a build before scaling up.*
3. **Well-foundedness / quorum-fixing (now internal to B6).** B6's discharge intersects `h`'s cache
   prepare-quorum `s` (578) with `precommit_backed_fwd`'s `t`, pinning `s` to `h`'s cache; the linchpin
   (anchor view = bound view = `argmax_recvd_view h W`) lives inside B6. The self-loop measure stays `W`,
   strictly decreasing — never shrinking `V` at fixed `W`.
4. **Per-(invariant × transition) checkpoints, discharged IN ORDER (debate-confirmed under-specification):**
   - **`prevote_matches_argmax`(B2) — write & discharge BEFORE B3/qc_descent** (B3 depends on it).
     (i) establish at `respond_propose_repropose` (`require ixn=ixn_max ∧ s_max=prevote`) / `_extend`
     (`require parent ixn_max ixn ∧ s_max=precommit`); (ii) **vacuous at `collect_recvd_locks`** — it writes
     the cache, but `¬recvd_collected`@399 + `prevoted_node_implies_recvd_collected`@714 make a pre-existing
     prevote-at-`W` contradict the firing, so there is no live obligation; (iii) frame elsewhere.
   - **precommit_qc extraction is a TWO-HOP** — to get `recvd_collected h W` from an honest *precommitter*
     `h`, route `precommitted_node h W J →(@1287, same-ixn) prevoted_node h W J →(@714) recvd_collected h W`;
     confirm both honest-guarded hops survive `respond_prevote`.
   - **`same_view_precommit_prevote_agree`(B4) preservation across `respond_prevote`** — that action creates
     new `precommitted_node` (hence new `precommit_backed`/`precommit_qc`); list it as an explicit checkpoint.
   - **Byzantine hygiene (B4/B5):** confirm the SMT discharge extracts the honest intersector via @32 over
     the two raw quorums, never reasoning over a possibly-Byzantine member (per the project's
     byzantine-quantifier guidance).
5. **Model fidelity (load-bearing, positive).** No unconstrained Byzantine free-write action exists
   (all actions @198–545 precondition-gated; init zeroes the vote relations). A `cert_qc` therefore
   implies every member passed the protocol checks. **Re-audit if a free Byzantine write-action is added.**
6. **`cert_qc` SMT surface.** Consider materializing `prevote_qc`/`precommit_qc` as ghost relations
   (written at `operator_prevote`/`operator_precommit`) with `_fwd` bridges, to keep the disjunctive
   antecedent EPR-friendly. Unconfirmed cost.

> **No longer a risk (improvement from Pass 2):** the design previously hinged on
> `prevote_lock_only_if_quorum_prevoted`(1065)/`precommit_lock_implies_precommit_backed`(1090) staying
> Byzantine-**unguarded** (the carrier recovered its anchor from a possibly-Byzantine `n_max`). With the
> cache-anchored carrier (B3 via 834) this dependence is gone; 1090 is now used only on the honest `m*`
> in the gap, where an honest guard would suffice.

---

### Net change vs the current file
**Add 7** — `qc_descent`(goal), `qc_anchored`, `prevote_matches_argmax`, `same_view_precommit_prevote_agree`,
`precommit_qc_unique_at_view`, `precommit_backed_above_zero`, `precommit_floats_down_to_argmax`(gap leaf, B6)
(all but the goal are descent-free).
**Delete 2** — LAP, F1. **Re-route 1** — `locks_analog_decided`. Everything else is already present.
Result: one self-loop, otherwise acyclic — and Byzantine-robust without relying on any accidental unguarded-ness.

> **Revision Pass 3 (adversarial debate).** A Convincer⇄ErrorFinder debate ruled the design **sound**
> (all four attacks on well-foundedness, the gap bound, the `precommit_qc` same-ixn extraction, and the
> carrier-cycle were withdrawn) but **dischargeability-risky**: the gap reasoning is this file's documented
> timeout point. Fixes folded in above: B6 isolates the gap as a descent-free leaf; §8 lists the B2 /
> two-hop / B4-across-`respond_prevote` per-transition checkpoints.
