## The Problem: A Circular Dependency

Two of our safety invariants each make a claim about descent — that one interaction is an ancestor of another. The issue is that each can only be proven by assuming the other is already true. This might result in the proof timing out. 

## The Fix: Separate "Carrying" from "Claiming"

We split the work into two kinds of statements:

- **Descent Information Carriers** — say only "this prevote was built on top of some certificate at an earlier view." They make no ancestry claim, so they can be proven directly from how the protocol works. 
- **Descent Claim** (`qc_descent`) — the single statement that actually claims ancestry. Its only dependency on an ancestry-claim is on **itself**, and every time it refers to itself it points to a **strictly earlier view**. Views only count upward and bottom out at genesis (view 0), so that chain of self-references always reaches the base case. 

---
## The Invariants

  Each heading gives the invariant's **number**, its name, and the numbers of the **other invariants in this list** it directly depends on. "Depends on: none" means it rests only on invariants we have already proven elsewhere.
### 1. `locks_analog_precommit` — depends on: 2

Once a precommit-certificate for an interaction exists at some view, every later honest prevote is for that interaction or one of its descendants. A precommit "locks the chain": no honest node will later prevote for something that conflicts with it.

### 3. `qc_descent` — depends on: 4, 6, 7, 8, 9, 10, 11
Once a precommit-certificate for interaction `I` exists at view `V`, every certificate for any interaction `J` at a later view `W` must be `I` itself or a descendant of `I` — and in both cases `height I ≤ height J`.

The height bound makes the descent concrete. Working backward from `J` through earlier views (invariant 4), each repropose step keeps the height and each extend step lowers it by one, so the chain of anchors steps down through the heights until it reaches `height I`. That gives a second, arithmetic measure — the height — alongside the strictly-decreasing view, and the height helpers (10, 11) pin the ancestor of `J` sitting at `height I` to be exactly `I`.

Its only ancestry dependency is on itself, always at a strictly earlier view. It feeds the existing main-safety argument. Genesis is an ancestor of everything and is handled separately, so `I` and `J` are assumed non-genesis here.

### 4. `qc_anchored` — depends on: 5 

If an honest node has prevoted on an interaction `J` of height `h`, then at some earlier view there is a qc for `J` itself at height `h` (repropose), or for `J`'s parent at height `h − 1` (extend — a child sits exactly one height above its parent). It only says "there is an earlier, at-most-one-step-lower qc," never that anything is an ancestor — so it carries the height-and-extension information without making a descent claim.

### 5. `prevote_matches_argmax` 

An honest node's prevote matches the highest lock it picked: either the prevote is on that interaction (repropose) or on its child (extend). This is the structural link from a prevote back to the node's 'highest lock'.

### 6. `same_view_precommit_prevote_agree` 

At each view, if there is a precommitQC and a prevoteQC then they must be on the same interaction. 

### 7. `precommit_qc_unique_at_view` 

There is at most one precommit-certificate per view — same quorum-intersection argument as above.

### 8. `precommit_floats_down_to_argmax` — the hard case

If an earlier precommit sits at a view *above* the prevoter's chosen lock view, that precommit "floats down" to a certificate at or below the chosen view, on the same interaction. 

### 9. `precommit_backed_above_zero` 
  
A precommit-certificate never exists at view 0. Holds because the precommit step requires a non-zero view, and the initial state has none.

### 10. `ancestor_height_strict` — depends on: none

If `I` is an ancestor of `J` (and `I ≠ J`), then `height I < height J`. The bridge between "extends" and height: descending the chain strictly increases height, since each child sits exactly one height above its parent. Lets the proof turn an ancestry goal into a height comparison and rule out a taller interaction being an ancestor of a shorter one.

### 11. `unique_precommit_backed_at_height` — depends on: none

If two precommit-certificates exist at the same height (both non-genesis), they are for the same interaction. The height twin of invariant 7: where 7 gives uniqueness per *view*, this gives uniqueness per *height*. So a height names a single block on the committed chain — which is exactly what lets a height match be upgraded to "same interaction" in invariant 3.

### 12. `decision_height_monotone` — depends on: none

If two honest nodes decide interactions `I1` (at view `V1`) and `I2` (at view `V2`) with `V1 < V2`, then `height I1 ≤ height I2`: a later decision is never shorter than an earlier one. Combined with 11, this is the height-based core of safety — of two committed interactions the earlier is no taller, and the unique interaction at its height on the later one's chain must be it. (Feeds main-safety directly.)


--- 
