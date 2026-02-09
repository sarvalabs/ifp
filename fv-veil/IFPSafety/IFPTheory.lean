-- skip eval
import Aesop
import Mathlib.Data.Set.Basic

theorem Set.ne_empty_iff_exists_mem {α : Type u} {s : Set α} : s ≠ ∅ ↔ ∃ a, a ∈ s := by
  rw [← Set.nonempty_iff_ne_empty] ; aesop

namespace IFPTheory

-- Core types
abbrev View := Nat
abbrev Node := Nat
abbrev Participant := Nat
abbrev Stage := Bool
-- inductive Stage where | prevote | precommit
--   deriving DecidableEq, Repr

structure Interaction where
  id : Nat
  prepareView : View
  commitView : View

-- The locked relation (as inductive predicate)
variable (locked : Node → Participant → Interaction → Stage → View → Prop)

-- Highest lock predicate
def IsHighestLock (n : Node) (p : Participant) (i : Interaction)
    (s : Stage) (v : View) : Prop :=
  locked n p i s v ∧ (∀ i' s' v', v' > v → ¬ locked n p i' s' v') ∧ (s = true → ¬ locked n p i false v)

-- The lock set for projection-style operations
def lockSet (n : Node) : Participant → Stage → Set View :=
  fun p S => {v | ∃ I, locked n p I S v}

-- Project locks to specific interaction
def projectLocks (n : Node) (validInter : Set Interaction)
    : Participant → Stage → Set View :=
  fun p S => {v | ∃ I ∈ validInter, locked n p I S v}

theorem highest_lock_unique (n : Node) (p : Participant) (I : Interaction)
    (S : Stage) (v1 v2 : View) :
    IsHighestLock locked n p I S v1 →
    IsHighestLock locked n p I S v2 →
    v1 = v2 := by
  intro ⟨h1_locked, h1_no_higher, h1_stage⟩ ⟨h2_locked, h2_no_higher, h2_stage⟩
  by_contra h_ne
  cases Nat.lt_or_gt_of_ne h_ne with
  | inl h_lt =>
      -- h_lt : v1 < v2
      -- h1_no_higher : ∀ i' s' v', v1 < v' → ¬locked n p i' s' v'
      -- We can apply it with v' = v2
      exact h1_no_higher I S v2 h_lt h2_locked
  | inr h_gt =>
      -- h_gt : v2 < v1 (since v1 > v2 means v2 < v1)
      -- h2_no_higher : ∀ i' s' v', v2 < v' → ¬locked n p i' s' v'
      -- We can apply it with v' = v1
      exact h2_no_higher I S v1 h_gt h1_locked


end IFPTheory
