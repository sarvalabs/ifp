-- IFPSafety/IFPTheory.lean
import Aesop
import Mathlib.Data.Set.Basic

set_option linter.unusedVariables false

theorem Set.ne_empty_iff_exists_mem {α : Type u} {s : Set α} : s ≠ ∅ ↔ ∃ a, a ∈ s := by
  rw [← Set.nonempty_iff_ne_empty] ; aesop

namespace IFPTheory

class TotalOrderWithMinimum (t : Type) where
  -- relation: strict total order
  le (x y : t) : Prop
  -- axioms
  le_refl (x : t) : le x x
  le_trans (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total (x y : t) : le x y ∨ le y x

  -- relation: nonstrict total order
  lt (x y : t) : Prop
  le_lt (x y : t) : lt x y ↔ (le x y ∧ x ≠ y)

  -- successor
  next (x y : t) : Prop
  next_def (x y : t) : next x y ↔ (lt x y ∧ ∀ z, lt x z → le y z)

  zero : t
  zero_lt (x : t) : le zero x


class ByzQuorum (node : Type) (is_byz : outParam (node → Prop)) (nset : outParam Type) where
  member (n : node) (s : nset) : Prop
  supermajority (s : nset) (c : nset) : Prop   -- s is a supermajority of context c  -- 2f + 1 nodes

  supermajority_s_belongs_to_c :
    ∀ (s c : nset), supermajority s c → ∀ (n : node), (member n s → member n c)

  supermajorities_intersect_in_honest :
    ∀ (s1 s2 c : nset),
      (supermajority s1 c ∧ supermajority s2 c) → (∃ (n : node), member n s1 ∧ member n s2 ∧ ¬ is_byz n)


-- /-- Minimal axioms for lock theory -/
-- class LockTheory (Node Participant View Interaction Stage : Type) where
--   /-- Total order on views -/
--   view_lt : View → View → Prop
--   view_le : View → View → Prop
--   view_le_refl : ∀ v, view_le v v
--   view_le_trans : ∀ a b c, view_le a b → view_le b c → view_le a c
--   view_le_antisymm : ∀ a b, view_le a b → view_le b a → a = b
--   view_le_total : ∀ a b, view_le a b ∨ view_le b a
--   view_lt_def : ∀ a b, view_lt a b ↔ (view_le a b ∧ a ≠ b)

def IsHighestLock
    {Node Participant View Interaction : Type}
    (view_lt view_le : View → View → Prop)
    (cur_view : Node → View → Prop)
    (locked : Node → Participant → Interaction → Bool → View → Prop)
    (n : Node) (p : Participant) (i : Interaction) (s : Bool) (v v_cur: View) : Prop :=
  cur_view n v_cur ∧
  locked n p i s v ∧
  view_lt v v_cur ∧  -- ← Changed from view_le to view_lt: lock is strictly before v_cur
  (∀ i' s' v', (view_lt v v' ∧ view_lt v' v_cur) → ¬ locked n p i' s' v') ∧
  (s = true → ¬ locked n p i false v)

  theorem highest_lock_unique
    {Node Participant View Interaction : Type}
    (view_lt view_le : View → View → Prop)
    (view_le_total : ∀ (a b : View), view_le a b ∨ view_le b a)
    (view_le_antisymm : ∀ (a b : View), view_le a b → view_le b a → a = b)
    (view_lt_def : ∀ (a b : View), view_lt a b ↔ (view_le a b ∧ a ≠ b))
    (cur_view : Node → View → Prop)
    (locked : Node → Participant → Interaction → Bool → View → Prop)
    (n : Node) (p : Participant) (i : Interaction)
    (s1 s2 : Bool) (v1 v2 v_cur : View) :
    (IsHighestLock view_lt view_le cur_view locked n p i s1 v1 v_cur ∧
    IsHighestLock view_lt view_le cur_view locked n p i s2 v2 v_cur) →
    (v1 = v2 ∧ s1 = s2) := by
  intro ⟨h1, h2⟩
  unfold IsHighestLock at h1 h2
  obtain ⟨h1_cur, h1_locked, h1_lt_cur, h1_no_higher, h1_stage⟩ := h1
  obtain ⟨h2_cur, h2_locked, h2_lt_cur, h2_no_higher, h2_stage⟩ := h2

  constructor
  · -- Prove v1 = v2
    by_contra h_ne
    cases view_le_total v1 v2 with
    | inl h_le =>
        cases eq_or_ne v1 v2 with
        | inl h_eq => exact h_ne h_eq
        | inr h_ne' =>
            -- v1 < v2 and both v1 < v_cur and v2 < v_cur
            have h_lt : view_lt v1 v2 := by rw [view_lt_def]; exact ⟨h_le, h_ne'⟩
            -- So v1 < v2 < v_cur, which means h1_no_higher applies
            exact h1_no_higher i s2 v2 ⟨h_lt, h2_lt_cur⟩ h2_locked
    | inr h_ge =>
        cases eq_or_ne v2 v1 with
        | inl h_eq => exact h_ne h_eq.symm
        | inr h_ne' =>
            -- v2 < v1 and both v2 < v_cur and v1 < v_cur
            have h_lt : view_lt v2 v1 := by rw [view_lt_def]; exact ⟨h_ge, h_ne'⟩
            -- So v2 < v1 < v_cur, which means h2_no_higher applies
            exact h2_no_higher i s1 v1 ⟨h_lt, h1_lt_cur⟩ h1_locked

  · -- Prove s1 = s2
    -- First establish v1 = v2 (copy from above)
    have h_v_eq : v1 = v2 := by
      by_contra h_ne
      cases view_le_total v1 v2 with
      | inl h_le =>
          cases eq_or_ne v1 v2 with
          | inl h_eq => exact h_ne h_eq
          | inr h_ne' =>
              have h_lt : view_lt v1 v2 := by rw [view_lt_def]; exact ⟨h_le, h_ne'⟩
              exact h1_no_higher i s2 v2 ⟨h_lt, h2_lt_cur⟩ h2_locked
      | inr h_ge =>
          cases eq_or_ne v2 v1 with
          | inl h_eq => exact h_ne h_eq.symm
          | inr h_ne' =>
              have h_lt : view_lt v2 v1 := by rw [view_lt_def]; exact ⟨h_ge, h_ne'⟩
              exact h2_no_higher i s1 v1 ⟨h_lt, h1_lt_cur⟩ h1_locked

    -- Now prove s1 = s2 by Bool case analysis
    rw [h_v_eq] at h1_locked h1_stage
    cases s1 <;> cases s2
    · rfl  -- both false (precommit)
    · -- s1 = false (precommit), s2 = true (prevote)
      -- h2_stage: s2 = true → ¬locked n p i false v2
      have : ¬ locked n p i false v2 := h2_stage rfl
      exact absurd h1_locked this
    · -- s1 = true (prevote), s2 = false (precommit)
      have : ¬ locked n p i false v2 := h1_stage rfl
      exact absurd h2_locked this
    · rfl  -- both true (prevote)

theorem highest_lock_implies_locked
    {Node Participant View Interaction : Type}
    (view_lt view_le : View → View → Prop)
    (cur_view : Node → View → Prop)
    (locked : Node → Participant → Interaction → Bool → View → Prop)
    (n : Node) (p : Participant) (i : Interaction) (s : Bool) (v v_cur : View) :
    IsHighestLock view_lt view_le cur_view locked n p i s v v_cur →
    locked n p i s v := by
  intro h
  unfold IsHighestLock at h
  exact h.2.1

theorem precommit_lock_persists_as_highest
    {Node Participant View Interaction : Type}
    (view_lt view_le : View → View → Prop)
    (view_next : View → View → Prop)
    (view_lt_def : ∀ a b, view_lt a b ↔ (view_le a b ∧ a ≠ b))
    (view_next_implies_lt : ∀ v v2, view_next v v2 → view_lt v v2)
    (view_next_no_between : ∀ v v2 v_mid, view_next v v2 → ¬(view_lt v v_mid ∧ view_lt v_mid v2))
    (cur_view : Node → View → Prop)
    (locked : Node → Participant → Interaction → Bool → View → Prop)
    (n : Node) (p : Participant) (i : Interaction) (v1 v2 : View) :
    view_next v1 v2 →                              -- v2 is next view after v1
    cur_view n v2 →                                -- n is currently in view v2
    locked n p i false v1 →                        -- Has precommit lock at v1
    IsHighestLock view_lt view_le cur_view locked n p i false v1 v2 := by
  intro h_next h_cur h_locked_v1
  unfold IsHighestLock
  refine ⟨h_cur, h_locked_v1, view_next_implies_lt v1 v2 h_next, ?_, ?_⟩
  · -- ∀ i' s' v', (view_lt v1 v' ∧ view_lt v' v2) → ¬locked n p i' s' v'
    intro i' s' v' ⟨h_lt1, h_lt2⟩
    -- By view_next_no_between, there is no v' such that v1 < v' < v2
    have : ¬(view_lt v1 v' ∧ view_lt v' v2) := view_next_no_between v1 v2 v' h_next
    exact absurd ⟨h_lt1, h_lt2⟩ this
  · -- false = true → ¬locked n p i false v1
    intro h_false_eq_true
    cases h_false_eq_true

end IFPTheory
