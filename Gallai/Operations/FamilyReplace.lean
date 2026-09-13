/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators

/-! # Simultaneous replacement of injectively indexed carriers

The scalar accounting lemma is used for edge counts and endpoint contributions.
-/

namespace Gallai

variable {α : Type*} {n k : ℕ}

/-- Replace distinct slots, retaining all other entries. -/
noncomputable def replaceFamily (F : Fin n → α) (j : Fin k ↪ Fin n)
    (R : Fin k → α) (i : Fin n) : α := by
  classical
  exact if h : ∃ l, j l = i then R h.choose else F i

/-- A selected slot receives its prescribed replacement. -/
theorem replaceFamily_selected (F : Fin n → α) (j : Fin k ↪ Fin n)
    (R : Fin k → α) (l : Fin k) : replaceFamily F j R (j l) = R l := by
  classical
  unfold replaceFamily
  have h : ∃ r, j r = j l := ⟨l, rfl⟩
  rw [dif_pos h]
  exact congrArg R (j.injective h.choose_spec)

/-- An unselected slot retains its old entry. -/
theorem replaceFamily_unselected (F : Fin n → α) (j : Fin k ↪ Fin n)
    (R : Fin k → α) (i : Fin n) (hi : ¬ ∃ l, j l = i) :
    replaceFamily F j R i = F i := by
  classical
  exact dif_neg hi

/-- Simultaneous local increments add exactly once to the total measure. -/
theorem sum_replaceFamily (F : Fin n → α) (j : Fin k ↪ Fin n)
    (R : Fin k → α) (measure : α → ℕ) (delta : Fin k → ℕ)
    (h : ∀ l, measure (R l) = measure (F (j l)) + delta l) :
    (∑ i, measure (replaceFamily F j R i)) = (∑ i, measure (F i)) + ∑ l, delta l := by
  classical
  have hpoint (i : Fin n) : measure (replaceFamily F j R i) =
      measure (F i) + ∑ l, if j l = i then delta l else 0 := by
    by_cases hi : ∃ l, j l = i
    · obtain ⟨l, rfl⟩ := hi
      rw [replaceFamily_selected, h l]
      simp only [j.injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · rw [replaceFamily_unselected F j R i hi]
      have hz : ∀ l, j l ≠ i := fun l he => hi ⟨l, he⟩
      simp [hz]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp

end Gallai
