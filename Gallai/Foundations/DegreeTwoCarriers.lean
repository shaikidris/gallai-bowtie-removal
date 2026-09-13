/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Foundations.HubProfiles

/-! # Exhaustive carrier selection at a degree-two hub -/
namespace Gallai.Decomposition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A degree-two hub has one through-carrier or two distinct terminal carriers. -/
theorem degree_two_carrier_partition (D : Decomposition G) (x : V)
    (hd : G.degree x = 2) :
    (∃ i, D.throughCarriers x = {i} ∧ D.terminalCarriers x = ∅) ∨
      (∃ i j, i ≠ j ∧ D.terminalCarriers x = {i,j} ∧ D.throughCarriers x = ∅) := by
  have hb := D.degree_eq_endpoint_add_twice_through x
  by_cases he : D.endpointCount x = 0
  · have ht : (D.throughCarriers x).card = 1 := by
      rw [D.card_throughCarriers]
      omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp ht
    exact Or.inl ⟨i, hi, Finset.card_eq_zero.mp (by rw [D.card_terminalCarriers, he])⟩
  · have ht : D.throughCount x = 0 := by omega
    have hc : (D.terminalCarriers x).card = 2 := by
      rw [D.card_terminalCarriers]
      omega
    obtain ⟨i, j, hij, heq⟩ := Finset.card_eq_two.mp hc
    exact Or.inr ⟨i, j, hij, heq,
      Finset.card_eq_zero.mp (by rw [D.card_throughCarriers, ht])⟩

/-- If the degree-two hub is passing, select its unique carrier with all
conditions needed by releaseLeft/releaseRight and exclude it from all others. -/
theorem degree_two_through_carrier (D : Decomposition G) (x : V)
    (hd : G.degree x = 2) (he : D.endpointCount x = 0) :
    ∃ i : Fin D.size, x ∈ (D.path i).walk.support ∧ (D.path i).start ≠ x ∧
      x ≠ (D.path i).finish ∧
      ∀ j : Fin D.size, j ≠ i → x ∉ (D.path j).walk.support := by
  have hb := D.degree_eq_endpoint_add_twice_through x
  have ht : (D.throughCarriers x).card = 1 := by
    rw [D.card_throughCarriers]
    omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp ht
  have hterm : D.terminalCarriers x = ∅ :=
    Finset.card_eq_zero.mp (by rw [D.card_terminalCarriers, he])
  have hm : i ∈ D.throughCarriers x := by simp [hi]
  have hrun := (Finset.mem_filter.mp hm).2
  refine ⟨i, hrun.1, hrun.2.1, Ne.symm hrun.2.2, ?_⟩
  intro j hji hj
  have h := (D.mem_support_iff_terminal_or_through x j).mp hj
  exact hji (by
    simpa only [hterm, Finset.notMem_empty, hi, Finset.mem_singleton, false_or] using h)

end Gallai.Decomposition
