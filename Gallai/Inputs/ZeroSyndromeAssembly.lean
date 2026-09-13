/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.ZeroSyndromeComponents
import Gallai.Operations.ComponentBudgetAssembly

/-! # Actual whole-puncture decomposition and its exact ceiling accounting -/

namespace Gallai

/-- Twice the component ceiling sum is order plus the number of odd components. -/
theorem component_ceiling_balance {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    2 * (∑ C : H.ConnectedComponent, (Fintype.card C.supp + 1) / 2) =
      Fintype.card W + ∑ C : H.ConnectedComponent, Fintype.card C.supp % 2 := by
  classical
  have htotal : (∑ C : H.ConnectedComponent, Fintype.card C.supp) =
      Fintype.card W := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv H.connectedComponentMk)
  rw [Finset.mul_sum, ← htotal, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro C _
  omega

namespace WholeBowtie

open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Produce the actual zero-syndrome puncture decomposition, including all
components, with the precise sum of their ceiling budgets and y exposed. -/
theorem zero_puncture_endpoint_sum (hz : B.syndrome = ∅) (hc : G.Connected)
    (y : {v : V // v ∉ B.vertices}) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ D : Decomposition B.puncture,
      D.size ≤ ∑ C : B.puncture.ConnectedComponent, (Fintype.card C.supp + 1) / 2 ∧
      2 ≤ D.endpointCount y := by
  classical
  obtain ⟨D, hs, he⟩ := B.zero_puncture_component_endpoint hz hc y hy
    (B.puncture.connectedComponentMk y) rfl hcap
  apply endpoint_budget_of_components B.puncture y
    (fun C => (Fintype.card C.supp + 1) / 2) D hs he
  intro C hC
  apply B.zero_puncture_other_ceiling hz y C _ hcap
  intro hyC
  exact hC (SimpleGraph.ConnectedComponent.eq_of_common_vertex hyC rfl)

end WholeBowtie
end Gallai
