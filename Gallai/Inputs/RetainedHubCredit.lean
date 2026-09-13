/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.RetainedHubBudget
import Gallai.Inputs.ZeroSyndromeCredit
import Gallai.Structure.RetainedHubComponents

/-! # Exact retained-hub reconstruction credits at every order -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Four deleted vertices and at most two components leave two credits,
unless both components are odd, in which case one credit remains. -/
theorem retained_credit_of_component_budget (H : SimpleGraph B.StarSurvivor)
    [DecidableRel H.Adj] (D : Decomposition H)
    (hb : D.size ≤ ∑ C : H.ConnectedComponent, (Fintype.card C.supp + 1) / 2)
    (hc : Fintype.card H.ConnectedComponent ≤ 2) :
    D.size + 2 ≤ (Fintype.card V + 1) / 2 ∨
      (D.size + 1 ≤ (Fintype.card V + 1) / 2 ∧
        Fintype.card H.ConnectedComponent = 2 ∧
        (∑ C : H.ConnectedComponent, Fintype.card C.supp % 2) = 2) := by
  have hn := B.completedStar_card
  have ho := component_odd_count_le H
  have hbalance := component_ceiling_balance H
  by_cases htwo : D.size + 2 ≤ (Fintype.card V + 1) / 2
  · exact Or.inl htwo
  · exact Or.inr ⟨by omega, by omega, by omega⟩

/-- An actual pair-repaired retained auxiliary supplies the exact credit
alternative together with the designated endpoint reserve. -/
theorem retainedHubRepair_endpoint_credit (p q : B.StarSurvivor) (hne : p ≠ q)
    (hs : B.privateDeletionSyndrome = {p,q}) (hr : (B.row 0).card = 2)
    (hA : B.anchors.card ≤ 3) (hc : G.Connected)
    (y : B.StarSurvivor) (hx : y.val ≠ B.label 0) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ D : Decomposition (B.retainedHubRepair p q), 2 ≤ D.endpointCount y ∧
      (D.size + 2 ≤ (Fintype.card V + 1) / 2 ∨
        (D.size + 1 ≤ (Fintype.card V + 1) / 2 ∧
          Fintype.card (B.retainedHubRepair p q).ConnectedComponent = 2 ∧
          (∑ C : (B.retainedHubRepair p q).ConnectedComponent,
            Fintype.card C.supp % 2) = 2)) := by
  obtain ⟨D, hb, he⟩ := B.retainedHubRepair_endpoint_sum p q hne hs (by omega) hc y hx hy hcap
  exact ⟨D, he, B.retained_credit_of_component_budget _ D hb
    (B.retainedHubRepair_components_le_two p q hs hc hA (by omega))⟩

/-- Empty private syndrome supplies the same sharp credit alternative. -/
theorem retainedHub_endpoint_credit (hs : B.privateDeletionSyndrome = ∅)
    (hr : (B.row 0).card = 2) (hA : B.anchors.card ≤ 3) (hc : G.Connected)
    (y : B.StarSurvivor) (hx : y.val ≠ B.label 0) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ D : Decomposition B.retainedHubGraph, 2 ≤ D.endpointCount y ∧
      (D.size + 2 ≤ (Fintype.card V + 1) / 2 ∨
        (D.size + 1 ≤ (Fintype.card V + 1) / 2 ∧
          Fintype.card B.retainedHubGraph.ConnectedComponent = 2 ∧
          (∑ C : B.retainedHubGraph.ConnectedComponent, Fintype.card C.supp % 2) = 2)) := by
  obtain ⟨D, hb, he⟩ := B.retainedHub_endpoint_sum hs (by omega) hc y hx hy hcap
  exact ⟨D, he, B.retained_credit_of_component_budget _ D hb
    (B.retainedHub_components_le_two hc hA (by omega))⟩

end Gallai.WholeBowtie
