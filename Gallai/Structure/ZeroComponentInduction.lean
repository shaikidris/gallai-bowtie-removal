/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ZeroPunctureFamily
import Gallai.Operations.ComponentBudgetAssembly
import Gallai.Operations.ComponentSumBudget

/-! # Smaller-family induction on components of a zero puncture

The induction premise is explicit. This module discharges its family-count
and admissibility obligations and assembles the actual component ceiling sum.
-/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
variable (hd : ∀ i j, i ≠ j → Disjoint (Bs i).vertices (Bs j).vertices)
variable (hz : (Bs 0).syndrome = ∅)

/-- The local form of the strong-induction premise used by zero deletion. -/
def ZeroComponentIH : Prop :=
  ∀ (K : (Bs 0).puncture.ConnectedComponent) (k : ℕ), k < t + 1 →
    ∀ (Cs : Fin k → WholeBowtie ((Bs 0).puncture.induce K.supp)) (e : Option K.supp),
      Admissible Cs e → Conclusion ((Bs 0).puncture.induce K.supp) e

/-- Every component has a strictly smaller family and inherits its requested conclusion. -/
theorem zero_component_conclusion (d : Option {v : V // v ∉ (Bs 0).vertices})
    (h : Admissible (zeroFamily Bs hd hz) d) (ih : ZeroComponentIH Bs)
    (K : (Bs 0).puncture.ConnectedComponent) (e : Option K.supp)
    (he : ∀ v : K.supp, v ∈ e ↔ v.val ∈ d) :
    Conclusion ((Bs 0).puncture.induce K.supp) e := by
  classical
  have hk := componentFamily_count (zeroFamily Bs hd hz) K
  apply ih K (Fintype.card (ComponentIndex (zeroFamily Bs hd hz) K)) (by omega)
    (componentFamily (zeroFamily Bs hd hz) K) e
  exact component_admissible (zeroFamily Bs hd hz) K d e h he

include hd hz in
/-- Designated component induction gives the ceiling sum on one common witness. -/
theorem zero_induction_endpoint_sum (y : {v : V // v ∉ (Bs 0).vertices})
    (h : Admissible Bs (some y.val)) (ih : ZeroComponentIH Bs) :
    ∃ D : Decomposition (Bs 0).puncture,
      D.size ≤ ∑ K : (Bs 0).puncture.ConnectedComponent,
        (Fintype.card K.supp + 1) / 2 ∧ 2 ≤ D.endpointCount y := by
  classical
  have hp := zeroFamily_admissible_some Bs hd hz y h
  let K₀ := (Bs 0).puncture.connectedComponentMk y
  have hc : Conclusion ((Bs 0).puncture.induce K₀.supp) (some ⟨y, rfl⟩) := by
    apply zero_component_conclusion Bs hd hz (some y) hp ih K₀ (some ⟨y, rfl⟩)
    intro v
    simp only [Option.mem_def, Option.some.injEq, Subtype.ext_iff]
  obtain ⟨D, hD, hy⟩ :=
    (conclusion_some (G := (Bs 0).puncture.induce K₀.supp) ⟨y, rfl⟩).mp hc
  apply endpoint_budget_of_components (Bs 0).puncture y
    (fun K => (Fintype.card K.supp + 1) / 2) D hD hy
  intro K hK
  have ha : Conclusion ((Bs 0).puncture.induce K.supp) none := by
    apply zero_component_conclusion Bs hd hz (some y) hp ih K none
    intro v
    have hne : y ≠ v.val := by
      intro heq
      have hym : y ∈ K.supp := heq ▸ v.property
      exact hK hym.symm
    simp [hne]
  exact (conclusion_none).mp ha

include hd hz in
/-- Undesignated induction assembles the same component ceiling sum. -/
theorem zero_induction_sum (h : Admissible Bs none) (ih : ZeroComponentIH Bs) :
    HasPathBudget (Bs 0).puncture
      (∑ K : (Bs 0).puncture.ConnectedComponent, (Fintype.card K.supp + 1) / 2) := by
  classical
  apply budget_sum_of_components
  intro K
  have hc := zero_component_conclusion Bs hd hz none
    (zeroFamily_admissible_none Bs hd hz h) ih K none (by simp)
  exact conclusion_none.mp hc

end Gallai.Composition
