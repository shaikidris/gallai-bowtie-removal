/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.RetainedHubFamily
import Gallai.Operations.ComponentBudgetAssembly
import Gallai.Operations.ComponentSumBudget

/-! # Smaller-family component budgets for retained-hub auxiliaries -/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
variable (hd : ∀ i j, i ≠ j → Disjoint (Bs i).vertices (Bs j).vertices)
variable (H : SimpleGraph (Bs 0).StarSurvivor) [DecidableRel H.Adj]
variable (hpar : ∀ v : (Bs 0).StarSurvivor, Even (H.degree v) ↔ Even (G.degree v.val))
variable (hadj : ∀ u v : (Bs 0).StarSurvivor, Even (G.degree u.val) →
  (H.Adj u v ↔ G.Adj u.val v.val))
variable (hr : ((Bs 0).row 0).card ≤ 3)

/-- The strict smaller-family premise on components of the actual retained auxiliary. -/
def RetainedComponentIH : Prop :=
  ∀ (K : H.ConnectedComponent) (k : ℕ), k < t + 1 →
    ∀ (Cs : Fin k → WholeBowtie (H.induce K.supp)) (e : Option K.supp),
      Admissible Cs e → Conclusion (H.induce K.supp) e

/-- Component restriction discharges the strict count and admissibility requirements. -/
theorem retained_component_conclusion (d : Option (Bs 0).StarSurvivor)
    (h : Admissible (retainedFamily Bs hd H hpar hadj) d)
    (ih : RetainedComponentIH Bs H)
    (K : H.ConnectedComponent) (e : Option K.supp)
    (he : ∀ v : K.supp, v ∈ e ↔ v.val ∈ d) : Conclusion (H.induce K.supp) e := by
  classical
  have hk := componentFamily_count (retainedFamily Bs hd H hpar hadj) K
  apply ih K (Fintype.card (ComponentIndex (retainedFamily Bs hd H hpar hadj) K))
    (by omega) (componentFamily (retainedFamily Bs hd H hpar hadj) K) e
  exact component_admissible (retainedFamily Bs hd H hpar hadj) K d e h he

include hd hpar hadj hr in
/-- A designated retained vertex is exposed on the actual ceiling-sum witness. -/
theorem retained_induction_endpoint_sum (y : (Bs 0).StarSurvivor)
    (h : Admissible Bs (some y.val)) (ih : RetainedComponentIH Bs H) :
    ∃ D : Decomposition H,
      D.size ≤ ∑ K : H.ConnectedComponent, (Fintype.card K.supp + 1) / 2 ∧
        2 ≤ D.endpointCount y := by
  classical
  have hp := retainedFamily_admissible_some Bs hd H hpar hadj hr y h
  let K₀ := H.connectedComponentMk y
  have hc : Conclusion (H.induce K₀.supp) (some ⟨y, rfl⟩) := by
    apply retained_component_conclusion Bs hd H hpar hadj (some y) hp ih
      K₀ (some ⟨y, rfl⟩)
    intro v
    simp only [Option.mem_def, Option.some.injEq, Subtype.ext_iff]
  obtain ⟨D, hD, hy⟩ := (conclusion_some (G := H.induce K₀.supp) ⟨y, rfl⟩).mp hc
  apply endpoint_budget_of_components H y (fun K => (Fintype.card K.supp + 1) / 2) D hD hy
  intro K hK
  have ha : Conclusion (H.induce K.supp) none := by
    apply retained_component_conclusion Bs hd H hpar hadj (some y) hp ih K none
    intro v
    have hne : y ≠ v.val := by
      intro heq
      have hym : y ∈ K.supp := heq ▸ v.property
      exact hK hym.symm
    simp [hne]
  exact conclusion_none.mp ha

include hd hpar hadj hr in
/-- Undesignated induction supplies the same sum, including isolated components. -/
theorem retained_induction_sum (h : Admissible Bs none) (ih : RetainedComponentIH Bs H) :
    HasPathBudget H (∑ K : H.ConnectedComponent, (Fintype.card K.supp + 1) / 2) := by
  classical
  apply budget_sum_of_components
  intro K
  have hc := retained_component_conclusion Bs hd H hpar hadj none
    (retainedFamily_admissible_none Bs hd H hpar hadj hr h) ih K none (by simp)
  exact conclusion_none.mp hc

end Gallai.Composition
