/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.PairPunctureFamily
import Gallai.Operations.ComponentBudgetAssembly
import Gallai.Operations.ComponentSumBudget

/-! # Smaller-family induction for syndrome-pair repaired components

This supplies an actual ceiling-sum decomposition, preserving a designated
endpoint reserve on that same witness. It does not presume a global budget
for a graph that still contains other exceptional bowties.
-/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
variable (hd : ∀ i j, i ≠ j → Disjoint (Bs i).vertices (Bs j).vertices)
variable (p q : {v : V // v ∉ (Bs 0).vertices}) (hpq : p ≠ q)
variable (hs : (Bs 0).syndrome = {p.val, q.val})

/-- The componentwise smaller-family premise for this particular repaired graph. -/
def PairComponentIH : Prop :=
  ∀ (K : ((Bs 0).pairRepairedPuncture p q).ConnectedComponent) (k : ℕ), k < t + 1 →
    ∀ (Cs : Fin k → WholeBowtie (((Bs 0).pairRepairedPuncture p q).induce K.supp))
      (e : Option K.supp),
      Admissible Cs e → Conclusion (((Bs 0).pairRepairedPuncture p q).induce K.supp) e

/-- Restriction to any repaired component has strictly fewer bowties. -/
theorem pair_component_conclusion (d : Option {v : V // v ∉ (Bs 0).vertices})
    (h : Admissible (pairFamily Bs hd p q hpq hs) d) (ih : PairComponentIH Bs p q)
    (K : ((Bs 0).pairRepairedPuncture p q).ConnectedComponent) (e : Option K.supp)
    (he : ∀ v : K.supp, v ∈ e ↔ v.val ∈ d) :
    Conclusion (((Bs 0).pairRepairedPuncture p q).induce K.supp) e := by
  classical
  have hk := componentFamily_count (pairFamily Bs hd p q hpq hs) K
  apply ih K (Fintype.card (ComponentIndex (pairFamily Bs hd p q hpq hs) K)) (by omega)
    (componentFamily (pairFamily Bs hd p q hpq hs) K) e
  exact component_admissible (pairFamily Bs hd p q hpq hs) K d e h he

include hd hpq hs in
/-- The designated induction hypotheses give one witness with the full ceiling sum. -/
theorem pair_induction_endpoint_sum (y : {v : V // v ∉ (Bs 0).vertices})
    (h : Admissible Bs (some y.val)) (ih : PairComponentIH Bs p q) :
    ∃ D : Decomposition ((Bs 0).pairRepairedPuncture p q),
      D.size ≤ ∑ K : ((Bs 0).pairRepairedPuncture p q).ConnectedComponent,
        (Fintype.card K.supp + 1) / 2 ∧ 2 ≤ D.endpointCount y := by
  classical
  have hp := pairFamily_admissible_some Bs hd p q hpq hs y h
  let K₀ := ((Bs 0).pairRepairedPuncture p q).connectedComponentMk y
  have hc : Conclusion (((Bs 0).pairRepairedPuncture p q).induce K₀.supp)
      (some ⟨y, rfl⟩) := by
    apply pair_component_conclusion Bs hd p q hpq hs (some y) hp ih K₀ (some ⟨y, rfl⟩)
    intro v
    simp only [Option.mem_def, Option.some.injEq, Subtype.ext_iff]
  obtain ⟨D, hD, hy⟩ :=
    (conclusion_some (G := ((Bs 0).pairRepairedPuncture p q).induce K₀.supp)
      ⟨y, rfl⟩).mp hc
  apply endpoint_budget_of_components ((Bs 0).pairRepairedPuncture p q) y
    (fun K => (Fintype.card K.supp + 1) / 2) D hD hy
  intro K hK
  have ha : Conclusion (((Bs 0).pairRepairedPuncture p q).induce K.supp) none := by
    apply pair_component_conclusion Bs hd p q hpq hs (some y) hp ih K none
    intro v
    have hne : y ≠ v.val := by
      intro heq
      have hym : y ∈ K.supp := heq ▸ v.property
      exact hK hym.symm
    simp [hne]
  exact conclusion_none.mp ha

include hd hpq hs in
/-- The undesignated component hypotheses supply the same exact ceiling budget. -/
theorem pair_induction_sum (h : Admissible Bs none) (ih : PairComponentIH Bs p q) :
    HasPathBudget ((Bs 0).pairRepairedPuncture p q)
      (∑ K : ((Bs 0).pairRepairedPuncture p q).ConnectedComponent,
        (Fintype.card K.supp + 1) / 2) := by
  classical
  apply budget_sum_of_components
  intro K
  have hc := pair_component_conclusion Bs hd p q hpq hs none
    (pairFamily_admissible_none Bs hd p q hpq hs h) ih K none (by simp)
  exact conclusion_none.mp hc

end Gallai.Composition
