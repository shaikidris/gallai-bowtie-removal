/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.CompositionBase
import Gallai.Structure.BowtieEvenDegree

/-! # A single undesignated bowtie is a one-exception instance -/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- No slot construction is needed when only one undesignated bowtie remains. -/
theorem single_undesignated (Bs : Fin 1 → WholeBowtie G)
    (hc : G.Connected) (h : Admissible Bs none) : Conclusion G none := by
  have hcap : ∀ v, Even (G.degree v) → v ≠ (Bs 0).label 0 → eDegree G v ≤ 3 := by
    intro v hv hne
    by_cases hm : v ∈ (Bs 0).vertices
    · rw [(Bs 0).mem_vertices, (Bs 0).component_vertices] at hm
      obtain ⟨i, rfl⟩ := hm
      have hi : i ≠ 0 := fun he => hne (congrArg (Bs 0).label he)
      rw [(Bs 0).eDegree_label, if_neg hi]
      omega
    · apply h.2.2.2 v hv
      · intro i
        have hi : i = 0 := Subsingleton.elim _ _
        simpa only [hi] using hm
      · simp
  have he := (Bs 0).even_degree_label 0
  have hp : 0 < G.degree ((Bs 0).label 0) := by
    have hl := eDegree_le_degree (G := G) ((Bs 0).label 0)
    rw [(Bs 0).eDegree_label, if_pos rfl] at hl
    omega
  obtain ⟨D, hD, _⟩ := one_exception_endpoint G ((Bs 0).label 0) hc hp he hcap
  exact ⟨D, hD, by simp⟩

end Gallai.Composition
