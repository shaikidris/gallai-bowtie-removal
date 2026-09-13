/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ComponentBowtieFamily
import Gallai.Structure.EvenSubgraphInduce

/-! # Componentwise admissibility for bowtie induction

Only the component containing the designated vertex retains its designation.
No connectivity or single-exception assumption is imposed on the ambient graph.
-/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {t : ℕ} (Bs : Fin t → WholeBowtie G) (K : G.ConnectedComponent)
variable [componentFinite : Fintype K.supp] [Fintype (ComponentIndex Bs K)]

/-- Component restriction preserves admissibility with exactly the retained designation. -/
theorem component_admissible (d : Option V) (e : Option K.supp)
    (h : Admissible Bs d) (he : ∀ v : K.supp, v ∈ e ↔ v.val ∈ d) :
    Admissible (componentFamily Bs K) e := by
  classical
  refine ⟨componentFamily_disjoint Bs K h.1,
    componentFamily_supported Bs K h.2.1, ?_, ?_⟩
  · intro v hv
    obtain ⟨hev, hpv, hout⟩ := h.2.2.1 v.val ((he v).mp hv)
    refine ⟨?_, ?_, ?_⟩
    · rwa [WholeBowtie.ambient_degree K v]
    · rwa [WholeBowtie.ambient_degree K v]
    · intro j hj
      let i := (Fintype.equivFin (ComponentIndex Bs K)).symm j
      exact hout i.val (((Bs i.val).component_mem_vertices K i.property v).mp hj)
  · intro v hv hout hne
    have hold : ∀ i, v.val ∉ (Bs i).vertices := by
      intro i hi
      obtain ⟨j, hj⟩ := componentFamily_covers Bs K v i hi
      exact hout j hj
    have hne' : ∀ y ∈ d, v.val ≠ y := by
      intro y hy hval
      have hvd : v.val ∈ d := hval ▸ hy
      exact hne v ((he v).mpr hvd) rfl
    have hcap := h.2.2.2 v.val ((WholeBowtie.ambient_degree K v) ▸ hv) hold hne'
    have hclosed : ∀ w ∈ K.supp, G.neighborSet w ⊆ K.supp :=
      fun _ hw _ ha => K.mem_supp_of_adj_mem_supp hw ha
    have heq : eDegree (G.induce K.supp) v = eDegree G v.val := by
      have hi : componentFinite = Subtype.fintype (· ∈ K.supp) := Subsingleton.elim _ _
      cases hi
      exact eDegree_induce_of_closed G K.supp hclosed v
    rwa [heq]

/-- An undesignated ambient family gives an undesignated family in every component. -/
theorem component_admissible_none (h : Admissible Bs none) :
    Admissible (componentFamily Bs K) none :=
  component_admissible Bs K none none h (by simp)

/-- The component containing the designated vertex keeps its endpoint obligation. -/
theorem component_admissible_some (y : V) (hy : y ∈ K.supp)
    (h : Admissible Bs (some y)) :
    Admissible (componentFamily Bs K) (some ⟨y, hy⟩) := by
  apply component_admissible Bs K (some y) (some ⟨y, hy⟩) h
  intro v
  simp only [Option.mem_def, Option.some.injEq, Subtype.ext_iff]

/-- Components not containing the designated vertex need no endpoint obligation. -/
theorem component_admissible_away (y : V) (hy : y ∉ K.supp)
    (h : Admissible Bs (some y)) :
    Admissible (componentFamily Bs K) none := by
  apply component_admissible Bs K (some y) none h
  intro v
  have hne : y ≠ v.val := fun heq => hy (heq ▸ v.property)
  simp [hne]

end Gallai.Composition
