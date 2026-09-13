/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.BowtieComponentRestriction

/-! # Filtering bowtie families by ambient connected component -/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {t : ℕ} (Bs : Fin t → WholeBowtie G) (K : G.ConnectedComponent)
variable [Fintype K.supp]

/-- Indices of the bowties whose hubs lie in the chosen component. -/
abbrev ComponentIndex := {i : Fin t // (Bs i).label 0 ∈ K.supp}

variable [Fintype (ComponentIndex Bs K)]

/-- The literal finite family used by componentwise induction. -/
noncomputable def componentFamily :
    Fin (Fintype.card (ComponentIndex Bs K)) → WholeBowtie (G.induce K.supp) := fun j =>
  let i := (Fintype.equivFin (ComponentIndex Bs K)).symm j
  (Bs i.val).componentBowtie K i.property

/-- Filtering cannot increase the number of bowties. -/
theorem componentFamily_count : Fintype.card (ComponentIndex Bs K) ≤ t := by
  simpa only [Fintype.card_fin] using
    Fintype.card_subtype_le (fun i : Fin t => (Bs i).label 0 ∈ K.supp)

/-- Pairwise disjointness is retained by filtering and component restriction. -/
theorem componentFamily_disjoint
    (hd : ∀ i j, i ≠ j → Disjoint (Bs i).vertices (Bs j).vertices)
    (i j : Fin (Fintype.card (ComponentIndex Bs K))) (hij : i ≠ j) :
    Disjoint (componentFamily Bs K i).vertices (componentFamily Bs K j).vertices := by
  let e := (Fintype.equivFin (ComponentIndex Bs K)).symm
  have hne : (e i).val ≠ (e j).val := by
    intro h
    exact hij (e.injective (Subtype.ext h))
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact Finset.disjoint_left.mp (hd _ _ hne)
    (((Bs (e i).val).component_mem_vertices K (e i).property v).mp hv)
    (((Bs (e j).val).component_mem_vertices K (e j).property v).mp hw)

/-- Every selected bowtie retains its supported class. -/
theorem componentFamily_supported (hs : ∀ i, Supported (Bs i))
    (j : Fin (Fintype.card (ComponentIndex Bs K))) :
    Supported (componentFamily Bs K j) := by
  let i := (Fintype.equivFin (ComponentIndex Bs K)).symm j
  exact (Bs i.val).component_supported K i.property (hs i.val)

/-- A vertex of a bowtie determines the same ambient component as its hub. -/
theorem hub_mem_of_vertex (i : Fin t) (v : K.supp) (hv : v.val ∈ (Bs i).vertices) :
    (Bs i).label 0 ∈ K.supp := by
  rw [(Bs i).mem_vertices, (Bs i).component_vertices] at hv
  obtain ⟨j, hj⟩ := hv
  by_cases h0 : j = 0
  · subst j
    exact hj.symm ▸ v.property
  · apply K.mem_supp_of_adj_mem_supp v.property
    rw [← hj]
    apply ((Bs i).adj_iff j 0).mpr
    have ha : bowtieGraph.Adj 0 j := by
      fin_cases j <;> first | contradiction | decide
    exact ha.symm

/-- No bowtie meeting the component is lost by the index filter. -/
theorem componentFamily_covers (v : K.supp) (i : Fin t) (hv : v.val ∈ (Bs i).vertices) :
    ∃ j, v ∈ (componentFamily Bs K j).vertices := by
  let k : ComponentIndex Bs K := ⟨i, hub_mem_of_vertex Bs K i v hv⟩
  refine ⟨(Fintype.equivFin (ComponentIndex Bs K)) k, ?_⟩
  simp only [componentFamily, Equiv.symm_apply_apply]
  exact ((Bs i).component_mem_vertices K k.property v).mpr hv

end Gallai.Composition
