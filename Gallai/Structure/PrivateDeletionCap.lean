/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.InactiveBowtieDeletion

/-! # E-degree bounds after inactive private deletion -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (B : WholeBowtie G) (I : Finset (Fin 5))
variable (hi : ∀ i ∈ I, B.row i = ∅)
include hi

/-- Inactive deletion cannot create an even vertex that was originally odd. -/
theorem privateFamilyDeletion_even_original (v : {w : V // w ∉ I.map B.label})
    (he : Even ((B.privateDeletion I).degree v)) : Even (G.degree v.val) := by
  by_cases hv : v.val ∈ B.vertices
  · exact even_of_mem_evenComponent B.component ((B.mem_vertices v.val).mp hv)
  · rwa [B.privateDeletion_degree_outside I hi v hv] at he

/-- Every surviving vertex has no more even neighbours than before deletion. -/
theorem privateFamilyDeletion_eDegree_le (v : {w : V // w ∉ I.map B.label}) :
    eDegree (B.privateDeletion I) v ≤ eDegree G v.val := by
  have hs : (evenNeighbors (B.privateDeletion I) v).map
      (Function.Embedding.subtype _) ⊆ evenNeighbors G v.val := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨ha, he⟩ := (mem_evenNeighbors _ _).mp hq
    exact (mem_evenNeighbors _ _).mpr ⟨ha, B.privateFamilyDeletion_even_original I hi q he⟩
  simpa only [eDegree, Finset.card_map] using Finset.card_le_card hs

/-- At a surviving bowtie vertex, all even neighbours lie in the undeleted bowtie. -/
theorem privateDeletion_eDegree_inside (v : {w : V // w ∉ I.map B.label})
    (hv : v.val ∈ B.vertices) :
    eDegree (B.privateDeletion I) v ≤ 5 - I.card := by
  have hs : (evenNeighbors (B.privateDeletion I) v).map
      (Function.Embedding.subtype _) ⊆ B.vertices \ I.map B.label := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨ha, he⟩ := (mem_evenNeighbors _ _).mp hq
    have hm := mem_evenComponent_of_adj B.component ((B.mem_vertices v.val).mp hv)
      ha (B.privateFamilyDeletion_even_original I hi q he)
    exact Finset.mem_sdiff.mpr ⟨(B.mem_vertices q.val).mpr hm, q.property⟩
  have hsub : I.map B.label ⊆ B.vertices := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
    exact (B.mem_vertices (B.label i)).mpr (B.label_mem_component i)
  have h := Finset.card_le_card hs
  simpa only [Finset.card_map, Finset.card_sdiff_of_subset hsub, B.card_vertices,
    eDegree] using h

end Gallai.WholeBowtie
