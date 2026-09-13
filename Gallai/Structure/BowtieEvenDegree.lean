/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.Bowtie

/-! # Exact E-degrees in a whole bowtie -/

namespace Gallai.WholeBowtie

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Whole-component closure makes every even neighbour internal. -/
theorem evenNeighbors_label (i : Fin 5) :
    evenNeighbors G (B.label i) = (bowtieGraph.neighborFinset i).map B.label := by
  rw [← B.internal_neighbors i]
  ext v
  rw [mem_evenNeighbors, Finset.mem_inter, G.mem_neighborFinset]
  constructor
  · rintro ⟨ha, he⟩
    exact ⟨ha, (B.mem_vertices v).mpr
      (mem_evenComponent_of_adj B.component (B.label_mem_component i) ha he)⟩
  · rintro ⟨ha, hv⟩
    exact ⟨ha, even_of_mem_evenComponent B.component ((B.mem_vertices v).mp hv)⟩

/-- The hub has E-degree four and each private vertex has E-degree two,
independently of the number of odd anchors. -/
theorem eDegree_label (i : Fin 5) : eDegree G (B.label i) = if i = 0 then 4 else 2 := by
  simp only [eDegree, B.evenNeighbors_label, Finset.card_map,
    SimpleGraph.card_neighborFinset_eq_degree, bowtieGraph_degree]

end Gallai.WholeBowtie
