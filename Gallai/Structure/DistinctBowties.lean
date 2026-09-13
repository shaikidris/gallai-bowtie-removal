/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ComposableBowties

/-! # Separation of whole bowties before a local reduction

Disjointness concerns the even components, not their odd anchor sets.
These facts ensure that deleting vertices of one bowtie removes no incident
edge of another. They do not yet establish parity of surviving anchors.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- Distinct whole even components have no original edge between their vertices. -/
theorem not_adj_of_disjoint (B C : WholeBowtie G)
    (hd : Disjoint B.vertices C.vertices) {v w : V}
    (hv : v ∈ B.vertices) (hw : w ∈ C.vertices) : ¬ G.Adj v w := by
  intro ha
  have he := even_of_mem_evenComponent C.component ((C.mem_vertices w).mp hw)
  have hb := mem_evenComponent_of_adj B.component ((B.mem_vertices v).mp hv) ha he
  exact Finset.disjoint_left.mp hd ((B.mem_vertices w).mpr hb) hw

/-- Every neighbour of another bowtie survives deletion inside the selected one. -/
theorem neighbor_not_mem_deleted (B C : WholeBowtie G)
    (hd : Disjoint B.vertices C.vertices) (D : Finset V) (hD : D ⊆ B.vertices)
    {v w : V} (hv : v ∈ C.vertices) (ha : G.Adj v w) : w ∉ D := by
  intro hw
  exact B.not_adj_of_disjoint C hd (hD hw) hv ha.symm

/-- An odd external anchor cannot be a vertex of any whole even bowtie. -/
theorem anchor_not_mem_other (B C : WholeBowtie G) {w : V}
    (hw : w ∈ B.anchors) : w ∉ C.vertices := by
  intro hc
  have ho := B.odd_degree_anchor hw
  have he := even_of_mem_evenComponent C.component ((C.mem_vertices w).mp hc)
  exact (Nat.not_even_iff_odd.mpr ho) he

/-- Deletion anywhere inside one whole bowtie preserves every other bowtie degree. -/
theorem degree_delete_other (B C : WholeBowtie G)
    (hd : Disjoint B.vertices C.vertices) (D : Finset V) (hD : D ⊆ B.vertices)
    (v : {w : V // w ∉ D}) (hv : v.val ∈ C.vertices) :
    (G.induce {w : V | w ∉ D}).degree v = G.degree v.val := by
  apply G.degree_induce_of_neighborSet_subset
  intro w hw
  exact B.neighbor_not_mem_deleted C hd D hD hv hw

end Gallai.WholeBowtie
