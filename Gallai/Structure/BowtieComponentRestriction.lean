/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ClosedBowtie
import Gallai.Structure.ComposableBowties

/-! # Restricting a whole bowtie to its ambient connected component -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (B : WholeBowtie G) (K : G.ConnectedComponent) [Fintype K.supp]

/-- Every bowtie label lies in the ambient component of its hub. -/
theorem label_mem_ambient (hx : B.label 0 ∈ K.supp) (i : Fin 5) : B.label i ∈ K.supp := by
  by_cases hi : i = 0
  · simpa only [hi] using hx
  · apply K.mem_supp_of_adj_mem_supp hx
    apply (B.adj_iff 0 i).mpr
    fin_cases i <;> first | contradiction | decide

/-- The component subtype contains all five original bowtie labels. -/
def componentLabel (hx : B.label 0 ∈ K.supp) : Fin 5 ↪ K.supp where
  toFun i := ⟨B.label i, B.label_mem_ambient K hx i⟩
  inj' := fun _ _ h => B.label.injective (congrArg Subtype.val h)

/-- Passing to an ambient component preserves ordinary degrees. -/
theorem ambient_degree (v : K.supp) : (G.induce K.supp).degree v = G.degree v.val := by
  classical
  have hclosed : G.neighborSet v.val ⊆ K.supp := fun _ hw =>
    K.mem_supp_of_adj_mem_supp v.property hw
  convert G.degree_induce_of_neighborSet_subset hclosed using 1
  congr 1
  exact Subsingleton.elim _ _

/-- A whole bowtie remains whole when restricted to its ambient component. -/
noncomputable def componentBowtie (hx : B.label 0 ∈ K.supp) :
    WholeBowtie (G.induce K.supp) := by
  let l := B.componentLabel K hx
  apply ofClosedEmbedding l
  · intro i
    rw [ambient_degree K (l i)]
    exact B.even_degree_label i
  · intro i j
    exact B.adj_iff i j
  · intro i v ha he
    rw [ambient_degree K v] at he
    have hm := mem_evenComponent_of_adj B.component (B.label_mem_component i) ha he
    rw [B.component_vertices] at hm
    obtain ⟨j, hj⟩ := hm
    exact ⟨j, Subtype.ext hj⟩

variable (hx : B.label 0 ∈ K.supp)

/-- Component restriction preserves labelled vertex membership. -/
theorem component_mem_vertices (v : K.supp) :
    v ∈ (B.componentBowtie K hx).vertices ↔ v.val ∈ B.vertices := by
  rw [mem_vertices, mem_vertices, (B.componentBowtie K hx).component_vertices,
    B.component_vertices]
  constructor
  · rintro ⟨i, h⟩
    exact ⟨i, congrArg Subtype.val h⟩
  · rintro ⟨i, h⟩
    exact ⟨i, Subtype.ext h⟩

/-- Incidence is unchanged inside the ambient component. -/
theorem component_mem_row (i : Fin 5) (v : K.supp) :
    v ∈ (B.componentBowtie K hx).row i ↔ v.val ∈ B.row i := by
  rw [mem_row, mem_row, B.component_mem_vertices K hx v]
  rfl

/-- Every original anchor belongs to the same ambient component. -/
theorem component_row_map (i : Fin 5) :
    ((B.componentBowtie K hx).row i).map (Function.Embedding.subtype _) = B.row i := by
  ext v
  constructor
  · intro h
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp h
    exact (B.component_mem_row K hx i w).mp hw
  · intro h
    have hv := K.mem_supp_of_adj_mem_supp (B.label_mem_ambient K hx i)
      ((B.mem_row i v).mp h).1
    exact Finset.mem_map.mpr ⟨⟨v, hv⟩, (B.component_mem_row K hx i ⟨v, hv⟩).mpr h, rfl⟩

/-- The full anchor set is recovered by the component inclusion. -/
theorem component_anchors_map :
    (B.componentBowtie K hx).anchors.map (Function.Embedding.subtype _) = B.anchors := by
  ext v
  simp only [Finset.mem_map, mem_anchors]
  constructor
  · rintro ⟨w, ⟨i, hw⟩, rfl⟩
    exact ⟨i, (B.component_mem_row K hx i w).mp hw⟩
  · rintro ⟨i, hv⟩
    rw [← B.component_row_map K hx i] at hv
    obtain ⟨w, hw, he⟩ := Finset.mem_map.mp hv
    exact ⟨w, ⟨i, hw⟩, he⟩

/-- Component restriction preserves the number of anchors. -/
theorem component_card_anchors : (B.componentBowtie K hx).anchors.card = B.anchors.card := by
  rw [← B.component_anchors_map K hx, Finset.card_map]

/-- Component restriction preserves activity. -/
theorem component_activity : (B.componentBowtie K hx).activity = B.activity := by
  have hn (i : Fin 5) : ((B.componentBowtie K hx).row i).Nonempty ↔ (B.row i).Nonempty := by
    rw [← B.component_row_map K hx i, Finset.map_nonempty]
  simp only [activity, activePrivate, hn]

/-- Syndrome membership is unchanged by the component inclusion. -/
theorem component_mem_syndrome (v : K.supp) :
    v ∈ (B.componentBowtie K hx).syndrome ↔ v.val ∈ B.syndrome := by
  simp only [syndrome, Finset.mem_symmDiff, B.component_mem_row K hx]

/-- Every manuscript-supported class is preserved by ambient component restriction. -/
theorem component_supported (hs : Gallai.Composition.Supported B) :
    Gallai.Composition.Supported (B.componentBowtie K hx) := by
  have hz (he : B.syndrome = ∅) : (B.componentBowtie K hx).syndrome = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hh := (B.component_mem_syndrome K hx v).mp hv
    simp only [he, Finset.notMem_empty] at hh
  have hf (he : B.syndrome = B.anchors) :
      (B.componentBowtie K hx).syndrome = (B.componentBowtie K hx).anchors := by
    ext v
    simp only [B.component_mem_syndrome K hx, he, mem_anchors, B.component_mem_row K hx]
  rcases hs with h | h | ⟨h, he | he⟩
  · exact Or.inl (by rwa [B.component_activity K hx])
  · exact Or.inr (Or.inl (by rwa [B.component_card_anchors K hx]))
  · exact Or.inr (Or.inr ⟨by rwa [B.component_card_anchors K hx], Or.inl (hz he)⟩)
  · exact Or.inr (Or.inr ⟨by rwa [B.component_card_anchors K hx], Or.inr (hf he)⟩)

end Gallai.WholeBowtie
