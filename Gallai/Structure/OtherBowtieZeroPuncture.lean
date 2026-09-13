/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ClosedBowtie
import Gallai.Structure.DistinctBowties
import Gallai.Inputs.ZeroSyndromeBudget

/-! # Whole-component preservation in a zero-syndrome puncture

No connectedness of the puncture is assumed. Componentwise induction will
subsequently restrict each preserved whole bowtie to its ambient component.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (B C : WholeBowtie G) (hd : Disjoint B.vertices C.vertices)

/-- The other bowtie's five labels survive whole deletion. -/
def otherPunctureLabel : Fin 5 ↪ {v : V // v ∉ B.vertices} where
  toFun i := ⟨C.label i, fun hv => Finset.disjoint_left.mp hd hv
    ((C.mem_vertices (C.label i)).mpr (C.label_mem_component i))⟩
  inj' := fun _ _ h => C.label.injective (congrArg Subtype.val h)

/-- Under zero syndrome, the embedded bowtie remains a whole even component. -/
noncomputable def otherZeroBowtie (hz : B.syndrome = ∅) : WholeBowtie B.puncture := by
  let l := B.otherPunctureLabel C hd
  apply ofClosedEmbedding l
  · intro i
    exact (B.zero_puncture_even_iff hz (l i)).mpr (C.even_degree_label i)
  · intro i j
    exact C.adj_iff i j
  · intro i v ha he
    have hm := mem_evenComponent_of_adj C.component (C.label_mem_component i)
      ha ((B.zero_puncture_even_iff hz v).mp he)
    rw [C.component_vertices] at hm
    obtain ⟨j, hj⟩ := hm
    exact ⟨j, Subtype.ext hj⟩

variable (hz : B.syndrome = ∅)

/-- The surviving bowtie keeps exactly its original labels. -/
theorem otherZero_mem_vertices (v : {w : V // w ∉ B.vertices}) :
    v ∈ (B.otherZeroBowtie C hd hz).vertices ↔ v.val ∈ C.vertices := by
  rw [mem_vertices, mem_vertices,
    (B.otherZeroBowtie C hd hz).component_vertices, C.component_vertices]
  constructor
  · rintro ⟨i, h⟩
    exact ⟨i, congrArg Subtype.val h⟩
  · rintro ⟨i, h⟩
    exact ⟨i, Subtype.ext h⟩

/-- Every retained boundary incidence is unchanged. -/
theorem otherZero_mem_row (i : Fin 5) (v : {w : V // w ∉ B.vertices}) :
    v ∈ (B.otherZeroBowtie C hd hz).row i ↔ v.val ∈ C.row i := by
  rw [mem_row, mem_row, B.otherZero_mem_vertices C hd hz v]
  rfl

/-- All original row vertices survive, including anchors shared with the deleted bowtie. -/
theorem otherZero_row_map (i : Fin 5) :
    ((B.otherZeroBowtie C hd hz).row i).map (Function.Embedding.subtype _) = C.row i := by
  ext v
  constructor
  · intro h
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp h
    exact (B.otherZero_mem_row C hd hz i w).mp hw
  · intro h
    have hv := C.anchor_not_mem_other B ((C.mem_anchors v).mpr ⟨i, h⟩)
    exact Finset.mem_map.mpr ⟨⟨v, hv⟩,
      (B.otherZero_mem_row C hd hz i ⟨v, hv⟩).mpr h, rfl⟩

/-- The whole anchor set survives zero-syndrome deletion. -/
theorem otherZero_anchors_map :
    (B.otherZeroBowtie C hd hz).anchors.map (Function.Embedding.subtype _) = C.anchors := by
  ext v
  simp only [Finset.mem_map, mem_anchors]
  constructor
  · rintro ⟨w, ⟨i, hw⟩, rfl⟩
    exact ⟨i, (B.otherZero_mem_row C hd hz i w).mp hw⟩
  · rintro ⟨i, hv⟩
    rw [← B.otherZero_row_map C hd hz i] at hv
    obtain ⟨w, hw, he⟩ := Finset.mem_map.mp hv
    exact ⟨w, ⟨i, hw⟩, he⟩

/-- Anchor cardinality is preserved, with no disjoint-anchor assumption. -/
theorem otherZero_card_anchors :
    (B.otherZeroBowtie C hd hz).anchors.card = C.anchors.card := by
  rw [← B.otherZero_anchors_map C hd hz, Finset.card_map]

/-- Every private row retains its activity. -/
theorem otherZero_activity : (B.otherZeroBowtie C hd hz).activity = C.activity := by
  have hn (i : Fin 5) : ((B.otherZeroBowtie C hd hz).row i).Nonempty ↔
      (C.row i).Nonempty := by
    rw [← B.otherZero_row_map C hd hz i, Finset.map_nonempty]
  simp only [activity, activePrivate, hn]

/-- Syndrome membership is preserved at every surviving vertex. -/
theorem otherZero_mem_syndrome (v : {w : V // w ∉ B.vertices}) :
    v ∈ (B.otherZeroBowtie C hd hz).syndrome ↔ v.val ∈ C.syndrome := by
  simp only [syndrome, Finset.mem_symmDiff, B.otherZero_mem_row C hd hz]

/-- All supported classes remain supported in the possibly disconnected puncture. -/
theorem otherZero_supported (hs : Gallai.Composition.Supported C) :
    Gallai.Composition.Supported (B.otherZeroBowtie C hd hz) := by
  have hempty (he : C.syndrome = ∅) : (B.otherZeroBowtie C hd hz).syndrome = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hh := (B.otherZero_mem_syndrome C hd hz v).mp hv
    simp only [he, Finset.notMem_empty] at hh
  have hfull (he : C.syndrome = C.anchors) :
      (B.otherZeroBowtie C hd hz).syndrome = (B.otherZeroBowtie C hd hz).anchors := by
    ext v
    simp only [B.otherZero_mem_syndrome C hd hz, he, mem_anchors,
      B.otherZero_mem_row C hd hz]
  rcases hs with h | h | ⟨h, he | he⟩
  · exact Or.inl (by rwa [B.otherZero_activity C hd hz])
  · exact Or.inr (Or.inl (by rwa [B.otherZero_card_anchors C hd hz]))
  · exact Or.inr (Or.inr ⟨by rwa [B.otherZero_card_anchors C hd hz], Or.inl (hempty he)⟩)
  · exact Or.inr (Or.inr ⟨by rwa [B.otherZero_card_anchors C hd hz], Or.inr (hfull he)⟩)

end Gallai.WholeBowtie
