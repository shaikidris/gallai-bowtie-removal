/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.OtherBowtieZeroPuncture
import Gallai.Structure.PairRepairedPuncture

/-! # Surviving whole bowties under either status of a syndrome-pair repair -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (B C : WholeBowtie G) (hd : Disjoint B.vertices C.vertices)
variable (p q : {v : V // v ∉ B.vertices}) (hne : p ≠ q)
variable (hs : B.syndrome = {p.val, q.val})

include hs in
/-- A repair toggles only an odd-odd edge, hence no edge at an original even vertex. -/
theorem pair_adj_at_even (u v : {w : V // w ∉ B.vertices})
    (hu : Even (G.degree u.val)) :
    (B.pairRepairedPuncture p q).Adj u v ↔ G.Adj u.val v.val := by
  have hp := B.odd_degree_anchor (B.syndrome_subset_anchors
    (show p.val ∈ B.syndrome by simp [hs]))
  have hq := B.odd_degree_anchor (B.syndrome_subset_anchors
    (show q.val ∈ B.syndrome by simp [hs]))
  have hup : u ≠ p := by
    intro h
    subst u
    exact Nat.not_even_iff_odd.mpr hp hu
  have huq : u ≠ q := by
    intro h
    subst u
    exact Nat.not_even_iff_odd.mpr hq hu
  rw [SimpleGraph.adj_comm, toggleEdge_adj_of_ne B.puncture p q v u hup huq,
    SimpleGraph.adj_comm]
  rfl

include hne hs in
/-- Every untouched bowtie remains a whole even component after pair repair. -/
noncomputable def otherPairBowtie : WholeBowtie (B.pairRepairedPuncture p q) := by
  let l := B.otherPunctureLabel C hd
  apply ofClosedEmbedding l
  · intro i
    exact (B.pairRepairedPuncture_even_iff p q hne hs (l i)).mpr (C.even_degree_label i)
  · intro i j
    exact (B.pair_adj_at_even p q hs (l i) (l j) (C.even_degree_label i)).trans (C.adj_iff i j)
  · intro i v ha he
    have ha' := (B.pair_adj_at_even p q hs (l i) v (C.even_degree_label i)).mp ha
    have he' := (B.pairRepairedPuncture_even_iff p q hne hs v).mp he
    have hm := mem_evenComponent_of_adj C.component (C.label_mem_component i) ha' he'
    rw [C.component_vertices] at hm
    obtain ⟨j, hj⟩ := hm
    exact ⟨j, Subtype.ext hj⟩

/-- Repaired whole components contain exactly their original labelled vertices. -/
theorem otherPair_mem_vertices (v : {w : V // w ∉ B.vertices}) :
    v ∈ (B.otherPairBowtie C hd p q hne hs).vertices ↔ v.val ∈ C.vertices := by
  rw [mem_vertices, mem_vertices,
    (B.otherPairBowtie C hd p q hne hs).component_vertices, C.component_vertices]
  constructor
  · rintro ⟨i, h⟩
    exact ⟨i, congrArg Subtype.val h⟩
  · rintro ⟨i, h⟩
    exact ⟨i, Subtype.ext h⟩

/-- All incidences at another bowtie are unchanged in either repair-edge status. -/
theorem otherPair_mem_row (i : Fin 5) (v : {w : V // w ∉ B.vertices}) :
    v ∈ (B.otherPairBowtie C hd p q hne hs).row i ↔ v.val ∈ C.row i := by
  rw [mem_row, mem_row, B.otherPair_mem_vertices C hd p q hne hs v]
  exact and_congr (B.pair_adj_at_even p q hs (B.otherPunctureLabel C hd i) v
    (C.even_degree_label i)) Iff.rfl

/-- Every row maps onto the full original row, including shared odd anchors. -/
theorem otherPair_row_map (i : Fin 5) :
    ((B.otherPairBowtie C hd p q hne hs).row i).map (Function.Embedding.subtype _) =
      C.row i := by
  ext v
  constructor
  · intro h
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp h
    exact (B.otherPair_mem_row C hd p q hne hs i w).mp hw
  · intro h
    have hv := C.anchor_not_mem_other B ((C.mem_anchors v).mpr ⟨i, h⟩)
    exact Finset.mem_map.mpr ⟨⟨v, hv⟩,
      (B.otherPair_mem_row C hd p q hne hs i ⟨v, hv⟩).mpr h, rfl⟩

/-- Pair repair preserves the entire anchor set under the survivor inclusion. -/
theorem otherPair_anchors_map :
    (B.otherPairBowtie C hd p q hne hs).anchors.map (Function.Embedding.subtype _) =
      C.anchors := by
  ext v
  simp only [Finset.mem_map, mem_anchors]
  constructor
  · rintro ⟨w, ⟨i, hw⟩, rfl⟩
    exact ⟨i, (B.otherPair_mem_row C hd p q hne hs i w).mp hw⟩
  · rintro ⟨i, hv⟩
    rw [← B.otherPair_row_map C hd p q hne hs i] at hv
    obtain ⟨w, hw, he⟩ := Finset.mem_map.mp hv
    exact ⟨w, ⟨i, hw⟩, he⟩

/-- Pair repair preserves anchor cardinality. -/
theorem otherPair_card_anchors :
    (B.otherPairBowtie C hd p q hne hs).anchors.card = C.anchors.card := by
  rw [← B.otherPair_anchors_map C hd p q hne hs, Finset.card_map]

/-- Pair repair preserves the activity count of every other bowtie. -/
theorem otherPair_activity :
    (B.otherPairBowtie C hd p q hne hs).activity = C.activity := by
  have hn (i : Fin 5) : ((B.otherPairBowtie C hd p q hne hs).row i).Nonempty ↔
      (C.row i).Nonempty := by
    rw [← B.otherPair_row_map C hd p q hne hs i, Finset.map_nonempty]
  simp only [activity, activePrivate, hn]

/-- Each retained vertex has the same syndrome membership at the other bowtie. -/
theorem otherPair_mem_syndrome (v : {w : V // w ∉ B.vertices}) :
    v ∈ (B.otherPairBowtie C hd p q hne hs).syndrome ↔ v.val ∈ C.syndrome := by
  simp only [syndrome, Finset.mem_symmDiff, B.otherPair_mem_row C hd p q hne hs]

/-- All manuscript-supported classes survive either pair-repair edge status. -/
theorem otherPair_supported (hC : Gallai.Composition.Supported C) :
    Gallai.Composition.Supported (B.otherPairBowtie C hd p q hne hs) := by
  have hempty (he : C.syndrome = ∅) :
      (B.otherPairBowtie C hd p q hne hs).syndrome = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hh := (B.otherPair_mem_syndrome C hd p q hne hs v).mp hv
    simp only [he, Finset.notMem_empty] at hh
  have hfull (he : C.syndrome = C.anchors) :
      (B.otherPairBowtie C hd p q hne hs).syndrome =
        (B.otherPairBowtie C hd p q hne hs).anchors := by
    ext v
    simp only [B.otherPair_mem_syndrome C hd p q hne hs, he, mem_anchors,
      B.otherPair_mem_row C hd p q hne hs]
  rcases hC with h | h | ⟨h, he | he⟩
  · exact Or.inl (by rwa [B.otherPair_activity C hd p q hne hs])
  · exact Or.inr (Or.inl (by rwa [B.otherPair_card_anchors C hd p q hne hs]))
  · exact Or.inr (Or.inr ⟨by rwa [B.otherPair_card_anchors C hd p q hne hs],
      Or.inl (hempty he)⟩)
  · exact Or.inr (Or.inr ⟨by rwa [B.otherPair_card_anchors C hd p q hne hs],
      Or.inr (hfull he)⟩)

end Gallai.WholeBowtie
