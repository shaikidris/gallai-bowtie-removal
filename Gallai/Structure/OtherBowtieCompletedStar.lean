/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.OtherBowtiePrivateDeletion
import Gallai.Structure.CompletedStarAuxiliary

/-! # Other whole bowties survive parity-correct star completion -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (B C : WholeBowtie G) (hd : Disjoint B.vertices C.vertices)

/-- Star completion changes no adjacency at another bowtie's labelled vertices. -/
theorem otherCompleted_adj (i : Fin 5) (v : B.StarSurvivor) :
    B.completedStar.Adj (B.otherPrivateLabel C hd (Finset.univ.erase 0) i) v ↔
      G.Adj (C.label i) v.val := by
  have hC := (C.mem_vertices (C.label i)).mpr (C.label_mem_component i)
  have hx : C.label i ≠ B.label 0 := by
    intro he
    exact Finset.disjoint_left.mp hd
      (he ▸ (B.mem_vertices (B.label 0)).mpr (B.label_mem_component 0)) hC
  have hA : C.label i ∉ B.anchors := fun h => B.anchor_not_mem_other C h hC
  change (G.Adj (C.label i) v.val ∨
    ((C.label i = B.label 0 ∧ v.val ∈ B.anchors) ∨
      (v.val = B.label 0 ∧ C.label i ∈ B.anchors))) ↔ _
  simp only [hx, hA, false_and, and_false, or_false]

/-- An entire other even component survives when star completion restores parity. -/
noncomputable def otherCompletedBowtie (hcard : Even B.anchors.card)
    (hcols : ∀ w ∈ B.anchors, Odd (G.neighborFinset w ∩ B.vertices).card) :
    WholeBowtie B.completedStar := by
  let l := B.otherPrivateLabel C hd (Finset.univ.erase 0)
  apply ofClosedEmbedding l
  · intro i
    exact (B.completedStar_even_iff hcard hcols (l i)).mpr (C.even_degree_label i)
  · intro i j
    exact (B.otherCompleted_adj C hd i (l j)).trans (C.adj_iff i j)
  · intro i v ha he
    have hm := mem_evenComponent_of_adj C.component (C.label_mem_component i)
      ((B.otherCompleted_adj C hd i v).mp ha)
      ((B.completedStar_even_iff hcard hcols v).mp he)
    rw [C.component_vertices] at hm
    obtain ⟨j, hj⟩ := hm
    exact ⟨j, Subtype.ext hj⟩

variable (hcard : Even B.anchors.card)
variable (hcols : ∀ w ∈ B.anchors, Odd (G.neighborFinset w ∩ B.vertices).card)

/-- Completed repair retains exactly the labels of the other whole bowtie. -/
theorem otherCompleted_mem_vertices (v : B.StarSurvivor) :
    v ∈ (B.otherCompletedBowtie C hd hcard hcols).vertices ↔ v.val ∈ C.vertices := by
  simp only [vertices, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, h⟩
    exact ⟨i, congrArg Subtype.val h⟩
  · rintro ⟨i, h⟩
    exact ⟨i, Subtype.ext h⟩

/-- External incidence at the other bowtie is unchanged by star completion. -/
theorem otherCompleted_mem_row (i : Fin 5) (v : B.StarSurvivor) :
    v ∈ (B.otherCompletedBowtie C hd hcard hcols).row i ↔ v.val ∈ C.row i := by
  rw [mem_row, mem_row, B.otherCompleted_mem_vertices C hd hcard hcols v]
  exact and_congr (B.otherCompleted_adj C hd i v) Iff.rfl

/-- Every original row survives and is recovered by forgetting the subtype. -/
theorem otherCompleted_row_map (i : Fin 5) :
    ((B.otherCompletedBowtie C hd hcard hcols).row i).map
      (Function.Embedding.subtype _) = C.row i := by
  ext v
  constructor
  · intro h
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp h
    exact (B.otherCompleted_mem_row C hd hcard hcols i w).mp hw
  · intro h
    have hout : v ∉ (Finset.univ.erase 0).map B.label := by
      intro hm
      obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hm
      have hb : v ∈ B.vertices := hj ▸
        (B.mem_vertices (B.label j)).mpr (B.label_mem_component j)
      exact C.anchor_not_mem_other B ((C.mem_anchors v).mpr ⟨i, h⟩) hb
    exact Finset.mem_map.mpr ⟨⟨v, hout⟩,
      (B.otherCompleted_mem_row C hd hcard hcols i ⟨v, hout⟩).mpr h, rfl⟩

/-- The complete anchor set, not just its cardinality, is preserved. -/
theorem otherCompleted_anchors_map :
    (B.otherCompletedBowtie C hd hcard hcols).anchors.map
      (Function.Embedding.subtype _) = C.anchors := by
  ext v
  simp only [Finset.mem_map, mem_anchors]
  constructor
  · rintro ⟨w, ⟨i, hw⟩, rfl⟩
    exact ⟨i, (B.otherCompleted_mem_row C hd hcard hcols i w).mp hw⟩
  · rintro ⟨i, hv⟩
    rw [← B.otherCompleted_row_map C hd hcard hcols i] at hv
    obtain ⟨w, hw, he⟩ := Finset.mem_map.mp hv
    exact ⟨w, ⟨i, hw⟩, he⟩

/-- Anchor cardinality is unchanged. -/
theorem otherCompleted_card_anchors :
    (B.otherCompletedBowtie C hd hcard hcols).anchors.card = C.anchors.card := by
  rw [← B.otherCompleted_anchors_map C hd hcard hcols, Finset.card_map]

/-- Private activity is unchanged. -/
theorem otherCompleted_activity :
    (B.otherCompletedBowtie C hd hcard hcols).activity = C.activity := by
  have hn (i : Fin 5) :
      ((B.otherCompletedBowtie C hd hcard hcols).row i).Nonempty ↔
        (C.row i).Nonempty := by
    rw [← B.otherCompleted_row_map C hd hcard hcols i, Finset.map_nonempty]
  simp only [activity, activePrivate, hn]

/-- Syndrome membership is transported exactly. -/
theorem otherCompleted_mem_syndrome (v : B.StarSurvivor) :
    v ∈ (B.otherCompletedBowtie C hd hcard hcols).syndrome ↔ v.val ∈ C.syndrome := by
  simp only [syndrome, Finset.mem_symmDiff, B.otherCompleted_mem_row C hd hcard hcols]

/-- Every supported class of another bowtie survives parity-correct completion. -/
theorem otherCompleted_supported (hs : Gallai.Composition.Supported C) :
    Gallai.Composition.Supported (B.otherCompletedBowtie C hd hcard hcols) := by
  have hz (he : C.syndrome = ∅) :
      (B.otherCompletedBowtie C hd hcard hcols).syndrome = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hh := (B.otherCompleted_mem_syndrome C hd hcard hcols v).mp hv
    simp only [he, Finset.notMem_empty] at hh
  have hf (he : C.syndrome = C.anchors) :
      (B.otherCompletedBowtie C hd hcard hcols).syndrome =
        (B.otherCompletedBowtie C hd hcard hcols).anchors := by
    ext v
    simp only [B.otherCompleted_mem_syndrome C hd hcard hcols, he, mem_anchors,
      B.otherCompleted_mem_row C hd hcard hcols]
  rcases hs with h | h | ⟨h, he | he⟩
  · exact Or.inl (by rwa [B.otherCompleted_activity C hd hcard hcols])
  · exact Or.inr (Or.inl (by rwa [B.otherCompleted_card_anchors C hd hcard hcols]))
  · exact Or.inr (Or.inr ⟨by rwa [B.otherCompleted_card_anchors C hd hcard hcols],
      Or.inl (hz he)⟩)
  · exact Or.inr (Or.inr ⟨by rwa [B.otherCompleted_card_anchors C hd hcard hcols],
      Or.inr (hf he)⟩)

end Gallai.WholeBowtie
