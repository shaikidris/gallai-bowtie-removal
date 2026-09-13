/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ClosedBowtie
import Gallai.Structure.DistinctBowties
import Gallai.Structure.InactiveBowtieDeletion

/-! # Other whole bowties survive an inactive private deletion -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Labels of a disjoint bowtie remain outside every selected deletion set. -/
def otherPrivateLabel (B C : WholeBowtie G) (hd : Disjoint B.vertices C.vertices)
    (I : Finset (Fin 5)) : Fin 5 ↪ {v : V // v ∉ I.map B.label} where
  toFun i := ⟨C.label i, by
    intro hm
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hm
    have hb : C.label i ∈ B.vertices := hj ▸
      (B.mem_vertices (B.label j)).mpr (B.label_mem_component j)
    exact Finset.disjoint_left.mp hd hb
      ((C.mem_vertices (C.label i)).mpr (C.label_mem_component i))⟩
  inj' := fun _ _ h => C.label.injective (congrArg Subtype.val h)

/-- Inactive deletion preserves the other whole even component, not only its shape. -/
noncomputable def otherPrivateBowtie (B C : WholeBowtie G)
    (hd : Disjoint B.vertices C.vertices) (I : Finset (Fin 5))
    (hi : ∀ i ∈ I, B.row i = ∅) : WholeBowtie (B.privateDeletion I) := by
  let l := B.otherPrivateLabel C hd I
  have hout (i : Fin 5) : C.label i ∉ B.vertices := by
    intro hb
    exact Finset.disjoint_left.mp hd hb
      ((C.mem_vertices (C.label i)).mpr (C.label_mem_component i))
  apply ofClosedEmbedding l
  · intro i
    rw [B.privateDeletion_degree_outside I hi (l i) (hout i)]
    exact C.even_degree_label i
  · intro i j
    exact C.adj_iff i j
  · intro i v hav hev
    have havG : G.Adj (C.label i) v.val := hav
    have hvout : v.val ∉ B.vertices := by
      intro hb
      exact B.not_adj_of_disjoint C hd hb
        ((C.mem_vertices (C.label i)).mpr (C.label_mem_component i)) havG.symm
    have heG : Even (G.degree v.val) := by
      rwa [B.privateDeletion_degree_outside I hi v hvout] at hev
    have hm := mem_evenComponent_of_adj C.component
      (C.label_mem_component i) havG heG
    rw [C.component_vertices] at hm
    obtain ⟨j, hj⟩ := hm
    exact ⟨j, Subtype.ext hj⟩

section Boundary
variable (B C : WholeBowtie G) (hd : Disjoint B.vertices C.vertices)
variable (I : Finset (Fin 5)) (hi : ∀ i ∈ I, B.row i = ∅)

/-- The preserved component has exactly the original five labels. -/
theorem otherPrivate_mem_vertices (v : {w : V // w ∉ I.map B.label}) :
    v ∈ (B.otherPrivateBowtie C hd I hi).vertices ↔ v.val ∈ C.vertices := by
  simp only [vertices, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, h⟩
    exact ⟨i, congrArg Subtype.val h⟩
  · rintro ⟨i, h⟩
    exact ⟨i, Subtype.ext h⟩

/-- Boundary incidence is unchanged at every surviving vertex. -/
theorem otherPrivate_mem_row (i : Fin 5) (v : {w : V // w ∉ I.map B.label}) :
    v ∈ (B.otherPrivateBowtie C hd I hi).row i ↔ v.val ∈ C.row i := by
  rw [mem_row, mem_row, B.otherPrivate_mem_vertices C hd I hi v]
  rfl

/-- Forgetting the deletion subtype recovers the entire original row. -/
theorem otherPrivate_row_map (i : Fin 5) :
    ((B.otherPrivateBowtie C hd I hi).row i).map (Function.Embedding.subtype _) =
      C.row i := by
  ext v
  constructor
  · intro h
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp h
    exact (B.otherPrivate_mem_row C hd I hi i w).mp hw
  · intro h
    have hout : v ∉ I.map B.label := by
      intro hm
      obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hm
      have hb : v ∈ B.vertices := hj ▸
        (B.mem_vertices (B.label j)).mpr (B.label_mem_component j)
      exact C.anchor_not_mem_other B ((C.mem_anchors v).mpr ⟨i, h⟩) hb
    exact Finset.mem_map.mpr ⟨⟨v, hout⟩,
      (B.otherPrivate_mem_row C hd I hi i ⟨v, hout⟩).mpr h, rfl⟩
/-- All external anchors survive, including anchors shared with other bowties. -/
theorem otherPrivate_anchors_map :
    (B.otherPrivateBowtie C hd I hi).anchors.map (Function.Embedding.subtype _) =
      C.anchors := by
  ext v
  simp only [Finset.mem_map, mem_anchors]
  constructor
  · rintro ⟨w, ⟨i, hw⟩, rfl⟩
    exact ⟨i, (B.otherPrivate_mem_row C hd I hi i w).mp hw⟩
  · rintro ⟨i, hv⟩
    rw [← B.otherPrivate_row_map C hd I hi i] at hv
    obtain ⟨w, hw, he⟩ := Finset.mem_map.mp hv
    exact ⟨w, ⟨i, hw⟩, he⟩

/-- The number of distinct external anchors is preserved. -/
theorem otherPrivate_card_anchors :
    (B.otherPrivateBowtie C hd I hi).anchors.card = C.anchors.card := by
  rw [← B.otherPrivate_anchors_map C hd I hi, Finset.card_map]

/-- Activity is preserved because every labelled row has the same incidences. -/
theorem otherPrivate_activity :
    (B.otherPrivateBowtie C hd I hi).activity = C.activity := by
  have hn (i : Fin 5) :
      ((B.otherPrivateBowtie C hd I hi).row i).Nonempty ↔ (C.row i).Nonempty := by
    rw [← B.otherPrivate_row_map C hd I hi i, Finset.map_nonempty]
  simp only [activity, activePrivate, hn]

/-- Syndrome membership is preserved on the retained vertex subtype. -/
theorem otherPrivate_mem_syndrome (v : {w : V // w ∉ I.map B.label}) :
    v ∈ (B.otherPrivateBowtie C hd I hi).syndrome ↔ v.val ∈ C.syndrome := by
  simp only [syndrome, Finset.mem_symmDiff, B.otherPrivate_mem_row C hd I hi]

/-- Empty syndrome remains empty after inactive deletion elsewhere. -/
theorem otherPrivate_syndrome_empty (he : C.syndrome = ∅) :
    (B.otherPrivateBowtie C hd I hi).syndrome = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have h := (B.otherPrivate_mem_syndrome C hd I hi v).mp hv
  simpa only [he, Finset.notMem_empty] using h

/-- Full syndrome remains full after inactive deletion elsewhere. -/
theorem otherPrivate_syndrome_full (he : C.syndrome = C.anchors) :
    (B.otherPrivateBowtie C hd I hi).syndrome =
      (B.otherPrivateBowtie C hd I hi).anchors := by
  ext v
  simp only [B.otherPrivate_mem_syndrome C hd I hi, he, mem_anchors,
    B.otherPrivate_mem_row C hd I hi]

/-- Each allowed local class survives deletion of inactive vertices in another bowtie. -/
theorem otherPrivate_supported (hs : Gallai.Composition.Supported C) :
    Gallai.Composition.Supported (B.otherPrivateBowtie C hd I hi) := by
  rcases hs with h | h | ⟨h, he | he⟩
  · exact Or.inl (by rwa [B.otherPrivate_activity C hd I hi])
  · exact Or.inr (Or.inl (by rwa [B.otherPrivate_card_anchors C hd I hi]))
  · exact Or.inr (Or.inr ⟨by rwa [B.otherPrivate_card_anchors C hd I hi],
      Or.inl (B.otherPrivate_syndrome_empty C hd I hi he)⟩)
  · exact Or.inr (Or.inr ⟨by rwa [B.otherPrivate_card_anchors C hd I hi],
      Or.inr (B.otherPrivate_syndrome_full C hd I hi he)⟩)
end Boundary

end Gallai.WholeBowtie
