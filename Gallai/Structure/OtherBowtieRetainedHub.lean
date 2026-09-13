/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.OtherBowtiePrivateDeletion
import Gallai.Structure.RetainedHubCap

/-! # Other whole bowties survive a parity-correct retained-hub auxiliary

The common interface covers unrepaired private deletion and either status of
an odd-anchor pair repair. Its two hypotheses are discharged below for those
actual auxiliaries; no path decomposition or budget is assumed.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (B C : WholeBowtie G) (hd : Disjoint B.vertices C.vertices)
variable (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj]
variable (hpar : ∀ v : B.StarSurvivor, Even (H.degree v) ↔ Even (G.degree v.val))
variable (hadj : ∀ u v : B.StarSurvivor, Even (G.degree u.val) →
  (H.Adj u v ↔ G.Adj u.val v.val))

include hpar hadj in
/-- The untouched labelled bowtie is an entire even component of the auxiliary. -/
noncomputable def otherRetainedBowtie : WholeBowtie H := by
  let l := B.otherPrivateLabel C hd (Finset.univ.erase 0)
  apply ofClosedEmbedding l
  · intro i
    exact (hpar (l i)).mpr (C.even_degree_label i)
  · intro i j
    exact (hadj (l i) (l j) (C.even_degree_label i)).trans (C.adj_iff i j)
  · intro i v ha he
    have hm := mem_evenComponent_of_adj C.component (C.label_mem_component i)
      ((hadj (l i) v (C.even_degree_label i)).mp ha) ((hpar v).mp he)
    rw [C.component_vertices] at hm
    obtain ⟨j, hj⟩ := hm
    exact ⟨j, Subtype.ext hj⟩

/-- The component has exactly its original five labelled vertices. -/
theorem otherRetained_mem_vertices (v : B.StarSurvivor) :
    v ∈ (B.otherRetainedBowtie C hd H hpar hadj).vertices ↔ v.val ∈ C.vertices := by
  rw [mem_vertices, mem_vertices,
    (B.otherRetainedBowtie C hd H hpar hadj).component_vertices, C.component_vertices]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Subtype.ext hi⟩

/-- Every retained row incidence is unchanged. -/
theorem otherRetained_mem_row (i : Fin 5) (v : B.StarSurvivor) :
    v ∈ (B.otherRetainedBowtie C hd H hpar hadj).row i ↔ v.val ∈ C.row i := by
  rw [mem_row, mem_row, B.otherRetained_mem_vertices C hd H hpar hadj v]
  exact and_congr (hadj (B.otherPrivateLabel C hd (Finset.univ.erase 0) i) v
    (C.even_degree_label i)) Iff.rfl

/-- All original row vertices survive, including shared odd anchors. -/
theorem otherRetained_row_map (i : Fin 5) :
    ((B.otherRetainedBowtie C hd H hpar hadj).row i).map
      (Function.Embedding.subtype _) = C.row i := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    exact (B.otherRetained_mem_row C hd H hpar hadj i w).mp hw
  · intro hv
    have hout : v ∉ (Finset.univ.erase 0).map B.label := by
      intro hm
      obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hm
      have hb : v ∈ B.vertices := hj ▸
        (B.mem_vertices (B.label j)).mpr (B.label_mem_component j)
      exact C.anchor_not_mem_other B ((C.mem_anchors v).mpr ⟨i, hv⟩) hb
    exact Finset.mem_map.mpr ⟨⟨v, hout⟩,
      (B.otherRetained_mem_row C hd H hpar hadj i ⟨v, hout⟩).mpr hv, rfl⟩

/-- The full anchor set maps onto its original value. -/
theorem otherRetained_anchors_map :
    (B.otherRetainedBowtie C hd H hpar hadj).anchors.map
      (Function.Embedding.subtype _) = C.anchors := by
  ext v
  simp only [Finset.mem_map, mem_anchors]
  constructor
  · rintro ⟨w, ⟨i, hw⟩, rfl⟩
    exact ⟨i, (B.otherRetained_mem_row C hd H hpar hadj i w).mp hw⟩
  · rintro ⟨i, hv⟩
    rw [← B.otherRetained_row_map C hd H hpar hadj i] at hv
    obtain ⟨w, hw, he⟩ := Finset.mem_map.mp hv
    exact ⟨w, ⟨i, hw⟩, he⟩

/-- Anchor cardinality is preserved. -/
theorem otherRetained_card_anchors :
    (B.otherRetainedBowtie C hd H hpar hadj).anchors.card = C.anchors.card := by
  rw [← B.otherRetained_anchors_map C hd H hpar hadj, Finset.card_map]

/-- Private activity is preserved. -/
theorem otherRetained_activity :
    (B.otherRetainedBowtie C hd H hpar hadj).activity = C.activity := by
  have hn (i : Fin 5) : ((B.otherRetainedBowtie C hd H hpar hadj).row i).Nonempty ↔
      (C.row i).Nonempty := by
    rw [← B.otherRetained_row_map C hd H hpar hadj i, Finset.map_nonempty]
  simp only [activity, activePrivate, hn]

/-- Syndrome membership is preserved exactly. -/
theorem otherRetained_mem_syndrome (v : B.StarSurvivor) :
    v ∈ (B.otherRetainedBowtie C hd H hpar hadj).syndrome ↔ v.val ∈ C.syndrome := by
  simp only [syndrome, Finset.mem_symmDiff, B.otherRetained_mem_row C hd H hpar hadj]

/-- Each supported manuscript case survives the retained-hub operation. -/
theorem otherRetained_supported (hs : Gallai.Composition.Supported C) :
    Gallai.Composition.Supported (B.otherRetainedBowtie C hd H hpar hadj) := by
  have hz (he : C.syndrome = ∅) :
      (B.otherRetainedBowtie C hd H hpar hadj).syndrome = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hh := (B.otherRetained_mem_syndrome C hd H hpar hadj v).mp hv
    simp only [he, Finset.notMem_empty] at hh
  have hf (he : C.syndrome = C.anchors) :
      (B.otherRetainedBowtie C hd H hpar hadj).syndrome =
        (B.otherRetainedBowtie C hd H hpar hadj).anchors := by
    ext v
    simp only [B.otherRetained_mem_syndrome C hd H hpar hadj, he, mem_anchors,
      B.otherRetained_mem_row C hd H hpar hadj]
  rcases hs with h | h | ⟨h, he | he⟩
  · exact Or.inl (by rwa [B.otherRetained_activity C hd H hpar hadj])
  · exact Or.inr (Or.inl (by rwa [B.otherRetained_card_anchors C hd H hpar hadj]))
  · exact Or.inr (Or.inr ⟨by rwa [B.otherRetained_card_anchors C hd H hpar hadj],
      Or.inl (hz he)⟩)
  · exact Or.inr (Or.inr ⟨by rwa [B.otherRetained_card_anchors C hd H hpar hadj],
      Or.inr (hf he)⟩)

omit [DecidableEq V] in
/-- Unrepaired retained deletion changes no adjacency between surviving vertices. -/
theorem retained_even_adj (u v : B.StarSurvivor) (_hu : Even (G.degree u.val)) :
    B.retainedHubGraph.Adj u v ↔ G.Adj u.val v.val := Iff.rfl

/-- Pair repair changes no adjacency at an original even vertex. -/
theorem retainedRepair_even_adj (p q : B.StarSurvivor)
    (hs : B.privateDeletionSyndrome = {p, q})
    (u v : B.StarSurvivor) (hu : Even (G.degree u.val)) :
    (B.retainedHubRepair p q).Adj u v ↔ G.Adj u.val v.val := by
  have hp := B.odd_degree_anchor (B.privateDeletionSyndrome_anchor p (by simp [hs]))
  have hq := B.odd_degree_anchor (B.privateDeletionSyndrome_anchor q (by simp [hs]))
  have hup : u ≠ p := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hp hu
  have huq : u ≠ q := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hq hu
  rw [SimpleGraph.adj_comm, toggleEdge_adj_of_ne B.retainedHubGraph p q v u hup huq,
    SimpleGraph.adj_comm]
  rfl

end Gallai.WholeBowtie
