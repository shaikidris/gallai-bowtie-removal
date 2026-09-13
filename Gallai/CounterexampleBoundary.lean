/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Corollaries

/-! # Counting the two-bowtie counterexample boundary -/
namespace Gallai.TwoBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {X Y : WholeBowtie G}

/-- Failure of the Gallai bound forces five anchors at the first bowtie. -/
theorem Kernel.five_anchors (h : Kernel X Y) (hc : G.Connected)
    (hn : ¬ ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2) :
    5 ≤ X.anchors.card := by
  by_contra ha
  obtain ⟨D, hD, _⟩ := h.expose_other hc (by omega)
  exact hn ⟨D, hD⟩

omit [DecidableEq V] in
/-- A bowtie's vertices are disjoint from the odd vertices. -/
theorem bowtie_disjoint_odd (X : WholeBowtie G) :
    Disjoint X.vertices (oddVertices G) := by
  apply Finset.disjoint_left.mpr
  intro v hv ho
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
  have he := X.even_degree_label i
  have hh := (Finset.mem_filter.mp ho).2
  exact (Nat.not_even_iff_odd.mpr hh) he

/-- Corollary A2, including the exact order-sixteen equality consequences. -/
theorem corollaryA2 (hc : G.Connected) (h : Kernel X Y)
    (hn : ¬ ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2) :
    5 ≤ X.anchors.card ∧ 5 ≤ Y.anchors.card ∧
    6 ≤ (oddVertices G).card ∧ 16 ≤ Fintype.card V ∧
    (Fintype.card V = 16 →
      (∀ v, Even (G.degree v) → v ∈ X.vertices ∪ Y.vertices) ∧
      4 ≤ (X.anchors ∩ Y.anchors).card) := by
  have hx := h.five_anchors hc hn
  have hy := h.symm.five_anchors hc hn
  have hxo := Finset.card_le_card (anchors_subset_odd X)
  have hodd : (oddVertices G).card % 2 = 0 := by
    exact Nat.even_iff.mp G.even_card_odd_degree_vertices
  have hsix : 6 ≤ (oddVertices G).card := by omega
  have hten : (X.vertices ∪ Y.vertices).card = 10 := by
    rw [Finset.card_union_of_disjoint h.1, X.card_vertices, Y.card_vertices]
  have hdis : Disjoint (X.vertices ∪ Y.vertices) (oddVertices G) :=
    Finset.disjoint_union_left.mpr ⟨bowtie_disjoint_odd X, bowtie_disjoint_odd Y⟩
  have htotal : ((X.vertices ∪ Y.vertices) ∪ oddVertices G).card =
      10 + (oddVertices G).card := by
    rw [Finset.card_union_of_disjoint hdis, hten]
  have hle := Finset.card_le_univ ((X.vertices ∪ Y.vertices) ∪ oddVertices G)
  have horder : 16 ≤ Fintype.card V := by omega
  refine ⟨hx, hy, hsix, horder, ?_⟩
  intro hn16
  have ho6 : (oddVertices G).card = 6 := by omega
  have hall : ((X.vertices ∪ Y.vertices) ∪ oddVertices G) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp only [Finset.card_univ, htotal, ho6, hn16]
    omega
  constructor
  · intro v hv
    have hm : v ∈ (X.vertices ∪ Y.vertices) ∪ oddVertices G := by
      rw [hall]
      exact Finset.mem_univ v
    rcases Finset.mem_union.mp hm with hb | ho
    · exact hb
    · exact ((Nat.not_even_iff_odd.mpr (Finset.mem_filter.mp ho).2) hv).elim
  · have hu : X.anchors ∪ Y.anchors ⊆ oddVertices G :=
      Finset.union_subset (anchors_subset_odd X) (anchors_subset_odd Y)
    have huc := Finset.card_le_card hu
    have hi := Finset.card_union_add_card_inter X.anchors Y.anchors
    omega

end Gallai.TwoBowtie
