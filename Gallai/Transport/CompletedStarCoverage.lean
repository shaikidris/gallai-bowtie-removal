/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.CompletedStarOwnership
import Gallai.Transport.CompletedStarBoundary
import Gallai.Operations.EraseCarrier

/-! # Sparse completed-star reconstruction as an actual decomposition

An accepted record supplies the local words, not a global coverage premise.
Old unique ownership and local unique ownership are combined across their
disjoint original-edge boundary. Certificate existence remains separate.
-/

namespace Gallai.WholeBowtie

open Certificate.CompletedStar
open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (D : Decomposition B.completedStar) (hfour : #B.anchors = 4)
variable {replacements added : List (List Star.Vertex)}
variable (h : AcceptedRecord (B.completedStarState (B.carrierAnchorOrder D hfour))
  (profileInterface (Star.profileOf D B.completedHub)) replacements added)

/-- Each old index retains precisely its nonspokes; added indices retain none. -/
def completedRetainedEdges (n : ℕ) : Fin D.size ⊕ Fin n → List (Sym2 B.StarSurvivor)
  | .inl i => (D.path i).walk.edges.filter (fun e => decide (B.completedHub ∉ e))
  | .inr _ => []

theorem completedRetainedEdges_sound (n : ℕ) (j : Fin D.size ⊕ Fin n)
    (f : Sym2 B.StarSurvivor) (hf : f ∈ B.completedRetainedEdges D n j) :
    f ∈ B.completedStar.edgeSet ∧ B.completedHub ∉ f := by
  rcases j with j | j
  · have he := List.mem_filter.mp hf
    exact ⟨(D.path j).walk.edges_subset_edgeSet he.1, of_decide_eq_true he.2⟩
  · exact False.elim (List.not_mem_nil hf)

theorem completedRetainedEdges_unique (n : ℕ) (f : Sym2 B.StarSurvivor)
    (hf : f ∈ B.completedStar.edgeSet) (hx : B.completedHub ∉ f) :
    ∃! j : Fin D.size ⊕ Fin n, f ∈ B.completedRetainedEdges D n j := by
  obtain ⟨i, hi, hu⟩ := D.covers f hf
  refine ⟨.inl i, List.mem_filter.mpr ⟨hi, decide_eq_true hx⟩, ?_⟩
  intro j hj
  rcases j with j | j
  · exact congrArg Sum.inl (hu j (List.mem_filter.mp hj).1)
  · exact False.elim (List.not_mem_nil hj)

theorem completedFamily_mem_edges (j : Fin D.size ⊕ Fin added.length) (e : Sym2 V) :
    e ∈ (B.completedFamily D hfour h j).walk.edges ↔
      e ∈ (B.completedRetainedEdges D added.length j).map (Sym2.map Subtype.val) ∨
      e ∈ (Certificate.wordEdges (B.completedCandidateWord D hfour h j)).map
        (Sym2.map (B.completedLabel (B.carrierAnchorOrder D hfour))) := by
  rcases j with j | j
  · exact (B.completedRestoredOld_edge_partition D hfour h j).mem_iff.trans List.mem_append
  · change e ∈ (B.completedAddedCarrier D hfour h j).walk.edges ↔ _
    rw [B.completedAddedCarrier_edges]
    simp only [completedRetainedEdges, List.map_nil, List.not_mem_nil, false_or]
    rfl

theorem completedFamily_retained_iff (j : Fin D.size ⊕ Fin added.length)
    (f : Sym2 B.StarSurvivor) (hx : B.completedHub ∉ f) :
    Sym2.map Subtype.val f ∈ (B.completedFamily D hfour h j).walk.edges ↔
      f ∈ B.completedRetainedEdges D added.length j := by
  rw [B.completedFamily_mem_edges]
  constructor
  · rintro (hr | hl)
    · obtain ⟨g, hg, he⟩ := List.mem_map.mp hr
      exact (Sym2.map.injective Subtype.val_injective he) ▸ hg
    · obtain ⟨g, hg, he⟩ := List.mem_map.mp hl
      exact False.elim (B.completed_retained_ne_target (B.carrierAnchorOrder D hfour) f hx g
        (B.completedCandidateWord_target D hfour h j g hg) he.symm)
  · intro hf
    exact Or.inl (List.mem_map.mpr ⟨f, hf, rfl⟩)

theorem completedFamily_target_iff (j : Fin D.size ⊕ Fin added.length) (e : Sym2 Star.Vertex)
    (he : e ∈ targetEdges (B.completedStarState (B.carrierAnchorOrder D hfour))) :
    Sym2.map (B.completedLabel (B.carrierAnchorOrder D hfour)) e ∈
        (B.completedFamily D hfour h j).walk.edges ↔
      e ∈ Certificate.wordEdges (B.completedCandidateWord D hfour h j) := by
  rw [B.completedFamily_mem_edges]
  constructor
  · rintro (hr | hl)
    · obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hr
      exact False.elim (B.completed_retained_ne_target (B.carrierAnchorOrder D hfour) f
        (B.completedRetainedEdges_sound D added.length j f hf).2 e he hfe)
    · obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hl
      exact (Sym2.map.injective (B.completedLabel_injective (B.carrierAnchorOrder D hfour)) hfe) ▸ hf
  · intro hf
    exact Or.inr (List.mem_map.mpr ⟨e, hf, rfl⟩)

/-- Every original edge has exactly one actual output carrier. -/
theorem completedFamily_covers :
    ∀ e ∈ G.edgeSet, ∃! j, e ∈ (B.completedFamily D hfour h j).walk.edges := by
  intro e he
  rcases B.completed_edge_cases (B.carrierAnchorOrder D hfour) e he with hr | hl
  · obtain ⟨f, hf, hx, rfl⟩ := hr
    obtain ⟨i, hi, hu⟩ := B.completedRetainedEdges_unique D added.length f hf hx
    refine ⟨i, (B.completedFamily_retained_iff D hfour h i f hx).mpr hi, ?_⟩
    intro j hj
    exact hu j ((B.completedFamily_retained_iff D hfour h j f hx).mp hj)
  · obtain ⟨f, hf, rfl⟩ := hl
    obtain ⟨i, hi, hu⟩ := B.completedCandidateWord_unique D hfour h f hf
    refine ⟨i, (B.completedFamily_target_iff D hfour h i f hf).mpr hi, ?_⟩
    intro j hj
    exact hu j ((B.completedFamily_target_iff D hfour h j f hf).mp hj)

/-- Restore the original graph from any accepted actual-interface sparse record. -/
noncomputable def completedReconstruction : Decomposition G :=
  Decomposition.ofFamily (B.completedFamily D hfour h) (B.completedFamily_covers D hfour h)

theorem completedReconstruction_size :
    (B.completedReconstruction D hfour h).size = D.size + added.length := by
  rw [completedReconstruction, Decomposition.ofFamily_size, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_fin]

theorem completedReconstruction_budget :
    (B.completedReconstruction D hfour h).size ≤ D.size + 2 := by
  rw [B.completedReconstruction_size]
  exact Nat.add_le_add_left h.2.2.1 _

theorem completedReconstruction_endpoint_reserve (w : B.StarSurvivor)
    (hw : w.val ∉ B.vertices) :
    D.endpointCount w ≤ (B.completedReconstruction D hfour h).endpointCount w.val := by
  rw [completedReconstruction, Decomposition.ofFamily_endpointCount]
  exact B.completedFamily_endpoint_reserve D hfour h w hw

end Gallai.WholeBowtie
