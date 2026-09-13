/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ZeroSyndromeAccounting
import Gallai.Transport.CompletedStarBoundary

/-! # Disjoint exhaustive original-edge boundary for whole deletion -/

namespace Gallai.WholeBowtie
open Certificate Certificate.CompletedStar Certificate.ZeroSyndrome
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Whole-deletion edges have no vertex in the bowtie, whereas every local
target edge does. No graph connectedness or parity assumption is needed. -/
theorem zero_puncture_ne_target (A : B.AnchorNumbering)
    (f : Sym2 {v // v ∉ B.vertices}) (e : Sym2 Star.Vertex)
    (he : e ∈ targetEdges (B.completedStarState A)) :
    Sym2.map Subtype.val f ≠ Sym2.map (B.completedLabel A) e := by
  intro heq
  obtain ⟨v, hv, hB⟩ := B.completed_target_incident A e he
  rw [← heq] at hv
  obtain ⟨w, _, rfl⟩ := Sym2.mem_map.mp hv
  exact w.property hB

/-- Every original edge is either a puncture edge or an original local edge. -/
theorem zero_original_edge_cases (A : B.AnchorNumbering) (e : Sym2 V)
    (he : e ∈ G.edgeSet) :
    (∃ f ∈ B.puncture.edgeSet, Sym2.map Subtype.val f = e) ∨
      ∃ f ∈ targetEdges (B.completedStarState A),
        Sym2.map (B.completedLabel A) f = e := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    change G.Adj u v at he
    by_cases hu : u ∈ B.vertices
    · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hu
      exact Or.inr (B.completedLabel_target_covers A i v he)
    by_cases hv : v ∈ B.vertices
    · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨f, hf, hfe⟩ := B.completedLabel_target_covers A i u he.symm
      exact Or.inr ⟨f, hf, hfe.trans Sym2.eq_swap⟩
    · exact Or.inl ⟨s(⟨u, hu⟩, ⟨v, hv⟩), he, rfl⟩

omit [DecidableEq V] in
theorem zero_punctureCarrier_edges (P : NonemptyPath B.puncture) :
    (B.punctureCarrier P).walk.edges = P.walk.edges.map (Sym2.map Subtype.val) := by
  simp only [punctureCarrier, NonemptyPath.map, SimpleGraph.Walk.edges_map]
  rfl

/-- Puncture multiplicity at an embedded old edge is inherited exactly. -/
theorem zero_puncture_count (D : Decomposition B.puncture)
    (f : Sym2 {v // v ∉ B.vertices}) (hf : f ∈ B.puncture.edgeSet) :
    (∑ k : Fin D.size,
      (B.punctureCarrier (D.path k)).walk.edges.count (Sym2.map Subtype.val f)) = 1 := by
  simp only [B.zero_punctureCarrier_edges,
    List.count_map_of_injective _ _ (Sym2.map.injective Subtype.val_injective)]
  exact (D.sum_edge_count f).trans (if_pos hf)

/-- A local edge occurs in no mapped puncture path. -/
theorem zero_puncture_count_target (A : B.AnchorNumbering)
    (D : Decomposition B.puncture) (e : Sym2 Star.Vertex)
    (he : e ∈ targetEdges (B.completedStarState A)) :
    (∑ k : Fin D.size, (B.punctureCarrier (D.path k)).walk.edges.count
      (Sym2.map (B.completedLabel A) e)) = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  apply List.count_eq_zero.mpr
  rw [B.zero_punctureCarrier_edges]
  intro hm
  obtain ⟨f, _, hfe⟩ := List.mem_map.mp hm
  exact B.zero_puncture_ne_target A f e he hfe

/-- Embedded puncture edges have zero local-record multiplicity. -/
theorem zero_local_count_puncture (A : B.AnchorNumbering)
    (f : Sym2 {v // v ∉ B.vertices}) :
    ((targetEdges (B.completedStarState A)).val.map
      (Sym2.map (B.completedLabel A))).count (Sym2.map Subtype.val f) = 0 := by
  apply Multiset.count_eq_zero.mpr
  intro hm
  obtain ⟨e, he, hef⟩ := Multiset.mem_map.mp hm
  exact B.zero_puncture_ne_target A f e he hef.symm

/-- Original local targets have multiplicity one after injective relabeling. -/
theorem zero_local_count_target (A : B.AnchorNumbering) (e : Sym2 Star.Vertex)
    (he : e ∈ targetEdges (B.completedStarState A)) :
    ((targetEdges (B.completedStarState A)).val.map
      (Sym2.map (B.completedLabel A))).count (Sym2.map (B.completedLabel A) e) = 1 := by
  rw [Multiset.count_map_eq_count' _ _ (Sym2.map.injective (B.completedLabel_injective A))]
  exact Multiset.count_eq_one_of_mem (targetEdges (B.completedStarState A)).nodup he

end Gallai.WholeBowtie
