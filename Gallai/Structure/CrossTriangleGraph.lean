/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.Subdivision
import Gallai.Operations.TwoEdgePath
import Gallai.Structure.CutVertexPieces

/-! # Graph identities for two inactive vertices in different triangles -/

namespace Gallai

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- The smaller induced graph, with the two removed labels reinstated as isolates. -/
abbrev crossTriangleBase (G : SimpleGraph V) (f : Fin 5 ↪ V) : SimpleGraph V :=
  (G.induce {v | v ≠ f 1 ∧ v ≠ f 3}).spanningCoe

/-- The cross-triangle construction derives isolation, surviving edges,
edge-disjointness and the original graph identity from the actual neighbourhoods. -/
theorem cross_triangle_graph (f : Fin 5 ↪ V)
    (h02 : G.Adj (f 0) (f 2)) (h04 : G.Adj (f 0) (f 4))
    (h1 : ∀ v, G.Adj (f 1) v ↔ v = f 0 ∨ v = f 2)
    (h3 : ∀ v, G.Adj (f 3) v ↔ v = f 0 ∨ v = f 4) :
    let H := crossTriangleBase G f
    let H1 := subdividedGraph H (f 1) (f 0) (f 2)
    let H2 := subdividedGraph H1 (f 3) (f 0) (f 4)
    (∀ v, ¬ H.Adj (f 1) v) ∧ H.Adj (f 0) (f 2) ∧
      (∀ v, ¬ H1.Adj (f 3) v) ∧ H1.Adj (f 0) (f 4) ∧
      Disjoint H2.edgeSet (twoEdgeGraph (f 0) (f 2) (f 4)).edgeSet ∧
      H2 ⊔ twoEdgeGraph (f 0) (f 2) (f 4) = G := by
  classical
  let H := crossTriangleBase G f
  let H1 := subdividedGraph H (f 1) (f 0) (f 2)
  let H2 := subdividedGraph H1 (f 3) (f 0) (f 4)
  have hb (a b : V) : H.Adj a b ↔
      G.Adj a b ∧ (a ≠ f 1 ∧ a ≠ f 3) ∧ (b ≠ f 1 ∧ b ≠ f 3) :=
    spanning_induce_adj_iff G _ a b
  have hiso1 : ∀ v, ¬ H.Adj (f 1) v := by intro v; simp [hb]
  have hiso3 : ∀ v, ¬ H.Adj (f 3) v := by intro v; simp [hb]
  have hB02 : H.Adj (f 0) (f 2) := by simp [hb, h02, f.injective.eq_iff]
  have hB04 : H.Adj (f 0) (f 4) := by simp [hb, h04, f.injective.eq_iff]
  have hI3 : ∀ v, ¬ H1.Adj (f 3) v := by
    intro v
    simp [H1, subdividedGraph, SimpleGraph.deleteEdges_adj, SimpleGraph.edge_adj,
      hiso3, f.injective.eq_iff]
  have hI04 : H1.Adj (f 0) (f 4) := by
    simp [H1, subdividedGraph, SimpleGraph.deleteEdges_adj, SimpleGraph.edge_adj,
      hB04, f.injective.eq_iff]
  have hedge (i j : Fin 5) (hij : i ≠ j) (a b : V) :
      (SimpleGraph.edge (f i) (f j)).Adj a b ↔
        a = f i ∧ b = f j ∨ a = f j ∧ b = f i := by
    rw [SimpleGraph.edge_adj]
    constructor
    · exact And.left
    · intro h
      refine ⟨h, ?_⟩
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact fun h => hij (f.injective h)
      · exact fun h => hij (f.injective h).symm
  have hH2 (a b : V) : H2.Adj a b ↔
      (((((H.Adj a b ∨ (a = f 0 ∧ b = f 1 ∨ a = f 1 ∧ b = f 0)) ∨
        (a = f 1 ∧ b = f 2 ∨ a = f 2 ∧ b = f 1)) ∧
        s(a, b) ≠ s(f 0, f 2)) ∨
        (a = f 0 ∧ b = f 3 ∨ a = f 3 ∧ b = f 0)) ∨
        (a = f 3 ∧ b = f 4 ∨ a = f 4 ∧ b = f 3)) ∧
        s(a, b) ≠ s(f 0, f 4) := by
    simp only [H2, H1, subdividedGraph, SimpleGraph.deleteEdges_adj,
      SimpleGraph.sup_adj, hedge 0 1 (by decide), hedge 1 2 (by decide),
      hedge 0 3 (by decide), hedge 3 4 (by decide), Set.mem_singleton_iff]
  have hL (a b : V) : (twoEdgeGraph (f 0) (f 2) (f 4)).Adj a b ↔
      (a = f 2 ∧ b = f 0 ∨ a = f 0 ∧ b = f 2) ∨
      (a = f 0 ∧ b = f 4 ∨ a = f 4 ∧ b = f 0) := by
    simp only [twoEdgeGraph, SimpleGraph.sup_adj,
      hedge 2 0 (by decide), hedge 0 4 (by decide)]
  have hdis : Disjoint H2.edgeSet (twoEdgeGraph (f 0) (f 2) (f 4)).edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hl
    induction e using Sym2.inductionOn with
    | _ a b =>
      change H2.Adj a b at he
      change (twoEdgeGraph (f 0) (f 2) (f 4)).Adj a b at hl
      rw [hL] at hl
      rcases hl with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        simp [hH2, f.injective.eq_iff] at he
  have hborder1 (v : V) : (H2 ⊔ twoEdgeGraph (f 0) (f 2) (f 4)).Adj (f 1) v ↔
      G.Adj (f 1) v := by
    rw [SimpleGraph.sup_adj, hH2, hL, h1]
    simp [hiso1, f.injective.eq_iff, eq_comm]
  have hborder3 (v : V) : (H2 ⊔ twoEdgeGraph (f 0) (f 2) (f 4)).Adj (f 3) v ↔
      G.Adj (f 3) v := by
    rw [SimpleGraph.sup_adj, hH2, hL, h3]
    simp [hiso3, f.injective.eq_iff, eq_comm]
  have hgraph : H2 ⊔ twoEdgeGraph (f 0) (f 2) (f 4) = G := by
    ext a b
    by_cases ha1 : a = f 1
    · subst a; exact hborder1 b
    by_cases ha3 : a = f 3
    · subst a; exact hborder3 b
    by_cases hb1 : b = f 1
    · subst b
      simpa only [SimpleGraph.adj_comm] using hborder1 a
    by_cases hb3 : b = f 3
    · subst b
      simpa only [SimpleGraph.adj_comm] using hborder3 a
    have hLsub : (twoEdgeGraph (f 0) (f 2) (f 4)).Adj a b → G.Adj a b := by
      intro h
      rw [hL] at h
      rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact h02.symm
      · exact h02
      · exact h04
      · exact h04.symm
    rw [hL] at hLsub
    rw [SimpleGraph.sup_adj, hH2, hL, hb]
    simp only [ha1, ha3, hb1, hb3, false_and, and_false, or_false]
    constructor
    · rintro (h | h)
      · exact h.1.1.1
      · exact hLsub h
    · intro hg
      by_cases h02' : s(a, b) = s(f 0, f 2)
      · rcases Sym2.eq_iff.mp h02' with h | h
        · exact Or.inr (Or.inl (Or.inr h))
        · exact Or.inr (Or.inl (Or.inl h))
      · by_cases h04' : s(a, b) = s(f 0, f 4)
        · rcases Sym2.eq_iff.mp h04' with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inl ⟨⟨⟨hg, ⟨ha1, ha3⟩, ⟨hb1, hb3⟩⟩, h02'⟩, h04'⟩
  exact ⟨hiso1, hB02, hI3, hI04, hdis, hgraph⟩

end Gallai
