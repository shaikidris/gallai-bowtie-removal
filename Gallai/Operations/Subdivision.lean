/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.SubdividePath
import Gallai.Operations.EdgeRun
import Gallai.Operations.DecompositionInduce
import Gallai.Foundations.EdgeCounts
import Mathlib.Combinatorics.SimpleGraph.Operations

/-! # Same-count subdivision of an actual decomposition carrier -/

namespace Gallai

open scoped Finset
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Replace the old edge by two edges incident with a formerly isolated vertex. -/
def subdividedGraph (G : SimpleGraph V) (z x y : V) : SimpleGraph V :=
  (G ⊔ SimpleGraph.edge x z ⊔ SimpleGraph.edge z y).deleteEdges {s(x, y)}

/-- Subdivision preserves decidable adjacency, including for a second subdivision. -/
instance (G : SimpleGraph V) [DecidableRel G.Adj] (z x y : V) :
    DecidableRel (subdividedGraph G z x y).Adj :=
  inferInstanceAs (DecidableRel
    ((G ⊔ SimpleGraph.edge x z ⊔ SimpleGraph.edge z y).deleteEdges {s(x, y)}).Adj)

/-- Subdivide one selected edge run using an isolated vertex. Every original
carrier is retained, and all endpoint multiplicities are unchanged. -/
theorem Decomposition.subdivide_of_run [DecidableRel G.Adj]
    (D : Decomposition G) (i : Fin D.size) (z x y : V)
    (L : G.Walk (D.path i).start x) (R : G.Walk y (D.path i).finish)
    (hxy : G.Adj x y) (hz : ∀ v, ¬ G.Adj z v)
    (hrun : (D.path i).walk = L.append (.cons hxy R)) :
    ∃ E : Decomposition (subdividedGraph G z x y), E.size = D.size ∧
      ∀ v, E.endpointCount v = D.endpointCount v := by
  classical
  have hxz : x ≠ z := fun h => hz y (h ▸ hxy)
  have hzy : z ≠ y := fun h => hz x (h ▸ hxy.symm)
  have he1 : s(x, z) ≠ s(x, y) := by
    intro h
    rcases Sym2.eq_iff.mp h with h | h
    · exact hzy h.2
    · exact hxz h.2.symm
  have he2 : s(z, y) ≠ s(x, y) := by
    intro h
    rcases Sym2.eq_iff.mp h with h | h
    · exact hxz h.1.symm
    · exact hzy h.1
  have he12 : s(x, z) ≠ s(z, y) := by
    intro h
    rcases Sym2.eq_iff.mp h with h | h
    · exact hxz h.1
    · exact hxy.ne h.1
  let K := G ⊔ SimpleGraph.edge x z ⊔ SimpleGraph.edge z y
  let f : G →g K := SimpleGraph.Hom.ofLE (le_sup_left.trans le_sup_left)
  have hf : Function.Injective f := by intro a b h; exact h
  have h1 : K.Adj x z := Or.inl (Or.inr (by simp [SimpleGraph.edge_adj, hxz]))
  have h2 : K.Adj z y := Or.inr (by simp [SimpleGraph.edge_adj, hzy])
  have hp : ((L.map f).append (.cons (f.map_adj hxy) (R.map f))).IsPath := by
    have h := (D.path i).isPath.map hf
    rw [hrun] at h
    simpa only [SimpleGraph.Walk.map_append, SimpleGraph.Walk.map_cons] using h
  have havoid : z ∉ ((L.map f).append (.cons (f.map_adj hxy) (R.map f))).support := by
    have h := (D.path i).notMem_support_of_isolated z hz
    simpa [hrun, SimpleGraph.Walk.support_map, f] using h
  let Q : NonemptyPath K := .subdivide (L.map f) (R.map f) (f.map_adj hxy) h1 h2 hp havoid
  have hqc (e : Sym2 V) : Q.walk.edges.count e + (if s(x, y) = e then 1 else 0) =
      (D.path i).walk.edges.count e + (if s(x, z) = e then 1 else 0) +
        (if s(z, y) = e then 1 else 0) := by
    have h := NonemptyPath.subdivide_edge_count (L.map f) (R.map f)
      (f.map_adj hxy) h1 h2 hp havoid e
    simpa [Q, hrun, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_map, f] using h
  have hused : s(x, y) ∈ (D.path i).walk.edges := by simp [hrun]
  have hQnot : s(x, y) ∉ Q.walk.edges := by
    have h := hqc s(x, y)
    have hc := List.count_eq_one_of_mem (D.path i).isPath.isTrail.edges_nodup hused
    rw [if_pos rfl, if_neg he1, if_neg he2, hc] at h
    have hc0 : Q.walk.edges.count s(x, y) = 0 := by omega
    exact List.count_eq_zero.mp hc0
  let raw : Fin D.size → NonemptyPath K := fun j =>
    if j = i then Q else (D.path j).map f hf
  have hraw (j : Fin D.size) : s(x, y) ∉ (raw j).walk.edges := by
    by_cases hj : j = i
    · dsimp only [raw]
      rw [if_pos hj]
      exact hQnot
    · have hn : s(x, y) ∉ (D.path j).walk.edges := by
        intro h
        obtain ⟨k, _, hu⟩ := D.covers s(x, y) hxy
        exact hj ((hu j h).trans (hu i hused).symm)
      dsimp only [raw]
      rw [if_neg hj, NonemptyPath.map_edges]
      simpa [f] using hn
  let paths : Fin D.size → NonemptyPath (subdividedGraph G z x y) := fun j =>
    (raw j).transfer _ (fun e he => by
      rw [subdividedGraph, SimpleGraph.edgeSet_deleteEdges]
      refine ⟨(raw j).walk.edges_subset_edgeSet he, ?_⟩
      intro h
      exact hraw j ((Set.mem_singleton_iff.mp h) ▸ he))
  have hj (e : Sym2 V) (hne : s(x, y) ≠ e) (j : Fin D.size) :
      (paths j).walk.edges.count e = (D.path j).walk.edges.count e +
        if j = i then (if s(x, z) = e then 1 else 0) +
          (if s(z, y) = e then 1 else 0) else 0 := by
    rw [show (paths j).walk.edges = (raw j).walk.edges from NonemptyPath.transfer_edges ..]
    by_cases hji : j = i
    · subst j
      have h := hqc e
      simp only [if_neg hne, add_zero] at h
      dsimp only [raw]
      rw [if_pos rfl, if_pos rfl]
      exact h.trans (Nat.add_assoc _ _ _)
    · dsimp only [raw]
      rw [if_neg hji, if_neg hji, NonemptyPath.map_edges]
      simp [f]
  have hcount (e : Sym2 V) (he : e ∈ (subdividedGraph G z x y).edgeSet) :
      (∑ j, (paths j).walk.edges.count e) = 1 := by
    have he' := he
    rw [subdividedGraph, SimpleGraph.edgeSet_deleteEdges] at he'
    have hne : s(x, y) ≠ e := fun h => he'.2 (by simp [h])
    simp_rw [hj e hne]
    rw [Finset.sum_add_distrib, D.sum_edge_count]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hG1 : s(x, z) ∉ G.edgeSet := fun h => hz x h.symm
    have hG2 : s(z, y) ∉ G.edgeSet := hz y
    by_cases h1e : s(x, z) = e
    · subst e
      simp [hG1, he12.symm]
    · by_cases h2e : s(z, y) = e
      · subst e
        simp [hG2, he12]
      · have hold : e ∈ G.edgeSet := by
          have h := he'.1
          simp only [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_edge_of_ne hxz,
            SimpleGraph.edgeSet_edge_of_ne hzy, Set.mem_union, Set.mem_singleton_iff] at h
          rcases h with (h | h) | h
          · exact h
          · exact (h1e h.symm).elim
          · exact (h2e h.symm).elim
        simp [hold, h1e, h2e]
  refine ⟨Decomposition.ofEdgeCounts paths hcount, rfl, ?_⟩
  intro v
  change (∑ j : Fin D.size, _) = _
  apply Finset.sum_congr rfl
  intro j _
  change ((if (paths j).start = v then 1 else 0) +
    (if (paths j).finish = v then 1 else 0)) =
    ((if (D.path j).start = v then 1 else 0) +
      (if (D.path j).finish = v then 1 else 0))
  have hs : (paths j).start = (D.path j).start := by
    dsimp only [paths, NonemptyPath.transfer, raw]
    by_cases h : j = i
    · subst j
      rw [if_pos rfl]
      rfl
    · rw [if_neg h]
      rfl
  have ht : (paths j).finish = (D.path j).finish := by
    dsimp only [paths, NonemptyPath.transfer, raw]
    by_cases h : j = i
    · subst j
      rw [if_pos rfl]
      rfl
    · rw [if_neg h]
      rfl
  simp only [hs, ht]

omit [DecidableEq V] in
/-- Subdivision depends on an unordered edge, not its selected orientation. -/
theorem subdividedGraph_comm (G : SimpleGraph V) (z x y : V) :
    subdividedGraph G z x y = subdividedGraph G z y x := by
  unfold subdividedGraph
  rw [SimpleGraph.edge_comm y z, SimpleGraph.edge_comm z x,
    show s(x, y) = s(y, x) from Sym2.eq_swap]
  congr 1
  ac_rfl

/-- Every existing edge can be subdivided at an isolated vertex. The actual
carrier and its orientation are selected from the decomposition, not assumed. -/
theorem Decomposition.subdivide_edge [DecidableRel G.Adj]
    (D : Decomposition G) (z x y : V) (hxy : G.Adj x y)
    (hz : ∀ v, ¬ G.Adj z v) :
    ∃ E : Decomposition (subdividedGraph G z x y), E.size = D.size ∧
      ∀ v, E.endpointCount v = D.endpointCount v := by
  obtain ⟨i, hi, _⟩ := D.covers s(x, y) hxy
  obtain ⟨u, v, L, R, huv, he, hr⟩ := exists_edge_run (D.path i).walk s(x, y) hi
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact D.subdivide_of_run i z _ _ L R huv hz hr
  · rw [subdividedGraph_comm G z x y]
    exact D.subdivide_of_run i z _ _ L R huv hz hr

end Gallai
