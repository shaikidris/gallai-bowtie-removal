/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Foundations.Parity
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Edge capacity of a path decomposition

Unique ownership partitions the graph's finite edge set. Each simple path
has fewer edges than the number of vertices, yielding the capacity bound
used in the sharpness example for star expansion. Isolated vertices and
empty graphs are allowed.
-/

namespace Gallai

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
variable [DecidableRel G.Adj]

/-- The edge sets of all decomposition carriers partition the graph edge finset. -/
theorem Decomposition.edge_partition (D : Decomposition G) :
    G.edgeFinset = Finset.univ.biUnion
      (fun i : Fin D.size => (D.path i).isPath.isTrail.edgesFinset) := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro he
    obtain ⟨i, hi, _⟩ := D.covers e he
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact (D.path i).walk.edges_subset_edgeSet hi

/-- The total number of graph edges is the sum of all carrier lengths. -/
theorem Decomposition.card_edgeFinset_eq_sum_length (D : Decomposition G) :
    #G.edgeFinset = ∑ i : Fin D.size, (D.path i).walk.length := by
  rw [D.edge_partition, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    change (D.path i).walk.edges.length = (D.path i).walk.length
    exact SimpleGraph.Walk.length_edges _
  · intro i _ j _ hne
    exact D.disjoint_path_edges hne

/-- Each carrier has capacity at most the vertex count minus one. -/
theorem Decomposition.edge_capacity (D : Decomposition G) :
    #G.edgeFinset ≤ D.size * (Fintype.card V - 1) := by
  rw [D.card_edgeFinset_eq_sum_length]
  calc
    _ ≤ ∑ _i : Fin D.size, (Fintype.card V - 1) :=
      Finset.sum_le_sum (fun i _ => by have h := (D.path i).isPath.length_lt; omega)
    _ = D.size * (Fintype.card V - 1) := by simp

end Gallai
