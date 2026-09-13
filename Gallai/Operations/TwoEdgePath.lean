/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Foundations.Endpoints
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Operations

/-! # The one-path decomposition of a two-edge path -/

namespace Gallai

universe u
variable {V : Type u}

/-- The graph of a two-edge path with the middle vertex named first. -/
abbrev twoEdgeGraph (x b d : V) : SimpleGraph V :=
  SimpleGraph.edge b x ⊔ SimpleGraph.edge x d

/-- A two-edge path is one nonempty simple carrier when its vertices are distinct. -/
def twoEdgeDecomposition (x b d : V) (hbx : b ≠ x) (hxd : x ≠ d) (hbd : b ≠ d) :
    Decomposition (twoEdgeGraph x b d) where
  size := 1
  path _ := {
    start := b
    finish := d
    walk := .cons (show (twoEdgeGraph x b d).Adj b x from
        Or.inl (by simp [SimpleGraph.edge_adj, hbx]))
      (.cons (show (twoEdgeGraph x b d).Adj x d from
        Or.inr (by simp [SimpleGraph.edge_adj, hxd])) .nil)
    isPath := by simp [SimpleGraph.Walk.cons_isPath_iff, hbx, hbd, hxd]
    nonempty := SimpleGraph.Walk.not_nil_cons }
  covers := by
    intro e he
    refine ⟨0, ?_, fun j _ => Subsingleton.elim j 0⟩
    rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_edge_of_ne hbx,
      SimpleGraph.edgeSet_edge_of_ne hxd] at he
    simpa only [Set.mem_union, Set.mem_singleton_iff,
      SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_cons, List.not_mem_nil, or_false] using he

/-- Only the two outer vertices acquire an endpoint from this path. -/
theorem twoEdgeDecomposition_endpointCount [DecidableEq V]
    (x b d v : V) (hbx : b ≠ x) (hxd : x ≠ d) (hbd : b ≠ d) :
    (twoEdgeDecomposition x b d hbx hxd hbd).endpointCount v =
      (if b = v then 1 else 0) + (if d = v then 1 else 0) := by
  change (∑ _ : Fin 1, ((if b = v then 1 else 0) + (if d = v then 1 else 0))) = _
  simp

end Gallai
