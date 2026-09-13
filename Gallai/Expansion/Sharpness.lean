/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Expansion.Endpoints
import Gallai.Foundations.Capacity
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Algebra.BigOperators.Fin

/-!
# Sharpness on the four-leaf star

The standard star on five vertices has a two-path decomposition and requires
at least two paths. Its full-incidence expansion has twenty-six edges on nine
vertices, requires at least four paths by capacity, and attains four via the
same all-order construction. This proves the additive loss cannot be one.
-/

namespace Gallai.Star

open scoped Finset

/-- First two-spoke carrier in the standard four-leaf star. -/
def fourStarFirst : NonemptyPath (SimpleGraph.starGraph (0 : Fin 5)) where
  start := 1
  finish := 2
  walk := .cons (v := 0) (by decide) (.cons (by decide) .nil)
  isPath := SimpleGraph.Walk.IsPath.mk' (by decide)
  nonempty := by decide

/-- Second two-spoke carrier in the standard four-leaf star. -/
def fourStarSecond : NonemptyPath (SimpleGraph.starGraph (0 : Fin 5)) where
  start := 3
  finish := 4
  walk := .cons (v := 0) (by decide) (.cons (by decide) .nil)
  isPath := SimpleGraph.Walk.IsPath.mk' (by decide)
  nonempty := by decide

/-- An explicit two-path edge decomposition of the four-leaf star. -/
def fourStarDecomposition : Decomposition (SimpleGraph.starGraph (0 : Fin 5)) where
  size := 2
  path := fun i => if i = 0 then fourStarFirst else fourStarSecond
  covers := by
    simp only [ExistsUnique]
    decide

/-- Four odd leaves force at least two paths in every decomposition of this star. -/
theorem fourStar_size_lower (D : Decomposition (SimpleGraph.starGraph (0 : Fin 5))) :
    2 ≤ D.size := by
  have hs := D.sum_endpointCount
  have h1 := D.endpointCount_pos_of_odd_degree 1 (by decide)
  have h2 := D.endpointCount_pos_of_odd_degree 2 (by decide)
  have h3 := D.endpointCount_pos_of_odd_degree 3 (by decide)
  have h4 := D.endpointCount_pos_of_odd_degree 4 (by decide)
  simp [Fin.sum_univ_succ] at hs
  change D.endpointCount 0 + (D.endpointCount 1 + (D.endpointCount 2 +
    (D.endpointCount 3 + D.endpointCount 4))) = 2 * D.size at hs
  omega

/-- The literal expanded sharpness graph has twenty-six edges. -/
theorem fourStar_expansion_edges :
    #(expansion (SimpleGraph.starGraph (0 : Fin 5)) 0).edgeFinset = 26 := by decide

/-- Edge capacity forces at least four paths in every decomposition of the expansion. -/
theorem fourStar_expansion_size_lower
    (D : Decomposition (expansion (SimpleGraph.starGraph (0 : Fin 5)) 0)) :
    4 ≤ D.size := by
  have hc := D.edge_capacity
  rw [fourStar_expansion_edges] at hc
  have hn : Fintype.card (Fin 5 ⊕ Fin 4) = 9 := by decide
  rw [hn] at hc
  omega

/-- The expansion attains the sharp four-path bound. -/
theorem fourStar_expansion_hasPathBudget :
    HasPathBudget (expansion (SimpleGraph.starGraph (0 : Fin 5)) 0) 4 := by
  exact ⟨expandDecomposition fourStarDecomposition 0 (by decide), by
    rw [expandDecomposition_size]; exact Nat.le_refl 4⟩

/-- The star has budget two but its expansion does not have budget three. -/
theorem expansion_additive_two_sharp :
    HasPathBudget (SimpleGraph.starGraph (0 : Fin 5)) 2 ∧
      ¬ HasPathBudget (expansion (SimpleGraph.starGraph (0 : Fin 5)) 0) 3 := by
  refine ⟨⟨fourStarDecomposition, Nat.le_refl 2⟩, ?_⟩
  rintro ⟨D, hD⟩
  have h := fourStar_expansion_size_lower D
  omega

end Gallai.Star
