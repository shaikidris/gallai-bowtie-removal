/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Expansion.Sharpness
import Gallai.Foundations.PathNumber

/-!
# Sharp full-incidence star expansion

The literal expansion adds four fresh vertices at an arbitrary degree-four
hub of a finite simple graph. One joint witness has the exact size and
endpoint vector. The attained path number gives the minimum-size consequence.
No connectivity or endpoint selection hypothesis is imposed.
-/

namespace Gallai.Star

universe u

variable {V : Type u} {H : SimpleGraph V} [Fintype V] [DecidableEq V]
variable [DecidableRel H.Adj]

/-- Every input decomposition lifts with exactly two additional paths and the stated endpoints. -/
theorem fullIncidence_expansion (D : Decomposition H) (x : V) (hd : H.degree x = 4) :
    ∃ E : Decomposition (expansion H x),
      E.size = D.size + 2 ∧
      (∀ v, v ≠ x → E.endpointCount (Sum.inl v) = D.endpointCount v) ∧
      (D.endpointCount x = 0 → E.endpointCount (Sum.inl x) = 0) ∧
      (D.endpointCount x = 2 → E.endpointCount (Sum.inl x) = 2) ∧
      (D.endpointCount x = 4 → E.endpointCount (Sum.inl x) = 0) := by
  exact ⟨expandDecomposition D x hd, expandDecomposition_size D x hd,
    expandDecomposition_endpointCount_old D x hd,
    expandDecomposition_endpointCount_profiles D x hd⟩

/-- Full-incidence expansion increases the minimum path number by at most two. -/
theorem expansion_pathNumber_le (x : V) (hd : H.degree x = 4) :
    pathNumber (expansion H x) ≤ pathNumber H + 2 :=
  (hasPathBudget_iff_pathNumber_le _).mp
    (expansion_hasPathBudget x hd (pathNumber H) (pathNumber_hasPathBudget H))

/-- The standard four-leaf star has minimum path number two. -/
theorem fourStar_pathNumber : pathNumber (SimpleGraph.starGraph (0 : Fin 5)) = 2 := by
  apply le_antisymm (pathNumber_le_size fourStarDecomposition)
  obtain ⟨D, hD⟩ := exists_minimumDecomposition (SimpleGraph.starGraph (0 : Fin 5))
  exact hD ▸ fourStar_size_lower D

/-- Its full-incidence expansion has minimum path number four. -/
theorem fourStar_expansion_pathNumber :
    pathNumber (expansion (SimpleGraph.starGraph (0 : Fin 5)) 0) = 4 := by
  apply le_antisymm ((hasPathBudget_iff_pathNumber_le 4).mp fourStar_expansion_hasPathBudget)
  obtain ⟨D, hD⟩ :=
    exists_minimumDecomposition (expansion (SimpleGraph.starGraph (0 : Fin 5)) 0)
  exact hD ▸ fourStar_expansion_size_lower D

/-- The additive two in the expansion bound is attained, so additive one is impossible. -/
theorem fullIncidence_expansion_sharp :
    pathNumber (SimpleGraph.starGraph (0 : Fin 5)) = 2 ∧
      pathNumber (expansion (SimpleGraph.starGraph (0 : Fin 5)) 0) = 4 :=
  ⟨fourStar_pathNumber, fourStar_expansion_pathNumber⟩

end Gallai.Star
