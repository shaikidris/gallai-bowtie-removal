/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarIndex

/-! # Explicit computable anchor permutations for coverage witnesses -/

namespace Gallai.Certificate.CompletedStar.Coverage

/-- Lexicographic old-to-new anchor permutations. -/
def permutationTable (p : Fin 24) : Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3],
    ![0, 1, 3, 2],
    ![0, 2, 1, 3],
    ![0, 2, 3, 1],
    ![0, 3, 1, 2],
    ![0, 3, 2, 1],
    ![1, 0, 2, 3],
    ![1, 0, 3, 2],
    ![1, 2, 0, 3],
    ![1, 2, 3, 0],
    ![1, 3, 0, 2],
    ![1, 3, 2, 0],
    ![2, 0, 1, 3],
    ![2, 0, 3, 1],
    ![2, 1, 0, 3],
    ![2, 1, 3, 0],
    ![2, 3, 0, 1],
    ![2, 3, 1, 0],
    ![3, 0, 1, 2],
    ![3, 0, 2, 1],
    ![3, 1, 0, 2],
    ![3, 1, 2, 0],
    ![3, 2, 0, 1],
    ![3, 2, 1, 0]] p

/-- Literal inverse tables, so witness checking requires no choice reduction. -/
def inverseTable (p : Fin 24) : Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3],
    ![0, 1, 3, 2],
    ![0, 2, 1, 3],
    ![0, 3, 1, 2],
    ![0, 2, 3, 1],
    ![0, 3, 2, 1],
    ![1, 0, 2, 3],
    ![1, 0, 3, 2],
    ![2, 0, 1, 3],
    ![3, 0, 1, 2],
    ![2, 0, 3, 1],
    ![3, 0, 2, 1],
    ![1, 2, 0, 3],
    ![1, 3, 0, 2],
    ![2, 1, 0, 3],
    ![3, 1, 0, 2],
    ![2, 3, 0, 1],
    ![3, 2, 0, 1],
    ![1, 2, 3, 0],
    ![1, 3, 2, 0],
    ![2, 1, 3, 0],
    ![3, 1, 2, 0],
    ![2, 3, 1, 0],
    ![3, 2, 1, 0]] p

/-- Each table entry is a genuine equivalence. -/
def anchorPermutation (p : Fin 24) : Equiv.Perm (Fin 4) where
  toFun := permutationTable p
  invFun := inverseTable p
  left_inv i := by revert p i; decide
  right_inv i := by revert p i; decide

end Gallai.Certificate.CompletedStar.Coverage
