/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCatalogueRows
import Gallai.Certificates.SizeTwoIndex
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Size-two exhaustive symmetry coverage block 00
Source SHA256 fd5147fd306d683ad48417072994ce74056cad840b5d22648c0687d132a20da6. Literal equalities, checked by ordinary Lean decide.
The anchor action also preserves the normalized syndrome pair.
-/
namespace Gallai.Certificate.SizeTwo.Coverage.Block00
open CompletedStar CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Representative index for each original state. -/
def orbit : Fin 256 → Fin 234 := ![0, 35, 84, 84, 84, 84, 164, 199, 0, 40, 88, 88, 88, 88, 167, 202,
    7, 43, 88, 102, 84, 106, 170, 205, 7, 43, 102, 88, 106, 84, 170, 205,
    7, 43, 84, 106, 88, 102, 170, 205, 7, 43, 106, 84, 102, 88, 170, 205,
    11, 47, 106, 106, 106, 106, 167, 199, 11, 50, 102, 102, 102, 102, 164, 202,
    0, 40, 88, 88, 88, 88, 167, 202, 3, 36, 95, 95, 95, 95, 176, 209,
    8, 44, 85, 110, 89, 113, 171, 206, 8, 44, 110, 85, 113, 89, 171, 206,
    8, 44, 89, 113, 85, 110, 171, 206, 8, 44, 113, 89, 110, 85, 171, 206,
    12, 51, 103, 103, 103, 103, 165, 203, 14, 48, 107, 107, 107, 107, 168, 200,
    7, 43, 88, 102, 84, 106, 170, 205, 8, 44, 85, 110, 89, 113, 171, 206,
    4, 37, 96, 98, 97, 99, 177, 210, 15, 49, 108, 108, 109, 109, 169, 201,
    1, 41, 92, 93, 92, 93, 174, 213, 13, 52, 104, 105, 105, 104, 166, 204,
    10, 45, 114, 90, 112, 87, 173, 207, 9, 46, 111, 86, 115, 91, 172, 208,
    7, 43, 102, 88, 106, 84, 170, 205, 8, 44, 110, 85, 113, 89, 171, 206,
    15, 49, 108, 108, 109, 109, 169, 201, 4, 37, 98, 96, 99, 97, 177, 210,
    13, 52, 105, 104, 104, 105, 166, 204, 1, 41, 93, 92, 93, 92, 174, 213,
    10, 45, 90, 114, 87, 112, 173, 207, 9, 46, 86, 111, 91, 115, 172, 208]
/-- Core row action. -/
def action : Fin 256 → Fin 8 := ![0, 0, 0, 0, 0, 0, 0, 0, 5, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 5, 2, 5, 2, 2, 2, 2, 2, 2, 5, 2, 5, 2, 2,
    2, 2, 5, 2, 5, 2, 2, 2, 2, 2, 2, 5, 2, 5, 2, 2,
    2, 2, 5, 5, 5, 5, 5, 5, 5, 2, 5, 5, 5, 5, 5, 5,
    4, 0, 0, 0, 0, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4,
    5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
    5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
    5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
    0, 0, 4, 0, 4, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 4, 5, 4, 4, 4,
    4, 4, 5, 5, 4, 4, 4, 4, 4, 4, 5, 4, 5, 4, 4, 4,
    5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
    0, 0, 0, 4, 0, 4, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 5, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 5, 4, 5, 4, 4, 4, 4, 5, 5, 4, 4, 4, 4,
    5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]
/-- Anchor action, restricted to the pair-preserving subgroup. -/
def permutation : Fin 256 → Fin 24 := ![0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    0, 6, 0, 1, 6, 7, 1, 7, 1, 7, 0, 1, 6, 7, 0, 6,
    6, 0, 0, 1, 6, 7, 7, 1, 7, 1, 0, 1, 6, 7, 6, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 6, 0, 1, 6, 7, 1, 7,
    0, 0, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    7, 1, 0, 1, 6, 7, 6, 0, 1, 7, 0, 1, 6, 7, 0, 6,
    1, 1, 0, 1, 6, 7, 1, 1, 1, 7, 0, 1, 6, 7, 0, 6,
    0, 0, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    6, 0, 0, 1, 6, 7, 7, 1, 0, 6, 0, 1, 6, 7, 1, 7]

/-- Every original indexed state is the displayed pair-preserving symmetry image. -/
theorem witness (i : Fin 256) :
    (∀ j : Fin 4, (anchorPermutation (permutation i) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action i) (anchorPermutation (permutation i))
      (SizeTwo.Catalogue.Rows.state (orbit i)) = pairEncodedAt (blockIndex 0 i) := by
  fin_cases i
  all_goals
    refine ⟨by decide, ?_⟩
    funext j
    fin_cases j <;> rfl

end Gallai.Certificate.SizeTwo.Coverage.Block00
