/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCatalogueRows
import Gallai.Certificates.SizeTwoIndex
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Size-two exhaustive symmetry coverage block 06
Source SHA256 fd5147fd306d683ad48417072994ce74056cad840b5d22648c0687d132a20da6. Literal equalities, checked by ordinary Lean decide.
The anchor action also preserves the normalized syndrome pair.
-/
namespace Gallai.Certificate.SizeTwo.Coverage.Block06
open CompletedStar CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Representative index for each original state. -/
def orbit : Fin 256 → Fin 234 := ![1, 37, 86, 85, 87, 84, 166, 201, 4, 41, 90, 88, 91, 89, 169, 204,
    9, 45, 93, 104, 99, 109, 171, 205, 8, 43, 105, 92, 109, 97, 172, 207,
    10, 46, 98, 108, 93, 105, 170, 206, 7, 44, 108, 96, 104, 92, 173, 208,
    13, 49, 110, 111, 106, 112, 174, 210, 15, 52, 102, 114, 113, 115, 177, 213,
    4, 41, 90, 88, 91, 89, 169, 204, 16, 54, 117, 116, 118, 95, 181, 216,
    19, 58, 121, 129, 126, 133, 171, 217, 8, 57, 129, 119, 132, 125, 183, 218,
    20, 59, 126, 132, 122, 130, 182, 206, 18, 44, 133, 125, 130, 120, 184, 219,
    22, 61, 103, 134, 131, 135, 185, 220, 23, 63, 128, 136, 107, 137, 188, 222,
    9, 45, 93, 104, 99, 109, 171, 205, 19, 58, 121, 129, 126, 133, 171, 217,
    25, 66, 138, 121, 149, 99, 191, 225, 29, 73, 129, 142, 109, 151, 192, 225,
    25, 71, 140, 93, 141, 126, 192, 227, 29, 76, 104, 146, 133, 145, 191, 227,
    19, 45, 146, 140, 151, 149, 196, 231, 9, 58, 142, 138, 145, 141, 196, 233,
    8, 43, 105, 92, 109, 97, 172, 207, 8, 57, 129, 119, 132, 125, 183, 218,
    29, 73, 129, 142, 109, 151, 192, 225, 24, 64, 152, 119, 160, 97, 190, 225,
    29, 75, 105, 144, 132, 150, 190, 227, 24, 70, 154, 92, 155, 125, 192, 227,
    30, 77, 154, 144, 160, 151, 183, 207, 30, 79, 152, 142, 155, 150, 172, 218]
/-- Core row action. -/
def action : Fin 256 → Fin 8 := ![0, 0, 0, 1, 0, 1, 0, 0, 2, 2, 2, 3, 2, 3, 2, 2,
    2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 2, 3, 2, 2, 2,
    2, 2, 2, 2, 3, 2, 3, 3, 3, 3, 3, 2, 3, 3, 2, 2,
    2, 2, 3, 2, 7, 2, 2, 2, 2, 2, 7, 2, 3, 2, 2, 2,
    0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 6, 0, 0,
    2, 2, 2, 2, 3, 2, 7, 3, 7, 3, 3, 2, 3, 3, 2, 2,
    2, 2, 2, 2, 2, 2, 3, 7, 3, 7, 3, 2, 3, 2, 2, 2,
    2, 2, 7, 2, 7, 2, 2, 2, 2, 2, 7, 2, 7, 2, 2, 2,
    0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 6, 1,
    0, 0, 0, 6, 0, 6, 1, 1, 0, 0, 7, 0, 7, 0, 4, 4,
    5, 1, 2, 7, 0, 6, 3, 1, 7, 0, 7, 4, 7, 0, 4, 6,
    7, 7, 3, 5, 7, 5, 2, 2, 7, 7, 7, 5, 7, 7, 5, 2,
    1, 1, 1, 0, 1, 0, 0, 0, 6, 1, 1, 0, 1, 1, 0, 0,
    2, 1, 6, 2, 6, 2, 5, 5, 0, 0, 0, 6, 0, 6, 0, 0,
    5, 1, 6, 2, 6, 2, 5, 5, 5, 1, 2, 7, 0, 6, 2, 2,
    2, 2, 5, 5, 5, 5, 7, 7, 5, 2, 5, 5, 7, 5, 7, 7]
/-- Anchor action, restricted to the pair-preserving subgroup. -/
def permutation : Fin 256 → Fin 24 := ![1, 1, 0, 1, 6, 7, 1, 1, 1, 1, 0, 1, 6, 7, 1, 1,
    0, 0, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    1, 1, 0, 1, 6, 7, 1, 1, 1, 1, 0, 1, 6, 7, 1, 1,
    1, 1, 0, 1, 6, 7, 1, 1, 1, 1, 0, 1, 6, 7, 1, 1,
    0, 0, 0, 1, 6, 7, 1, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 6, 1, 7, 1, 0, 1, 6, 7, 7, 7,
    1, 1, 0, 1, 6, 7, 1, 1, 1, 1, 0, 1, 6, 7, 1, 1,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 1, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    1, 6, 0, 1, 6, 7, 0, 6, 0, 7, 0, 1, 6, 7, 1, 7,
    1, 1, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 1, 0,
    1, 1, 0, 1, 6, 7, 1, 1, 1, 1, 0, 1, 6, 7, 1, 1,
    1, 0, 0, 1, 6, 7, 1, 1, 1, 1, 0, 1, 6, 7, 1, 1,
    1, 6, 0, 1, 6, 7, 1, 1, 1, 7, 0, 1, 6, 7, 1, 1,
    1, 1, 0, 1, 6, 7, 1, 1, 1, 1, 0, 1, 6, 7, 1, 1]

/-- Every original indexed state is the displayed pair-preserving symmetry image. -/
theorem witness (i : Fin 256) :
    (∀ j : Fin 4, (anchorPermutation (permutation i) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action i) (anchorPermutation (permutation i))
      (SizeTwo.Catalogue.Rows.state (orbit i)) = pairEncodedAt (blockIndex 6 i) := by
  fin_cases i
  all_goals
    refine ⟨by decide, ?_⟩
    funext j
    fin_cases j <;> rfl

end Gallai.Certificate.SizeTwo.Coverage.Block06
