/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCatalogueRows
import Gallai.Certificates.SizeTwoIndex
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Size-two exhaustive symmetry coverage block 02
Source SHA256 fd5147fd306d683ad48417072994ce74056cad840b5d22648c0687d132a20da6. Literal equalities, checked by ordinary Lean decide.
The anchor action also preserves the normalized syndrome pair.
-/
namespace Gallai.Certificate.SizeTwo.Coverage.Block02
open CompletedStar CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Representative index for each original state. -/
def orbit : Fin 256 → Fin 234 := ![0, 36, 85, 85, 85, 85, 165, 200, 3, 40, 89, 89, 89, 89, 168, 203,
    8, 44, 88, 103, 95, 107, 171, 206, 8, 44, 103, 88, 107, 95, 171, 206,
    8, 44, 95, 107, 88, 103, 171, 206, 8, 44, 107, 95, 103, 88, 171, 206,
    12, 48, 110, 110, 110, 110, 167, 209, 14, 51, 113, 113, 113, 113, 176, 202,
    3, 40, 89, 89, 89, 89, 168, 203, 3, 53, 116, 116, 116, 116, 180, 215,
    18, 57, 116, 128, 89, 131, 182, 217, 18, 57, 128, 116, 131, 89, 182, 217,
    18, 57, 89, 131, 116, 128, 182, 217, 18, 57, 131, 89, 128, 116, 182, 217,
    21, 60, 131, 131, 131, 131, 180, 203, 21, 62, 128, 128, 128, 128, 168, 215,
    8, 44, 88, 103, 95, 107, 171, 206, 18, 57, 116, 128, 89, 131, 182, 217,
    4, 54, 119, 121, 120, 122, 185, 222, 22, 63, 129, 129, 130, 130, 169, 216,
    16, 41, 125, 126, 125, 126, 188, 220, 23, 61, 132, 133, 133, 132, 181, 204,
    19, 59, 134, 90, 137, 118, 183, 219, 20, 58, 136, 117, 135, 91, 184, 218,
    8, 44, 103, 88, 107, 95, 171, 206, 18, 57, 128, 116, 131, 89, 182, 217,
    22, 63, 129, 129, 130, 130, 169, 216, 4, 54, 121, 119, 122, 120, 185, 222,
    23, 61, 133, 132, 132, 133, 181, 204, 16, 41, 126, 125, 126, 125, 188, 220,
    19, 59, 90, 134, 118, 137, 183, 219, 20, 58, 117, 136, 91, 135, 184, 218]
/-- Core row action. -/
def action : Fin 256 → Fin 8 := ![1, 0, 0, 0, 0, 0, 0, 0, 2, 3, 2, 2, 2, 2, 2, 2,
    2, 2, 7, 2, 2, 2, 2, 2, 2, 2, 2, 7, 2, 2, 2, 2,
    2, 2, 2, 2, 7, 2, 2, 2, 2, 2, 2, 2, 2, 7, 2, 2,
    2, 2, 2, 2, 2, 2, 7, 2, 2, 2, 2, 2, 2, 2, 2, 7,
    0, 1, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0,
    2, 2, 5, 2, 7, 2, 2, 2, 2, 2, 2, 5, 2, 7, 2, 2,
    2, 2, 7, 2, 5, 2, 2, 2, 2, 2, 2, 7, 2, 5, 2, 2,
    2, 2, 5, 5, 5, 5, 5, 7, 5, 2, 5, 5, 5, 5, 7, 5,
    0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 4, 0, 6, 0, 0, 0,
    6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 4, 5, 4, 6, 4,
    4, 6, 5, 5, 4, 4, 4, 4, 4, 4, 5, 4, 5, 4, 4, 6,
    5, 5, 5, 7, 5, 5, 5, 5, 5, 5, 5, 5, 5, 7, 5, 5,
    0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 4, 0, 6, 0, 0,
    4, 4, 4, 5, 4, 5, 6, 4, 6, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 5, 4, 5, 4, 6, 4, 6, 5, 5, 4, 4, 4, 4,
    5, 5, 7, 5, 5, 5, 5, 5, 5, 5, 5, 5, 7, 5, 5, 5]
/-- Anchor action, restricted to the pair-preserving subgroup. -/
def permutation : Fin 256 → Fin 24 := ![0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    1, 7, 0, 1, 6, 7, 0, 6, 7, 1, 0, 1, 6, 7, 6, 0,
    1, 1, 0, 1, 6, 7, 1, 1, 1, 1, 0, 1, 6, 7, 1, 1,
    0, 0, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    0, 6, 0, 1, 6, 7, 1, 7, 6, 0, 0, 1, 6, 7, 7, 1]

/-- Every original indexed state is the displayed pair-preserving symmetry image. -/
theorem witness (i : Fin 256) :
    (∀ j : Fin 4, (anchorPermutation (permutation i) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action i) (anchorPermutation (permutation i))
      (SizeTwo.Catalogue.Rows.state (orbit i)) = pairEncodedAt (blockIndex 2 i) := by
  fin_cases i
  all_goals
    refine ⟨by decide, ?_⟩
    funext j
    fin_cases j <;> rfl

end Gallai.Certificate.SizeTwo.Coverage.Block02
