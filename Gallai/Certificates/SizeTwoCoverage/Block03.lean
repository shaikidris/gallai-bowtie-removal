/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCatalogueRows
import Gallai.Certificates.SizeTwoIndex
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Size-two exhaustive symmetry coverage block 03
Source SHA256 fd5147fd306d683ad48417072994ce74056cad840b5d22648c0687d132a20da6. Literal equalities, checked by ordinary Lean decide.
The anchor action also preserves the normalized syndrome pair.
-/
namespace Gallai.Certificate.SizeTwo.Coverage.Block03
open CompletedStar CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Representative index for each original state. -/
def orbit : Fin 256 → Fin 234 := ![8, 44, 95, 107, 88, 103, 171, 206, 18, 57, 89, 131, 116, 128, 182, 217,
    16, 41, 125, 126, 125, 126, 188, 220, 23, 61, 133, 132, 132, 133, 181, 204,
    4, 54, 120, 122, 119, 121, 185, 222, 22, 63, 130, 130, 129, 129, 169, 216,
    19, 59, 137, 118, 134, 90, 183, 219, 20, 58, 135, 91, 136, 117, 184, 218,
    8, 44, 107, 95, 103, 88, 171, 206, 18, 57, 131, 89, 128, 116, 182, 217,
    23, 61, 132, 133, 133, 132, 181, 204, 16, 41, 126, 125, 126, 125, 188, 220,
    22, 63, 130, 130, 129, 129, 169, 216, 4, 54, 122, 120, 121, 119, 185, 222,
    19, 59, 118, 137, 90, 134, 183, 219, 20, 58, 91, 135, 117, 136, 184, 218,
    12, 48, 110, 110, 110, 110, 167, 209, 21, 60, 131, 131, 131, 131, 180, 203,
    19, 59, 134, 90, 137, 118, 183, 219, 19, 59, 90, 134, 118, 137, 183, 219,
    19, 59, 137, 118, 134, 90, 183, 219, 19, 59, 118, 137, 90, 134, 183, 219,
    5, 55, 123, 123, 123, 123, 186, 223, 17, 42, 127, 127, 127, 127, 189, 221,
    14, 51, 113, 113, 113, 113, 176, 202, 21, 62, 128, 128, 128, 128, 168, 215,
    20, 58, 136, 117, 135, 91, 184, 218, 20, 58, 117, 136, 91, 135, 184, 218,
    20, 58, 135, 91, 136, 117, 184, 218, 20, 58, 91, 135, 117, 136, 184, 218,
    17, 42, 127, 127, 127, 127, 189, 221, 6, 56, 124, 124, 124, 124, 187, 224]
/-- Core row action. -/
def action : Fin 256 → Fin 8 := ![0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 6, 0, 4, 0, 0, 0,
    4, 6, 4, 4, 5, 5, 4, 4, 4, 4, 5, 4, 5, 4, 4, 6,
    6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 4, 5, 4, 6, 4,
    5, 5, 5, 5, 5, 7, 5, 5, 5, 5, 5, 7, 5, 5, 5, 5,
    0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 6, 0, 4, 0, 0,
    4, 4, 4, 5, 4, 5, 4, 6, 4, 6, 4, 4, 5, 5, 4, 4,
    4, 4, 4, 5, 4, 5, 6, 4, 6, 4, 4, 4, 4, 4, 4, 4,
    5, 5, 5, 5, 7, 5, 5, 5, 5, 5, 7, 5, 5, 5, 5, 5,
    0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 4, 4, 4, 4, 4, 6,
    4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4,
    6, 4, 4, 4, 4, 4, 4, 4, 5, 7, 5, 5, 5, 5, 5, 5,
    0, 0, 0, 0, 0, 0, 0, 6, 4, 0, 4, 4, 4, 4, 6, 4,
    4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4,
    4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4,
    4, 6, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 4]
/-- Anchor action, restricted to the pair-preserving subgroup. -/
def permutation : Fin 256 → Fin 24 := ![6, 6, 0, 1, 6, 7, 6, 6, 6, 6, 0, 1, 6, 7, 6, 6,
    0, 0, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    7, 1, 0, 1, 6, 7, 6, 0, 1, 7, 0, 1, 6, 7, 0, 6,
    7, 7, 0, 1, 6, 7, 7, 7, 7, 7, 0, 1, 6, 7, 7, 7,
    0, 0, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    6, 0, 0, 1, 6, 7, 7, 1, 0, 6, 0, 1, 6, 7, 1, 7,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    1, 7, 0, 1, 6, 7, 0, 6, 0, 6, 0, 1, 6, 7, 1, 7,
    7, 1, 0, 1, 6, 7, 6, 0, 6, 0, 0, 1, 6, 7, 7, 1,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    7, 1, 0, 1, 6, 7, 6, 0, 6, 0, 0, 1, 6, 7, 7, 1,
    1, 7, 0, 1, 6, 7, 0, 6, 0, 6, 0, 1, 6, 7, 1, 7,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0]

/-- Every original indexed state is the displayed pair-preserving symmetry image. -/
theorem witness (i : Fin 256) :
    (∀ j : Fin 4, (anchorPermutation (permutation i) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action i) (anchorPermutation (permutation i))
      (SizeTwo.Catalogue.Rows.state (orbit i)) = pairEncodedAt (blockIndex 3 i) := by
  fin_cases i
  all_goals
    refine ⟨by decide, ?_⟩
    funext j
    fin_cases j <;> rfl

end Gallai.Certificate.SizeTwo.Coverage.Block03
