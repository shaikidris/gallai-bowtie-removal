/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCatalogueRows
import Gallai.Certificates.SizeTwoIndex
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Size-two exhaustive symmetry coverage block 05
Source SHA256 fd5147fd306d683ad48417072994ce74056cad840b5d22648c0687d132a20da6. Literal equalities, checked by ordinary Lean decide.
The anchor action also preserves the normalized syndrome pair.
-/
namespace Gallai.Certificate.SizeTwo.Coverage.Block05
open CompletedStar CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Representative index for each original state. -/
def orbit : Fin 256 → Fin 234 := ![7, 44, 96, 108, 92, 104, 173, 208, 18, 44, 125, 133, 120, 130, 184, 219,
    24, 70, 92, 154, 125, 155, 192, 227, 29, 76, 146, 104, 145, 133, 191, 227,
    24, 65, 120, 157, 96, 153, 191, 226, 29, 74, 147, 130, 143, 108, 192, 226,
    31, 78, 143, 153, 146, 154, 173, 219, 32, 78, 145, 155, 147, 157, 184, 208,
    10, 46, 108, 98, 105, 93, 170, 206, 20, 59, 132, 126, 130, 122, 182, 206,
    29, 75, 144, 105, 150, 132, 190, 227, 25, 71, 93, 140, 126, 141, 192, 227,
    29, 74, 147, 130, 143, 108, 192, 226, 25, 67, 122, 148, 98, 139, 190, 226,
    10, 59, 139, 143, 140, 144, 197, 232, 20, 46, 141, 150, 148, 147, 198, 232,
    13, 49, 111, 110, 112, 106, 174, 210, 22, 61, 134, 103, 135, 131, 185, 220,
    30, 77, 144, 154, 151, 160, 183, 207, 19, 45, 140, 146, 149, 151, 196, 231,
    31, 78, 143, 153, 146, 154, 173, 219, 10, 59, 139, 143, 140, 144, 197, 232,
    27, 68, 123, 158, 100, 161, 194, 228, 26, 72, 94, 156, 127, 163, 193, 230,
    15, 52, 114, 102, 115, 113, 177, 213, 23, 63, 136, 128, 137, 107, 188, 222,
    30, 79, 142, 152, 150, 155, 172, 218, 9, 58, 138, 142, 141, 145, 196, 233,
    32, 78, 145, 155, 147, 157, 184, 208, 20, 46, 141, 150, 148, 147, 198, 232,
    26, 72, 94, 156, 127, 163, 193, 230, 28, 69, 124, 159, 101, 162, 195, 229]
/-- Core row action. -/
def action : Fin 256 → Fin 8 := ![1, 1, 0, 1, 1, 1, 0, 0, 1, 6, 0, 1, 0, 1, 0, 0,
    4, 0, 6, 0, 7, 2, 0, 0, 6, 1, 5, 6, 2, 6, 5, 7,
    1, 0, 6, 4, 6, 0, 0, 0, 1, 1, 5, 6, 2, 6, 7, 5,
    2, 2, 5, 5, 2, 7, 7, 7, 2, 5, 5, 5, 2, 2, 7, 7,
    0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 6,
    4, 0, 0, 7, 0, 7, 4, 4, 4, 0, 6, 0, 7, 2, 1, 3,
    3, 0, 4, 7, 0, 7, 6, 4, 1, 0, 6, 0, 6, 0, 1, 1,
    7, 7, 5, 7, 7, 7, 2, 2, 7, 7, 5, 7, 5, 3, 2, 5,
    0, 0, 0, 1, 0, 6, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0,
    0, 0, 4, 4, 4, 4, 6, 6, 6, 6, 4, 1, 4, 6, 0, 0,
    0, 0, 4, 4, 0, 6, 6, 6, 6, 6, 4, 6, 6, 6, 0, 0,
    4, 4, 6, 4, 6, 4, 4, 4, 5, 5, 7, 5, 7, 5, 5, 5,
    0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0,
    4, 0, 4, 4, 4, 6, 6, 6, 6, 6, 4, 6, 6, 6, 4, 0,
    0, 4, 4, 4, 0, 0, 6, 6, 6, 6, 4, 6, 4, 1, 0, 4,
    4, 4, 6, 4, 6, 4, 4, 4, 4, 4, 6, 4, 6, 4, 4, 4]
/-- Anchor action, restricted to the pair-preserving subgroup. -/
def permutation : Fin 256 → Fin 24 := ![6, 6, 0, 1, 6, 7, 6, 6, 6, 0, 0, 1, 6, 7, 6, 6,
    0, 0, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 0, 6,
    6, 6, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 6, 0,
    6, 6, 0, 1, 6, 7, 0, 0, 6, 0, 0, 1, 6, 7, 0, 0,
    7, 7, 0, 1, 6, 7, 7, 7, 7, 7, 0, 1, 6, 7, 7, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 1, 0, 1, 6, 7, 1, 7,
    7, 6, 0, 1, 6, 7, 6, 0, 7, 7, 0, 1, 6, 7, 7, 7,
    0, 0, 0, 1, 6, 7, 7, 7, 0, 0, 0, 1, 6, 7, 7, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 7, 7,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 1,
    6, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 7, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0]

/-- Every original indexed state is the displayed pair-preserving symmetry image. -/
theorem witness (i : Fin 256) :
    (∀ j : Fin 4, (anchorPermutation (permutation i) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action i) (anchorPermutation (permutation i))
      (SizeTwo.Catalogue.Rows.state (orbit i)) = pairEncodedAt (blockIndex 5 i) := by
  fin_cases i
  all_goals
    refine ⟨by decide, ?_⟩
    funext j
    fin_cases j <;> rfl

end Gallai.Certificate.SizeTwo.Coverage.Block05
