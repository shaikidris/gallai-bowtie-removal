/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCatalogueRows
import Gallai.Certificates.SizeTwoIndex
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Size-two exhaustive symmetry coverage block 07
Source SHA256 fd5147fd306d683ad48417072994ce74056cad840b5d22648c0687d132a20da6. Literal equalities, checked by ordinary Lean decide.
The anchor action also preserves the normalized syndrome pair.
-/
namespace Gallai.Certificate.SizeTwo.Coverage.Block07
open CompletedStar CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Representative index for each original state. -/
def orbit : Fin 256 → Fin 234 := ![10, 46, 98, 108, 93, 105, 170, 206, 20, 59, 126, 132, 122, 130, 182, 206,
    25, 71, 140, 93, 141, 126, 192, 227, 29, 75, 105, 144, 132, 150, 190, 227,
    25, 67, 148, 122, 139, 98, 190, 226, 29, 74, 130, 147, 108, 143, 192, 226,
    10, 59, 143, 139, 144, 140, 197, 232, 20, 46, 150, 141, 147, 148, 198, 232,
    7, 44, 108, 96, 104, 92, 173, 208, 18, 44, 133, 125, 130, 120, 184, 219,
    29, 76, 104, 146, 133, 145, 191, 227, 24, 70, 154, 92, 155, 125, 192, 227,
    29, 74, 130, 147, 108, 143, 192, 226, 24, 65, 157, 120, 153, 96, 191, 226,
    31, 78, 153, 143, 154, 146, 173, 219, 32, 78, 155, 145, 157, 147, 184, 208,
    13, 49, 110, 111, 106, 112, 174, 210, 22, 61, 103, 134, 131, 135, 185, 220,
    19, 45, 146, 140, 151, 149, 196, 231, 30, 77, 154, 144, 160, 151, 183, 207,
    10, 59, 143, 139, 144, 140, 197, 232, 31, 78, 153, 143, 154, 146, 173, 219,
    27, 68, 158, 123, 161, 100, 194, 228, 26, 72, 156, 94, 163, 127, 193, 230,
    15, 52, 102, 114, 113, 115, 177, 213, 23, 63, 128, 136, 107, 137, 188, 222,
    9, 58, 142, 138, 145, 141, 196, 233, 30, 79, 152, 142, 155, 150, 172, 218,
    20, 46, 150, 141, 147, 148, 198, 232, 32, 78, 155, 145, 157, 147, 184, 208,
    26, 72, 156, 94, 163, 127, 193, 230, 28, 69, 159, 124, 162, 101, 195, 229]
/-- Core row action. -/
def action : Fin 256 → Fin 8 := ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 6,
    4, 0, 0, 6, 2, 7, 1, 3, 4, 0, 7, 0, 7, 0, 4, 4,
    1, 0, 0, 6, 0, 6, 1, 1, 3, 0, 7, 4, 7, 0, 6, 4,
    7, 7, 7, 5, 7, 7, 2, 2, 7, 7, 7, 5, 3, 5, 2, 5,
    1, 1, 1, 0, 1, 1, 0, 0, 1, 6, 1, 0, 1, 0, 0, 0,
    6, 1, 6, 5, 6, 2, 5, 7, 4, 0, 0, 6, 2, 7, 0, 0,
    1, 1, 6, 5, 6, 2, 7, 5, 1, 0, 4, 6, 0, 6, 0, 0,
    2, 2, 5, 5, 7, 2, 7, 7, 2, 5, 5, 5, 2, 2, 7, 7,
    0, 0, 1, 0, 6, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0,
    6, 6, 1, 4, 6, 4, 0, 0, 0, 0, 4, 4, 4, 4, 6, 6,
    6, 6, 6, 4, 6, 6, 0, 0, 0, 0, 4, 4, 6, 0, 6, 6,
    4, 4, 4, 6, 4, 6, 4, 4, 5, 5, 5, 7, 5, 7, 5, 5,
    0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0,
    6, 6, 6, 4, 6, 6, 4, 0, 4, 0, 4, 4, 6, 4, 6, 6,
    6, 6, 6, 4, 1, 4, 0, 4, 0, 4, 4, 4, 0, 0, 6, 6,
    4, 4, 4, 6, 4, 6, 4, 4, 4, 4, 4, 6, 4, 6, 4, 4]
/-- Anchor action, restricted to the pair-preserving subgroup. -/
def permutation : Fin 256 → Fin 24 := ![6, 6, 0, 1, 6, 7, 6, 6, 6, 6, 0, 1, 6, 7, 6, 1,
    1, 0, 0, 1, 6, 7, 0, 6, 1, 1, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 6, 7, 0, 1, 6, 7, 7, 1,
    1, 1, 0, 1, 6, 7, 6, 6, 1, 1, 0, 1, 6, 7, 6, 1,
    7, 7, 0, 1, 6, 7, 7, 7, 7, 1, 0, 1, 6, 7, 7, 7,
    0, 0, 0, 1, 6, 7, 1, 7, 1, 1, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 7, 1, 7, 7, 0, 1, 6, 7, 7, 7,
    7, 7, 0, 1, 6, 7, 1, 1, 7, 1, 0, 1, 6, 7, 1, 1,
    1, 1, 0, 1, 6, 7, 1, 1, 1, 1, 0, 1, 6, 7, 1, 1,
    1, 1, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    1, 1, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 1, 1,
    1, 1, 0, 1, 6, 7, 1, 1, 1, 1, 0, 1, 6, 7, 1, 1,
    1, 1, 0, 1, 6, 7, 1, 1, 1, 1, 0, 1, 6, 7, 1, 1,
    1, 1, 0, 1, 6, 7, 1, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    1, 1, 0, 1, 6, 7, 6, 1, 7, 1, 0, 1, 6, 7, 1, 1,
    1, 1, 0, 1, 6, 7, 1, 1, 1, 1, 0, 1, 6, 7, 1, 1]

/-- Every original indexed state is the displayed pair-preserving symmetry image. -/
theorem witness (i : Fin 256) :
    (∀ j : Fin 4, (anchorPermutation (permutation i) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action i) (anchorPermutation (permutation i))
      (SizeTwo.Catalogue.Rows.state (orbit i)) = pairEncodedAt (blockIndex 7 i) := by
  fin_cases i
  all_goals
    refine ⟨by decide, ?_⟩
    funext j
    fin_cases j <;> rfl

end Gallai.Certificate.SizeTwo.Coverage.Block07
