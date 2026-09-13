/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCatalogueRows
import Gallai.Certificates.SizeTwoIndex
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Size-two exhaustive symmetry coverage block 09
Source SHA256 fd5147fd306d683ad48417072994ce74056cad840b5d22648c0687d132a20da6. Literal equalities, checked by ordinary Lean decide.
The anchor action also preserves the normalized syndrome pair.
-/
namespace Gallai.Certificate.SizeTwo.Coverage.Block09
open CompletedStar CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Representative index for each original state. -/
def orbit : Fin 256 → Fin 234 := ![8, 43, 97, 109, 92, 105, 172, 207, 8, 57, 125, 132, 119, 129, 183, 218,
    24, 70, 125, 155, 92, 154, 192, 227, 29, 75, 150, 132, 144, 105, 190, 227,
    24, 64, 97, 160, 119, 152, 190, 225, 29, 73, 151, 109, 142, 129, 192, 225,
    30, 77, 151, 160, 144, 154, 183, 207, 30, 79, 150, 155, 142, 152, 172, 218,
    9, 45, 109, 99, 104, 93, 171, 205, 19, 58, 133, 126, 129, 121, 171, 217,
    29, 76, 145, 133, 146, 104, 191, 227, 25, 71, 126, 141, 93, 140, 192, 227,
    29, 73, 151, 109, 142, 129, 192, 225, 25, 66, 99, 149, 121, 138, 191, 225,
    19, 45, 149, 151, 140, 146, 196, 231, 9, 58, 141, 145, 138, 142, 196, 233,
    13, 49, 112, 106, 111, 110, 174, 210, 22, 61, 135, 131, 134, 103, 185, 220,
    31, 78, 146, 154, 143, 153, 173, 219, 10, 59, 140, 144, 139, 143, 197, 232,
    30, 77, 151, 160, 144, 154, 183, 207, 19, 45, 149, 151, 140, 146, 196, 231,
    27, 68, 100, 161, 123, 158, 194, 228, 26, 72, 127, 163, 94, 156, 193, 230,
    15, 52, 115, 113, 114, 102, 177, 213, 23, 63, 137, 107, 136, 128, 188, 222,
    32, 78, 147, 157, 145, 155, 184, 208, 20, 46, 148, 147, 141, 150, 198, 232,
    30, 79, 150, 155, 142, 152, 172, 218, 9, 58, 141, 145, 138, 142, 196, 233,
    26, 72, 127, 163, 94, 156, 193, 230, 28, 69, 101, 162, 124, 159, 195, 229]
/-- Core row action. -/
def action : Fin 256 → Fin 8 := ![1, 1, 0, 1, 0, 1, 0, 0, 6, 1, 1, 1, 0, 1, 0, 0,
    5, 1, 6, 0, 7, 2, 2, 2, 5, 1, 2, 6, 2, 6, 5, 5,
    0, 0, 6, 0, 6, 0, 0, 0, 2, 1, 2, 6, 2, 6, 5, 5,
    2, 2, 5, 5, 5, 5, 7, 7, 5, 2, 5, 7, 5, 5, 7, 7,
    0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 6, 1,
    7, 0, 0, 7, 4, 7, 4, 6, 5, 1, 6, 0, 7, 2, 3, 1,
    0, 0, 0, 7, 0, 7, 4, 4, 0, 0, 6, 0, 6, 0, 1, 1,
    7, 7, 5, 7, 5, 3, 2, 2, 7, 7, 7, 7, 5, 7, 5, 2,
    0, 0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0,
    0, 0, 0, 6, 4, 4, 6, 6, 6, 6, 6, 6, 4, 6, 0, 0,
    0, 0, 4, 4, 4, 4, 6, 6, 6, 6, 4, 6, 4, 1, 0, 0,
    4, 4, 6, 4, 6, 4, 4, 4, 5, 5, 7, 5, 7, 5, 5, 5,
    0, 0, 0, 1, 0, 6, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0,
    0, 4, 0, 0, 4, 4, 6, 6, 6, 6, 4, 1, 4, 6, 0, 4,
    4, 0, 4, 6, 4, 4, 6, 6, 6, 6, 6, 6, 4, 6, 4, 0,
    4, 4, 6, 4, 6, 4, 4, 4, 4, 4, 6, 4, 6, 4, 4, 4]
/-- Anchor action, restricted to the pair-preserving subgroup. -/
def permutation : Fin 256 → Fin 24 := ![6, 6, 0, 1, 6, 7, 6, 6, 6, 6, 0, 1, 6, 7, 6, 6,
    6, 0, 0, 1, 6, 7, 6, 6, 6, 1, 0, 1, 6, 7, 6, 6,
    6, 6, 0, 1, 6, 7, 6, 6, 6, 7, 0, 1, 6, 7, 6, 6,
    6, 6, 0, 1, 6, 7, 6, 6, 6, 6, 0, 1, 6, 7, 6, 6,
    7, 7, 0, 1, 6, 7, 7, 7, 7, 7, 0, 1, 6, 7, 6, 7,
    7, 0, 0, 1, 6, 7, 6, 0, 6, 1, 0, 1, 6, 7, 7, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    6, 6, 0, 1, 6, 7, 7, 7, 6, 6, 0, 1, 6, 7, 6, 7,
    6, 6, 0, 1, 6, 7, 6, 6, 6, 6, 0, 1, 6, 7, 6, 6,
    0, 0, 0, 1, 6, 7, 6, 6, 6, 6, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 6, 6, 0, 1, 6, 7, 7, 7,
    6, 6, 0, 1, 6, 7, 6, 6, 6, 6, 0, 1, 6, 7, 6, 6,
    6, 6, 0, 1, 6, 7, 6, 6, 6, 6, 0, 1, 6, 7, 6, 6,
    0, 6, 0, 1, 6, 7, 6, 6, 6, 6, 0, 1, 6, 7, 1, 6,
    6, 6, 0, 1, 6, 7, 6, 6, 6, 6, 0, 1, 6, 7, 6, 7,
    6, 6, 0, 1, 6, 7, 6, 6, 6, 6, 0, 1, 6, 7, 6, 6]

/-- Every original indexed state is the displayed pair-preserving symmetry image. -/
theorem witness (i : Fin 256) :
    (∀ j : Fin 4, (anchorPermutation (permutation i) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action i) (anchorPermutation (permutation i))
      (SizeTwo.Catalogue.Rows.state (orbit i)) = pairEncodedAt (blockIndex 9 i) := by
  fin_cases i
  all_goals
    refine ⟨by decide, ?_⟩
    funext j
    fin_cases j <;> rfl

end Gallai.Certificate.SizeTwo.Coverage.Block09
