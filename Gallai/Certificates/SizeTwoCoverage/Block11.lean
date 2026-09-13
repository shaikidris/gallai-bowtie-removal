/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCatalogueRows
import Gallai.Certificates.SizeTwoIndex
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Size-two exhaustive symmetry coverage block 11
Source SHA256 fd5147fd306d683ad48417072994ce74056cad840b5d22648c0687d132a20da6. Literal equalities, checked by ordinary Lean decide.
The anchor action also preserves the normalized syndrome pair.
-/
namespace Gallai.Certificate.SizeTwo.Coverage.Block11
open CompletedStar CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Representative index for each original state. -/
def orbit : Fin 256 → Fin 234 := ![9, 45, 99, 109, 93, 104, 171, 205, 19, 58, 126, 133, 121, 129, 171, 217,
    25, 71, 141, 126, 140, 93, 192, 227, 29, 76, 133, 145, 104, 146, 191, 227,
    25, 66, 149, 99, 138, 121, 191, 225, 29, 73, 109, 151, 129, 142, 192, 225,
    19, 45, 151, 149, 146, 140, 196, 231, 9, 58, 145, 141, 142, 138, 196, 233,
    8, 43, 109, 97, 105, 92, 172, 207, 8, 57, 132, 125, 129, 119, 183, 218,
    29, 75, 132, 150, 105, 144, 190, 227, 24, 70, 155, 125, 154, 92, 192, 227,
    29, 73, 109, 151, 129, 142, 192, 225, 24, 64, 160, 97, 152, 119, 190, 225,
    30, 77, 160, 151, 154, 144, 183, 207, 30, 79, 155, 150, 152, 142, 172, 218,
    13, 49, 106, 112, 110, 111, 174, 210, 22, 61, 131, 135, 103, 134, 185, 220,
    10, 59, 144, 140, 143, 139, 197, 232, 31, 78, 154, 146, 153, 143, 173, 219,
    19, 45, 151, 149, 146, 140, 196, 231, 30, 77, 160, 151, 154, 144, 183, 207,
    27, 68, 161, 100, 158, 123, 194, 228, 26, 72, 163, 127, 156, 94, 193, 230,
    15, 52, 113, 115, 102, 114, 177, 213, 23, 63, 107, 137, 128, 136, 188, 222,
    20, 46, 147, 148, 150, 141, 198, 232, 32, 78, 157, 147, 155, 145, 184, 208,
    9, 58, 145, 141, 142, 138, 196, 233, 30, 79, 155, 150, 152, 142, 172, 218,
    26, 72, 163, 127, 156, 94, 193, 230, 28, 69, 162, 101, 159, 124, 195, 229]
/-- Core row action. -/
def action : Fin 256 → Fin 8 := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 6, 1,
    5, 1, 0, 6, 2, 7, 3, 1, 7, 0, 7, 0, 7, 4, 4, 6,
    0, 0, 0, 6, 0, 6, 1, 1, 0, 0, 7, 0, 7, 0, 4, 4,
    7, 7, 7, 5, 3, 5, 2, 2, 7, 7, 7, 7, 7, 5, 5, 2,
    1, 1, 1, 0, 1, 0, 0, 0, 6, 1, 1, 1, 1, 0, 0, 0,
    5, 1, 6, 2, 6, 2, 5, 5, 5, 1, 0, 6, 2, 7, 2, 2,
    2, 1, 6, 2, 6, 2, 5, 5, 0, 0, 0, 6, 0, 6, 0, 0,
    2, 2, 5, 5, 5, 5, 7, 7, 5, 2, 7, 5, 5, 5, 7, 7,
    0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0,
    6, 6, 6, 6, 6, 4, 0, 0, 0, 0, 6, 0, 4, 4, 6, 6,
    6, 6, 6, 4, 1, 4, 0, 0, 0, 0, 4, 4, 4, 4, 6, 6,
    4, 4, 4, 6, 4, 6, 4, 4, 5, 5, 5, 7, 5, 7, 5, 5,
    0, 0, 1, 0, 6, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0,
    6, 6, 1, 4, 6, 4, 0, 4, 0, 4, 0, 0, 4, 4, 6, 6,
    6, 6, 6, 6, 6, 4, 4, 0, 4, 0, 6, 4, 4, 4, 6, 6,
    4, 4, 4, 6, 4, 6, 4, 4, 4, 4, 4, 6, 4, 6, 4, 4]
/-- Anchor action, restricted to the pair-preserving subgroup. -/
def permutation : Fin 256 → Fin 24 := ![6, 6, 0, 1, 6, 7, 6, 6, 6, 6, 0, 1, 6, 7, 7, 6,
    7, 0, 0, 1, 6, 7, 6, 0, 6, 1, 0, 1, 6, 7, 7, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    7, 7, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 6,
    7, 7, 0, 1, 6, 7, 7, 7, 7, 7, 0, 1, 6, 7, 7, 7,
    7, 0, 0, 1, 6, 7, 7, 7, 7, 1, 0, 1, 6, 7, 7, 7,
    7, 6, 0, 1, 6, 7, 7, 7, 7, 7, 0, 1, 6, 7, 7, 7,
    7, 7, 0, 1, 6, 7, 7, 7, 7, 7, 0, 1, 6, 7, 7, 7,
    7, 7, 0, 1, 6, 7, 7, 7, 7, 7, 0, 1, 6, 7, 7, 7,
    7, 7, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 7, 7,
    7, 7, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    7, 7, 0, 1, 6, 7, 7, 7, 7, 7, 0, 1, 6, 7, 7, 7,
    7, 7, 0, 1, 6, 7, 7, 7, 7, 7, 0, 1, 6, 7, 7, 7,
    7, 7, 0, 1, 6, 7, 0, 7, 1, 7, 0, 1, 6, 7, 7, 7,
    7, 7, 0, 1, 6, 7, 7, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    7, 7, 0, 1, 6, 7, 7, 7, 7, 7, 0, 1, 6, 7, 7, 7]

/-- Every original indexed state is the displayed pair-preserving symmetry image. -/
theorem witness (i : Fin 256) :
    (∀ j : Fin 4, (anchorPermutation (permutation i) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action i) (anchorPermutation (permutation i))
      (SizeTwo.Catalogue.Rows.state (orbit i)) = pairEncodedAt (blockIndex 11 i) := by
  fin_cases i
  all_goals
    refine ⟨by decide, ?_⟩
    funext j
    fin_cases j <;> rfl

end Gallai.Certificate.SizeTwo.Coverage.Block11
