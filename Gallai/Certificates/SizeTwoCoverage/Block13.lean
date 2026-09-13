/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCatalogueRows
import Gallai.Certificates.SizeTwoIndex
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Size-two exhaustive symmetry coverage block 13
Source SHA256 fd5147fd306d683ad48417072994ce74056cad840b5d22648c0687d132a20da6. Literal equalities, checked by ordinary Lean decide.
The anchor action also preserves the normalized syndrome pair.
-/
namespace Gallai.Certificate.SizeTwo.Coverage.Block13
open CompletedStar CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Representative index for each original state. -/
def orbit : Fin 256 → Fin 234 := ![10, 45, 100, 106, 94, 103, 173, 207, 19, 59, 127, 131, 123, 110, 183, 219,
    27, 72, 140, 154, 140, 154, 174, 220, 13, 61, 146, 144, 144, 146, 194, 230,
    26, 68, 149, 160, 139, 153, 185, 210, 22, 49, 151, 151, 143, 143, 193, 228,
    31, 77, 112, 161, 134, 156, 197, 231, 30, 78, 135, 163, 111, 158, 196, 232,
    10, 45, 106, 100, 103, 94, 173, 207, 19, 59, 131, 127, 110, 123, 183, 219,
    13, 61, 144, 146, 146, 144, 194, 230, 27, 72, 154, 140, 154, 140, 174, 220,
    22, 49, 151, 151, 143, 143, 193, 228, 26, 68, 160, 149, 153, 139, 185, 210,
    31, 77, 161, 112, 156, 134, 197, 231, 30, 78, 163, 135, 158, 111, 196, 232,
    12, 47, 112, 112, 112, 112, 175, 211, 12, 60, 134, 134, 134, 134, 186, 221,
    31, 77, 134, 156, 112, 161, 197, 231, 31, 77, 156, 134, 161, 112, 197, 231,
    31, 77, 112, 161, 134, 156, 197, 231, 31, 77, 161, 112, 156, 134, 197, 231,
    33, 80, 161, 161, 161, 161, 186, 211, 33, 82, 156, 156, 156, 156, 175, 221,
    11, 51, 114, 114, 114, 114, 178, 214, 21, 48, 137, 137, 137, 137, 189, 223,
    30, 78, 111, 158, 135, 163, 196, 232, 30, 78, 158, 111, 163, 135, 196, 232,
    30, 78, 135, 163, 111, 158, 196, 232, 30, 78, 163, 135, 158, 111, 196, 232,
    33, 82, 156, 156, 156, 156, 175, 221, 34, 81, 162, 162, 162, 162, 187, 212]
/-- Core row action. -/
def action : Fin 256 → Fin 8 := ![1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 6, 1, 1,
    0, 0, 1, 1, 3, 3, 6, 6, 6, 6, 7, 1, 3, 6, 0, 0,
    0, 0, 1, 1, 1, 1, 6, 6, 6, 6, 3, 1, 3, 1, 0, 0,
    3, 3, 7, 2, 7, 2, 3, 3, 7, 7, 7, 2, 7, 2, 7, 7,
    1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 6, 0, 1, 1,
    6, 6, 1, 7, 6, 3, 0, 0, 0, 0, 1, 1, 3, 3, 6, 6,
    6, 6, 1, 3, 1, 3, 0, 0, 0, 0, 1, 1, 1, 1, 6, 6,
    3, 3, 2, 7, 2, 7, 3, 3, 7, 7, 2, 7, 2, 7, 7, 7,
    1, 1, 1, 1, 1, 1, 0, 0, 6, 1, 1, 1, 1, 1, 0, 0,
    1, 1, 6, 0, 6, 0, 1, 1, 1, 1, 0, 6, 0, 6, 1, 1,
    1, 1, 6, 0, 6, 0, 1, 1, 1, 1, 0, 6, 0, 6, 1, 1,
    0, 0, 6, 6, 6, 6, 6, 6, 5, 2, 7, 7, 7, 7, 7, 7,
    6, 1, 1, 1, 1, 1, 0, 0, 6, 6, 1, 1, 1, 1, 0, 0,
    6, 6, 6, 0, 6, 0, 6, 6, 6, 6, 0, 6, 0, 6, 6, 6,
    6, 6, 6, 0, 6, 0, 6, 6, 6, 6, 0, 6, 0, 6, 6, 6,
    4, 0, 6, 6, 6, 6, 6, 6, 4, 4, 6, 6, 6, 6, 6, 6]
/-- Anchor action, restricted to the pair-preserving subgroup. -/
def permutation : Fin 256 → Fin 24 := ![6, 6, 0, 1, 6, 7, 6, 6, 6, 6, 0, 1, 6, 7, 6, 6,
    0, 0, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    6, 6, 0, 1, 6, 7, 6, 6, 6, 0, 0, 1, 6, 7, 7, 1,
    7, 7, 0, 1, 6, 7, 7, 7, 7, 7, 0, 1, 6, 7, 7, 7,
    0, 0, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    7, 7, 0, 1, 6, 7, 7, 7, 7, 1, 0, 1, 6, 7, 6, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 1, 1, 0, 1, 6, 7, 1, 1,
    6, 6, 0, 1, 6, 7, 6, 6, 7, 7, 0, 1, 6, 7, 7, 7,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0,
    0, 6, 0, 1, 6, 7, 1, 7, 1, 7, 0, 1, 6, 7, 0, 6,
    6, 0, 0, 1, 6, 7, 7, 1, 7, 1, 0, 1, 6, 7, 6, 0,
    0, 0, 0, 1, 6, 7, 0, 0, 0, 0, 0, 1, 6, 7, 0, 0]

/-- Every original indexed state is the displayed pair-preserving symmetry image. -/
theorem witness (i : Fin 256) :
    (∀ j : Fin 4, (anchorPermutation (permutation i) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action i) (anchorPermutation (permutation i))
      (SizeTwo.Catalogue.Rows.state (orbit i)) = pairEncodedAt (blockIndex 13 i) := by
  fin_cases i
  all_goals
    refine ⟨by decide, ?_⟩
    funext j
    fin_cases j <;> rfl

end Gallai.Certificate.SizeTwo.Coverage.Block13
