/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarCatalogue
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Exhaustive coverage witnesses, block 12

Generated from certificate SHA256 4dbb85f7bef9f06a6b4701c7bd611c60507ecedfcf83c46b2c6b1a44828f513d.
All 256 literal transformed-state equalities are checked by ordinary Lean decide.
-/

namespace Gallai.Certificate.CompletedStar.Coverage.Block12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Stored representative index. -/
def orbit : Fin 256 → Fin 67 :=
  ![1, 13, 15, 15, 15, 15, 14, 49, 2, 17, 20, 20, 20, 20, 23, 53,
    4, 21, 18, 22, 19, 24, 20, 52, 4, 21, 22, 18, 24, 19, 20, 52,
    4, 21, 19, 24, 18, 22, 20, 52, 4, 21, 24, 19, 22, 18, 20, 52,
    3, 25, 21, 21, 21, 21, 17, 51, 5, 28, 27, 27, 27, 27, 16, 55,
    2, 17, 20, 20, 20, 20, 23, 53, 7, 23, 40, 40, 40, 40, 37, 58,
    9, 33, 20, 40, 41, 46, 33, 62, 9, 33, 40, 20, 46, 41, 33, 62,
    9, 33, 41, 46, 20, 40, 33, 62, 9, 33, 46, 41, 40, 20, 33, 62,
    7, 35, 41, 41, 41, 41, 17, 63, 12, 37, 46, 46, 46, 46, 35, 53,
    4, 21, 18, 22, 19, 24, 20, 52, 9, 33, 20, 40, 41, 46, 33, 62,
    8, 24, 30, 40, 39, 42, 36, 57, 10, 42, 33, 33, 45, 45, 34, 52,
    4, 34, 31, 33, 31, 33, 30, 61, 8, 44, 34, 41, 41, 34, 18, 64,
    9, 45, 32, 41, 39, 21, 31, 60, 10, 46, 36, 22, 47, 44, 32, 61,
    4, 21, 22, 18, 24, 19, 20, 52, 9, 33, 40, 20, 46, 41, 33, 62,
    10, 42, 33, 33, 45, 45, 34, 52, 8, 24, 40, 30, 42, 39, 36, 57,
    8, 44, 41, 34, 34, 41, 18, 64, 4, 34, 33, 31, 33, 31, 30, 61,
    9, 45, 41, 32, 21, 39, 31, 60, 10, 46, 22, 36, 44, 47, 32, 61]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Core action index, in the verifier's new-to-old row convention. -/
def action : Fin 256 → Fin 8 :=
  ![0, 1, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 3, 3, 2, 2,
    2, 3, 2, 2, 3, 2, 2, 2, 2, 3, 2, 2, 2, 3, 2, 2,
    2, 3, 3, 2, 2, 2, 2, 2, 2, 3, 2, 3, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 7, 2,
    1, 1, 1, 1, 1, 1, 0, 0, 1, 6, 1, 1, 1, 1, 4, 0,
    1, 3, 6, 4, 3, 2, 4, 0, 1, 3, 4, 6, 2, 3, 4, 0,
    1, 3, 3, 2, 6, 4, 4, 0, 1, 3, 2, 3, 4, 6, 4, 0,
    4, 2, 4, 4, 4, 4, 6, 0, 2, 2, 5, 5, 5, 5, 5, 7,
    0, 1, 0, 0, 1, 0, 0, 0, 3, 1, 7, 5, 1, 0, 5, 1,
    0, 6, 0, 0, 1, 4, 4, 0, 0, 0, 2, 0, 2, 0, 4, 6,
    6, 6, 3, 7, 1, 6, 4, 0, 4, 0, 2, 7, 6, 0, 6, 0,
    0, 3, 2, 0, 4, 6, 0, 0, 5, 7, 2, 7, 2, 5, 5, 5,
    0, 1, 0, 0, 0, 1, 0, 0, 3, 1, 5, 7, 0, 1, 5, 1,
    0, 0, 0, 2, 0, 2, 4, 6, 0, 6, 0, 0, 4, 1, 4, 0,
    4, 0, 7, 2, 0, 6, 6, 0, 6, 6, 7, 3, 6, 1, 4, 0,
    0, 3, 0, 2, 6, 4, 0, 0, 5, 7, 7, 2, 5, 2, 5, 5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Computable anchor permutation index. -/
def permutation : Fin 256 → Fin 24 :=
  ![16, 0, 13, 19, 15, 21, 16, 16, 0, 0, 2, 4, 8, 10, 16, 0,
    13, 0, 13, 5, 14, 21, 16, 13, 19, 1, 3, 19, 15, 20, 22, 19,
    15, 6, 12, 19, 15, 11, 17, 15, 21, 7, 13, 18, 9, 21, 23, 21,
    16, 0, 13, 19, 15, 21, 16, 16, 16, 0, 13, 19, 15, 21, 16, 16,
    0, 0, 2, 4, 8, 10, 16, 0, 0, 0, 2, 4, 8, 10, 16, 0,
    2, 0, 13, 19, 8, 10, 22, 2, 4, 1, 13, 19, 8, 10, 16, 4,
    8, 6, 2, 4, 15, 21, 23, 8, 10, 7, 2, 4, 15, 21, 17, 10,
    16, 0, 13, 19, 15, 21, 16, 16, 0, 0, 13, 19, 15, 21, 16, 16,
    13, 0, 13, 5, 14, 21, 16, 13, 2, 0, 13, 19, 8, 10, 22, 0,
    13, 0, 13, 5, 14, 21, 16, 13, 5, 1, 3, 5, 14, 20, 22, 22,
    17, 6, 12, 19, 14, 21, 17, 14, 23, 7, 13, 5, 9, 21, 23, 21,
    16, 0, 13, 19, 15, 21, 16, 16, 22, 7, 13, 19, 14, 21, 16, 17,
    19, 1, 3, 19, 15, 20, 22, 19, 4, 1, 13, 19, 8, 10, 16, 1,
    3, 0, 3, 5, 14, 20, 16, 16, 19, 1, 3, 19, 15, 20, 22, 19,
    17, 6, 3, 19, 15, 11, 17, 15, 23, 7, 13, 18, 15, 20, 23, 20,
    22, 1, 13, 19, 15, 21, 22, 22, 16, 6, 13, 19, 15, 20, 22, 23]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every indexed state in this block has the displayed symmetry witness. -/
theorem witness (i : Fin 256) :
    transformedState (action i) (anchorPermutation (permutation i))
      (Catalogue.state (orbit i)) = encodedAt (blockIndex 12 i) := by
  revert i
  decide

end Gallai.Certificate.CompletedStar.Coverage.Block12
