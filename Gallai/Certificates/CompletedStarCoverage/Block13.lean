/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarCatalogue
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Exhaustive coverage witnesses, block 13

Generated from certificate SHA256 4dbb85f7bef9f06a6b4701c7bd611c60507ecedfcf83c46b2c6b1a44828f513d.
All 256 literal transformed-state equalities are checked by ordinary Lean decide.
-/

namespace Gallai.Certificate.CompletedStar.Coverage.Block13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Stored representative index. -/
def orbit : Fin 256 → Fin 67 :=
  ![4, 21, 19, 24, 18, 22, 20, 52, 9, 33, 41, 46, 20, 40, 33, 62,
    4, 34, 31, 33, 31, 33, 30, 61, 8, 44, 41, 34, 34, 41, 18, 64,
    8, 24, 39, 42, 30, 40, 36, 57, 10, 42, 45, 45, 33, 33, 34, 52,
    9, 45, 39, 21, 32, 41, 31, 60, 10, 46, 47, 44, 36, 22, 32, 61,
    4, 21, 24, 19, 22, 18, 20, 52, 9, 33, 46, 41, 40, 20, 33, 62,
    8, 44, 34, 41, 41, 34, 18, 64, 4, 34, 33, 31, 33, 31, 30, 61,
    10, 42, 45, 45, 33, 33, 34, 52, 8, 24, 42, 39, 40, 30, 36, 57,
    9, 45, 21, 39, 41, 32, 31, 60, 10, 46, 44, 47, 22, 36, 32, 61,
    3, 25, 21, 21, 21, 21, 17, 51, 7, 35, 41, 41, 41, 41, 17, 63,
    9, 45, 32, 41, 39, 21, 31, 60, 9, 45, 41, 32, 21, 39, 31, 60,
    9, 45, 39, 21, 32, 41, 31, 60, 9, 45, 21, 39, 41, 32, 31, 60,
    7, 25, 39, 39, 39, 39, 29, 56, 3, 35, 32, 32, 32, 32, 29, 65,
    5, 28, 27, 27, 27, 27, 16, 55, 12, 37, 46, 46, 46, 46, 35, 53,
    10, 46, 36, 22, 47, 44, 32, 61, 10, 46, 22, 36, 44, 47, 32, 61,
    10, 46, 47, 44, 36, 22, 32, 61, 10, 46, 44, 47, 22, 36, 32, 61,
    3, 35, 32, 32, 32, 32, 29, 65, 11, 26, 43, 43, 43, 43, 38, 59]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Core action index, in the verifier's new-to-old row convention. -/
def action : Fin 256 → Fin 8 :=
  ![0, 1, 1, 0, 0, 0, 0, 0, 3, 1, 1, 0, 7, 5, 5, 1,
    6, 6, 1, 6, 3, 7, 4, 0, 4, 0, 6, 0, 2, 7, 6, 0,
    0, 6, 1, 4, 0, 0, 4, 0, 0, 0, 2, 0, 2, 0, 4, 6,
    0, 3, 4, 6, 2, 0, 0, 0, 5, 7, 2, 5, 2, 7, 5, 5,
    0, 1, 0, 1, 0, 0, 0, 0, 3, 1, 0, 1, 5, 7, 5, 1,
    4, 0, 0, 6, 7, 2, 6, 0, 6, 6, 6, 1, 7, 3, 4, 0,
    0, 0, 0, 2, 0, 2, 4, 6, 0, 6, 4, 1, 0, 0, 4, 0,
    0, 3, 6, 4, 0, 2, 0, 0, 5, 7, 5, 2, 7, 2, 5, 5,
    0, 0, 0, 0, 0, 0, 0, 1, 5, 0, 5, 5, 5, 5, 7, 1,
    2, 1, 0, 2, 5, 7, 2, 1, 2, 1, 2, 0, 7, 5, 2, 1,
    2, 1, 5, 7, 0, 2, 2, 1, 2, 1, 7, 5, 2, 0, 2, 1,
    0, 6, 0, 0, 0, 0, 0, 0, 7, 7, 7, 7, 7, 7, 5, 2,
    0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 4, 4, 4, 4, 4, 6,
    4, 6, 0, 6, 0, 4, 4, 4, 4, 6, 6, 0, 4, 0, 4, 4,
    4, 6, 0, 4, 0, 6, 4, 4, 4, 6, 4, 0, 6, 0, 4, 4,
    6, 6, 6, 6, 6, 6, 4, 0, 4, 6, 4, 4, 4, 4, 4, 4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Computable anchor permutation index. -/
def permutation : Fin 256 → Fin 24 :=
  ![15, 6, 12, 19, 15, 11, 17, 15, 8, 6, 2, 4, 15, 21, 23, 6,
    16, 0, 12, 19, 14, 21, 16, 12, 22, 1, 3, 19, 15, 11, 22, 19,
    15, 6, 12, 19, 15, 11, 17, 15, 11, 7, 12, 18, 9, 11, 23, 23,
    17, 6, 13, 19, 15, 21, 17, 17, 23, 1, 12, 19, 15, 21, 17, 16,
    21, 7, 13, 18, 9, 21, 23, 21, 10, 7, 2, 4, 15, 21, 17, 7,
    16, 0, 13, 5, 9, 21, 16, 13, 22, 1, 13, 18, 15, 20, 22, 18,
    9, 6, 12, 18, 9, 11, 17, 17, 21, 7, 13, 18, 9, 21, 23, 21,
    23, 7, 13, 19, 15, 21, 23, 23, 17, 0, 13, 18, 15, 21, 23, 22,
    16, 0, 13, 19, 15, 21, 16, 16, 16, 0, 13, 19, 15, 21, 16, 0,
    16, 0, 13, 19, 15, 21, 16, 13, 22, 1, 13, 19, 15, 21, 22, 19,
    17, 6, 13, 19, 15, 21, 17, 15, 23, 7, 13, 19, 15, 21, 23, 21,
    16, 0, 13, 19, 15, 21, 16, 16, 16, 0, 13, 19, 15, 21, 16, 16,
    16, 0, 13, 19, 15, 21, 16, 16, 0, 0, 13, 19, 15, 21, 16, 16,
    22, 7, 13, 19, 14, 21, 16, 17, 16, 6, 13, 19, 15, 20, 22, 23,
    23, 1, 12, 19, 15, 21, 17, 16, 17, 0, 13, 18, 15, 21, 23, 22,
    16, 0, 13, 19, 15, 21, 16, 16, 16, 0, 13, 19, 15, 21, 16, 16]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every indexed state in this block has the displayed symmetry witness. -/
theorem witness (i : Fin 256) :
    transformedState (action i) (anchorPermutation (permutation i))
      (Catalogue.state (orbit i)) = encodedAt (blockIndex 13 i) := by
  revert i
  decide

end Gallai.Certificate.CompletedStar.Coverage.Block13
