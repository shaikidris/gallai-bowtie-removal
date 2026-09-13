/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarCatalogue
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Exhaustive coverage witnesses, block 11

Generated from certificate SHA256 4dbb85f7bef9f06a6b4701c7bd611c60507ecedfcf83c46b2c6b1a44828f513d.
All 256 literal transformed-state equalities are checked by ordinary Lean decide.
-/

namespace Gallai.Certificate.CompletedStar.Coverage.Block11

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Stored representative index. -/
def orbit : Fin 256 → Fin 67 :=
  ![4, 19, 21, 24, 18, 20, 22, 52, 4, 31, 34, 33, 31, 30, 33, 61,
    9, 41, 33, 46, 20, 33, 40, 62, 8, 41, 44, 34, 34, 18, 41, 64,
    8, 39, 24, 42, 30, 36, 40, 57, 9, 39, 45, 21, 32, 31, 41, 60,
    10, 45, 42, 45, 33, 34, 33, 52, 10, 47, 46, 44, 36, 32, 22, 61,
    3, 21, 25, 21, 21, 17, 21, 51, 9, 32, 45, 41, 39, 31, 21, 60,
    7, 41, 35, 41, 41, 17, 41, 63, 9, 41, 45, 32, 21, 31, 39, 60,
    9, 39, 45, 21, 32, 31, 41, 60, 7, 39, 25, 39, 39, 29, 39, 56,
    9, 21, 45, 39, 41, 31, 32, 60, 3, 32, 35, 32, 32, 29, 32, 65,
    4, 24, 21, 19, 22, 20, 18, 52, 8, 34, 44, 41, 41, 18, 34, 64,
    9, 46, 33, 41, 40, 33, 20, 62, 4, 33, 34, 31, 33, 30, 31, 61,
    10, 45, 42, 45, 33, 34, 33, 52, 9, 21, 45, 39, 41, 31, 32, 60,
    8, 42, 24, 39, 40, 36, 30, 57, 10, 44, 46, 47, 22, 32, 36, 61,
    5, 27, 28, 27, 27, 16, 27, 55, 10, 36, 46, 22, 47, 32, 44, 61,
    12, 46, 37, 46, 46, 35, 46, 53, 10, 22, 46, 36, 44, 32, 47, 61,
    10, 47, 46, 44, 36, 32, 22, 61, 3, 32, 35, 32, 32, 29, 32, 65,
    10, 44, 46, 47, 22, 32, 36, 61, 11, 43, 26, 43, 43, 38, 43, 59]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Core action index, in the verifier's new-to-old row convention. -/
def action : Fin 256 → Fin 8 :=
  ![0, 1, 1, 0, 0, 0, 0, 0, 6, 1, 6, 6, 3, 4, 7, 0,
    3, 1, 1, 0, 7, 5, 5, 1, 4, 6, 0, 0, 2, 6, 7, 0,
    0, 1, 6, 4, 0, 4, 0, 0, 0, 4, 3, 6, 2, 0, 0, 0,
    0, 2, 0, 0, 2, 4, 0, 6, 5, 2, 7, 5, 2, 5, 7, 5,
    0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 2, 5, 2, 7, 1,
    5, 5, 0, 5, 5, 7, 5, 1, 2, 2, 1, 0, 7, 2, 5, 1,
    2, 5, 1, 7, 0, 2, 2, 1, 0, 0, 6, 0, 0, 0, 0, 0,
    2, 7, 1, 5, 2, 2, 0, 1, 7, 7, 7, 7, 7, 5, 7, 2,
    0, 0, 1, 1, 0, 0, 0, 0, 4, 0, 0, 6, 7, 6, 2, 0,
    3, 0, 1, 1, 5, 5, 7, 1, 6, 6, 6, 1, 7, 4, 3, 0,
    0, 0, 0, 2, 0, 4, 2, 6, 0, 6, 3, 4, 0, 0, 2, 0,
    0, 4, 6, 1, 0, 4, 0, 0, 5, 5, 7, 2, 7, 5, 2, 5,
    0, 0, 0, 0, 0, 6, 0, 0, 4, 0, 6, 6, 0, 4, 4, 4,
    0, 4, 0, 4, 4, 4, 4, 6, 4, 6, 6, 0, 4, 4, 0, 4,
    4, 0, 6, 4, 0, 4, 6, 4, 6, 6, 6, 6, 6, 4, 6, 0,
    4, 4, 6, 0, 6, 4, 0, 4, 4, 4, 6, 4, 4, 4, 4, 4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Computable anchor permutation index. -/
def permutation : Fin 256 → Fin 24 :=
  ![9, 6, 12, 18, 9, 11, 17, 9, 10, 6, 2, 18, 8, 10, 23, 6,
    14, 0, 12, 5, 9, 21, 23, 12, 20, 1, 3, 18, 9, 20, 17, 18,
    9, 6, 12, 18, 9, 11, 17, 9, 11, 7, 12, 18, 9, 11, 23, 11,
    17, 6, 13, 19, 15, 21, 17, 21, 21, 6, 3, 18, 9, 11, 23, 10,
    10, 7, 2, 18, 9, 10, 23, 10, 10, 7, 2, 18, 9, 10, 23, 7,
    10, 7, 2, 18, 9, 10, 23, 2, 20, 7, 3, 18, 9, 20, 23, 18,
    11, 7, 12, 18, 9, 11, 23, 9, 10, 7, 2, 18, 9, 10, 23, 10,
    21, 7, 13, 18, 9, 21, 23, 23, 10, 7, 2, 18, 9, 10, 23, 10,
    23, 7, 13, 19, 15, 21, 23, 23, 10, 7, 2, 4, 15, 10, 23, 7,
    16, 0, 13, 5, 9, 11, 23, 13, 20, 7, 3, 19, 9, 20, 22, 19,
    15, 6, 12, 19, 15, 11, 17, 11, 21, 7, 13, 18, 9, 21, 23, 21,
    23, 7, 13, 19, 15, 21, 23, 23, 11, 7, 2, 19, 9, 21, 23, 20,
    10, 7, 2, 18, 9, 10, 23, 10, 20, 7, 13, 18, 8, 10, 23, 11,
    2, 7, 2, 18, 9, 10, 23, 10, 10, 7, 12, 18, 9, 20, 22, 21,
    21, 6, 3, 18, 9, 11, 23, 10, 10, 7, 2, 18, 9, 10, 23, 10,
    11, 7, 2, 19, 9, 21, 23, 20, 10, 7, 2, 18, 9, 10, 23, 10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every indexed state in this block has the displayed symmetry witness. -/
theorem witness (i : Fin 256) :
    transformedState (action i) (anchorPermutation (permutation i))
      (Catalogue.state (orbit i)) = encodedAt (blockIndex 11 i) := by
  revert i
  decide

end Gallai.Certificate.CompletedStar.Coverage.Block11
