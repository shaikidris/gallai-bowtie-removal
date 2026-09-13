/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarCatalogue
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Exhaustive coverage witnesses, block 03

Generated from certificate SHA256 4dbb85f7bef9f06a6b4701c7bd611c60507ecedfcf83c46b2c6b1a44828f513d.
All 256 literal transformed-state equalities are checked by ordinary Lean decide.
-/

namespace Gallai.Certificate.CompletedStar.Coverage.Block03

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Stored representative index. -/
def orbit : Fin 256 → Fin 67 :=
  ![4, 20, 22, 24, 18, 19, 21, 52, 9, 31, 41, 21, 32, 39, 45, 60,
    10, 34, 33, 45, 33, 45, 42, 52, 8, 18, 41, 34, 34, 41, 44, 64,
    8, 36, 40, 42, 30, 39, 24, 57, 4, 30, 33, 33, 31, 31, 34, 61,
    9, 33, 40, 46, 20, 41, 33, 62, 10, 32, 22, 44, 36, 47, 46, 61,
    4, 20, 24, 22, 19, 18, 21, 52, 9, 31, 21, 41, 39, 32, 45, 60,
    8, 18, 34, 41, 41, 34, 44, 64, 10, 34, 45, 33, 45, 33, 42, 52,
    4, 30, 33, 33, 31, 31, 34, 61, 8, 36, 42, 40, 39, 30, 24, 57,
    9, 33, 46, 40, 41, 20, 33, 62, 10, 32, 44, 22, 47, 36, 46, 61,
    2, 23, 20, 20, 20, 20, 17, 53, 7, 17, 41, 41, 41, 41, 35, 63,
    9, 33, 20, 41, 40, 46, 33, 62, 9, 33, 41, 20, 46, 40, 33, 62,
    9, 33, 40, 46, 20, 41, 33, 62, 9, 33, 46, 40, 41, 20, 33, 62,
    7, 37, 40, 40, 40, 40, 23, 58, 12, 35, 46, 46, 46, 46, 37, 53,
    5, 16, 27, 27, 27, 27, 28, 55, 3, 29, 32, 32, 32, 32, 35, 65,
    10, 32, 36, 47, 22, 44, 46, 61, 10, 32, 47, 36, 44, 22, 46, 61,
    10, 32, 22, 44, 36, 47, 46, 61, 10, 32, 44, 22, 47, 36, 46, 61,
    12, 35, 46, 46, 46, 46, 37, 53, 11, 38, 43, 43, 43, 43, 26, 59]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Core action index, in the verifier's new-to-old row convention. -/
def action : Fin 256 → Fin 8 :=
  ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 6, 2, 4, 3, 0,
    0, 4, 0, 0, 2, 2, 0, 6, 4, 6, 7, 0, 2, 6, 0, 0,
    0, 4, 0, 4, 0, 1, 6, 0, 6, 4, 7, 6, 3, 1, 6, 0,
    3, 5, 5, 0, 7, 1, 1, 1, 5, 5, 7, 5, 2, 2, 7, 5,
    0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 6, 0, 4, 2, 3, 0,
    4, 6, 0, 7, 6, 2, 0, 0, 0, 4, 0, 0, 2, 2, 0, 6,
    6, 4, 6, 7, 1, 3, 6, 0, 0, 4, 4, 0, 1, 0, 6, 0,
    3, 5, 0, 5, 1, 7, 1, 1, 5, 5, 5, 7, 2, 2, 7, 5,
    1, 0, 1, 1, 1, 1, 1, 0, 4, 6, 4, 4, 4, 4, 2, 0,
    1, 4, 6, 3, 4, 2, 3, 0, 1, 4, 3, 6, 2, 4, 3, 0,
    1, 4, 4, 2, 6, 3, 3, 0, 1, 4, 2, 4, 3, 6, 3, 0,
    1, 4, 1, 1, 1, 1, 6, 0, 2, 5, 5, 5, 5, 5, 2, 7,
    0, 6, 0, 0, 0, 0, 0, 0, 6, 4, 6, 6, 6, 6, 6, 0,
    4, 4, 0, 0, 6, 4, 6, 4, 4, 4, 0, 0, 4, 6, 6, 4,
    4, 4, 6, 4, 0, 0, 6, 4, 4, 4, 4, 6, 0, 0, 6, 4,
    0, 4, 4, 4, 4, 4, 0, 6, 4, 4, 4, 4, 4, 4, 6, 4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Computable anchor permutation index. -/
def permutation : Fin 256 → Fin 24 :=
  ![8, 6, 12, 4, 8, 11, 17, 8, 6, 6, 2, 4, 8, 10, 17, 6,
    12, 0, 12, 5, 14, 11, 16, 0, 1, 1, 12, 4, 8, 20, 22, 4,
    8, 6, 12, 4, 8, 11, 17, 8, 7, 7, 2, 4, 9, 11, 23, 11,
    15, 0, 2, 19, 8, 21, 17, 17, 0, 6, 2, 4, 8, 11, 22, 7,
    10, 7, 2, 18, 9, 10, 23, 10, 7, 7, 2, 4, 8, 10, 23, 7,
    0, 0, 2, 18, 14, 10, 16, 2, 18, 1, 3, 18, 9, 20, 22, 1,
    6, 6, 2, 4, 9, 11, 17, 9, 10, 7, 2, 18, 9, 10, 23, 10,
    21, 1, 13, 4, 15, 10, 23, 23, 1, 7, 2, 4, 9, 10, 16, 6,
    16, 0, 13, 19, 15, 21, 16, 16, 0, 0, 2, 4, 8, 10, 16, 0,
    13, 6, 2, 19, 8, 21, 16, 13, 19, 7, 13, 4, 15, 10, 22, 19,
    15, 0, 2, 19, 8, 21, 17, 15, 21, 1, 13, 4, 15, 10, 23, 21,
    16, 0, 13, 19, 15, 21, 16, 16, 16, 0, 2, 4, 8, 10, 16, 0,
    0, 0, 2, 4, 8, 10, 16, 0, 0, 0, 2, 4, 8, 10, 16, 0,
    6, 0, 2, 5, 8, 10, 23, 1, 7, 1, 3, 4, 8, 10, 17, 0,
    0, 6, 2, 4, 8, 11, 22, 7, 1, 7, 2, 4, 9, 10, 16, 6,
    16, 0, 2, 4, 8, 10, 16, 0, 0, 0, 2, 4, 8, 10, 16, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every indexed state in this block has the displayed symmetry witness. -/
theorem witness (i : Fin 256) :
    transformedState (action i) (anchorPermutation (permutation i))
      (Catalogue.state (orbit i)) = encodedAt (blockIndex 3 i) := by
  revert i
  decide

end Gallai.Certificate.CompletedStar.Coverage.Block03
