/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarCatalogue
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Exhaustive coverage witnesses, block 10

Generated from certificate SHA256 4dbb85f7bef9f06a6b4701c7bd611c60507ecedfcf83c46b2c6b1a44828f513d.
All 256 literal transformed-state equalities are checked by ordinary Lean decide.
-/

namespace Gallai.Certificate.CompletedStar.Coverage.Block10

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Stored representative index. -/
def orbit : Fin 256 → Fin 67 :=
  ![1, 15, 13, 15, 15, 14, 15, 49, 4, 18, 21, 22, 19, 20, 24, 52,
    2, 20, 17, 20, 20, 23, 20, 53, 4, 22, 21, 18, 24, 20, 19, 52,
    4, 19, 21, 24, 18, 20, 22, 52, 3, 21, 25, 21, 21, 17, 21, 51,
    4, 24, 21, 19, 22, 20, 18, 52, 5, 27, 28, 27, 27, 16, 27, 55,
    4, 18, 21, 22, 19, 20, 24, 52, 8, 30, 24, 40, 39, 36, 42, 57,
    9, 20, 33, 40, 41, 33, 46, 62, 10, 33, 42, 33, 45, 34, 45, 52,
    4, 31, 34, 33, 31, 30, 33, 61, 9, 32, 45, 41, 39, 31, 21, 60,
    8, 34, 44, 41, 41, 18, 34, 64, 10, 36, 46, 22, 47, 32, 44, 61,
    2, 20, 17, 20, 20, 23, 20, 53, 9, 20, 33, 40, 41, 33, 46, 62,
    7, 40, 23, 40, 40, 37, 40, 58, 9, 40, 33, 20, 46, 33, 41, 62,
    9, 41, 33, 46, 20, 33, 40, 62, 7, 41, 35, 41, 41, 17, 41, 63,
    9, 46, 33, 41, 40, 33, 20, 62, 12, 46, 37, 46, 46, 35, 46, 53,
    4, 22, 21, 18, 24, 20, 19, 52, 10, 33, 42, 33, 45, 34, 45, 52,
    9, 40, 33, 20, 46, 33, 41, 62, 8, 40, 24, 30, 42, 36, 39, 57,
    8, 41, 44, 34, 34, 18, 41, 64, 9, 41, 45, 32, 21, 31, 39, 60,
    4, 33, 34, 31, 33, 30, 31, 61, 10, 22, 46, 36, 44, 32, 47, 61]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Core action index, in the verifier's new-to-old row convention. -/
def action : Fin 256 → Fin 8 :=
  ![0, 0, 1, 0, 0, 0, 0, 0, 2, 2, 3, 2, 3, 2, 2, 2,
    3, 3, 3, 3, 3, 2, 3, 2, 2, 2, 3, 2, 2, 2, 3, 2,
    2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3,
    2, 2, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 2, 2,
    0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 6, 0, 1, 4, 4, 0,
    3, 7, 1, 5, 1, 5, 0, 1, 0, 2, 0, 0, 2, 4, 0, 6,
    6, 3, 6, 7, 1, 4, 6, 0, 0, 2, 3, 0, 4, 0, 6, 0,
    4, 2, 0, 7, 6, 6, 0, 0, 5, 2, 7, 7, 2, 5, 5, 5,
    1, 1, 1, 1, 1, 0, 1, 0, 1, 6, 3, 4, 3, 4, 2, 0,
    1, 1, 6, 1, 1, 4, 1, 0, 1, 4, 3, 6, 2, 4, 3, 0,
    1, 3, 3, 2, 6, 4, 4, 0, 4, 4, 2, 4, 4, 6, 4, 0,
    1, 2, 3, 3, 4, 4, 6, 0, 2, 5, 2, 5, 5, 5, 5, 7,
    0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 4, 2, 6,
    3, 5, 1, 7, 0, 5, 1, 1, 0, 0, 6, 0, 4, 4, 1, 0,
    4, 7, 0, 2, 0, 6, 6, 0, 0, 0, 3, 2, 6, 0, 4, 0,
    6, 7, 6, 3, 6, 4, 1, 0, 5, 7, 7, 2, 5, 5, 2, 5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Computable anchor permutation index. -/
def permutation : Fin 256 → Fin 24 :=
  ![10, 7, 2, 18, 9, 10, 23, 10, 7, 7, 2, 4, 8, 10, 23, 7,
    2, 0, 2, 5, 14, 10, 16, 2, 18, 1, 3, 18, 9, 20, 22, 18,
    9, 6, 12, 18, 9, 11, 17, 9, 10, 7, 2, 18, 9, 10, 23, 10,
    23, 7, 13, 19, 15, 21, 23, 23, 10, 7, 2, 18, 9, 10, 23, 10,
    7, 7, 2, 4, 8, 10, 23, 7, 7, 7, 2, 4, 8, 10, 23, 7,
    0, 7, 2, 18, 14, 20, 16, 2, 4, 1, 3, 4, 8, 20, 22, 20,
    11, 6, 12, 18, 8, 11, 23, 8, 10, 7, 2, 18, 9, 10, 23, 10,
    21, 7, 13, 4, 15, 21, 23, 23, 20, 7, 13, 18, 8, 10, 23, 11,
    2, 0, 2, 5, 14, 10, 16, 2, 0, 7, 2, 18, 14, 20, 16, 0,
    2, 0, 2, 5, 14, 10, 16, 2, 5, 7, 3, 18, 14, 10, 16, 5,
    14, 0, 12, 5, 9, 21, 23, 14, 10, 7, 2, 18, 9, 10, 23, 10,
    16, 0, 13, 5, 9, 11, 23, 16, 2, 7, 2, 18, 9, 10, 23, 10,
    18, 1, 3, 18, 9, 20, 22, 18, 1, 1, 2, 4, 8, 10, 22, 10,
    5, 7, 3, 18, 14, 10, 16, 3, 18, 1, 3, 18, 9, 20, 22, 18,
    11, 1, 12, 18, 9, 11, 17, 9, 20, 7, 3, 18, 9, 20, 23, 20,
    21, 7, 13, 19, 9, 21, 22, 22, 10, 7, 12, 18, 9, 20, 22, 21]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every indexed state in this block has the displayed symmetry witness. -/
theorem witness (i : Fin 256) :
    transformedState (action i) (anchorPermutation (permutation i))
      (Catalogue.state (orbit i)) = encodedAt (blockIndex 10 i) := by
  revert i
  decide

end Gallai.Certificate.CompletedStar.Coverage.Block10
