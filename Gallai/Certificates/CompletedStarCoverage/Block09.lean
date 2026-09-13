/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarCatalogue
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Exhaustive coverage witnesses, block 09

Generated from certificate SHA256 4dbb85f7bef9f06a6b4701c7bd611c60507ecedfcf83c46b2c6b1a44828f513d.
All 256 literal transformed-state equalities are checked by ordinary Lean decide.
-/

namespace Gallai.Certificate.CompletedStar.Coverage.Block09

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Stored representative index. -/
def orbit : Fin 256 → Fin 67 :=
  ![3, 21, 21, 25, 17, 21, 21, 51, 9, 32, 41, 45, 31, 39, 21, 60,
    9, 41, 32, 45, 31, 21, 39, 60, 7, 41, 41, 35, 17, 41, 41, 63,
    7, 39, 39, 25, 29, 39, 39, 56, 9, 39, 21, 45, 31, 32, 41, 60,
    9, 21, 39, 45, 31, 41, 32, 60, 3, 32, 32, 35, 29, 32, 32, 65,
    4, 19, 24, 21, 20, 18, 22, 52, 4, 31, 33, 34, 30, 31, 33, 61,
    8, 41, 34, 44, 18, 34, 41, 64, 9, 41, 46, 33, 33, 20, 40, 62,
    9, 39, 21, 45, 31, 32, 41, 60, 8, 39, 42, 24, 36, 30, 40, 57,
    10, 45, 45, 42, 34, 33, 33, 52, 10, 47, 44, 46, 32, 36, 22, 61,
    4, 24, 19, 21, 20, 22, 18, 52, 8, 34, 41, 44, 18, 41, 34, 64,
    4, 33, 31, 34, 30, 33, 31, 61, 9, 46, 41, 33, 33, 40, 20, 62,
    9, 21, 39, 45, 31, 41, 32, 60, 10, 45, 45, 42, 34, 33, 33, 52,
    8, 42, 39, 24, 36, 40, 30, 57, 10, 44, 47, 46, 32, 22, 36, 61,
    5, 27, 27, 28, 16, 27, 27, 55, 10, 36, 22, 46, 32, 47, 44, 61,
    10, 22, 36, 46, 32, 44, 47, 61, 12, 46, 46, 37, 35, 46, 46, 53,
    3, 32, 32, 35, 29, 32, 32, 65, 10, 47, 44, 46, 32, 36, 22, 61,
    10, 44, 47, 46, 32, 22, 36, 61, 11, 43, 43, 26, 38, 43, 43, 59]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Core action index, in the verifier's new-to-old row convention. -/
def action : Fin 256 → Fin 8 :=
  ![0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 2, 1, 2, 5, 7, 1,
    2, 2, 0, 1, 2, 7, 5, 1, 5, 5, 5, 0, 7, 5, 5, 1,
    0, 0, 0, 6, 0, 0, 0, 0, 2, 5, 7, 1, 2, 0, 2, 1,
    2, 7, 5, 1, 2, 2, 0, 1, 7, 7, 7, 7, 5, 7, 7, 2,
    0, 1, 0, 1, 0, 0, 0, 0, 6, 1, 6, 6, 4, 3, 7, 0,
    4, 6, 0, 0, 6, 2, 7, 0, 3, 1, 0, 1, 5, 7, 5, 1,
    0, 4, 6, 3, 0, 2, 0, 0, 0, 1, 4, 6, 4, 0, 0, 0,
    0, 2, 0, 0, 4, 2, 0, 6, 5, 2, 5, 7, 5, 2, 7, 5,
    0, 0, 1, 1, 0, 0, 0, 0, 4, 0, 6, 0, 6, 7, 2, 0,
    6, 6, 1, 6, 4, 7, 3, 0, 3, 0, 1, 1, 5, 5, 7, 1,
    0, 6, 4, 3, 0, 0, 2, 0, 0, 0, 2, 0, 4, 0, 2, 6,
    0, 4, 1, 6, 4, 0, 0, 0, 5, 5, 2, 7, 5, 7, 2, 5,
    0, 0, 0, 0, 6, 0, 0, 0, 4, 0, 6, 6, 4, 0, 4, 4,
    4, 6, 0, 6, 4, 4, 0, 4, 0, 4, 4, 0, 4, 4, 4, 6,
    6, 6, 6, 6, 4, 6, 6, 0, 4, 0, 4, 6, 4, 0, 6, 4,
    4, 4, 0, 6, 4, 6, 0, 4, 4, 4, 4, 6, 4, 4, 4, 4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Computable anchor permutation index. -/
def permutation : Fin 256 → Fin 24 :=
  ![8, 6, 12, 4, 8, 11, 17, 8, 8, 6, 12, 4, 8, 11, 17, 6,
    14, 6, 12, 5, 14, 11, 17, 12, 8, 6, 12, 4, 8, 11, 17, 4,
    8, 6, 12, 4, 8, 11, 17, 8, 9, 6, 12, 18, 9, 11, 17, 11,
    15, 6, 12, 19, 15, 11, 17, 17, 8, 6, 12, 4, 8, 11, 17, 8,
    11, 7, 12, 18, 9, 11, 23, 11, 8, 7, 12, 4, 8, 10, 17, 7,
    14, 0, 12, 5, 14, 11, 23, 12, 20, 1, 3, 18, 15, 11, 17, 18,
    9, 6, 12, 18, 9, 11, 17, 9, 11, 7, 12, 18, 9, 11, 23, 11,
    23, 7, 13, 19, 15, 21, 23, 15, 15, 7, 12, 5, 9, 11, 17, 8,
    17, 6, 13, 19, 15, 21, 17, 17, 8, 6, 2, 4, 8, 21, 17, 6,
    14, 6, 13, 5, 14, 11, 16, 13, 22, 1, 3, 19, 9, 11, 17, 19,
    15, 6, 12, 19, 15, 11, 17, 15, 21, 7, 13, 18, 9, 21, 23, 9,
    17, 6, 13, 19, 15, 21, 17, 17, 9, 6, 13, 4, 15, 11, 17, 14,
    8, 6, 12, 4, 8, 11, 17, 8, 14, 6, 12, 19, 8, 10, 17, 9,
    8, 6, 12, 18, 14, 11, 16, 15, 4, 6, 12, 4, 8, 11, 17, 8,
    8, 6, 12, 4, 8, 11, 17, 8, 15, 7, 12, 5, 9, 11, 17, 8,
    9, 6, 13, 4, 15, 11, 17, 14, 8, 6, 12, 4, 8, 11, 17, 8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every indexed state in this block has the displayed symmetry witness. -/
theorem witness (i : Fin 256) :
    transformedState (action i) (anchorPermutation (permutation i))
      (Catalogue.state (orbit i)) = encodedAt (blockIndex 9 i) := by
  revert i
  decide

end Gallai.Certificate.CompletedStar.Coverage.Block09
