/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarCatalogue
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Exhaustive coverage witnesses, block 14

Generated from certificate SHA256 4dbb85f7bef9f06a6b4701c7bd611c60507ecedfcf83c46b2c6b1a44828f513d.
All 256 literal transformed-state equalities are checked by ordinary Lean decide.
-/

namespace Gallai.Certificate.CompletedStar.Coverage.Block14

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Stored representative index. -/
def orbit : Fin 256 → Fin 67 :=
  ![0, 14, 14, 14, 14, 14, 14, 50, 3, 16, 22, 22, 22, 22, 26, 53,
    3, 22, 16, 22, 22, 26, 22, 53, 3, 22, 22, 16, 26, 22, 22, 53,
    3, 22, 22, 26, 16, 22, 22, 53, 3, 22, 26, 22, 22, 16, 22, 53,
    3, 26, 22, 22, 22, 22, 16, 53, 6, 28, 28, 28, 28, 28, 28, 54,
    3, 16, 22, 22, 22, 22, 26, 53, 5, 29, 36, 36, 36, 36, 37, 59,
    10, 32, 32, 43, 27, 46, 46, 61, 10, 32, 43, 32, 46, 27, 46, 61,
    10, 32, 27, 46, 32, 43, 46, 61, 10, 32, 46, 27, 43, 32, 46, 61,
    11, 35, 44, 44, 44, 44, 35, 55, 12, 38, 47, 47, 47, 47, 28, 65,
    3, 22, 16, 22, 22, 26, 22, 53, 10, 32, 32, 43, 27, 46, 46, 61,
    5, 36, 29, 36, 36, 37, 36, 59, 10, 43, 32, 32, 46, 46, 27, 61,
    10, 27, 32, 46, 32, 46, 43, 61, 11, 44, 35, 44, 44, 35, 44, 55,
    10, 46, 32, 27, 43, 46, 32, 61, 12, 47, 38, 47, 47, 28, 47, 65,
    3, 22, 22, 16, 26, 22, 22, 53, 10, 32, 43, 32, 46, 27, 46, 61,
    10, 43, 32, 32, 46, 46, 27, 61, 5, 36, 36, 29, 37, 36, 36, 59,
    11, 44, 44, 35, 35, 44, 44, 55, 10, 27, 46, 32, 46, 32, 43, 61,
    10, 46, 27, 32, 46, 43, 32, 61, 12, 47, 47, 38, 28, 47, 47, 65]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Core action index, in the verifier's new-to-old row convention. -/
def action : Fin 256 → Fin 8 :=
  ![1, 1, 1, 1, 1, 1, 1, 0, 3, 3, 3, 3, 3, 3, 2, 3,
    3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3,
    3, 3, 3, 2, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3,
    3, 2, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3, 3,
    1, 1, 1, 1, 1, 1, 0, 1, 6, 1, 6, 6, 6, 6, 6, 0,
    1, 3, 1, 0, 6, 3, 1, 1, 1, 3, 0, 1, 3, 6, 1, 1,
    1, 3, 6, 3, 1, 0, 1, 1, 1, 3, 3, 6, 0, 1, 1, 1,
    0, 3, 1, 1, 1, 1, 1, 6, 3, 2, 3, 3, 3, 3, 7, 3,
    1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 3, 0, 6, 1, 3, 1,
    6, 6, 1, 6, 6, 6, 6, 0, 1, 0, 3, 1, 3, 1, 6, 1,
    1, 6, 3, 3, 1, 1, 0, 1, 0, 1, 3, 1, 1, 1, 1, 6,
    1, 3, 3, 6, 0, 1, 1, 1, 3, 3, 2, 3, 3, 7, 3, 3,
    1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 3, 1, 6, 3, 1,
    1, 0, 1, 3, 1, 3, 6, 1, 6, 6, 6, 1, 6, 6, 6, 0,
    0, 1, 1, 3, 1, 1, 1, 6, 1, 6, 3, 3, 1, 1, 0, 1,
    1, 3, 6, 3, 1, 0, 1, 1, 3, 3, 3, 2, 7, 3, 3, 3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Computable anchor permutation index. -/
def permutation : Fin 256 → Fin 24 :=
  ![0, 0, 2, 4, 8, 10, 16, 0, 0, 0, 2, 4, 8, 10, 16, 0,
    2, 0, 2, 5, 14, 10, 16, 2, 4, 1, 3, 4, 8, 20, 22, 4,
    8, 6, 12, 4, 8, 11, 17, 8, 10, 7, 2, 18, 9, 10, 23, 10,
    16, 0, 13, 19, 15, 21, 16, 16, 0, 0, 2, 4, 8, 10, 16, 0,
    0, 0, 2, 4, 8, 10, 16, 0, 0, 0, 2, 4, 8, 10, 16, 0,
    2, 0, 2, 5, 14, 10, 16, 2, 4, 1, 3, 4, 8, 20, 22, 4,
    8, 6, 12, 4, 8, 11, 17, 8, 10, 7, 2, 18, 9, 10, 23, 10,
    16, 0, 13, 19, 15, 21, 16, 16, 0, 0, 2, 4, 8, 10, 16, 0,
    2, 0, 2, 5, 14, 10, 16, 2, 0, 0, 2, 4, 8, 10, 16, 0,
    2, 0, 2, 5, 14, 10, 16, 2, 5, 1, 3, 5, 14, 20, 22, 5,
    14, 6, 12, 5, 14, 11, 17, 14, 10, 7, 2, 18, 9, 10, 23, 10,
    16, 0, 13, 19, 15, 21, 16, 16, 2, 0, 2, 5, 14, 10, 16, 2,
    4, 1, 3, 4, 8, 20, 22, 4, 1, 1, 2, 4, 8, 10, 22, 1,
    3, 0, 3, 5, 14, 20, 16, 3, 4, 1, 3, 4, 8, 20, 22, 4,
    8, 6, 12, 4, 8, 11, 17, 8, 20, 7, 3, 18, 9, 20, 23, 20,
    22, 1, 13, 19, 15, 21, 22, 22, 4, 1, 3, 4, 8, 20, 22, 4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every indexed state in this block has the displayed symmetry witness. -/
theorem witness (i : Fin 256) :
    transformedState (action i) (anchorPermutation (permutation i))
      (Catalogue.state (orbit i)) = encodedAt (blockIndex 14 i) := by
  revert i
  decide

end Gallai.Certificate.CompletedStar.Coverage.Block14
