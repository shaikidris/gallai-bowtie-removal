/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarCatalogue
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Exhaustive coverage witnesses, block 01

Generated from certificate SHA256 4dbb85f7bef9f06a6b4701c7bd611c60507ecedfcf83c46b2c6b1a44828f513d.
All 256 literal transformed-state equalities are checked by ordinary Lean decide.
-/

namespace Gallai.Certificate.CompletedStar.Coverage.Block01

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Stored representative index. -/
def orbit : Fin 256 → Fin 67 :=
  ![2, 19, 19, 13, 16, 19, 19, 51, 4, 20, 27, 21, 20, 15, 21, 52,
    4, 27, 20, 21, 20, 21, 15, 52, 1, 18, 18, 17, 17, 18, 18, 55,
    5, 24, 24, 25, 23, 24, 24, 49, 4, 15, 21, 21, 20, 20, 27, 52,
    4, 21, 15, 21, 20, 27, 20, 52, 3, 22, 22, 28, 14, 22, 22, 53,
    2, 19, 13, 19, 19, 16, 19, 51, 4, 20, 21, 27, 15, 20, 21, 52,
    1, 18, 17, 18, 18, 17, 18, 55, 4, 27, 21, 20, 21, 20, 15, 52,
    4, 15, 21, 21, 20, 20, 27, 52, 5, 24, 25, 24, 24, 23, 24, 49,
    4, 21, 21, 15, 27, 20, 20, 52, 3, 22, 28, 22, 22, 14, 22, 53,
    2, 13, 19, 19, 19, 19, 16, 51, 1, 17, 18, 18, 18, 18, 17, 55,
    4, 21, 20, 27, 15, 21, 20, 52, 4, 21, 27, 20, 21, 15, 20, 52,
    4, 21, 15, 21, 20, 27, 20, 52, 4, 21, 21, 15, 27, 20, 20, 52,
    5, 25, 24, 24, 24, 24, 23, 49, 3, 28, 22, 22, 22, 22, 14, 53,
    0, 16, 16, 16, 16, 16, 16, 54, 3, 14, 22, 22, 22, 22, 28, 53,
    3, 22, 14, 22, 22, 28, 22, 53, 3, 22, 22, 14, 28, 22, 22, 53,
    3, 22, 22, 28, 14, 22, 22, 53, 3, 22, 28, 22, 22, 14, 22, 53,
    3, 28, 22, 22, 22, 22, 14, 53, 6, 26, 26, 26, 26, 26, 26, 50]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Core action index, in the verifier's new-to-old row convention. -/
def action : Fin 256 → Fin 8 :=
  ![0, 0, 0, 4, 0, 0, 0, 0, 4, 4, 4, 4, 5, 4, 5, 4,
    4, 4, 4, 4, 5, 5, 4, 4, 4, 4, 4, 4, 5, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 4, 5, 4, 4, 4,
    4, 5, 4, 4, 5, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5,
    0, 0, 4, 0, 0, 0, 0, 0, 4, 4, 4, 4, 4, 5, 5, 4,
    4, 4, 4, 4, 4, 5, 4, 4, 4, 4, 4, 4, 5, 5, 4, 4,
    4, 4, 4, 5, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 5, 4, 4, 4, 5, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5,
    0, 4, 0, 0, 0, 0, 0, 0, 4, 4, 4, 4, 4, 4, 5, 4,
    4, 4, 4, 4, 4, 5, 5, 4, 4, 4, 4, 4, 5, 4, 5, 4,
    4, 4, 4, 5, 4, 4, 5, 4, 4, 4, 5, 4, 4, 4, 5, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5,
    4, 4, 4, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Computable anchor permutation index. -/
def permutation : Fin 256 → Fin 24 :=
  ![8, 6, 12, 4, 8, 11, 17, 8, 10, 1, 2, 4, 15, 10, 17, 2,
    16, 0, 3, 5, 9, 11, 16, 0, 4, 1, 3, 4, 8, 20, 22, 4,
    8, 6, 12, 4, 8, 11, 17, 8, 7, 7, 12, 18, 14, 20, 23, 23,
    13, 6, 13, 19, 8, 21, 22, 21, 8, 0, 2, 4, 8, 21, 23, 4,
    10, 7, 2, 18, 9, 10, 23, 10, 8, 0, 2, 4, 8, 21, 23, 4,
    2, 0, 2, 5, 14, 10, 16, 2, 22, 1, 3, 5, 9, 11, 22, 1,
    6, 6, 12, 18, 14, 20, 17, 17, 10, 7, 2, 18, 9, 10, 23, 10,
    19, 7, 13, 19, 15, 10, 16, 15, 10, 1, 2, 4, 15, 10, 17, 2,
    16, 0, 13, 19, 15, 21, 16, 16, 0, 0, 2, 4, 8, 10, 16, 0,
    14, 0, 2, 5, 14, 21, 23, 5, 20, 1, 3, 4, 15, 20, 17, 3,
    12, 6, 12, 19, 8, 11, 22, 11, 18, 7, 13, 18, 9, 10, 16, 9,
    16, 0, 13, 19, 15, 21, 16, 16, 16, 0, 3, 5, 9, 11, 16, 0,
    0, 0, 2, 4, 8, 10, 16, 0, 0, 0, 12, 18, 14, 20, 16, 16,
    2, 6, 2, 19, 8, 10, 22, 10, 4, 7, 13, 4, 8, 10, 16, 8,
    8, 0, 2, 4, 8, 21, 23, 4, 10, 1, 2, 4, 15, 10, 17, 2,
    16, 0, 3, 5, 9, 11, 16, 0, 0, 0, 2, 4, 8, 10, 16, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every indexed state in this block has the displayed symmetry witness. -/
theorem witness (i : Fin 256) :
    transformedState (action i) (anchorPermutation (permutation i))
      (Catalogue.state (orbit i)) = encodedAt (blockIndex 1 i) := by
  revert i
  decide

end Gallai.Certificate.CompletedStar.Coverage.Block01
