/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarCatalogue
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Exhaustive coverage witnesses, block 00

Generated from certificate SHA256 4dbb85f7bef9f06a6b4701c7bd611c60507ecedfcf83c46b2c6b1a44828f513d.
All 256 literal transformed-state equalities are checked by ordinary Lean decide.
-/

namespace Gallai.Certificate.CompletedStar.Coverage.Block00

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Stored representative index. -/
def orbit : Fin 256 → Fin 67 :=
  ![0, 13, 13, 13, 13, 13, 13, 48, 2, 16, 19, 19, 19, 19, 13, 51,
    2, 19, 16, 19, 19, 13, 19, 51, 2, 19, 19, 16, 13, 19, 19, 51,
    2, 19, 19, 13, 16, 19, 19, 51, 2, 19, 13, 19, 19, 16, 19, 51,
    2, 13, 19, 19, 19, 19, 16, 51, 0, 16, 16, 16, 16, 16, 16, 54,
    2, 16, 19, 19, 19, 19, 13, 51, 5, 23, 24, 24, 24, 24, 25, 49,
    4, 20, 20, 15, 27, 21, 21, 52, 4, 20, 15, 20, 21, 27, 21, 52,
    4, 20, 27, 21, 20, 15, 21, 52, 4, 20, 21, 27, 15, 20, 21, 52,
    1, 17, 18, 18, 18, 18, 17, 55, 3, 14, 22, 22, 22, 22, 28, 53,
    2, 19, 16, 19, 19, 13, 19, 51, 4, 20, 20, 15, 27, 21, 21, 52,
    5, 24, 23, 24, 24, 25, 24, 49, 4, 15, 20, 20, 21, 21, 27, 52,
    4, 27, 20, 21, 20, 21, 15, 52, 1, 18, 17, 18, 18, 17, 18, 55,
    4, 21, 20, 27, 15, 21, 20, 52, 3, 22, 14, 22, 22, 28, 22, 53,
    2, 19, 19, 16, 13, 19, 19, 51, 4, 20, 15, 20, 21, 27, 21, 52,
    4, 15, 20, 20, 21, 21, 27, 52, 5, 24, 24, 23, 25, 24, 24, 49,
    1, 18, 18, 17, 17, 18, 18, 55, 4, 27, 21, 20, 21, 20, 15, 52,
    4, 21, 27, 20, 21, 15, 20, 52, 3, 22, 22, 14, 28, 22, 22, 53]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Core action index, in the verifier's new-to-old row convention. -/
def action : Fin 256 → Fin 8 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 5, 2,
    2, 2, 2, 2, 2, 5, 2, 2, 2, 2, 2, 2, 5, 2, 2, 2,
    2, 2, 2, 5, 2, 2, 2, 2, 2, 2, 5, 2, 2, 2, 2, 2,
    2, 5, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 2,
    0, 0, 0, 0, 0, 0, 4, 0, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 5, 4, 4, 4, 5, 4, 4, 4, 5, 4, 4, 5, 4, 4, 4,
    4, 5, 4, 5, 4, 4, 4, 4, 4, 5, 5, 4, 4, 4, 4, 4,
    4, 5, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5,
    0, 0, 0, 0, 0, 4, 0, 0, 4, 4, 5, 4, 4, 4, 5, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 4, 5, 4, 4, 4,
    4, 4, 5, 5, 4, 4, 4, 4, 4, 4, 5, 4, 4, 4, 4, 4,
    4, 5, 5, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5,
    0, 0, 0, 0, 4, 0, 0, 0, 4, 4, 4, 5, 4, 4, 5, 4,
    4, 4, 4, 5, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 5, 4, 4, 4, 4, 4, 4, 5, 5, 4, 4, 4, 4,
    4, 5, 4, 5, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Computable anchor permutation index. -/
def permutation : Fin 256 → Fin 24 :=
  ![0, 0, 2, 4, 8, 10, 16, 0, 0, 0, 2, 4, 8, 10, 16, 0,
    2, 0, 2, 5, 14, 10, 16, 2, 4, 1, 3, 4, 8, 20, 22, 4,
    8, 6, 12, 4, 8, 11, 17, 8, 10, 7, 2, 18, 9, 10, 23, 10,
    16, 0, 13, 19, 15, 21, 16, 16, 0, 0, 2, 4, 8, 10, 16, 0,
    0, 0, 2, 4, 8, 10, 16, 0, 0, 0, 2, 4, 8, 10, 16, 0,
    5, 7, 13, 5, 14, 10, 16, 14, 3, 6, 3, 19, 8, 20, 22, 20,
    11, 1, 12, 4, 15, 11, 17, 12, 9, 0, 2, 18, 9, 21, 23, 18,
    16, 0, 13, 19, 15, 21, 16, 16, 0, 0, 12, 18, 14, 20, 16, 16,
    2, 0, 2, 5, 14, 10, 16, 2, 4, 7, 13, 4, 8, 10, 16, 8,
    2, 0, 2, 5, 14, 10, 16, 2, 1, 1, 12, 18, 14, 20, 22, 22,
    17, 6, 3, 5, 9, 11, 17, 6, 10, 7, 2, 18, 9, 10, 23, 10,
    15, 0, 2, 19, 15, 21, 23, 19, 2, 6, 2, 19, 8, 10, 22, 10,
    4, 1, 3, 4, 8, 20, 22, 4, 2, 6, 2, 19, 8, 10, 22, 10,
    0, 0, 12, 18, 14, 20, 16, 16, 4, 1, 3, 4, 8, 20, 22, 4,
    8, 6, 12, 4, 8, 11, 17, 8, 23, 7, 3, 5, 9, 11, 23, 7,
    21, 1, 13, 4, 15, 21, 17, 13, 4, 7, 13, 4, 8, 10, 16, 8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every indexed state in this block has the displayed symmetry witness. -/
theorem witness (i : Fin 256) :
    transformedState (action i) (anchorPermutation (permutation i))
      (Catalogue.state (orbit i)) = encodedAt (blockIndex 0 i) := by
  revert i
  decide

end Gallai.Certificate.CompletedStar.Coverage.Block00
