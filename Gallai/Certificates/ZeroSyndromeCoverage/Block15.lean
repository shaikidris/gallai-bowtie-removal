/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeCatalogue
import Gallai.Certificates.ZeroSyndromeIndex
import Gallai.Certificates.CompletedStarSymmetry
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Zero-state coverage block 15
Source SHA256 32c2c172fa37de8b8de229fb2f531543e2e9274cfa5316796c582c6989ebdd59. Ordinary decide checks every guarded equality.
-/
namespace Gallai.Certificate.ZeroSyndrome.Coverage.Block15
open CompletedStar
open CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Representative index; excluded inputs use an irrelevant default. -/
def orbit : Fin 256 → Fin 44 := ![0, 12, 12, 0, 11, 12, 12, 34, 4, 20, 27, 29, 20, 17, 29, 41,
    4, 27, 20, 29, 20, 29, 17, 41, 1, 23, 23, 21, 21, 23, 23, 42,
    3, 25, 25, 32, 18, 25, 25, 36, 4, 17, 29, 29, 20, 20, 27, 41,
    4, 29, 17, 29, 20, 27, 20, 41, 8, 31, 31, 33, 16, 31, 31, 43,
    0, 12, 0, 12, 12, 11, 12, 34, 4, 20, 29, 27, 17, 20, 29, 41,
    1, 23, 21, 23, 23, 21, 23, 42, 4, 27, 29, 20, 29, 20, 17, 41,
    4, 17, 29, 29, 20, 20, 27, 41, 3, 25, 32, 25, 25, 18, 25, 36,
    4, 29, 29, 17, 27, 20, 20, 41, 8, 31, 33, 31, 31, 16, 31, 43,
    0, 0, 12, 12, 12, 12, 11, 34, 1, 21, 23, 23, 23, 23, 21, 42,
    4, 29, 20, 27, 17, 29, 20, 41, 4, 29, 27, 20, 29, 17, 20, 41,
    4, 29, 17, 29, 20, 27, 20, 41, 4, 29, 29, 17, 27, 20, 20, 41,
    3, 32, 25, 25, 25, 25, 18, 36, 8, 33, 31, 31, 31, 31, 16, 43,
    0, 16, 16, 16, 16, 16, 16, 37, 8, 16, 31, 31, 31, 31, 33, 43,
    8, 31, 16, 31, 31, 33, 31, 43, 8, 31, 31, 16, 33, 31, 31, 43,
    8, 31, 31, 33, 16, 31, 31, 43, 8, 31, 33, 31, 31, 16, 31, 43,
    8, 33, 31, 31, 31, 31, 16, 43, 9, 33, 33, 33, 33, 33, 33, 37]
/-- Core action. -/
def action : Fin 256 → Fin 8 := ![1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 3, 6, 3, 1,
    1, 0, 1, 1, 3, 3, 6, 1, 6, 6, 6, 1, 3, 6, 6, 0,
    0, 1, 1, 1, 1, 1, 1, 6, 1, 6, 3, 1, 3, 1, 0, 1,
    1, 3, 6, 1, 3, 0, 1, 1, 3, 3, 3, 2, 7, 3, 3, 3,
    1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 6, 3, 3, 1,
    6, 6, 1, 6, 6, 3, 6, 0, 1, 0, 1, 1, 3, 3, 6, 1,
    1, 6, 1, 3, 1, 3, 0, 1, 0, 1, 1, 1, 1, 1, 1, 6,
    1, 3, 1, 6, 0, 3, 1, 1, 3, 3, 2, 3, 3, 7, 3, 3,
    1, 0, 1, 1, 1, 1, 0, 1, 6, 1, 6, 6, 6, 6, 3, 0,
    1, 1, 1, 0, 6, 3, 3, 1, 1, 1, 0, 1, 3, 6, 3, 1,
    1, 1, 6, 3, 1, 0, 3, 1, 1, 1, 3, 6, 0, 1, 3, 1,
    0, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 3, 3, 3, 7, 3,
    0, 1, 1, 1, 1, 1, 1, 0, 1, 6, 1, 1, 1, 1, 0, 1,
    1, 1, 6, 1, 1, 0, 1, 1, 1, 1, 1, 6, 0, 1, 1, 1,
    1, 1, 1, 0, 6, 1, 1, 1, 1, 1, 0, 1, 1, 6, 1, 1,
    1, 0, 1, 1, 1, 1, 6, 1, 0, 6, 6, 6, 6, 6, 6, 6]
/-- Anchor action. -/
def permutation : Fin 256 → Fin 24 := ![8, 6, 12, 0, 8, 11, 17, 8, 6, 6, 2, 4, 8, 10, 17, 6,
    12, 0, 12, 5, 14, 11, 16, 12, 4, 1, 3, 4, 8, 20, 22, 4,
    8, 6, 12, 4, 8, 11, 17, 8, 11, 7, 12, 18, 9, 11, 23, 11,
    17, 6, 13, 19, 15, 21, 17, 17, 8, 6, 12, 4, 8, 11, 17, 8,
    10, 7, 0, 18, 9, 10, 23, 10, 7, 7, 2, 4, 8, 10, 23, 7,
    2, 0, 2, 5, 14, 10, 16, 2, 18, 1, 3, 18, 9, 20, 22, 18,
    9, 6, 12, 18, 9, 11, 17, 9, 10, 7, 2, 18, 9, 10, 23, 10,
    23, 7, 13, 19, 15, 21, 23, 23, 10, 7, 2, 18, 9, 10, 23, 10,
    16, 0, 13, 19, 15, 21, 16, 16, 0, 0, 2, 4, 8, 10, 16, 0,
    13, 0, 13, 5, 14, 21, 16, 13, 19, 1, 3, 19, 15, 20, 22, 19,
    15, 6, 12, 19, 15, 11, 17, 15, 21, 7, 13, 18, 9, 21, 23, 21,
    16, 0, 13, 19, 15, 21, 16, 16, 16, 0, 13, 19, 15, 21, 16, 16,
    0, 0, 2, 4, 8, 10, 16, 0, 0, 0, 2, 4, 8, 10, 16, 0,
    2, 0, 2, 5, 14, 10, 16, 2, 4, 1, 3, 4, 8, 20, 22, 4,
    8, 6, 12, 4, 8, 11, 17, 8, 10, 7, 2, 18, 9, 10, 23, 10,
    16, 0, 13, 19, 15, 21, 16, 16, 0, 0, 2, 4, 8, 10, 16, 0]

/-- Every eligible index has the displayed exact symmetry witness. -/
theorem witness (i : Fin 256) :
    HighBoundary (zeroEncodedAt (blockIndex 15 i)) →
    transformedState (action i) (anchorPermutation (permutation i))
      (ZeroSyndrome.Catalogue.state (orbit i)) = zeroEncodedAt (blockIndex 15 i) := by
  revert i
  decide
end Gallai.Certificate.ZeroSyndrome.Coverage.Block15
