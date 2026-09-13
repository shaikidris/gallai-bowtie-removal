/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeCatalogue
import Gallai.Certificates.ZeroSyndromeIndex
import Gallai.Certificates.CompletedStarSymmetry
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Zero-state coverage block 13
Source SHA256 32c2c172fa37de8b8de229fb2f531543e2e9274cfa5316796c582c6989ebdd59. Ordinary decide checks every guarded equality.
-/
namespace Gallai.Certificate.ZeroSyndrome.Coverage.Block13
open CompletedStar
open CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Representative index; excluded inputs use an irrelevant default. -/
def orbit : Fin 256 → Fin 44 := ![0, 13, 12, 15, 0, 0, 0, 35, 5, 19, 24, 13, 20, 28, 19, 40,
    4, 26, 19, 30, 19, 30, 22, 35, 7, 15, 28, 22, 22, 28, 23, 39,
    0, 25, 24, 26, 0, 0, 0, 39, 0, 22, 19, 19, 0, 0, 0, 41,
    0, 30, 28, 29, 0, 0, 0, 40, 4, 29, 12, 25, 23, 31, 20, 41,
    0, 13, 15, 12, 0, 0, 0, 35, 5, 19, 13, 24, 28, 20, 19, 40,
    7, 15, 22, 28, 28, 22, 23, 39, 4, 26, 30, 19, 30, 19, 22, 35,
    0, 22, 19, 19, 0, 0, 0, 41, 0, 25, 26, 24, 0, 0, 0, 39,
    0, 30, 29, 28, 0, 0, 0, 40, 4, 29, 25, 12, 31, 23, 20, 41,
    0, 14, 0, 0, 0, 0, 0, 34, 6, 14, 28, 28, 28, 28, 21, 38,
    0, 30, 0, 0, 28, 29, 0, 40, 0, 30, 0, 0, 29, 28, 0, 40,
    0, 30, 28, 29, 0, 0, 0, 40, 0, 30, 29, 28, 0, 0, 0, 40,
    0, 32, 0, 0, 0, 0, 0, 38, 8, 32, 29, 29, 29, 29, 21, 34,
    1, 0, 17, 17, 17, 17, 16, 36, 0, 21, 20, 20, 20, 20, 18, 43,
    4, 29, 23, 31, 12, 25, 20, 41, 4, 29, 31, 23, 25, 12, 20, 41,
    4, 29, 12, 25, 23, 31, 20, 41, 4, 29, 25, 12, 31, 23, 20, 41,
    8, 32, 29, 29, 29, 29, 21, 34, 3, 33, 27, 27, 27, 27, 11, 42]
/-- Core action. -/
def action : Fin 256 → Fin 8 := ![0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 5, 6, 2, 1, 5, 3,
    0, 0, 0, 0, 2, 2, 4, 6, 0, 6, 7, 0, 2, 6, 4, 4,
    0, 0, 0, 4, 0, 0, 0, 0, 0, 6, 7, 6, 0, 0, 0, 0,
    0, 3, 0, 0, 0, 0, 0, 0, 5, 7, 7, 5, 2, 2, 5, 5,
    0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 6, 5, 1, 2, 5, 3,
    0, 6, 0, 7, 6, 2, 4, 4, 0, 0, 0, 0, 2, 2, 4, 6,
    0, 6, 6, 7, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0,
    0, 3, 0, 0, 0, 0, 0, 0, 5, 7, 5, 7, 2, 2, 5, 5,
    0, 1, 0, 0, 0, 0, 0, 0, 1, 6, 5, 5, 5, 5, 2, 5,
    0, 1, 0, 0, 2, 2, 0, 2, 0, 1, 0, 0, 2, 2, 0, 2,
    0, 1, 2, 2, 0, 0, 0, 2, 0, 1, 2, 2, 0, 0, 0, 2,
    0, 0, 0, 0, 0, 0, 0, 0, 2, 5, 5, 5, 5, 5, 5, 7,
    0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 4, 0,
    4, 6, 0, 0, 6, 4, 4, 4, 4, 6, 0, 0, 4, 6, 4, 4,
    4, 6, 6, 4, 0, 0, 4, 4, 4, 6, 4, 6, 0, 0, 4, 4,
    0, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 4, 4, 6, 4]
/-- Anchor action. -/
def permutation : Fin 256 → Fin 24 := ![0, 6, 12, 19, 0, 0, 0, 15, 6, 6, 13, 19, 8, 10, 16, 8,
    12, 0, 12, 5, 14, 11, 16, 16, 19, 1, 12, 19, 15, 20, 22, 22,
    0, 6, 12, 19, 0, 0, 0, 15, 0, 7, 13, 19, 0, 0, 0, 11,
    0, 6, 13, 19, 0, 0, 0, 17, 16, 6, 13, 19, 15, 11, 22, 23,
    0, 7, 13, 18, 0, 0, 0, 21, 7, 7, 13, 19, 8, 10, 22, 10,
    13, 0, 13, 18, 14, 21, 16, 16, 18, 1, 3, 18, 9, 20, 22, 22,
    0, 6, 13, 19, 0, 0, 0, 9, 0, 7, 13, 18, 0, 0, 0, 21,
    0, 7, 13, 19, 0, 0, 0, 23, 22, 7, 13, 19, 9, 21, 16, 17,
    0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 13, 19, 15, 21, 16, 16,
    0, 0, 0, 0, 15, 21, 0, 16, 0, 1, 0, 0, 15, 21, 0, 22,
    0, 6, 13, 19, 0, 0, 0, 17, 0, 7, 13, 19, 0, 0, 0, 23,
    0, 0, 0, 0, 0, 0, 0, 16, 16, 0, 13, 19, 15, 21, 16, 16,
    16, 0, 13, 19, 15, 21, 16, 16, 16, 0, 13, 19, 15, 21, 16, 0,
    17, 0, 13, 5, 15, 21, 23, 22, 23, 1, 3, 19, 15, 21, 17, 16,
    16, 6, 13, 19, 15, 11, 22, 23, 22, 7, 13, 19, 9, 21, 16, 17,
    16, 0, 13, 19, 15, 21, 16, 16, 16, 0, 13, 19, 15, 21, 16, 16]

/-- Every eligible index has the displayed exact symmetry witness. -/
theorem witness (i : Fin 256) :
    HighBoundary (zeroEncodedAt (blockIndex 13 i)) →
    transformedState (action i) (anchorPermutation (permutation i))
      (ZeroSyndrome.Catalogue.state (orbit i)) = zeroEncodedAt (blockIndex 13 i) := by
  revert i
  decide
end Gallai.Certificate.ZeroSyndrome.Coverage.Block13
