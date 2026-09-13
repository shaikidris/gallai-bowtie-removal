/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeCatalogue
import Gallai.Certificates.ZeroSyndromeIndex
import Gallai.Certificates.CompletedStarSymmetry
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Zero-state coverage block 02
Source SHA256 32c2c172fa37de8b8de229fb2f531543e2e9274cfa5316796c582c6989ebdd59. Ordinary decide checks every guarded equality.
-/
namespace Gallai.Certificate.ZeroSyndrome.Coverage.Block02
open CompletedStar
open CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Representative index; excluded inputs use an irrelevant default. -/
def orbit : Fin 256 → Fin 44 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 34,
    0, 0, 0, 12, 0, 15, 13, 35, 0, 0, 12, 0, 15, 0, 13, 35,
    0, 0, 0, 15, 0, 12, 13, 35, 0, 0, 15, 0, 12, 0, 13, 35,
    0, 14, 13, 13, 13, 13, 10, 0, 1, 16, 17, 17, 17, 17, 0, 36,
    0, 0, 0, 0, 0, 0, 14, 34, 0, 0, 0, 0, 0, 0, 32, 38,
    0, 0, 0, 28, 0, 29, 30, 40, 0, 0, 28, 0, 29, 0, 30, 40,
    0, 0, 0, 29, 0, 28, 30, 40, 0, 0, 29, 0, 28, 0, 30, 40,
    6, 21, 28, 28, 28, 28, 14, 38, 8, 21, 29, 29, 29, 29, 32, 34,
    0, 0, 0, 12, 0, 15, 13, 35, 0, 0, 0, 28, 0, 29, 30, 40,
    0, 0, 0, 24, 0, 26, 25, 39, 4, 22, 19, 19, 30, 30, 26, 35,
    0, 0, 0, 19, 0, 19, 22, 41, 7, 23, 22, 28, 28, 22, 15, 39,
    5, 19, 20, 24, 28, 13, 19, 40, 4, 20, 23, 12, 31, 25, 29, 41,
    0, 0, 12, 0, 15, 0, 13, 35, 0, 0, 28, 0, 29, 0, 30, 40,
    4, 22, 19, 19, 30, 30, 26, 35, 0, 0, 24, 0, 26, 0, 25, 39,
    7, 23, 28, 22, 22, 28, 15, 39, 0, 0, 19, 0, 19, 0, 22, 41,
    5, 19, 24, 20, 13, 28, 19, 40, 4, 20, 12, 23, 25, 31, 29, 41]
/-- Core action. -/
def action : Fin 256 → Fin 8 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2,
    0, 0, 0, 2, 0, 2, 3, 2, 0, 0, 2, 0, 2, 0, 3, 2,
    0, 0, 0, 2, 0, 2, 3, 2, 0, 0, 2, 0, 2, 0, 3, 2,
    2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 2, 2, 2, 2, 0, 2,
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 2, 0, 2, 1, 2, 0, 0, 2, 0, 2, 0, 1, 2,
    0, 0, 0, 2, 0, 2, 1, 2, 0, 0, 2, 0, 2, 0, 1, 2,
    1, 2, 5, 5, 5, 5, 6, 5, 2, 5, 5, 5, 5, 5, 5, 7,
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0,
    0, 0, 0, 0, 0, 4, 0, 0, 0, 4, 2, 0, 2, 0, 0, 6,
    0, 0, 0, 7, 0, 6, 6, 0, 0, 4, 2, 7, 6, 0, 6, 4,
    1, 5, 2, 5, 1, 6, 1, 3, 5, 5, 2, 7, 2, 5, 7, 5,
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0,
    0, 4, 0, 2, 0, 2, 0, 6, 0, 0, 0, 0, 4, 0, 0, 0,
    0, 4, 7, 2, 0, 6, 6, 4, 0, 0, 7, 0, 6, 0, 6, 0,
    1, 5, 5, 2, 6, 1, 1, 3, 5, 5, 7, 2, 5, 2, 7, 5]
/-- Anchor action. -/
def permutation : Fin 256 → Fin 24 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0,
    0, 0, 0, 5, 0, 10, 16, 2, 0, 0, 3, 0, 8, 0, 22, 4,
    0, 0, 0, 4, 0, 11, 17, 8, 0, 0, 2, 0, 9, 0, 23, 10,
    16, 0, 13, 19, 15, 21, 16, 0, 0, 0, 2, 4, 8, 10, 0, 0,
    0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 16, 0,
    0, 0, 0, 4, 0, 10, 16, 0, 0, 0, 2, 0, 8, 0, 22, 1,
    0, 0, 0, 4, 0, 10, 17, 6, 0, 0, 2, 0, 8, 0, 23, 7,
    16, 0, 2, 4, 8, 10, 16, 0, 0, 0, 2, 4, 8, 10, 16, 0,
    0, 0, 0, 5, 0, 10, 16, 2, 0, 0, 0, 4, 0, 10, 16, 0,
    0, 0, 0, 5, 0, 10, 16, 2, 5, 1, 3, 5, 14, 20, 22, 1,
    0, 0, 0, 4, 0, 10, 17, 14, 10, 7, 2, 5, 9, 10, 23, 7,
    16, 1, 13, 4, 15, 10, 16, 13, 1, 7, 2, 4, 14, 10, 16, 6,
    0, 0, 3, 0, 8, 0, 22, 4, 0, 0, 2, 0, 8, 0, 22, 1,
    3, 0, 3, 5, 14, 20, 16, 0, 0, 0, 3, 0, 8, 0, 22, 4,
    8, 6, 3, 4, 8, 11, 17, 6, 0, 0, 2, 0, 8, 0, 23, 20,
    22, 0, 2, 19, 8, 21, 22, 19, 0, 6, 2, 4, 8, 20, 22, 7]

/-- Every eligible index has the displayed exact symmetry witness. -/
theorem witness (i : Fin 256) :
    HighBoundary (zeroEncodedAt (blockIndex 2 i)) →
    transformedState (action i) (anchorPermutation (permutation i))
      (ZeroSyndrome.Catalogue.state (orbit i)) = zeroEncodedAt (blockIndex 2 i) := by
  revert i
  decide
end Gallai.Certificate.ZeroSyndrome.Coverage.Block02
