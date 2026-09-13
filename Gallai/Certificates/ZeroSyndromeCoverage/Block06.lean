/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeCatalogue
import Gallai.Certificates.ZeroSyndromeIndex
import Gallai.Certificates.CompletedStarSymmetry
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Zero-state coverage block 06
Source SHA256 32c2c172fa37de8b8de229fb2f531543e2e9274cfa5316796c582c6989ebdd59. Ordinary decide checks every guarded equality.
-/
namespace Gallai.Certificate.ZeroSyndrome.Coverage.Block06
open CompletedStar
open CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Representative index; excluded inputs use an irrelevant default. -/
def orbit : Fin 256 → Fin 44 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 13, 0, 15, 35,
    0, 12, 0, 0, 13, 15, 0, 35, 0, 0, 0, 0, 14, 0, 0, 34,
    0, 13, 13, 14, 10, 13, 13, 0, 0, 0, 15, 0, 13, 0, 12, 35,
    0, 15, 0, 0, 13, 12, 0, 35, 1, 17, 17, 16, 0, 17, 17, 36,
    0, 0, 12, 0, 13, 0, 15, 35, 0, 0, 24, 0, 25, 0, 26, 39,
    4, 19, 19, 22, 26, 30, 30, 35, 0, 0, 28, 0, 30, 0, 29, 40,
    5, 20, 24, 19, 19, 28, 13, 40, 0, 0, 19, 0, 22, 0, 19, 41,
    7, 22, 28, 23, 15, 28, 22, 39, 4, 23, 12, 20, 29, 31, 25, 41,
    0, 12, 0, 0, 13, 15, 0, 35, 4, 19, 19, 22, 26, 30, 30, 35,
    0, 24, 0, 0, 25, 26, 0, 39, 0, 28, 0, 0, 30, 29, 0, 40,
    5, 24, 20, 19, 19, 13, 28, 40, 7, 28, 22, 23, 15, 22, 28, 39,
    0, 19, 0, 0, 22, 19, 0, 41, 4, 12, 23, 20, 29, 25, 31, 41,
    0, 0, 0, 0, 14, 0, 0, 34, 0, 0, 28, 0, 30, 0, 29, 40,
    0, 28, 0, 0, 30, 29, 0, 40, 0, 0, 0, 0, 32, 0, 0, 38,
    6, 28, 28, 21, 14, 28, 28, 38, 0, 0, 29, 0, 30, 0, 28, 40,
    0, 29, 0, 0, 30, 28, 0, 40, 8, 29, 29, 21, 32, 29, 29, 34]
/-- Core action. -/
def action : Fin 256 → Fin 8 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 2, 2,
    0, 2, 0, 0, 3, 2, 0, 2, 0, 0, 0, 0, 3, 0, 0, 2,
    2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 2, 0, 3, 0, 2, 2,
    0, 2, 0, 0, 3, 2, 0, 2, 2, 2, 2, 2, 0, 2, 2, 2,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0,
    0, 2, 0, 4, 0, 2, 0, 6, 0, 0, 0, 0, 3, 0, 0, 0,
    1, 2, 5, 5, 1, 1, 6, 3, 0, 0, 7, 0, 6, 0, 6, 0,
    0, 2, 7, 4, 6, 6, 0, 4, 5, 2, 7, 5, 7, 2, 5, 5,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 4, 0, 0, 2, 6,
    0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0,
    1, 5, 2, 5, 1, 6, 1, 3, 0, 7, 2, 4, 6, 0, 6, 4,
    0, 7, 0, 0, 6, 6, 0, 0, 5, 7, 2, 5, 7, 5, 2, 5,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2, 2,
    0, 2, 0, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 5, 5, 2, 6, 5, 5, 5, 0, 0, 2, 0, 1, 0, 2, 2,
    0, 2, 0, 0, 1, 2, 0, 2, 2, 5, 5, 5, 5, 5, 5, 7]
/-- Anchor action. -/
def permutation : Fin 256 → Fin 24 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 8, 0, 22, 1,
    0, 0, 0, 0, 14, 20, 0, 3, 0, 0, 0, 0, 8, 0, 0, 4,
    8, 6, 12, 4, 8, 11, 17, 0, 0, 0, 3, 0, 9, 0, 23, 20,
    0, 1, 0, 0, 15, 21, 0, 22, 4, 1, 3, 4, 0, 20, 22, 4,
    0, 0, 2, 0, 8, 0, 22, 1, 0, 0, 2, 0, 8, 0, 22, 1,
    2, 0, 2, 5, 14, 10, 16, 5, 0, 0, 3, 0, 8, 0, 22, 4,
    8, 6, 3, 5, 8, 11, 22, 6, 0, 0, 3, 0, 9, 0, 22, 10,
    22, 1, 2, 19, 15, 21, 22, 19, 5, 1, 3, 19, 8, 10, 22, 18,
    0, 0, 0, 0, 14, 20, 0, 3, 0, 0, 2, 4, 8, 10, 16, 4,
    0, 0, 0, 0, 14, 20, 0, 3, 0, 1, 0, 0, 14, 20, 0, 5,
    14, 1, 12, 4, 14, 20, 17, 12, 20, 0, 3, 18, 9, 20, 23, 18,
    0, 1, 0, 0, 15, 20, 0, 16, 4, 1, 3, 18, 14, 20, 16, 19,
    0, 0, 0, 0, 8, 0, 0, 4, 0, 0, 3, 0, 8, 0, 22, 4,
    0, 1, 0, 0, 14, 20, 0, 5, 0, 0, 0, 0, 8, 0, 0, 4,
    8, 1, 3, 4, 8, 20, 22, 4, 0, 0, 3, 0, 9, 0, 22, 18,
    0, 1, 0, 0, 15, 20, 0, 19, 4, 1, 3, 4, 8, 20, 22, 4]

/-- Every eligible index has the displayed exact symmetry witness. -/
theorem witness (i : Fin 256) :
    HighBoundary (zeroEncodedAt (blockIndex 6 i)) →
    transformedState (action i) (anchorPermutation (permutation i))
      (ZeroSyndrome.Catalogue.state (orbit i)) = zeroEncodedAt (blockIndex 6 i) := by
  revert i
  decide
end Gallai.Certificate.ZeroSyndrome.Coverage.Block06
