/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeCatalogue
import Gallai.Certificates.ZeroSyndromeIndex
import Gallai.Certificates.CompletedStarSymmetry
import Gallai.Certificates.CompletedStarCoverage.Permutations

/-! # Zero-state coverage block 01
Source SHA256 32c2c172fa37de8b8de229fb2f531543e2e9274cfa5316796c582c6989ebdd59. Ordinary decide checks every guarded equality.
-/
namespace Gallai.Certificate.ZeroSyndrome.Coverage.Block01
open CompletedStar
open CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Representative index; excluded inputs use an irrelevant default. -/
def orbit : Fin 256 → Fin 44 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 17, 13, 35,
    0, 0, 0, 13, 0, 13, 17, 35, 1, 15, 15, 14, 14, 15, 15, 0,
    0, 0, 0, 10, 0, 0, 0, 36, 0, 17, 13, 13, 0, 0, 0, 35,
    0, 13, 17, 13, 0, 0, 0, 35, 0, 12, 12, 0, 16, 12, 12, 34,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 17, 0, 13, 35,
    1, 15, 14, 15, 15, 14, 15, 0, 0, 0, 13, 0, 13, 0, 17, 35,
    0, 17, 13, 13, 0, 0, 0, 35, 0, 0, 10, 0, 0, 0, 0, 36,
    0, 13, 13, 17, 0, 0, 0, 35, 0, 12, 0, 12, 12, 16, 12, 34,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 14, 15, 15, 15, 15, 14, 0,
    0, 13, 0, 0, 17, 13, 0, 35, 0, 13, 0, 0, 13, 17, 0, 35,
    0, 13, 17, 13, 0, 0, 0, 35, 0, 13, 13, 17, 0, 0, 0, 35,
    0, 10, 0, 0, 0, 0, 0, 36, 0, 0, 12, 12, 12, 12, 16, 34,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 12, 12, 12, 12, 0, 34,
    0, 12, 16, 12, 12, 0, 12, 34, 0, 12, 12, 16, 0, 12, 12, 34,
    0, 12, 12, 0, 16, 12, 12, 34, 0, 12, 0, 12, 12, 16, 12, 34,
    0, 0, 12, 12, 12, 12, 16, 34, 0, 11, 11, 11, 11, 11, 11, 37]
/-- Core action. -/
def action : Fin 256 → Fin 8 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 5, 4,
    0, 0, 0, 4, 0, 5, 4, 4, 4, 4, 4, 4, 5, 4, 4, 0,
    0, 0, 0, 4, 0, 0, 0, 4, 0, 4, 5, 4, 0, 0, 0, 4,
    0, 5, 4, 4, 0, 0, 0, 4, 5, 5, 5, 0, 5, 5, 5, 5,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 5, 4,
    4, 4, 4, 4, 4, 5, 4, 0, 0, 0, 4, 0, 5, 0, 4, 4,
    0, 4, 4, 5, 0, 0, 0, 4, 0, 0, 4, 0, 0, 0, 0, 4,
    0, 5, 4, 4, 0, 0, 0, 4, 5, 5, 0, 5, 5, 5, 5, 5,
    0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 4, 4, 4, 4, 5, 0,
    0, 4, 0, 0, 4, 5, 0, 4, 0, 4, 0, 0, 5, 4, 0, 4,
    0, 4, 4, 5, 0, 0, 0, 4, 0, 4, 5, 4, 0, 0, 0, 4,
    0, 4, 0, 0, 0, 0, 0, 4, 5, 0, 5, 5, 5, 5, 5, 5,
    0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 4, 4, 4, 4, 0, 4,
    4, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 4, 0, 4, 4, 4,
    4, 4, 4, 0, 4, 4, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4,
    4, 0, 4, 4, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 4, 4]
/-- Anchor action. -/
def permutation : Fin 256 → Fin 24 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 10, 22, 10,
    0, 0, 0, 18, 0, 20, 16, 16, 4, 1, 3, 4, 8, 20, 22, 0,
    0, 0, 0, 4, 0, 0, 0, 8, 0, 7, 3, 5, 0, 0, 0, 7,
    0, 1, 13, 4, 0, 0, 0, 13, 4, 7, 13, 0, 8, 10, 16, 8,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 8, 0, 16, 8,
    2, 0, 2, 5, 14, 10, 16, 0, 0, 0, 12, 0, 14, 0, 22, 22,
    0, 6, 3, 5, 0, 0, 0, 6, 0, 0, 2, 0, 0, 0, 0, 10,
    0, 0, 2, 19, 0, 0, 0, 19, 2, 6, 0, 19, 8, 10, 22, 10,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 8, 10, 16, 0,
    0, 7, 0, 0, 14, 10, 0, 14, 0, 6, 0, 0, 8, 20, 0, 20,
    0, 1, 12, 4, 0, 0, 0, 12, 0, 0, 2, 18, 0, 0, 0, 18,
    0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 12, 18, 14, 20, 16, 16,
    0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 3, 5, 9, 11, 0, 0,
    10, 1, 2, 4, 15, 0, 17, 2, 8, 0, 2, 4, 0, 21, 23, 4,
    4, 7, 13, 0, 8, 10, 16, 8, 2, 6, 0, 19, 8, 10, 22, 10,
    0, 0, 12, 18, 14, 20, 16, 16, 0, 0, 2, 4, 8, 10, 16, 0]

/-- Every eligible index has the displayed exact symmetry witness. -/
theorem witness (i : Fin 256) :
    HighBoundary (zeroEncodedAt (blockIndex 1 i)) →
    transformedState (action i) (anchorPermutation (permutation i))
      (ZeroSyndrome.Catalogue.state (orbit i)) = zeroEncodedAt (blockIndex 1 i) := by
  revert i
  decide
end Gallai.Certificate.ZeroSyndrome.Coverage.Block01
