/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeCoverage.Block01.Core

namespace Gallai.Certificate.ZeroSyndrome.Coverage.Block01
open CompletedStar
open CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_chunk_1 (r : Fin 64) :
    HighBoundary (zeroEncodedAt (blockIndex 1 ⟨1 * 64 + r.val, by omega⟩)) →
    transformedState (action ⟨1 * 64 + r.val, by omega⟩)
      (anchorPermutation (permutation ⟨1 * 64 + r.val, by omega⟩))
      (ZeroSyndrome.Catalogue.state (orbit ⟨1 * 64 + r.val, by omega⟩)) =
        zeroEncodedAt (blockIndex 1 ⟨1 * 64 + r.val, by omega⟩) := by
  revert r
  decide
end Gallai.Certificate.ZeroSyndrome.Coverage.Block01
