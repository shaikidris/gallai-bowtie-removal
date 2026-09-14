/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeCoverage.Block08.Core

namespace Gallai.Certificate.ZeroSyndrome.Coverage.Block08
open CompletedStar
open CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_chunk_3 (r : Fin 64) :
    HighBoundary (zeroEncodedAt (blockIndex 8 ⟨3 * 64 + r.val, by omega⟩)) →
    transformedState (action ⟨3 * 64 + r.val, by omega⟩)
      (anchorPermutation (permutation ⟨3 * 64 + r.val, by omega⟩))
      (ZeroSyndrome.Catalogue.state (orbit ⟨3 * 64 + r.val, by omega⟩)) =
        zeroEncodedAt (blockIndex 8 ⟨3 * 64 + r.val, by omega⟩) := by
  revert r
  decide
end Gallai.Certificate.ZeroSyndrome.Coverage.Block08
