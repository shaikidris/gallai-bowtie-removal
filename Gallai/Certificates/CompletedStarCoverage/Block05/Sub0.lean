/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarCoverage.Block05.Core

namespace Gallai.Certificate.CompletedStar.Coverage.Block05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_chunk_0 (r : Fin 64) :
    transformedState (action ⟨0 * 64 + r.val, by omega⟩)
      (anchorPermutation (permutation ⟨0 * 64 + r.val, by omega⟩))
      (Catalogue.state (orbit ⟨0 * 64 + r.val, by omega⟩)) =
        encodedAt (blockIndex 5 ⟨0 * 64 + r.val, by omega⟩) := by
  revert r
  decide
end Gallai.Certificate.CompletedStar.Coverage.Block05
