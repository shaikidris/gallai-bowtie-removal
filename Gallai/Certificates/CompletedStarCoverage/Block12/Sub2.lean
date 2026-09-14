/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarCoverage.Block12.Core

namespace Gallai.Certificate.CompletedStar.Coverage.Block12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_chunk_2 (r : Fin 64) :
    transformedState (action ⟨2 * 64 + r.val, by omega⟩)
      (anchorPermutation (permutation ⟨2 * 64 + r.val, by omega⟩))
      (Catalogue.state (orbit ⟨2 * 64 + r.val, by omega⟩)) =
        encodedAt (blockIndex 12 ⟨2 * 64 + r.val, by omega⟩) := by
  revert r
  decide
end Gallai.Certificate.CompletedStar.Coverage.Block12
