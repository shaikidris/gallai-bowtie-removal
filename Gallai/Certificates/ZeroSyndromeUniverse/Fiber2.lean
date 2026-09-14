/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeUniverse.Core

namespace Gallai.Certificate.ZeroSyndrome
open CompletedStar
open scoped Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- A first-row fiber of the high-activity domain. -/
theorem highInputs_first_2 :
    ((Finset.univ : Finset (Fin 8 × Fin 8 × Fin 8)).filter
      (fun p => HighBoundary (zeroEncodedState (restTriple 2 p)))).card = 380 := by decide
end Gallai.Certificate.ZeroSyndrome
