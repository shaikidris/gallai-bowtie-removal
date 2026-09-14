/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.RetainedOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem retained_chunk_14 : ∀ rem : Fin 32,
    (⟨14 * 32 + rem.val, by omega⟩ : Fin 1024) ∈ retainedCodes →
    ∃ typ : Fin 6, ∃ c : Fin 8, ∃ a : Fin 6,
      Normalizes (decode (⟨14 * 32 + rem.val, by omega⟩)) typ c a := by decide
end Gallai.Certificate.ThreeAnchor.RetainedOrbits
