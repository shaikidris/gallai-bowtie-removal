/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorZeroOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.ZeroOrbits
open Orbits RetainedOrbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem highZero_card_0 : (highZeroBlock 0).card = 0 := by decide
theorem zero_check_0 : ∀ rem : Fin 32,
    HighZero (⟨0 * 32 + rem.val, by omega⟩ : Fin 1024) →
      NormalizesZero (decode (⟨0 * 32 + rem.val, by omega⟩))
        (normalizationWitness (⟨0 * 32 + rem.val, by omega⟩)).1
        (normalizationWitness (⟨0 * 32 + rem.val, by omega⟩)).2.1
        (normalizationWitness (⟨0 * 32 + rem.val, by omega⟩)).2.2 := by decide
end Gallai.Certificate.ThreeAnchor.ZeroOrbits
