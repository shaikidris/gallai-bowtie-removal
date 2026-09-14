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
theorem highZero_card_9 : (highZeroBlock 9).card = 6 := by decide
theorem zero_check_9 : ∀ rem : Fin 32,
    HighZero (⟨9 * 32 + rem.val, by omega⟩ : Fin 1024) →
      NormalizesZero (decode (⟨9 * 32 + rem.val, by omega⟩))
        (normalizationWitness (⟨9 * 32 + rem.val, by omega⟩)).1
        (normalizationWitness (⟨9 * 32 + rem.val, by omega⟩)).2.1
        (normalizationWitness (⟨9 * 32 + rem.val, by omega⟩)).2.2 := by decide
end Gallai.Certificate.ThreeAnchor.ZeroOrbits
