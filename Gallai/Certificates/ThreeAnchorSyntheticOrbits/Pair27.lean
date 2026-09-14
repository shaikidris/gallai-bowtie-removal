/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem pair_chunk_27 : ∀ rem : Fin 32,
    highPair (⟨27 * 32 + rem.val, by omega⟩ : Fin 1024) →
    (⟨27 * 32 + rem.val, by omega⟩ : Fin 1024) ∈ syntheticCodes ∨
    (⟨27 * 32 + rem.val, by omega⟩ : Fin 1024) ∈ retainedCodes := by decide
end Gallai.Certificate.ThreeAnchor.Orbits
