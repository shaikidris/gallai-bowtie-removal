/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair00
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair01
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair02
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair03
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair04
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair05
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair06
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair07
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair08
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair09
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair10
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair11
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair12
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair13
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair14
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair15
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair16
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair17
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair18
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair19
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair20
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair21
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair22
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair23
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair24
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair25
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair26
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair27
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair28
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair29
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair30
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Pair31
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Block00
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Block01
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Block02
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Block03
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Block04
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Block05
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Block06
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Block07
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Block08
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Block09
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Block10
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Block11
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Block12
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Block13
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Block14
import Mathlib.Tactic.FinCases

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem pair_chunked (q rem : Fin 32) :
    highPair (⟨q.val * 32 + rem.val, by omega⟩ : Fin 1024) →
    (⟨q.val * 32 + rem.val, by omega⟩ : Fin 1024) ∈ syntheticCodes ∨
    (⟨q.val * 32 + rem.val, by omega⟩ : Fin 1024) ∈ retainedCodes := by
  fin_cases q
  · exact pair_chunk_0 rem
  · exact pair_chunk_1 rem
  · exact pair_chunk_2 rem
  · exact pair_chunk_3 rem
  · exact pair_chunk_4 rem
  · exact pair_chunk_5 rem
  · exact pair_chunk_6 rem
  · exact pair_chunk_7 rem
  · exact pair_chunk_8 rem
  · exact pair_chunk_9 rem
  · exact pair_chunk_10 rem
  · exact pair_chunk_11 rem
  · exact pair_chunk_12 rem
  · exact pair_chunk_13 rem
  · exact pair_chunk_14 rem
  · exact pair_chunk_15 rem
  · exact pair_chunk_16 rem
  · exact pair_chunk_17 rem
  · exact pair_chunk_18 rem
  · exact pair_chunk_19 rem
  · exact pair_chunk_20 rem
  · exact pair_chunk_21 rem
  · exact pair_chunk_22 rem
  · exact pair_chunk_23 rem
  · exact pair_chunk_24 rem
  · exact pair_chunk_25 rem
  · exact pair_chunk_26 rem
  · exact pair_chunk_27 rem
  · exact pair_chunk_28 rem
  · exact pair_chunk_29 rem
  · exact pair_chunk_30 rem
  · exact pair_chunk_31 rem

/-- Exhaustive classification of the pair-syndrome domain. -/
theorem pair_partition : ∀ n : Fin 1024, highPair n →
    n ∈ syntheticCodes ∨ n ∈ retainedCodes := by
  intro n
  let q : Fin 32 := ⟨n.val / 32, by omega⟩
  let r : Fin 32 := ⟨n.val % 32, by omega⟩
  have h := pair_chunked q r
  have heq : (⟨q.val * 32 + r.val, by omega⟩ : Fin 1024) = n := by
    apply Fin.ext
    dsimp [q, r]
    omega
  simpa only [heq] using h

end Gallai.Certificate.ThreeAnchor.Orbits
