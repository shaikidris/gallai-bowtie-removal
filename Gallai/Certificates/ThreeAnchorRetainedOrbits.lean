/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Core
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block00
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block01
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block02
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block03
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block04
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block05
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block06
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block07
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block08
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block09
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block10
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block11
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block12
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block13
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block14
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block15
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block16
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block17
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block18
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block19
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block20
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block21
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block22
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block23
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block24
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block25
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block26
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block27
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block28
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block29
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block30
import Gallai.Certificates.ThreeAnchorRetainedOrbits.Block31
import Mathlib.Tactic.FinCases

/-! # Exhaustive normalization of retained three-anchor states -/
namespace Gallai.Certificate.ThreeAnchor.RetainedOrbits
open Orbits

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem retained_chunked (q rem : Fin 32) :
    (⟨q.val * 32 + rem.val, by omega⟩ : Fin 1024) ∈ retainedCodes →
    ∃ typ : Fin 6, ∃ c : Fin 8, ∃ a : Fin 6,
      Normalizes (decode (⟨q.val * 32 + rem.val, by omega⟩)) typ c a := by
  fin_cases q
  · exact retained_chunk_0 rem
  · exact retained_chunk_1 rem
  · exact retained_chunk_2 rem
  · exact retained_chunk_3 rem
  · exact retained_chunk_4 rem
  · exact retained_chunk_5 rem
  · exact retained_chunk_6 rem
  · exact retained_chunk_7 rem
  · exact retained_chunk_8 rem
  · exact retained_chunk_9 rem
  · exact retained_chunk_10 rem
  · exact retained_chunk_11 rem
  · exact retained_chunk_12 rem
  · exact retained_chunk_13 rem
  · exact retained_chunk_14 rem
  · exact retained_chunk_15 rem
  · exact retained_chunk_16 rem
  · exact retained_chunk_17 rem
  · exact retained_chunk_18 rem
  · exact retained_chunk_19 rem
  · exact retained_chunk_20 rem
  · exact retained_chunk_21 rem
  · exact retained_chunk_22 rem
  · exact retained_chunk_23 rem
  · exact retained_chunk_24 rem
  · exact retained_chunk_25 rem
  · exact retained_chunk_26 rem
  · exact retained_chunk_27 rem
  · exact retained_chunk_28 rem
  · exact retained_chunk_29 rem
  · exact retained_chunk_30 rem
  · exact retained_chunk_31 rem

/-- Every retained code in the independently partitioned high-pair universe
normalizes to one of the six reconstructed types. Ordinary kernel reduction
checks the entire listed universe; no native decision oracle is used. -/
theorem retained_coverage : ∀ n ∈ retainedCodes,
    ∃ r : Fin 6, ∃ c : Fin 8, ∃ a : Fin 6, Normalizes (decode n) r c a := by
  intro n
  let q : Fin 32 := ⟨n.val / 32, by omega⟩
  let r : Fin 32 := ⟨n.val % 32, by omega⟩
  have h := retained_chunked q r
  have heq : (⟨q.val * 32 + r.val, by omega⟩ : Fin 1024) = n := by
    apply Fin.ext
    dsimp [q, r]
    omega
  simpa only [heq] using h

/-- The coverage index transfers back to arbitrary row functions. -/
theorem state_coverage (s : State) (hs : encode s ∈ retainedCodes) :
    ∃ r : Fin 6, ∃ c : Fin 8, ∃ a : Fin 6, Normalizes s r c a := by
  have h := retained_coverage (encode s) hs
  simpa only [decode_encode] using h

end Gallai.Certificate.ThreeAnchor.RetainedOrbits
