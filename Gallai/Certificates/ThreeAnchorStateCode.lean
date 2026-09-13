/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Mathlib.Tactic.FinCases

/-! # Every actual three-anchor state has a finite coverage index -/

namespace Gallai.Certificate.ThreeAnchor.Orbits

/-- The five row codes are the five base-four digits of the coverage index. -/
def encode (s : State) : Fin 1024 :=
  ⟨(s 0).val + 4 * (s 1).val + 16 * (s 2).val + 64 * (s 3).val + 256 * (s 4).val,
    by have h0 := (s 0).isLt; have h1 := (s 1).isLt
       have h2 := (s 2).isLt; have h3 := (s 3).isLt; have h4 := (s 4).isLt
       omega⟩

/-- The finite index loses no row information. -/
theorem decode_encode (s : State) : decode (encode s) = s := by
  have h0 := (s 0).isLt
  have h1 := (s 1).isLt
  have h2 := (s 2).isLt
  have h3 := (s 3).isLt
  have h4 := (s 4).isLt
  funext i
  apply Fin.ext
  fin_cases i
  · change (encode s).val / 1 % 4 = (s 0).val
    dsimp [encode]
    omega
  · change (encode s).val / 4 % 4 = (s 1).val
    dsimp [encode]
    omega
  · change (encode s).val / 16 % 4 = (s 2).val
    dsimp [encode]
    omega
  · change (encode s).val / 64 % 4 = (s 3).val
    dsimp [encode]
    omega
  · change (encode s).val / 256 % 4 = (s 4).val
    dsimp [encode]
    omega

/-- Arbitrary high pair states, not only a preselected list, enter the partition. -/
theorem state_pair_partition (s : State)
    (ha : 3 ≤ (Finset.univ.filter fun i : Fin 5 => i ≠ 0 ∧ s i ≠ 0).card)
    (hs : (syndrome s).card = 2) :
    encode s ∈ syntheticCodes ∨ encode s ∈ retainedCodes := by
  apply pair_partition
  simpa only [highPair, decode_encode] using And.intro ha hs

end Gallai.Certificate.ThreeAnchor.Orbits
