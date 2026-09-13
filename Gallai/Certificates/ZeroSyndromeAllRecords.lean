/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeRecordSymmetry
import Gallai.Certificates.ZeroSyndromeCoverage
import Gallai.Certificates.ZeroSyndromeRepresentativeRecords

/-! # Accepted zero-syndrome records for all original states and interfaces -/
namespace Gallai.Certificate.ZeroSyndrome
open CompletedStar

/-- The vertex action corresponding to core-row and anchor-bit actions. -/
def stateEquiv (k : Fin 8) (σ : Equiv.Perm (Fin 4)) : Equiv.Perm Star.Vertex :=
  (coreEquiv k).trans (anchorEquiv σ)

/-- The combined action sends each old anchor to its indexed image. -/
theorem stateEquiv_anchor (k : Fin 8) (σ : Equiv.Perm (Fin 4)) (j : Fin 4) :
    stateEquiv k σ (anchor j) = anchor (σ j) := by
  change anchorEquiv σ (coreEquiv k (anchor j)) = _
  rw [coreEquiv_anchor]
  exact permuteAnchor_anchor σ j

/-- Deleted vertices remain deleted vertices under the action. -/
theorem stateEquiv_fresh (k : Fin 8) (σ : Equiv.Perm (Fin 4)) :
    ∀ v ∈ Star.fresh, stateEquiv k σ v ∈ Star.fresh := by
  revert k σ
  decide

/-- The action realizes exactly the transformed original incidence state. -/
theorem stateEquiv_target (k : Fin 8) (σ : Equiv.Perm (Fin 4)) (s : State) :
    (targetEdges s).map (stateEquiv k σ).toEmbedding.sym2Map =
      targetEdges (transformedState k σ s) := by
  apply targetEdges_equivariant s (transformedState k σ s) (stateEquiv k σ)
    (coreRowEquiv k).symm σ
  · revert k σ
    decide
  · intro i
    change anchorEquiv σ (coreEquiv k (core i)) = _
    rw [coreEquiv_core]
    have hr (j : Fin 5) : anchorEquiv σ (core j) = core j := by fin_cases j <;> rfl
    exact hr _
  · exact stateEquiv_anchor k σ
  · intro i j
    change (permuteMask σ (s (coreRowEquiv k ((coreRowEquiv k).symm i)))).val.testBit
      (σ j).val = _
    rw [Equiv.apply_symm_apply, permuteMask_bit, Equiv.symm_apply_apply]

/-- Every high original state has a two-credit record at every legal interface. -/
theorem all_two_records (s : State) (hs : HighZeroState s) (c l : Labels)
    (hi : (c, l) ∈ interfaces) : ∃ tails added, TwoCreditAccepted s c l tails added := by
  obtain ⟨o, k, σ, rfl⟩ := Coverage.highZeroState_covered s hs
  obtain ⟨tails, added, h⟩ := Catalogue.two_records o _ _ (pullLabels_interface σ hi)
  exact ⟨_, _, h.map_pullback (stateEquiv k σ) σ (stateEquiv_anchor k σ)
    (stateEquiv_fresh k σ) (stateEquiv_target k σ _) hi⟩

/-- Every high original state has a one-credit record at every separated interface. -/
theorem all_one_records (s : State) (hs : HighZeroState s) (c : Labels)
    (hi : c ∈ separatedPartitions) : ∃ tails added, OneCreditAccepted s c tails added := by
  obtain ⟨o, k, σ, rfl⟩ := Coverage.highZeroState_covered s hs
  obtain ⟨tails, added, h⟩ := Catalogue.one_records o _ (pullLabels_separated σ hi)
  exact ⟨_, _, h.map_pullback (stateEquiv k σ) σ (stateEquiv_anchor k σ)
    (stateEquiv_fresh k σ) (stateEquiv_target k σ _) hi⟩

end Gallai.Certificate.ZeroSyndrome
