/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeUniverse.Core
import Gallai.Certificates.ZeroSyndromeUniverse.Fiber0
import Gallai.Certificates.ZeroSyndromeUniverse.Fiber1
import Gallai.Certificates.ZeroSyndromeUniverse.Fiber2
import Gallai.Certificates.ZeroSyndromeUniverse.Fiber3
import Gallai.Certificates.ZeroSyndromeUniverse.Fiber4
import Gallai.Certificates.ZeroSyndromeUniverse.Fiber5
import Gallai.Certificates.ZeroSyndromeUniverse.Fiber6
import Gallai.Certificates.ZeroSyndromeUniverse.Fiber7
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-! # Independent zero-syndrome incidence universe -/
namespace Gallai.Certificate.ZeroSyndrome
open CompletedStar
open scoped Finset

private theorem highInputs_fiber_eq (i : Fin 8) :
    highInputs.filter (fun q => q 0 = i) =
      Finset.univ.filter (fun q : Fin 4 → Fin 8 =>
        q 0 = i ∧ HighBoundary (zeroEncodedState q)) := by
  simp [highInputs, Finset.filter_filter, and_comm]

private def packRest (q : Fin 4 → Fin 8) : Fin 8 × Fin 8 × Fin 8 :=
  (q 1, q 2, q 3)

private theorem restTriple_zero (i : Fin 8) (p : Fin 8 × Fin 8 × Fin 8) :
    restTriple i p 0 = i := rfl

private theorem rest_pack (i : Fin 8) (q : Fin 4 → Fin 8) (h : q 0 = i) :
    restTriple i (packRest q) = q := by
  funext j
  fin_cases j <;> simp [restTriple, packRest, h]

private theorem pack_rest (i : Fin 8) (p : Fin 8 × Fin 8 × Fin 8) :
    packRest (restTriple i p) = p := by
  rcases p with ⟨a, b, c⟩
  simp [packRest, restTriple]

private theorem highInputs_first (i : Fin 8) :
    ((Finset.univ : Finset (Fin 8 × Fin 8 × Fin 8)).filter
      (fun p => HighBoundary (zeroEncodedState (restTriple i p)))).card =
      (![295, 380, 380, 380, 380, 380, 380, 472] : Fin 8 → ℕ) i := by
  fin_cases i
  · exact highInputs_first_0
  · exact highInputs_first_1
  · exact highInputs_first_2
  · exact highInputs_first_3
  · exact highInputs_first_4
  · exact highInputs_first_5
  · exact highInputs_first_6
  · exact highInputs_first_7

private theorem fiber_rest_card (i : Fin 8) :
    #{q ∈ highInputs | q 0 = i} =
      ((Finset.univ : Finset (Fin 8 × Fin 8 × Fin 8)).filter
        (fun p => HighBoundary (zeroEncodedState (restTriple i p)))).card := by
  rw [highInputs_fiber_eq]
  refine (Finset.card_nbij' (restTriple i) packRest ?_ ?_ ?_ ?_).symm
  · intro p hp
    have hb := (Finset.mem_filter.mp hp).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨restTriple_zero i p, hb⟩⟩
  · intro q hq
    have h := (Finset.mem_filter.mp hq).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa [rest_pack i q h.1] using h.2
  · intro p _hp
    exact pack_rest i p
  · intro q hq
    exact rest_pack i q (Finset.mem_filter.mp hq).2.1

/-- The complete original high-activity four-anchor domain has3047 states. -/
theorem highInputs_card : highInputs.card = 3047 := by
  have hi (i : Fin 8) :
      #{q ∈ highInputs | q 0 = i} =
        (![295, 380, 380, 380, 380, 380, 380, 472] : Fin 8 → ℕ) i := by
    rw [fiber_rest_card, highInputs_first]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun q : Fin 4 → Fin 8 => q 0)
      (t := (Finset.univ : Finset (Fin 8))) (fun _ _ => Finset.mem_univ _)]
  trans ∑ i : Fin 8, (![295, 380, 380, 380, 380, 380, 380, 472] : Fin 8 → ℕ) i
  · exact Finset.sum_congr rfl fun i _ => hi i
  · decide

end Gallai.Certificate.ZeroSyndrome
