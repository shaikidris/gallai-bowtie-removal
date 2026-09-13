/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeUniverse
import Gallai.Certificates.CompletedStarIndex

/-! # Exhaustive indexing and exact cardinality of original zero states -/

namespace Gallai.Certificate.ZeroSyndrome

open CompletedStar

/-- The independent filtered inputs and high zero states correspond exactly. -/
noncomputable def highZeroEquiv :
    {q // q ∈ highInputs} ≃ {s : State // HighZeroState s} :=
  Equiv.ofBijective
    (fun q => ⟨zeroEncodedState q.val,
      ⟨zeroEncodedState_zero q.val, (Finset.mem_filter.mp q.property).2⟩⟩)
    ⟨fun _ _ h => Subtype.ext (zeroEncodedState_injective (congrArg Subtype.val h)), by
      rintro ⟨s, hs⟩
      obtain ⟨q, hq, he⟩ := highZeroState_encoded s hs
      exact ⟨⟨q, hq⟩, Subtype.ext he⟩⟩

/-- Exactly3047 original high zero states, not merely3047 enumerator outputs. -/
theorem highZeroState_card : Fintype.card {s : State // HighZeroState s} = 3047 := by
  rw [← Fintype.card_congr highZeroEquiv, Fintype.card_coe]
  exact highInputs_card

/-- Reuse the already-proved exhaustive base-eight index; only parity differs. -/
def zeroEncodedAt (n : Fin 4096) : State := zeroEncodedState (inputDigits n)

/-- Every original high zero state reaches an index satisfying the exact filter. -/
theorem highZeroState_indexed (s : State) (h : HighZeroState s) :
    ∃ n : Fin 4096, HighBoundary (zeroEncodedAt n) ∧ zeroEncodedAt n = s := by
  obtain ⟨q, hq, he⟩ := highZeroState_encoded s h
  obtain ⟨n, hn⟩ := inputDigits_surjective q
  refine ⟨n, ?_, ?_⟩
  · simpa only [zeroEncodedAt, hn] using (Finset.mem_filter.mp hq).2
  · exact (congrArg zeroEncodedState hn).trans he

end Gallai.Certificate.ZeroSyndrome
