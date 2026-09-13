/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.CompositionBase
import Gallai.Inputs.CompositionLowActivity
import Gallai.Inputs.CompositionFullSyndrome
import Gallai.Inputs.CompositionZeroSyndrome
import Gallai.Inputs.CompositionSmallZeroStep
import Gallai.Inputs.CompositionSmallPairStep

/-! # Simultaneous designated and undesignated composition by family size -/
namespace Gallai.Composition
universe u

/-- Every admissible finite bowtie family has the literal optional-endpoint
conclusion. All local auxiliary premises are discharged by strong induction. -/
theorem compose (t : ℕ) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (Bs : Fin t → WholeBowtie G) (d : Option V),
      G.Connected → Admissible Bs d → Conclusion G d := by
  induction t using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G _ Bs d hc h
    cases n with
    | zero => exact empty_family hc Bs d h
    | succ t =>
      by_cases ha : (Bs 0).activity ≤ 2
      · apply low_activity_step Bs d h hc ha
        intro I hi d' hc' had
        exact ih t (by omega) _ _ d' hc' had
      · have hhigh : 3 ≤ (Bs 0).activity := by omega
        have hiz : ZeroComponentIH Bs := by
          intro K k hk Cs e had
          exact ih k hk _ Cs e K.connected_toSimpleGraph had
        rcases h.2.1 0 with hlow | hsmall | ⟨hfour, hzero | hfull⟩
        · exact (ha hlow).elim
        · have hbound := Finset.card_le_card (Bs 0).syndrome_subset_anchors
          rcases (Bs 0).syndrome_card_cases (by omega) with hz | hp | hf
          · exact small_zero_step Bs d h hc hsmall hhigh
              (Finset.card_eq_zero.mp hz) hiz
          · apply small_pair_step Bs d h hc hsmall hhigh hp
            · intro p q K k hk Cs e had
              exact ih k hk _ Cs e K.connected_toSimpleGraph had
            · intro c H hdec
              let : DecidableRel H.Adj := hdec
              intro K k hk Cs e had
              let : Fintype K.supp := @Subtype.fintype _ _
                (fun v => H.instDecidableMemSupp K v) inferInstance
              let : DecidableRel (H.induce K.supp).Adj := fun a b => hdec a.val b.val
              exact ih k hk _ Cs e K.connected_toSimpleGraph had
          · omega
        · exact zero_syndrome_step Bs d h hc hfour hzero hhigh hiz
        · apply full_syndrome_step Bs d h hc hfour hfull
          intro he cols d' hc' had
          exact ih t (by omega) _ _ d' hc' had

end Gallai.Composition
