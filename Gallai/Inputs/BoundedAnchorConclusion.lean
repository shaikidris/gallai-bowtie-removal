/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.SizeTwoConclusion
import Gallai.Inputs.LowActivityConclusion
import Gallai.Inputs.FullSyndromeConclusion
import Gallai.Transport.ZeroSyndromeRemoval
import Gallai.Transport.ThreeAnchorZeroRemoval
import Gallai.Transport.ThreeAnchorRetainedRemoval

/-! # Exhaustive at-most-four-anchor endpoint conclusion -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Join both high-activity small-anchor syndrome branches and low activity. -/
theorem three_anchor_endpoint (hA : B.anchors.card ≤ 3) (hc : G.Connected)
    (y : V) (hyout : y ∉ B.vertices) (hy : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y → eDegree G v ≤ 3) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ P.endpointCount y := by
  by_cases hlow : B.activity ≤ 2
  · exact B.low_activity_endpoint hlow hc y hyout hy hcap
  have ha : 3 ≤ B.activity := by omega
  rcases B.syndrome_card_cases (by omega) with hz | hp | hf
  · exact B.threeAnchor_high_zero_removal hc hA ⟨y,hyout⟩ hy ha
      (Finset.card_eq_zero.mp hz) hcap
  · exact B.threeAnchor_high_pair_removal hc hA ⟨y,hyout⟩ hy ha hp hcap
  · have hh := Finset.card_le_card B.syndrome_subset_anchors
    omega

/-- Every syndrome size for at most four anchors has an actual graph consumer.
Auxiliary connectedness and finite-catalogue membership are not hypotheses. -/
theorem bounded_anchor_endpoint (hA : B.anchors.card ≤ 4) (hc : G.Connected)
    (y : V) (hyout : y ∉ B.vertices) (hy : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y → eDegree G v ≤ 3) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ P.endpointCount y := by
  by_cases hsmall : B.anchors.card ≤ 3
  · exact B.three_anchor_endpoint hsmall hc y hyout hy hcap
  have hfour : B.anchors.card = 4 := by omega
  by_cases hlow : B.activity ≤ 2
  · exact B.low_activity_endpoint hlow hc y hyout hy hcap
  have ha : 3 ≤ B.activity := by omega
  rcases B.syndrome_card_cases hA with hz | hp | hf
  · exact B.high_zero_four_anchor_removal (Finset.card_eq_zero.mp hz) hc hfour ha
      ⟨y,hyout⟩ hy hcap
  · exact B.sizeTwo_endpoint hfour hp hc y hyout hy hcap
  · have hfull : B.syndrome = B.anchors :=
      Finset.eq_of_subset_of_card_le B.syndrome_subset_anchors (by omega)
    exact B.full_syndrome_endpoint hfour hfull hc y hyout hy hcap

end Gallai.WholeBowtie
