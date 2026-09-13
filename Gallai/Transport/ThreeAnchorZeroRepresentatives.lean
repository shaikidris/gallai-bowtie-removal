/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ThreeAnchorZeroParity
import Gallai.Transport.ThreeAnchorZeroSharpTransport
import Gallai.Inputs.ZeroSyndromeCredit
import Gallai.Structure.ThreeAnchorUsed

/-! # Actual removal for all ten zero-syndrome representatives -/
namespace Gallai.WholeBowtie
open Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Both ordinary and sharp component budgets are consumed. No decomposition,
credit alternative or finite witness is supplied by the caller. -/
theorem threeAnchor_zero_representative_removal
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (r : Fin 10)
    (hcover : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (ZeroCatalogue.state r i)).val.testBit j.val = true ∧ (A j).val = v)
    (hc : G.Connected) (hA : B.anchors.card ≤ 3)
    (y : {v : V // v ∉ B.vertices}) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y.val := by
  classical
  have hz : B.syndrome = ∅ := by
    rw [← B.threeAnchor_syndrome_image A hcover (ZeroCatalogue.state r) hrows,
      (ZeroCatalogue.two_checked r).1]
    simp
  obtain ⟨D, hyD, hcredit⟩ := B.zero_puncture_endpoint_credit hz hc (by omega) y hy hcap
  rcases hcredit with htwo | ⟨hone, hthree⟩
  · obtain ⟨E, _, hsize, hends⟩ := B.zeroThree_reconstruction_of_parity A
      (ZeroCatalogue.state r) hrows (ZeroCatalogue.attachment r) (ZeroCatalogue.tail r)
      (ZeroCatalogue.added r) (ZeroCatalogue.two_checked r) D
    exact ⟨E, hsize.trans htwo, hyD.trans (hends y hy)⟩
  · have hle := B.puncture_components_le_anchors hc
    have hcard : B.anchors.card = 3 := by omega
    have hC : Fintype.card B.puncture.ConnectedComponent = 3 := by omega
    have hused := B.threeAnchor_all_used A hcover (ZeroCatalogue.state r) hrows hcard
    have full : ∀ r : Fin 10,
        (∀ j : Fin 3, ∃ i : Fin 5,
          (rowMask (ZeroCatalogue.state r i)).val.testBit j.val = true) →
        ∃ f : Fin 8, ZeroCatalogue.fullIndex f = r := by decide
    obtain ⟨f, hfr⟩ := full r hused
    subst r
    obtain ⟨E, _, hsize, hends⟩ := B.zeroSharpThree_reconstruction A
      (ZeroCatalogue.state (ZeroCatalogue.fullIndex f)) hrows hcover
      (ZeroCatalogue.tails f) (ZeroCatalogue.oneAdded f) (ZeroCatalogue.sources f)
      (ZeroCatalogue.one_checked f) hc hA hC D
    exact ⟨E, hsize.trans hone, hyD.trans (hends y hy)⟩

end Gallai.WholeBowtie
