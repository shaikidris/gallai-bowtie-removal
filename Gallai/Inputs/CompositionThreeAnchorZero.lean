/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ZeroInductionCredit
import Gallai.Transport.ThreeAnchorZeroRepresentatives

/-! # Budget-independent reconstruction for the ten small-anchor zero representatives

The supplied puncture witness may come from many-bowtie induction. Both
credit cases preserve every outside even endpoint reserve on the same output.
-/
namespace Gallai.Composition
open Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every normalized small-anchor zero record lifts an arbitrary component-sum witness. -/
theorem three_zero_representative_lift (B : WholeBowtie G)
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (r : Fin 10)
    (hcover : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (ZeroCatalogue.state r i)).val.testBit j.val = true ∧ (A j).val = v)
    (hc : G.Connected) (hA : B.anchors.card ≤ 3) (D : Decomposition B.puncture)
    (hs : D.size ≤ ∑ K : B.puncture.ConnectedComponent, (Fintype.card K.supp + 1) / 2) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      ∀ v : {v : V // v ∉ B.vertices}, Even (G.degree v.val) →
        D.endpointCount v ≤ E.endpointCount v.val := by
  classical
  rcases zero_credit_of_sum B hc (by omega) D hs with htwo | ⟨hone, hthree⟩
  · obtain ⟨E, _, hsize, hends⟩ := B.zeroThree_reconstruction_of_parity A
      (ZeroCatalogue.state r) hrows (ZeroCatalogue.attachment r) (ZeroCatalogue.tail r)
      (ZeroCatalogue.added r) (ZeroCatalogue.two_checked r) D
    exact ⟨E, hsize.trans htwo, hends⟩
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
    exact ⟨E, hsize.trans hone, hends⟩

end Gallai.Composition
