/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.CompositionThreeAnchorZero
import Gallai.Certificates.ThreeAnchorZeroOrbits
import Gallai.Structure.RetainedRelabeling

/-! # Arbitrary encoded small-anchor zero states lift induction witnesses -/
namespace Gallai.Composition
open Certificate Certificate.ThreeAnchor Certificate.ThreeAnchor.Orbits
open Certificate.ThreeAnchor.RetainedOrbits
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Normalize incidence rows without changing the puncture witness or its endpoint obligations. -/
theorem three_zero_encoded_lift (B : WholeBowtie G)
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (s j)).val.testBit k.val = true ∧ (A k).val = v)
    (ha : 3 ≤ (Finset.univ.filter fun j : Fin 5 => j ≠ 0 ∧ s j ≠ 0).card)
    (hs : Certificate.ThreeAnchor.syndrome s = ∅) (hc : G.Connected)
    (hbound : B.anchors.card ≤ 3) :
    ∀ D : Decomposition B.puncture,
      D.size ≤ (∑ K : B.puncture.ConnectedComponent, (Fintype.card K.supp + 1) / 2) →
      ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
        ∀ v : {v : V // v ∉ B.vertices}, Even (G.degree v.val) →
          D.endpointCount v ≤ E.endpointCount v.val := by
  obtain ⟨r,c,a,hn⟩ := ZeroOrbits.state_coverage s ha hs
  let B' := B.retainedRelabel c
  have hvertices : B'.vertices = B.vertices := B.retainedRelabel_vertices c
  let A' : Fin 3 ↪ {v : V // v ∉ B'.vertices} :=
    ⟨fun k => ⟨(A (anchorOrder a k)).val, by rw [hvertices]; exact (A _).property⟩,
      fun j k h => (anchorOrder_bijective a).1 (A.injective
        (Subtype.ext (congrArg (fun v : {v : V // v ∉ B'.vertices} => v.val) h)))⟩
  have hrows' : ∀ j v, v ∈ B'.row j ↔ ∃ k,
      (rowMask (ZeroCatalogue.state r j)).val.testBit k.val = true ∧ (A' k).val = v := by
    intro j v
    rw [B.retainedRelabel_row, hrows]
    constructor
    · rintro ⟨k,hk,hv⟩
      obtain ⟨l,hl⟩ := (anchorOrder_bijective a).2 k
      refine ⟨l,?_,?_⟩
      · rw [← hn j l,hl]
        exact hk
      · change (A (anchorOrder a l)).val = v
        rw [hl]
        exact hv
    · rintro ⟨k,hk,hv⟩
      exact ⟨anchorOrder a k,by rw [hn j k]; exact hk,hv⟩
  have hA' : ∀ v ∈ B'.anchors, ∃ j, (A' j).val = v := by
    intro v hv
    change v ∈ (B.retainedRelabel c).anchors at hv
    rw [B.retainedRelabel_anchors] at hv
    obtain ⟨k,hk⟩ := hA v hv
    obtain ⟨j,hj⟩ := (anchorOrder_bijective a).2 k
    exact ⟨j,by change (A (anchorOrder a j)).val = v; rw [hj]; exact hk⟩
  have hbound' : B'.anchors.card ≤ 3 := by
    change (B.retainedRelabel c).anchors.card ≤ 3
    rw [B.retainedRelabel_anchors]
    exact hbound
  have lift := three_zero_representative_lift B' A' r hA' hrows' hc hbound'
  unfold WholeBowtie.puncture at lift
  rw [hvertices] at lift
  exact lift

end Gallai.Composition
