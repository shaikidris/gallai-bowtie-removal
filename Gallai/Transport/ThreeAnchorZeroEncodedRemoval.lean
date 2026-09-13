/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ThreeAnchorZeroRepresentatives
import Gallai.Certificates.ThreeAnchorZeroOrbits
import Gallai.Structure.RetainedRelabeling

/-! # Exhaustive encoded zero-syndrome removal -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor Certificate.ThreeAnchor.Orbits
open Certificate.ThreeAnchor.RetainedOrbits
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Every high-activity zero incidence state reaches the ten normalized removal
theorems by actual core/anchor relabelling on the same ambient graph. -/
theorem threeAnchor_zero_encoded_removal
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (s j)).val.testBit k.val = true ∧ (A k).val = v)
    (ha : 3 ≤ (Finset.univ.filter fun j : Fin 5 => j ≠ 0 ∧ s j ≠ 0).card)
    (hs : Certificate.ThreeAnchor.syndrome s = ∅) (hG : G.Connected)
    (hbound : B.anchors.card ≤ 3)
    (y : {v : V // v ∉ B.vertices}) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y.val := by
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
  have hyout : y.val ∉ B'.vertices := by rw [hvertices]; exact y.property
  let y' : {v : V // v ∉ B'.vertices} := ⟨y.val,hyout⟩
  have hcap' : ∀ v, Even (G.degree v) → v ≠ B'.label 0 → v ≠ y'.val → eDegree G v ≤ 3 := by
    change ∀ v, Even (G.degree v) → v ≠ (B.retainedRelabel c).label 0 →
      v ≠ y.val → eDegree G v ≤ 3
    rw [B.retainedRelabel_hub]
    exact hcap
  have hbound' : B'.anchors.card ≤ 3 := by
    change (B.retainedRelabel c).anchors.card ≤ 3
    rw [B.retainedRelabel_anchors]
    exact hbound
  exact B'.threeAnchor_zero_representative_removal A' r hA' hrows' hG hbound' y' hy hcap'

end Gallai.WholeBowtie
