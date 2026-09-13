/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedSixRemoval
import Gallai.Structure.RetainedRelabeling
import Gallai.Transport.ThreeAnchorSharpRemoval

/-! # Exhaustive retained removal and the three-anchor pair-syndrome branch -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor Certificate.ThreeAnchor.Orbits
open Certificate.ThreeAnchor.RetainedOrbits
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Every retained incidence state reaches the six normalized removal
theorems by actual core/anchor relabelling on the same ambient graph. -/
theorem threeAnchor_retained_removal
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (s j)).val.testBit k.val = true ∧ (A k).val = v)
    (hs : encode s ∈ retainedCodes) (hG : G.Connected)
    (y : {v : V // v ∉ B.vertices}) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y.val := by
  obtain ⟨r,c,a,hn⟩ := state_coverage s hs
  let B' := B.retainedRelabel c
  have hvertices : B'.vertices = B.vertices := B.retainedRelabel_vertices c
  let A' : Fin 3 ↪ {v : V // v ∉ B'.vertices} :=
    ⟨fun k => ⟨(A (anchorOrder a k)).val, by rw [hvertices]; exact (A _).property⟩,
      fun j k h => (anchorOrder_bijective a).1 (A.injective
        (Subtype.ext (congrArg (fun v : {v : V // v ∉ B'.vertices} => v.val) h)))⟩
  have hrows' : ∀ j v, v ∈ B'.row j ↔ ∃ k,
      (rowMask (Retained.state r j)).val.testBit k.val = true ∧ (A' k).val = v := by
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
  let y' : B'.StarSurvivor := ⟨y.val,by
    intro h
    obtain ⟨j,_,hj⟩ := Finset.mem_map.mp h
    exact hyout (Finset.mem_map.mpr ⟨j,Finset.mem_univ _,hj⟩)⟩
  have hx : y'.val ≠ B'.label 0 := by
    intro h
    exact hyout (h ▸ Finset.mem_map.mpr ⟨0,Finset.mem_univ _,rfl⟩)
  have hcap' : ∀ v, Even (G.degree v) → v ≠ B'.label 0 → v ≠ y'.val → eDegree G v ≤ 3 := by
    change ∀ v, Even (G.degree v) → v ≠ (B.retainedRelabel c).label 0 →
      v ≠ y.val → eDegree G v ≤ 3
    rw [B.retainedRelabel_hub]
    exact hcap
  exact B'.retainedSix_removal A' r hrows' hA' hG y' hx hy hcap'

/-- Complete high-activity three-anchor pair-syndrome removal, including
ordinary, sharp, original-edge, synthetic-edge and retained-hub cases. -/
theorem threeAnchor_high_pair_removal
    (hc : G.Connected) (hA : B.anchors.card ≤ 3)
    (y : {v : V // v ∉ B.vertices}) (hy : Even (G.degree y.val))
    (ha : 3 ≤ B.activity) (hs : B.syndrome.card = 2)
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y.val := by
  obtain ⟨A,s,hcover,hrows,hdone | hret⟩ :=
    B.threeAnchor_retained_frontier hc hA y hy ha hs hcap
  · exact hdone
  · exact B.threeAnchor_retained_removal A s hcover hrows hret hc y hy hcap

end Gallai.WholeBowtie
