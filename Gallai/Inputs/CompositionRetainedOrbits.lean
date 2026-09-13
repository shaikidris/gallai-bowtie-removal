/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.CompositionRetainedStep
import Gallai.Structure.RetainedRelabeledFamily

/-! # Arbitrary retained incidence states in the family induction -/
namespace Gallai.Composition
open Certificate Certificate.ThreeAnchor Certificate.ThreeAnchor.Orbits
open Certificate.ThreeAnchor.RetainedOrbits
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Orbit coverage closes every retained state, using smaller-family induction
on the actual normalized auxiliary rather than a single-exception input. -/
theorem retained_encoded_step {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
    (d : Option V) (h : Admissible Bs d) (hc : G.Connected)
    (hsmall : (Bs 0).anchors.card ≤ 3)
    (A : Fin 3 ↪ {v : V // v ∉ (Bs 0).vertices}) (s : State)
    (hcover : ∀ v ∈ (Bs 0).anchors, ∃ j, (A j).val = v)
    (hrows : ∀ j v, v ∈ (Bs 0).row j ↔ ∃ k,
      (rowMask (s j)).val.testBit k.val = true ∧ (A k).val = v)
    (hs : encode s ∈ retainedCodes)
    (ih : ∀ (c : Fin 8) (H : SimpleGraph ((Bs 0).retainedRelabel c).StarSurvivor)
      [hdec : DecidableRel H.Adj],
      @RetainedComponentIH V _ _ G _ t (retainedRelabeledFamily Bs c) H hdec) :
    Conclusion G d := by
  obtain ⟨r, c, a, hn⟩ := state_coverage s hs
  let B' := (Bs 0).retainedRelabel c
  have hvertices : B'.vertices = (Bs 0).vertices := (Bs 0).retainedRelabel_vertices c
  let A' : Fin 3 ↪ {v : V // v ∉ B'.vertices} :=
    ⟨fun k => ⟨(A (anchorOrder a k)).val, by rw [hvertices]; exact (A _).property⟩,
      fun j k he => (anchorOrder_bijective a).1 (A.injective
        (Subtype.ext (congrArg (fun v : {v : V // v ∉ B'.vertices} => v.val) he)))⟩
  have hrows' : ∀ j v, v ∈ B'.row j ↔ ∃ k,
      (rowMask (Retained.state r j)).val.testBit k.val = true ∧ (A' k).val = v := by
    intro j v
    rw [(Bs 0).retainedRelabel_row, hrows]
    constructor
    · rintro ⟨k, hk, hv⟩
      obtain ⟨l, hl⟩ := (anchorOrder_bijective a).2 k
      refine ⟨l, ?_, ?_⟩
      · rw [← hn j l, hl]
        exact hk
      · change (A (anchorOrder a l)).val = v
        rw [hl]
        exact hv
    · rintro ⟨k, hk, hv⟩
      exact ⟨anchorOrder a k, by rw [hn j k]; exact hk, hv⟩
  have hcover' : ∀ v ∈ B'.anchors, ∃ j, (A' j).val = v := by
    intro v hv
    change v ∈ ((Bs 0).retainedRelabel c).anchors at hv
    rw [(Bs 0).retainedRelabel_anchors] at hv
    obtain ⟨k, hk⟩ := hcover v hv
    obtain ⟨j, hj⟩ := (anchorOrder_bijective a).2 k
    exact ⟨j, by change (A (anchorOrder a j)).val = v; rw [hj]; exact hk⟩
  have ha := retainedRelabeledFamily_admissible Bs c d h hsmall
  by_cases hr : r = 0
  · subst r
    exact retained_zero_step (retainedRelabeledFamily Bs c) d ha hc A' hrows' hcover'
      (ih c B'.retainedHubGraph)
  · obtain ⟨j, hj⟩ := (by decide : ∀ i : Fin 6, i ≠ 0 →
        ∃ j : Fin 5, Retained.cheapIndex j = i) r hr
    subst r
    exact retained_five_step (retainedRelabeledFamily Bs c) d ha hc A' j hrows' hcover'
      (ih c (B'.retainedCheapAuxiliary A' j))

end Gallai.Composition
