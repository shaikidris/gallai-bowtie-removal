/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.CompositionRetainedOrbits
import Gallai.Inputs.CompositionThreeAnchorPair
import Gallai.Inputs.CompositionSingleUndesignated
import Gallai.Structure.ThreeAnchorSlots

/-! # Complete small-anchor pair-syndrome induction step -/
namespace Gallai.Composition
open Certificate Certificate.ThreeAnchor Certificate.ThreeAnchor.Orbits
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A surviving even vertex supplies slots; exhaustive state selection chooses
the actual whole-deletion or retained-hub induction route. -/
theorem small_pair_step_of_even_survivor {t : ℕ}
    (Bs : Fin (t + 1) → WholeBowtie G) (d : Option V)
    (h : Admissible Bs d) (hc : G.Connected)
    (hA : (Bs 0).anchors.card ≤ 3) (ha : 3 ≤ (Bs 0).activity)
    (hs : (Bs 0).syndrome.card = 2)
    (w : {v : V // v ∉ (Bs 0).vertices}) (hw : Even (G.degree w.val))
    (ihpair : ∀ p q, PairComponentIH Bs p q)
    (ihret : ∀ (c : Fin 8) (H : SimpleGraph ((Bs 0).retainedRelabel c).StarSurvivor)
      [hdec : DecidableRel H.Adj],
      @RetainedComponentIH V _ _ G _ t (retainedRelabeledFamily Bs c) H hdec) :
    Conclusion G d := by
  obtain ⟨A, s, hcover, hrows⟩ := (Bs 0).exists_threeAnchorSlots_state_connected hc hA w hw
  have hactivity : 3 ≤ (Finset.univ.filter fun i : Fin 5 => i ≠ 0 ∧ s i ≠ 0).card := by
    rw [(Bs 0).threeAnchor_activity A s hrows]
    exact ha
  have hcard := Finset.card_image_of_injective (Certificate.ThreeAnchor.syndrome s)
    (Subtype.val_injective.comp A.injective)
  change ((Certificate.ThreeAnchor.syndrome s).image (fun j => (A j).val)).card =
    (Certificate.ThreeAnchor.syndrome s).card at hcard
  rw [(Bs 0).threeAnchor_syndrome_image A hcover s hrows, hs] at hcard
  rcases state_pair_partition s hactivity hcard.symm with hcode | hret
  · obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hs
    have hp : p ∈ (Bs 0).syndrome := by simp [hset]
    have hq : q ∈ (Bs 0).syndrome := by simp [hset]
    let p' : {v : V // v ∉ (Bs 0).vertices} :=
      ⟨p, (Bs 0).anchor_not_mem_vertices ((Bs 0).syndrome_subset_anchors hp)⟩
    let q' : {v : V // v ∉ (Bs 0).vertices} :=
      ⟨q, (Bs 0).anchor_not_mem_vertices ((Bs 0).syndrome_subset_anchors hq)⟩
    have hne : p' ≠ q' := fun he => hpq (congrArg Subtype.val he)
    exact three_pair_encoded_step Bs d h hc hA A s hcover hrows hcode
      p' q' hne hset (ihpair p' q')
  · exact retained_encoded_step Bs d h hc hA A s hcover hrows hret ihret

/-- Complete small-anchor pair branch for both optional-designation choices. -/
theorem small_pair_step {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
    (d : Option V) (h : Admissible Bs d) (hc : G.Connected)
    (hA : (Bs 0).anchors.card ≤ 3) (ha : 3 ≤ (Bs 0).activity)
    (hs : (Bs 0).syndrome.card = 2)
    (ihpair : ∀ p q, PairComponentIH Bs p q)
    (ihret : ∀ (c : Fin 8) (H : SimpleGraph ((Bs 0).retainedRelabel c).StarSurvivor)
      [hdec : DecidableRel H.Adj],
      @RetainedComponentIH V _ _ G _ t (retainedRelabeledFamily Bs c) H hdec) :
    Conclusion G d := by
  cases d with
  | none =>
    cases t with
    | zero => exact single_undesignated Bs hc h
    | succ t =>
      let i : Fin (t + 2) := 1
      have hi : (0 : Fin (t + 2)) ≠ i := by simp [i]
      have hout : (Bs i).label 0 ∉ (Bs 0).vertices := by
        intro hm
        exact Finset.disjoint_left.mp (h.1 0 i hi) hm
          (((Bs i).mem_vertices _).mpr ((Bs i).label_mem_component 0))
      exact small_pair_step_of_even_survivor Bs none h hc hA ha hs
        ⟨(Bs i).label 0, hout⟩ ((Bs i).even_degree_label 0) ihpair ihret
  | some y =>
    have hy := h.2.2.1 y (by simp)
    exact small_pair_step_of_even_survivor Bs (some y) h hc hA ha hs
      ⟨y, hy.2.2 0⟩ hy.1 ihpair ihret

end Gallai.Composition
