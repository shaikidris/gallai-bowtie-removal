/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.CompositionThreeAnchorZeroOrbits
import Gallai.Inputs.CompositionSingleUndesignated
import Gallai.Structure.ThreeAnchorSlots

/-! # Complete small-anchor zero-syndrome induction step -/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A retained even vertex supplies slots; it need not be the designated vertex. -/
theorem small_zero_lift (B : WholeBowtie G) (hc : G.Connected)
    (hA : B.anchors.card ≤ 3) (ha : 3 ≤ B.activity) (hz : B.syndrome = ∅)
    (w : {v : V // v ∉ B.vertices}) (hw : Even (G.degree w.val)) :
    ∀ D : Decomposition B.puncture,
      D.size ≤ (∑ K : B.puncture.ConnectedComponent, (Fintype.card K.supp + 1) / 2) →
      ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
        ∀ v : {v : V // v ∉ B.vertices}, Even (G.degree v.val) →
          D.endpointCount v ≤ E.endpointCount v.val := by
  obtain ⟨A,s,hcover,hrows⟩ := B.exists_threeAnchorSlots_state_connected hc hA w hw
  have hactivity : 3 ≤ (Finset.univ.filter fun j : Fin 5 => j ≠ 0 ∧ s j ≠ 0).card := by
    rw [B.threeAnchor_activity A s hrows]
    exact ha
  have hs : Certificate.ThreeAnchor.syndrome s = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hm := (B.threeAnchor_mem_syndrome A s hrows j).mp hj
    simp [hz] at hm
  exact three_zero_encoded_lift B A s hcover hrows hactivity hs hc hA

/-- Both optional-designation versions of the small-anchor zero branch. -/
theorem small_zero_step {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
    (d : Option V) (h : Admissible Bs d) (hc : G.Connected)
    (hA : (Bs 0).anchors.card ≤ 3) (ha : 3 ≤ (Bs 0).activity)
    (hz : (Bs 0).syndrome = ∅) (ih : ZeroComponentIH Bs) : Conclusion G d := by
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
      let w : {v : V // v ∉ (Bs 0).vertices} := ⟨(Bs i).label 0, hout⟩
      obtain ⟨D, hD⟩ := zero_induction_sum Bs h.1 hz h ih
      obtain ⟨E, hE, _⟩ := small_zero_lift (Bs 0) hc hA ha hz w
        ((Bs i).even_degree_label 0) D hD
      exact ⟨E, hE, by simp⟩
  | some y =>
    have hy := h.2.2.1 y (by simp)
    let y' : {v : V // v ∉ (Bs 0).vertices} := ⟨y, hy.2.2 0⟩
    obtain ⟨D, hD, hends⟩ := zero_induction_endpoint_sum Bs h.1 hz y' h ih
    obtain ⟨E, hE, hr⟩ := small_zero_lift (Bs 0) hc hA ha hz y' hy.1 D hD
    refine ⟨E, hE, ?_⟩
    intro z hz'
    have heq : z = y := by
      simpa only [Option.mem_def, Option.some.injEq, eq_comm] using hz'
    subst z
    exact hends.trans (hr y' hy.1)

end Gallai.Composition
