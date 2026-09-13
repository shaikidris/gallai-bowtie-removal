/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ZeroInductionCredit
import Gallai.Transport.ZeroSyndromeRemoval

/-! # Zero-syndrome reconstruction in simultaneous bowtie induction

The puncture budget comes from smaller-family induction, not a single-exception
theorem. One-credit reconstruction retains the actual component separation.
-/
namespace Gallai.Composition
open Certificate.ZeroSyndrome
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Lift any ceiling-sum puncture witness while retaining every outside even reserve. -/
theorem zero_syndrome_lift (B : WholeBowtie G) (hz : B.syndrome = ∅)
    (hc : G.Connected) (hfour : B.anchors.card = 4) (ha : 3 ≤ B.activity)
    (D : Decomposition B.puncture)
    (hs : D.size ≤ ∑ K : B.puncture.ConnectedComponent, (Fintype.card K.supp + 1) / 2) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      ∀ v : {v : V // v ∉ B.vertices}, Even (G.degree v.val) →
        D.endpointCount v ≤ E.endpointCount v.val := by
  classical
  let A := B.anchorNumbering hfour
  have hstate := B.completedStarState_highZero A hz ha
  obtain ⟨f, hf⟩ := B.zero_anchor_carriers hz D
  rcases zero_credit_of_sum B hc (by omega) D hs with htwo | ⟨hone, hthree⟩
  · obtain ⟨tails, added, hr⟩ := all_two_records _ hstate _ _ (B.zero_interface_mem A D f hf)
    exact ⟨B.zeroReconstruction A D f hf tails added hr,
      (B.zeroReconstruction_budget A D f hf tails added hr).trans htwo,
      B.zeroReconstruction_endpoint_reserve A D f hf tails added hr⟩
  · obtain ⟨tails, added, hr⟩ := all_one_records _ hstate _ (B.zero_separated_mem A hc hthree)
    let ht := hr.toTwo (B.zero_interface_mem A D f hf)
    refine ⟨B.zeroReconstruction A D f hf tails added ht, ?_,
      B.zeroReconstruction_endpoint_reserve A D f hf tails added ht⟩
    rw [B.zeroReconstruction_size]
    exact (Nat.add_le_add_left hr.2.2.1 D.size).trans hone

/-- Close the high-activity four-anchor zero branch from the strict smaller-family premise. -/
theorem zero_syndrome_step {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
    (d : Option V) (h : Admissible Bs d) (hc : G.Connected)
    (hfour : (Bs 0).anchors.card = 4) (hz : (Bs 0).syndrome = ∅)
    (ha : 3 ≤ (Bs 0).activity) (ih : ZeroComponentIH Bs) : Conclusion G d := by
  cases d with
  | none =>
    obtain ⟨D, hD⟩ := zero_induction_sum Bs h.1 hz h ih
    obtain ⟨E, hE, _⟩ := zero_syndrome_lift (Bs 0) hz hc hfour ha D hD
    exact ⟨E, hE, by simp⟩
  | some y =>
    have hy := h.2.2.1 y (by simp)
    let y' : {v : V // v ∉ (Bs 0).vertices} := ⟨y, hy.2.2 0⟩
    obtain ⟨D, hD, hends⟩ := zero_induction_endpoint_sum Bs h.1 hz y' h ih
    obtain ⟨E, hE, hr⟩ := zero_syndrome_lift (Bs 0) hz hc hfour ha D hD
    refine ⟨E, hE, ?_⟩
    intro z hz'
    have heq : z = y := by
      simpa only [Option.mem_def, Option.some.injEq, eq_comm] using hz'
    subst z
    exact hends.trans (hr y' hy.1)

end Gallai.Composition
