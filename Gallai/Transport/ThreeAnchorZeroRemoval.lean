/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ThreeAnchorZeroEncodedRemoval
import Gallai.Structure.ThreeAnchorSlots

/-! # Complete high-activity three-anchor zero-syndrome removal -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Actual rows, exhaustive normalization, both component budgets and carrier
restoration are all discharged under the original graph hypotheses. -/
theorem threeAnchor_high_zero_removal (hc : G.Connected) (hA : B.anchors.card ≤ 3)
    (y : {v : V // v ∉ B.vertices}) (hy : Even (G.degree y.val))
    (ha : 3 ≤ B.activity) (hs : B.syndrome = ∅)
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y.val := by
  obtain ⟨A,s,hcover,hrows⟩ := B.exists_threeAnchorSlots_state_connected hc hA y hy
  have hactivity : 3 ≤ (Finset.univ.filter fun j : Fin 5 => j ≠ 0 ∧ s j ≠ 0).card := by
    rw [B.threeAnchor_activity A s hrows]
    exact ha
  have hz : Certificate.ThreeAnchor.syndrome s = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hm := (B.threeAnchor_mem_syndrome A s hrows j).mp hj
    simp [hs] at hm
  exact B.threeAnchor_zero_encoded_removal A s hcover hrows hactivity hz hc hA y hy hcap

end Gallai.WholeBowtie
