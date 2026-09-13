/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeIndex

/-! # Actual whole-bowtie hypotheses supply the complete zero-state domain -/

namespace Gallai.WholeBowtie
open Certificate.CompletedStar Certificate.ZeroSyndrome
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Encoded column incidence equals the actual original row-incidence count. -/
theorem zeroState_column_count (A : B.AnchorNumbering) (j : Fin 4) :
    #{i : Fin 5 | (B.completedStarState A i).val.testBit j.val = true} =
      B.columnCount (A j).val := by
  unfold columnCount
  congr 1
  ext i
  simp [B.completedStarState_bit, B.mem_row, B.numberedAnchor_not_mem A j]

/-- Empty actual syndrome gives even column counts as well as even row counts. -/
theorem completedStarState_zero (A : B.AnchorNumbering) (hz : B.syndrome = ∅) :
    ZeroState (B.completedStarState A) := by
  refine ⟨B.completedStarState_even A, ?_⟩
  intro j
  rw [B.zeroState_column_count]
  apply Nat.not_odd_iff_even.mp
  intro ho
  have hm := (B.mem_syndrome_iff_odd_column (A j).val).mpr ho
  simp [hz] at hm

/-- Mask zero is exactly inactivity of the actual external row. -/
theorem completedStarState_eq_zero_iff (A : B.AnchorNumbering) (i : Fin 5) :
    B.completedStarState A i = 0 ↔ B.row i = ∅ := by
  rw [← maskSupport_empty_iff, completedStarState, maskSupport_maskOf]
  rw [← Finset.card_eq_zero, B.numberedRow_card A i, Finset.card_eq_zero]

/-- Actual anchors and private activity imply the independent boundary filter. -/
theorem completedStarState_high (A : B.AnchorNumbering) (ha : 3 ≤ B.activity) :
    HighBoundary (B.completedStarState A) := by
  constructor
  · intro j
    obtain ⟨i, hi⟩ := (B.mem_anchors (A j).val).mp (A j).property
    exact ⟨i, (B.completedStarState_bit A i j).mpr ((B.mem_row i _).mp hi).1⟩
  · have hs : (Finset.univ.filter fun i : Fin 5 =>
        i ≠ 0 ∧ B.completedStarState A i ≠ 0) = B.activePrivate := by
      ext i
      simp [activePrivate, B.completedStarState_eq_zero_iff, Finset.nonempty_iff_ne_empty]
    rw [hs]
    exact ha

/-- Every original graph in this branch reaches the independently enumerated
3047-state domain; catalogue membership is not an extra graph hypothesis. -/
theorem completedStarState_highZero (A : B.AnchorNumbering)
    (hz : B.syndrome = ∅) (ha : 3 ≤ B.activity) :
    HighZeroState (B.completedStarState A) :=
  ⟨B.completedStarState_zero A hz, B.completedStarState_high A ha⟩

/-- The actual graph reaches the exhaustive index with no catalogue assumption. -/
theorem completedStarState_zero_indexed (A : B.AnchorNumbering)
    (hz : B.syndrome = ∅) (ha : 3 ≤ B.activity) :
    ∃ n : Fin 4096, HighBoundary (zeroEncodedAt n) ∧
      zeroEncodedAt n = B.completedStarState A :=
  highZeroState_indexed _ (B.completedStarState_highZero A hz ha)

end Gallai.WholeBowtie
