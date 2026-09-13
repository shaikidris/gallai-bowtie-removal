/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ZeroSyndromeRows
import Gallai.Inputs.LowActivityConclusion

/-! # Direct discharge of the size-two low-activity exception

The catalogue's two-ear state is not a missing local edge identity. Its actual
graph falls under the already proved all-order low-activity theorem.
-/
namespace Gallai.WholeBowtie
open Certificate.CompletedStar
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Literal nonzero private masks count actual active private vertices. -/
theorem completedStarState_activity (A : B.AnchorNumbering) :
    B.activity = #{i : Fin 5 | i ≠ 0 ∧ B.completedStarState A i ≠ 0} := by
  unfold activity
  congr 1
  ext i
  simp [activePrivate,B.completedStarState_eq_zero_iff,Finset.nonempty_iff_ne_empty]

/-- The exact two-ear catalogue state is discharged without a reconstruction record. -/
theorem sizeTwo_twoEar_endpoint (A : B.AnchorNumbering)
    (hstate : B.completedStarState A = ![15,0,0,0,12]) (hc : G.Connected)
    (y : V) (hy : y ∉ B.vertices) (hyEven : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y → eDegree G v ≤ 3) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount y := by
  apply B.low_activity_endpoint ?_ hc y hy hyEven hcap
  rw [B.completedStarState_activity A,hstate]
  decide

end Gallai.WholeBowtie
