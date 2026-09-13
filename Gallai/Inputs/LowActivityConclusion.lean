/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.InactiveCrossConclusion
import Gallai.Inputs.InactiveTriangleConclusion

/-! # The low-private-activity branch of manuscript Theorem A

All deletion geometries and labelled cases are discharged. The auxiliary
endpoint theorem is a proved dependency, not an input hypothesis.
-/

namespace Gallai.WholeBowtie

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- At most two active private vertices suffice at every order and with no
anchor bound. The resulting ceiling-budget decomposition exposes the other
exception at least twice. -/
theorem low_activity_endpoint (ha : B.activity ≤ 2) (hc : G.Connected)
    (y : V) (hy : y ∉ B.vertices) (hyEven : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y → eDegree G v ≤ 3) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y := by
  rcases B.low_activity_cases ha with ⟨hL, hR⟩ | ⟨h1, h2⟩ | ⟨h3, h4⟩
  · rcases hL with h1 | h2 <;> rcases hR with h3 | h4
    · exact B.inactive_cross_endpoint false false h1 h3 hc y hy hyEven hcap
    · exact B.inactive_cross_endpoint false true h1 h4 hc y hy hyEven hcap
    · exact B.inactive_cross_endpoint true false h2 h3 hc y hy hyEven hcap
    · exact B.inactive_cross_endpoint true true h2 h4 hc y hy hyEven hcap
  · apply B.inactive_triangle_endpoint false ?_ hc y hy hyEven hcap
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact h1
    · exact h2
  · apply B.inactive_triangle_endpoint true ?_ hc y hy hyEven hcap
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact h3
    · exact h4

end Gallai.WholeBowtie
