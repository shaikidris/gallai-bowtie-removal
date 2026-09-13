/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.InactiveFamilyLift
import Mathlib.Tactic.FinCases

/-! # Selecting a complete low-activity reduction for family induction -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The local reduction interface includes exact deletion size and endpoint transport. -/
def InactiveReduction (I : Finset (Fin 5)) : Prop :=
  0 ∉ I ∧ I.card = 2 ∧ (∀ i ∈ I, B.row i = ∅) ∧
    ∀ D : Decomposition (B.privateDeletion I),
      ∃ E : Decomposition G, E.size = D.size + 1 ∧
        ∀ v, v.val ∉ B.vertices → E.endpointCount v.val = D.endpointCount v

/-- Cross-pair geometry supplies all fields of the reduction interface. -/
theorem inactiveReduction_cross (left right : Bool)
    (h1 : B.row (bowtieCrossLabels left right 1) = ∅)
    (h3 : B.row (bowtieCrossLabels left right 3) = ∅) :
    B.InactiveReduction {bowtieCrossLabels left right 1, bowtieCrossLabels left right 3} := by
  refine ⟨?_, ?_, ?_, B.inactive_cross_family_lift left right h1 h3⟩
  · cases left <;> cases right <;> decide
  · cases left <;> cases right <;> decide
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact h1
    · have he := Finset.mem_singleton.mp hi
      subst i
      exact h3

/-- A same-triangle pair supplies all fields of the reduction interface. -/
theorem inactiveReduction_triangle (right : Bool)
    (hr : ∀ i : Fin 3, i ≠ 0 → B.row (bowtieTriangle right i) = ∅) :
    B.InactiveReduction {bowtieTriangle right 1, bowtieTriangle right 2} := by
  refine ⟨?_, ?_, ?_, B.inactive_triangle_family_lift right hr⟩
  · cases right <;> decide
  · cases right <;> decide
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hr 1 (by decide)
    · have he := Finset.mem_singleton.mp hi
      subst i
      exact hr 2 (by decide)

/-- Every low-activity bowtie admits a two-vertex reduction usable by family induction. -/
theorem exists_inactiveReduction (ha : B.activity ≤ 2) :
    ∃ I, B.InactiveReduction I := by
  rcases B.low_activity_cases ha with ⟨hL, hR⟩ | ⟨h1, h2⟩ | ⟨h3, h4⟩
  · rcases hL with h1 | h2 <;> rcases hR with h3 | h4
    · exact ⟨_, B.inactiveReduction_cross false false h1 h3⟩
    · exact ⟨_, B.inactiveReduction_cross false true h1 h4⟩
    · exact ⟨_, B.inactiveReduction_cross true false h2 h3⟩
    · exact ⟨_, B.inactiveReduction_cross true true h2 h4⟩
  · refine ⟨_, B.inactiveReduction_triangle false ?_⟩
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact h1
    · exact h2
  · refine ⟨_, B.inactiveReduction_triangle true ?_⟩
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact h3
    · exact h4

end Gallai.WholeBowtie
