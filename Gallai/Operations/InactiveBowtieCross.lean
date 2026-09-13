/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.CrossTriangleDeletion
import Gallai.Structure.LowActivity
import Mathlib.Tactic.FinCases

/-! # All four labelled cross-triangle restoration choices -/

namespace Gallai

/-- Independently swap the two private labels in either triangle, fixing the hub. -/
def bowtieCrossLabels (left right : Bool) : Fin 5 ↪ Fin 5 where
  toFun i := if i = 0 then 0 else if i = 1 then (if left then 2 else 1)
    else if i = 2 then (if left then 1 else 2)
    else if i = 3 then (if right then 4 else 3) else (if right then 3 else 4)
  inj' := by cases left <;> cases right <;> decide

/-- Every cross-pair selection has the same actual local neighbourhood identities. -/
theorem bowtieCrossLabels_local (left right : Bool) :
    let f := bowtieCrossLabels left right
    f 0 = 0 ∧ bowtieGraph.Adj (f 0) (f 2) ∧ bowtieGraph.Adj (f 0) (f 4) ∧
      (∀ j, bowtieGraph.Adj (f 1) j ↔ j = f 0 ∨ j = f 2) ∧
      (∀ j, bowtieGraph.Adj (f 3) j ↔ j = f 0 ∨ j = f 4) := by
  cases left <;> cases right
  all_goals refine ⟨rfl, by decide, by decide, ?_, ?_⟩
  all_goals intro j; fin_cases j <;> decide

namespace WholeBowtie

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Restore any one inactive private vertex from each triangle. No carrier
separation or favourable orientation is assumed. -/
theorem restore_inactive_cross (left right : Bool)
    (h1 : B.row (bowtieCrossLabels left right 1) = ∅)
    (h3 : B.row (bowtieCrossLabels left right 3) = ∅)
    (D : Decomposition (G.induce {v | v ≠ B.label (bowtieCrossLabels left right 1) ∧
      v ≠ B.label (bowtieCrossLabels left right 3)})) :
    ∃ E : Decomposition G, E.size = D.size + 1 ∧
      ∀ v : {v : V // v ≠ B.label (bowtieCrossLabels left right 1) ∧
        v ≠ B.label (bowtieCrossLabels left right 3)},
        v.val ≠ B.label (bowtieCrossLabels left right 2) →
        v.val ≠ B.label (bowtieCrossLabels left right 4) →
        E.endpointCount v.val = D.endpointCount v := by
  classical
  let f := bowtieCrossLabels left right
  obtain ⟨_, he02, he04, hn1, hn3⟩ := bowtieCrossLabels_local left right
  have neighbor (i l r : Fin 5) (hi : B.row i = ∅)
      (hn : ∀ j, bowtieGraph.Adj i j ↔ j = l ∨ j = r) :
      ∀ v, G.Adj (B.label i) v ↔ v = B.label l ∨ v = B.label r := by
    intro v
    rw [← G.mem_neighborFinset, B.neighbors_of_row_empty i hi]
    constructor
    · intro hv
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hv
      rcases (hn j).mp ((bowtieGraph.mem_neighborFinset _ _).mp hj) with h | h
      · exact Or.inl (congrArg B.label h)
      · exact Or.inr (congrArg B.label h)
    · rintro (rfl | rfl)
      · exact Finset.mem_map.mpr ⟨l,
          (bowtieGraph.mem_neighborFinset _ _).mpr ((hn l).mpr (Or.inl rfl)), rfl⟩
      · exact Finset.mem_map.mpr ⟨r,
          (bowtieGraph.mem_neighborFinset _ _).mpr ((hn r).mpr (Or.inr rfl)), rfl⟩
  exact Decomposition.restore_cross_triangle_deletion (f.trans B.label)
    ((B.adj_iff _ _).mpr he02) ((B.adj_iff _ _).mpr he04)
    (neighbor (f 1) (f 0) (f 2) h1 hn1) (neighbor (f 3) (f 0) (f 4) h3 hn3) D

end WholeBowtie
end Gallai
