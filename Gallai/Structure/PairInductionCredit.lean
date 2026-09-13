/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.PairComponentInduction
import Gallai.Inputs.PairRepairedCredit

/-! # Pair-reconstruction credits from the inductive component sum

The supplied decomposition is kept fixed. No one-exception hypothesis or
independent endpoint-budget witness is used in this accounting step.
-/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Three anchors yield two credits, or one with exactly three odd components. -/
theorem pair_three_credit_of_sum (B : WholeBowtie G)
    (p q : {v : V // v ∉ B.vertices}) (hs : B.syndrome = {p.val, q.val})
    (hc : G.Connected) (hA : B.anchors.card ≤ 3)
    (D : Decomposition (B.pairRepairedPuncture p q))
    (hb : D.size ≤ ∑ K : (B.pairRepairedPuncture p q).ConnectedComponent,
      (Fintype.card K.supp + 1) / 2) :
    D.size + 2 ≤ (Fintype.card V + 1) / 2 ∨
      (D.size + 1 ≤ (Fintype.card V + 1) / 2 ∧
        Fintype.card (B.pairRepairedPuncture p q).ConnectedComponent = 3 ∧
        (∑ K : (B.pairRepairedPuncture p q).ConnectedComponent,
          Fintype.card K.supp % 2) = 3) := by
  classical
  have hn := B.puncture_card_add_five
  have hcomp := B.pairRepaired_components_le_anchors p q hs hc
  have ho := component_odd_count_le (B.pairRepairedPuncture p q)
  have hbalance := component_ceiling_balance (B.pairRepairedPuncture p q)
  by_cases htwo : D.size + 2 ≤ (Fintype.card V + 1) / 2
  · exact Or.inl htwo
  · exact Or.inr ⟨by omega, by omega, by omega⟩

end Gallai.Composition
