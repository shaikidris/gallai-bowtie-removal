/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ZeroComponentInduction
import Gallai.Inputs.ZeroSyndromeCredit

/-! # Reconstruction credits from the actual inductive ceiling sum -/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Any puncture witness within the component ceiling sum supplies the exact credit dichotomy. -/
theorem zero_credit_of_sum (B : WholeBowtie G) (hc : G.Connected)
    (hA : B.anchors.card ≤ 4) (D : Decomposition B.puncture)
    (hs : D.size ≤ ∑ K : B.puncture.ConnectedComponent, (Fintype.card K.supp + 1) / 2) :
    D.size + 2 ≤ (Fintype.card V + 1) / 2 ∨
      (D.size + 1 ≤ (Fintype.card V + 1) / 2 ∧
        3 ≤ Fintype.card B.puncture.ConnectedComponent) := by
  classical
  have hn := B.puncture_card_add_five
  have hcomp := B.puncture_components_le_anchors hc
  have ho := component_odd_count_le B.puncture
  have hb := component_ceiling_balance B.puncture
  by_cases htwo : D.size + 2 ≤ (Fintype.card V + 1) / 2
  · exact Or.inl htwo
  · right
    constructor <;> omega

end Gallai.Composition
