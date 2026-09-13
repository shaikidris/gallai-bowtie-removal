/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.SyndromeStarBudget
import Gallai.Inputs.ZeroSyndromeCredit

/-! # Baseline credit before exploiting non-SET floors -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Four private deletions and at most three components always save one path.
Failure to save two requires at least two odd components; it does not by
itself imply that one of them is SET. -/
theorem syndromeStar_baseline_credit (hc : G.Connected)
    (hA : B.anchors.card ≤ 4) (hs : B.syndrome.card = 2)
    (y : B.StarSurvivor) (hx : y.val ≠ B.label 0) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ D : Decomposition B.syndromeStar, 2 ≤ D.endpointCount y ∧
      D.size + 1 ≤ (Fintype.card V + 1) / 2 ∧
      (D.size + 2 ≤ (Fintype.card V + 1) / 2 ∨
        2 ≤ ∑ C : B.syndromeStar.ConnectedComponent, Fintype.card C.supp % 2) := by
  obtain ⟨D,hb,he⟩ := B.syndromeStar_endpoint_sum hc y hx hy hcap
  have hn := B.completedStar_card
  have hC := B.syndromeStar_components_le_three hc hA hs
  have ho := component_odd_count_le B.syndromeStar
  have hbalance := component_ceiling_balance B.syndromeStar
  refine ⟨D,he,by omega,?_⟩
  by_cases htwo : D.size + 2 ≤ (Fintype.card V + 1) / 2
  · exact Or.inl htwo
  · exact Or.inr (by omega)

end Gallai.WholeBowtie
