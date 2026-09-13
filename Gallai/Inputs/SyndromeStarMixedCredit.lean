/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.ComponentFloorReserve
import Gallai.Inputs.SyndromeStarReserves
import Gallai.Inputs.SyndromeStarCredit

/-! # The ordinary or SET-rich reconstruction budget for size-two syndrome -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The actual auxiliary supplies either two reconstruction credits or one
credit and three remote endpoints. No SET inference is made from parity alone. -/
theorem syndromeStar_mixed_credit (hc : G.Connected)
    (hA : B.anchors.card ≤ 4) (hs : B.syndrome.card = 2)
    (y : B.StarSurvivor) (hx : y.val ≠ B.label 0) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ D : Decomposition B.syndromeStar, 2 ≤ D.endpointCount y ∧
      (D.size + 2 ≤ (Fintype.card V + 1) / 2 ∨
        (D.size + 1 ≤ (Fintype.card V + 1) / 2 ∧
          ∃ w : B.StarSurvivor, w.val ∈ B.anchors ∧ w.val ∉ B.syndrome ∧
            ¬ B.syndromeStar.Reachable B.completedHub w ∧ 3 ≤ D.endpointCount w)) := by
  classical
  have hn := B.completedStar_card
  by_cases hset : ∃ C : B.syndromeStar.ConnectedComponent,
      y ∉ C.supp ∧ IsSET (B.syndromeStar.induce C.supp)
  · obtain ⟨C,hyC,hC⟩ := hset
    have hsne : B.syndrome.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨w,hwA,hwS,hwC,D,hD,hyD,hwD⟩ :=
      B.syndromeStar_set_simultaneous hc hsne y hx hy hcap C hyC hC
    have hcount := B.syndromeStar_components_le_three hc hA hs
    have hodd := component_odd_count_le B.syndromeStar
    have hbalance := component_ceiling_balance B.syndromeStar
    refine ⟨D,hyD,Or.inr ⟨by omega,w,hwA,hwS,?_,hwD⟩⟩
    intro hr
    have heq := SimpleGraph.ConnectedComponent.sound hr
    have hwHub : w ∈ (B.syndromeStar.connectedComponentMk B.completedHub).supp := by
      change B.syndromeStar.connectedComponentMk w = _
      exact heq.symm
    have hCH := SimpleGraph.ConnectedComponent.eq_of_common_vertex hwC hwHub
    apply B.syndromeStar_set_excludes_hub C hC
    rw [hCH]
    exact rfl
  · push Not at hset
    have : Nontrivial V := ⟨⟨y.val,B.label 0,hx⟩⟩
    have hp : 0 < B.syndromeStar.degree y := by
      rw [B.syndromeStar_degree_of_even y hx hy]
      exact hc.preconnected.degree_pos_of_nontrivial y.val
    obtain ⟨D,hD,hyD⟩ := endpoint_ceiling_of_other_components_not_set
      B.syndromeStar y hp ((B.syndromeStar_even_iff y).mpr hy)
      (B.syndromeStar_cap y hcap) hset
    exact ⟨D,hyD,Or.inl (by omega)⟩

end Gallai.WholeBowtie
