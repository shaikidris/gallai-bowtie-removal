/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.SyndromeStarComponents
import Gallai.Inputs.ZeroSyndromeAssembly

/-! # Endpoint-rich component decompositions for the syndrome star -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- A non-hub even survivor is not an anchor; its degree is unchanged. -/
theorem syndromeStar_degree_of_even (v : B.StarSurvivor)
    (hx : v.val ≠ B.label 0) (he : Even (G.degree v.val)) :
    B.syndromeStar.degree v = G.degree v.val := by
  have hn : v.val ∉ B.anchors := fun h =>
    (Nat.not_even_iff_odd.mpr (B.odd_degree_anchor h)) he
  have hs : v.val ∉ B.syndrome := fun h => hn (B.syndrome_subset_anchors h)
  have hd := B.syndromeStar_degree_balance v hx
  simpa only [B.no_anchor_incidence v hx hn, Finset.card_empty,
    if_neg hs, Nat.add_zero] using hd

/-- Component ceilings provide an actual auxiliary decomposition exposing y.
The sharper mixed floor/SET budget is a separate next obligation. -/
theorem syndromeStar_endpoint_sum (hc : G.Connected)
    (y : B.StarSurvivor) (hx : y.val ≠ B.label 0) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ D : Decomposition B.syndromeStar,
      D.size ≤ ∑ C : B.syndromeStar.ConnectedComponent,
        (Fintype.card C.supp + 1) / 2 ∧ 2 ≤ D.endpointCount y := by
  classical
  have : Nontrivial V := ⟨⟨y.val,B.label 0,hx⟩⟩
  have hp : 0 < B.syndromeStar.degree y := by
    rw [B.syndromeStar_degree_of_even y hx hy]
    exact hc.preconnected.degree_pos_of_nontrivial y.val
  have he := (B.syndromeStar_even_iff y).mpr hy
  have hcapH := B.syndromeStar_cap y hcap
  obtain ⟨D,hb,hyD⟩ := component_endpoint_of_cap B.syndromeStar y
    (B.syndromeStar.connectedComponentMk y) rfl hp he hcapH
  apply endpoint_budget_of_components B.syndromeStar y
    (fun C => (Fintype.card C.supp + 1) / 2) D hb hyD
  intro C hC
  apply other_component_ceiling B.syndromeStar y C _ hcapH
  intro hyC
  exact hC (SimpleGraph.ConnectedComponent.eq_of_common_vertex hyC rfl)

end Gallai.WholeBowtie
