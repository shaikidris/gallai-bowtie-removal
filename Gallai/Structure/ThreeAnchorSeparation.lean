/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.PairRepairedCredit

/-! # Sharp three-component repair forces anchor separation -/

namespace Gallai.WholeBowtie

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- With three components and at most three anchors, distinct anchors occupy
distinct repaired components. This is the separation needed by cheap tails. -/
theorem pairRepaired_anchor_separation (p q : {v : V // v ∉ B.vertices})
    (hs : B.syndrome = {p.val, q.val}) (hc : G.Connected)
    (hA : B.anchors.card ≤ 3)
    (hC : Fintype.card (B.pairRepairedPuncture p q).ConnectedComponent = 3) :
    Function.Injective (fun a : B.anchors =>
      (B.pairRepairedPuncture p q).connectedComponentMk (B.anchorPunctureVertex a)) := by
  classical
  let f : B.anchors → (B.pairRepairedPuncture p q).ConnectedComponent :=
    fun a => (B.pairRepairedPuncture p q).connectedComponentMk (B.anchorPunctureVertex a)
  have hf : Function.Surjective f := by
    intro C
    obtain ⟨u, hu, ha⟩ := B.pairRepaired_component_anchor p q hs hc C
    refine ⟨⟨u.val, ha⟩, ?_⟩
    exact (SimpleGraph.ConnectedComponent.eq_of_common_vertex hu
      (show u ∈ (f ⟨u.val, ha⟩).supp from rfl)).symm
  have hcard : Fintype.card B.anchors =
      Fintype.card (B.pairRepairedPuncture p q).ConnectedComponent := by
    have hle := B.pairRepaired_components_le_anchors p q hs hc
    rw [Fintype.card_coe]
    omega
  exact hf.injective_of_finite (Fintype.equivOfCardEq hcard)

/-- A path in a sharply separated repair cannot join two distinct actual
anchors. This conclusion applies to every auxiliary decomposition. -/
theorem pairRepaired_reachable_anchors_eq (p q : {v : V // v ∉ B.vertices})
    (hs : B.syndrome = {p.val, q.val}) (hc : G.Connected)
    (hA : B.anchors.card ≤ 3)
    (hC : Fintype.card (B.pairRepairedPuncture p q).ConnectedComponent = 3)
    (u v : {v : V // v ∉ B.vertices}) (hu : u.val ∈ B.anchors)
    (hv : v.val ∈ B.anchors) (hr : (B.pairRepairedPuncture p q).Reachable u v) :
    u = v := by
  have he := B.pairRepaired_anchor_separation p q hs hc hA hC
    (a₁ := ⟨u.val, hu⟩) (a₂ := ⟨v.val, hv⟩)
    (SimpleGraph.ConnectedComponent.sound hr)
  have hval : u.val = v.val := congrArg (fun a : B.anchors => a.val) he
  exact Subtype.ext hval

/-- Three separated components cannot arise by adding a synthetic pair edge:
that edge would join its two distinct anchor components. -/
theorem pairRepaired_three_components_original (p q : {v : V // v ∉ B.vertices})
    (hne : p ≠ q) (hs : B.syndrome = {p.val, q.val}) (hc : G.Connected)
    (hA : B.anchors.card ≤ 3)
    (hC : Fintype.card (B.pairRepairedPuncture p q).ConnectedComponent = 3) :
    G.Adj p.val q.val := by
  classical
  by_contra hmissing
  have hadj : (B.pairRepairedPuncture p q).Adj p q := by
    change (toggleEdge B.puncture p q).Adj p q
    simp only [toggleEdge, show ¬ B.puncture.Adj p q from hmissing, if_false,
      SimpleGraph.sup_adj, SimpleGraph.edge_adj]
    simp [hne]
  exact hne (B.pairRepaired_reachable_anchors_eq p q hs hc hA hC p q
    (B.syndrome_subset_anchors (by simp [hs]))
    (B.syndrome_subset_anchors (by simp [hs])) hadj.reachable)

end Gallai.WholeBowtie
