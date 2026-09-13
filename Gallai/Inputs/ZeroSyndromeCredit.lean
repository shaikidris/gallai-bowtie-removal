/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.ZeroSyndromeAssembly
import Gallai.Structure.PunctureComponents

/-! # Actual one- or two-path reconstruction credit

The one-path alternative carries its necessary component-separation resource.
No connectivity hypothesis on the whole puncture or parity of ambient order
is added to the original four-anchor zero-syndrome case.
-/

namespace Gallai

/-- The sum of component order remainders is bounded by the component count. -/
theorem component_odd_count_le {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    (∑ C : H.ConnectedComponent, Fintype.card C.supp % 2) ≤
      Fintype.card H.ConnectedComponent := by
  classical
  calc
    _ ≤ ∑ _C : H.ConnectedComponent, 1 := Finset.sum_le_sum fun C _ => by omega
    _ = _ := by simp

namespace WholeBowtie

open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The actual puncture supplies two credits, or one credit together with
at least three components, while preserving the designated endpoint reserve. -/
theorem zero_puncture_endpoint_credit (hz : B.syndrome = ∅) (hc : G.Connected)
    (hA : #B.anchors ≤ 4) (y : {v : V // v ∉ B.vertices})
    (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ D : Decomposition B.puncture, 2 ≤ D.endpointCount y ∧
      (D.size + 2 ≤ (Fintype.card V + 1) / 2 ∨
        (D.size + 1 ≤ (Fintype.card V + 1) / 2 ∧
          3 ≤ Fintype.card B.puncture.ConnectedComponent)) := by
  classical
  obtain ⟨D, hs, he⟩ := B.zero_puncture_endpoint_sum hz hc y hy hcap
  have hn := B.puncture_card_add_five
  have hcA := B.puncture_components_le_anchors hc
  have ho := component_odd_count_le B.puncture
  have hb := component_ceiling_balance B.puncture
  refine ⟨D, he, ?_⟩
  by_cases htwo : D.size + 2 ≤ (Fintype.card V + 1) / 2
  · exact Or.inl htwo
  · right
    constructor <;> omega

end WholeBowtie
end Gallai
