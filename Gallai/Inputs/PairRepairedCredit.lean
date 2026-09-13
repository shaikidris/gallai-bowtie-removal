/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.PairRepairedBudget
import Gallai.Inputs.ZeroSyndromeCredit

/-! # Component assembly and reconstruction credit after pair repair

Deleting an original repair edge may split a puncture component. Each resulting
component still meets an actual anchor: the only deleted edge has anchor ends.
Thus the component ceiling accounting applies to either repair status.
-/

namespace Gallai.WholeBowtie

open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Every component after syndrome-pair repair contains an actual anchor. -/
theorem pairRepaired_component_anchor (p q : {v : V // v ∉ B.vertices})
    (hs : B.syndrome = {p.val, q.val}) (hc : G.Connected)
    (C : (B.pairRepairedPuncture p q).ConnectedComponent) :
    ∃ u : {v : V // v ∉ B.vertices}, u ∈ C.supp ∧ u.val ∈ B.anchors := by
  classical
  by_contra hn
  push Not at hn
  have step (u : {v : V // v ∉ B.vertices}) (hu : u ∈ C.supp)
      (w : V) (ha : G.Adj u.val w) :
      ∃ hw : w ∉ B.vertices, (⟨w, hw⟩ : {v : V // v ∉ B.vertices}) ∈ C.supp := by
    have hw : w ∉ B.vertices := by
      intro hwB
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hwB
      exact hn u hu ((B.mem_anchors _).mpr
        ⟨i, (B.mem_row i _).mpr ⟨ha.symm, u.property⟩⟩)
    have hp : u ≠ p := by
      intro he
      subst u
      exact hn p hu (B.syndrome_subset_anchors (by simp [hs]))
    have hq : u ≠ q := by
      intro he
      subst u
      exact hn q hu (B.syndrome_subset_anchors (by simp [hs]))
    have hadj : (B.pairRepairedPuncture p q).Adj ⟨w, hw⟩ u :=
      (toggleEdge_adj_of_ne B.puncture p q ⟨w, hw⟩ u hp hq).mpr ha.symm
    exact ⟨hw, C.mem_supp_of_adj_mem_supp hu hadj.symm⟩
  have along {v w : V} (walk : G.Walk v w) :
      (∃ hv : v ∉ B.vertices, (⟨v, hv⟩ : {v : V // v ∉ B.vertices}) ∈ C.supp) →
      (∃ hw : w ∉ B.vertices, (⟨w, hw⟩ : {v : V // v ∉ B.vertices}) ∈ C.supp) := by
    induction walk with
    | nil => exact id
    | @cons v w t hvw walk ih =>
      rintro ⟨hv, hvC⟩
      exact ih (step ⟨v, hv⟩ hvC w hvw)
  obtain ⟨u, hu⟩ := C.nonempty_supp
  obtain ⟨walk⟩ := hc u.val (B.label 0)
  obtain ⟨h, _⟩ := along walk ⟨u.property, hu⟩
  exact h ((B.mem_vertices _).mpr (B.label_mem_component 0))

/-- Pair repair does not increase the component count beyond the actual boundary. -/
theorem pairRepaired_components_le_anchors (p q : {v : V // v ∉ B.vertices})
    (hs : B.syndrome = {p.val, q.val}) (hc : G.Connected) :
    Fintype.card (B.pairRepairedPuncture p q).ConnectedComponent ≤ #B.anchors := by
  classical
  let f : B.anchors → (B.pairRepairedPuncture p q).ConnectedComponent :=
    fun a => (B.pairRepairedPuncture p q).connectedComponentMk
      (B.anchorPunctureVertex a)
  have hf : Function.Surjective f := by
    intro C
    obtain ⟨u, hu, ha⟩ := B.pairRepaired_component_anchor p q hs hc C
    refine ⟨⟨u.val, ha⟩, ?_⟩
    exact (SimpleGraph.ConnectedComponent.eq_of_common_vertex hu
      (show u ∈ (f ⟨u.val, ha⟩).supp from rfl)).symm
  simpa only [Fintype.card_coe] using Fintype.card_le_of_surjective f hf

/-- Assemble all repaired components with their exact ceiling sum and y exposed. -/
theorem pairRepaired_endpoint_sum (p q : {v : V // v ∉ B.vertices})
    (hne : p ≠ q) (hs : B.syndrome = {p.val, q.val}) (hc : G.Connected)
    (y : {v : V // v ∉ B.vertices}) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ D : Decomposition (B.pairRepairedPuncture p q),
      D.size ≤ ∑ C : (B.pairRepairedPuncture p q).ConnectedComponent,
        (Fintype.card C.supp + 1) / 2 ∧ 2 ≤ D.endpointCount y := by
  classical
  obtain ⟨D, hb, he⟩ := B.pairRepaired_component_endpoint p q hne hs hc y hy
    ((B.pairRepairedPuncture p q).connectedComponentMk y) rfl hcap
  apply endpoint_budget_of_components (B.pairRepairedPuncture p q) y
    (fun C => (Fintype.card C.supp + 1) / 2) D hb he
  intro C hC
  apply B.pairRepaired_other_ceiling p q hne hs y C _ hcap
  intro hyC
  exact hC (SimpleGraph.ConnectedComponent.eq_of_common_vertex hyC rfl)

/-- Up to four anchors supply two credits, or one with at least three components. -/
theorem pairRepaired_endpoint_credit (p q : {v : V // v ∉ B.vertices})
    (hne : p ≠ q) (hs : B.syndrome = {p.val, q.val}) (hc : G.Connected)
    (hA : #B.anchors ≤ 4) (y : {v : V // v ∉ B.vertices})
    (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ D : Decomposition (B.pairRepairedPuncture p q), 2 ≤ D.endpointCount y ∧
      (D.size + 2 ≤ (Fintype.card V + 1) / 2 ∨
        (D.size + 1 ≤ (Fintype.card V + 1) / 2 ∧
          3 ≤ Fintype.card (B.pairRepairedPuncture p q).ConnectedComponent)) := by
  classical
  obtain ⟨D, hb, he⟩ := B.pairRepaired_endpoint_sum p q hne hs hc y hy hcap
  have hn := B.puncture_card_add_five
  have hcA := B.pairRepaired_components_le_anchors p q hs hc
  have ho := component_odd_count_le (B.pairRepairedPuncture p q)
  have hbalance := component_ceiling_balance (B.pairRepairedPuncture p q)
  refine ⟨D, he, ?_⟩
  by_cases htwo : D.size + 2 ≤ (Fintype.card V + 1) / 2
  · exact Or.inl htwo
  · right
    constructor <;> omega

/-- With at most three anchors, the one-credit case has exactly three odd
components, as required by the cheaper whole-deletion reconstruction records. -/
theorem pairRepaired_three_anchor_credit (p q : {v : V // v ∉ B.vertices})
    (hne : p ≠ q) (hs : B.syndrome = {p.val, q.val}) (hc : G.Connected)
    (hA : #B.anchors ≤ 3) (y : {v : V // v ∉ B.vertices})
    (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ D : Decomposition (B.pairRepairedPuncture p q), 2 ≤ D.endpointCount y ∧
      (D.size + 2 ≤ (Fintype.card V + 1) / 2 ∨
        (D.size + 1 ≤ (Fintype.card V + 1) / 2 ∧
          Fintype.card (B.pairRepairedPuncture p q).ConnectedComponent = 3 ∧
          (∑ C : (B.pairRepairedPuncture p q).ConnectedComponent,
            Fintype.card C.supp % 2) = 3)) := by
  classical
  obtain ⟨D, hb, he⟩ := B.pairRepaired_endpoint_sum p q hne hs hc y hy hcap
  have hn := B.puncture_card_add_five
  have hcA := B.pairRepaired_components_le_anchors p q hs hc
  have ho := component_odd_count_le (B.pairRepairedPuncture p q)
  have hbalance := component_ceiling_balance (B.pairRepairedPuncture p q)
  refine ⟨D, he, ?_⟩
  by_cases htwo : D.size + 2 ≤ (Fintype.card V + 1) / 2
  · exact Or.inl htwo
  · exact Or.inr ⟨by omega, by omega, by omega⟩

end Gallai.WholeBowtie
