/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.Incidence
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-! # Every whole-bowtie deletion component meets the actual boundary

This uses original connectedness, not zero syndrome. It supplies the component
bound required before converting component ceilings into reconstruction credit.
-/

namespace Gallai.WholeBowtie

open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Every actual puncture component contains an original anchor. -/
theorem puncture_component_anchor (hc : G.Connected) (C : B.puncture.ConnectedComponent) :
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
    exact ⟨hw, C.mem_supp_of_adj_mem_supp hu
      (show B.puncture.Adj u ⟨w, hw⟩ from ha)⟩
  have along {v w : V} (p : G.Walk v w) :
      (∃ hv : v ∉ B.vertices, (⟨v, hv⟩ : {v : V // v ∉ B.vertices}) ∈ C.supp) →
      (∃ hw : w ∉ B.vertices, (⟨w, hw⟩ : {v : V // v ∉ B.vertices}) ∈ C.supp) := by
    induction p with
    | nil => exact id
    | @cons v w t hvw p ih =>
      rintro ⟨hv, hvC⟩
      exact ih (step ⟨v, hv⟩ hvC w hvw)
  obtain ⟨u, hu⟩ := C.nonempty_supp
  obtain ⟨p⟩ := hc u.val (B.label 0)
  obtain ⟨h, _⟩ := along p ⟨u.property, hu⟩
  exact h ((B.mem_vertices _).mpr (B.label_mem_component 0))

/-- An actual anchor as a retained vertex. -/
def anchorPunctureVertex (a : B.anchors) : {v : V // v ∉ B.vertices} :=
  ⟨a.val, by
    obtain ⟨i, hi⟩ := (B.mem_anchors _).mp a.property
    exact ((B.mem_row i _).mp hi).2⟩

/-- The component occupied by a labelled actual anchor. -/
def anchorComponent (a : B.anchors) : B.puncture.ConnectedComponent :=
  B.puncture.connectedComponentMk (B.anchorPunctureVertex a)

/-- All components, including singleton components, occur among anchor components. -/
theorem anchorComponent_surjective (hc : G.Connected) :
    Function.Surjective B.anchorComponent := by
  intro C
  obtain ⟨u, hu, ha⟩ := B.puncture_component_anchor hc C
  refine ⟨⟨u.val, ha⟩, ?_⟩
  exact (SimpleGraph.ConnectedComponent.eq_of_common_vertex hu
    (show u ∈ (B.anchorComponent ⟨u.val, ha⟩).supp from rfl)).symm

/-- The number of components is bounded by the number of actual anchors. -/
theorem puncture_components_le_anchors (hc : G.Connected) :
    Fintype.card B.puncture.ConnectedComponent ≤ #B.anchors := by
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_surjective B.anchorComponent (B.anchorComponent_surjective hc)

end Gallai.WholeBowtie
