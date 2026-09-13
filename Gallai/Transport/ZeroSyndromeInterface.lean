/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.ZeroSyndromeCredit

/-! # Actual anchor carriers for whole deletion

Odd anchors supply endpoint carriers. A carrier can serve at most two anchors,
and its support stays in their actual puncture component. These are the
interface constraints consumed by zero-syndrome reconstruction records.
-/

namespace Gallai

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Positive endpoint multiplicity supplies an actual indexed carrier. -/
theorem Decomposition.exists_endpoint_carrier (D : Decomposition G) (v : V)
    (hv : 0 < D.endpointCount v) :
    ∃ i : Fin D.size, (D.path i).start = v ∨ (D.path i).finish = v := by
  by_contra hn
  push Not at hn
  have hz : D.endpointCount v = 0 := by
    simp [Decomposition.endpointCount, fun i => (hn i).1, fun i => (hn i).2]
  omega

/-- Every vertex of a carrier belongs to the component of either endpoint. -/
theorem NonemptyPath.component_eq_of_endpoint (P : NonemptyPath G) (a v : V)
    (ha : P.start = a ∨ P.finish = a) (hv : v ∈ P.walk.support) :
    G.connectedComponentMk a = G.connectedComponentMk v := by
  apply SimpleGraph.ConnectedComponent.sound
  have hp := (P.walk.takeUntil v hv).reachable
  rcases ha with rfl | rfl
  · exact hp
  · exact P.walk.reachable.symm.trans hp

namespace WholeBowtie

open scoped Finset
variable [Fintype V] [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Zero syndrome supplies a simultaneous choice of actual anchor carriers. -/
theorem zero_anchor_carriers (hz : B.syndrome = ∅) (D : Decomposition B.puncture) :
    ∃ f : B.anchors → Fin D.size, ∀ a,
      (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a := by
  classical
  have h (a : B.anchors) := D.exists_endpoint_carrier (B.anchorPunctureVertex a)
    (D.endpointCount_pos_of_odd_degree _
      (B.zero_puncture_anchor_odd hz _ a.property))
  exact ⟨fun a => Classical.choose (h a), fun a => Classical.choose_spec (h a)⟩

/-- An endpoint carrier stays inside the actual component of its anchor. -/
theorem anchor_carrier_component (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (a : B.anchors) (v : {v : V // v ∉ B.vertices})
    (hv : v ∈ (D.path (f a)).walk.support) :
    B.anchorComponent a = B.puncture.connectedComponentMk v :=
  (D.path (f a)).component_eq_of_endpoint _ _ (hf a) hv

/-- Coincident carriers cannot join anchors in different puncture components. -/
theorem same_carrier_same_component (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (a b : B.anchors) (hab : f a = f b) :
    B.anchorComponent a = B.anchorComponent b := by
  have h (c : B.anchors) := B.anchor_carrier_component D f hf c
    (D.path (f c)).start (D.path (f c)).walk.start_mem_support
  exact (h a).trans (hab ▸ (h b).symm)

/-- The chosen carrier fiber has at most two actual anchors. -/
theorem anchor_carrier_fiber_le_two (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (i : Fin D.size) : #{a | f a = i} ≤ 2 := by
  classical
  let e : B.anchors ↪ {v : V // v ∉ B.vertices} :=
    ⟨B.anchorPunctureVertex, fun a b h => by
      apply Subtype.ext
      exact congrArg (fun v : {v : V // v ∉ B.vertices} => v.val) h⟩
  have hs : (Finset.univ.filter (fun a => f a = i)).map e ⊆
      {(D.path i).start, (D.path i).finish} := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
    have hi := (Finset.mem_filter.mp ha).2
    have he := hf a
    rw [hi] at he
    change B.anchorPunctureVertex a ∈ {(D.path i).start, (D.path i).finish}
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact he.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
  have hh := Finset.card_le_card hs
  simp only [Finset.card_map] at hh
  exact hh.trans (by
    have h := Finset.card_insert_le (D.path i).start {(D.path i).finish}
    simpa using h)

/-- An anchor outside the carrier's component is safe from every old vertex
of that carrier, not merely from its endpoints. -/
theorem other_component_anchor_avoids_carrier (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (a b : B.anchors) (hab : B.anchorComponent a ≠ B.anchorComponent b) :
    B.anchorPunctureVertex b ∉ (D.path (f a)).walk.support := by
  intro hv
  exact hab (B.anchor_carrier_component D f hf a _ hv)

/-- The one-credit record's one-tail-per-component condition ensures that
distinct extended anchors use distinct old carriers. -/
theorem carriers_injective_on_separated_anchors (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (s : Set B.anchors) (hs : Set.InjOn B.anchorComponent s) : Set.InjOn f s := by
  intro a ha b hb hab
  exact hs ha hb (B.same_carrier_same_component D f hf a b hab)

end WholeBowtie
end Gallai
