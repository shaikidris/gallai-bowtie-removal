/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.PunctureComponents
import Gallai.Operations.Orient
import Gallai.Foundations.EndpointBounds

/-! # Simultaneous distinct carrier selection at separated anchors -/

namespace Gallai.WholeBowtie

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)


/-- At the sharp three-component budget each actual anchor occupies a distinct
component. No parity assumption is needed for this separation. -/
theorem zeroPuncture_reachable_anchors_eq (hc : G.Connected)
    (hA : B.anchors.card ≤ 3)
    (hC : Fintype.card B.puncture.ConnectedComponent = 3)
    (u v : {v : V // v ∉ B.vertices}) (hu : u.val ∈ B.anchors)
    (hv : v.val ∈ B.anchors) (hr : B.puncture.Reachable u v) : u = v := by
  classical
  have hcard : Fintype.card B.anchors =
      Fintype.card B.puncture.ConnectedComponent := by
    have hle := B.puncture_components_le_anchors hc
    rw [Fintype.card_coe]
    omega
  have hinj := (B.anchorComponent_surjective hc).injective_of_finite
    (Fintype.equivOfCardEq hcard)
  have he := hinj (a₁ := ⟨u.val,hu⟩) (a₂ := ⟨v.val,hv⟩)
    (SimpleGraph.ConnectedComponent.sound hr)
  exact Subtype.ext (congrArg (fun a : B.anchors => a.val) he)

/-- Any two actual anchors on one auxiliary path coincide in the sharp case. -/
theorem zeroSeparatedCarrier_anchors_eq (hc : G.Connected)
    (hA : B.anchors.card ≤ 3)
    (hC : Fintype.card B.puncture.ConnectedComponent = 3)
    (P : NonemptyPath B.puncture)
    (u v : {v : V // v ∉ B.vertices}) (hu : u.val ∈ B.anchors)
    (hv : v.val ∈ B.anchors) (hup : u ∈ P.walk.support) (hvp : v ∈ P.walk.support) :
    u = v := by
  classical
  exact B.zeroPuncture_reachable_anchors_eq hc hA hC u v hu hv
    ((P.walk.takeUntil u hup).reverse.append (P.walk.takeUntil v hvp)).reachable

/-- Every family of distinct actual anchors selects distinct old carriers,
oriented toward those anchors. Endpoint supply follows from repaired parity. -/
theorem zeroSeparatedCarrier_selection (hs : B.syndrome = ∅) (hc : G.Connected)
    (hA : B.anchors.card ≤ 3)
    (hC : Fintype.card B.puncture.ConnectedComponent = 3)
    (D : Decomposition B.puncture) {k : ℕ}
    (a : Fin k ↪ {v : V // v ∉ B.vertices}) (ha : ∀ i, (a i).val ∈ B.anchors) :
    ∃ j : Fin k ↪ Fin D.size, ∀ i,
      ((D.path (j i)).start = a i ∨ (D.path (j i)).finish = a i) ∧
      ((D.path (j i)).toward (a i)).finish = a i := by
  classical
  have hex (i : Fin k) : ∃ j, (D.path j).start = a i ∨ (D.path j).finish = a i := by
    have hodd : Odd (B.puncture.degree (a i)) := by
      apply Nat.not_even_iff_odd.mp
      intro he
      have hm := (B.anchor_even_puncture_iff (a i) (ha i)).mp he
      simp [hs] at hm
    have hpos := D.endpointCount_pos_of_odd_degree (a i) hodd
    by_contra hn
    have hz : D.endpointCount (a i) = 0 := by
      unfold Decomposition.endpointCount
      apply Finset.sum_eq_zero
      intro j _
      have hstart : (D.path j).start ≠ a i := fun he => hn ⟨j, Or.inl he⟩
      have hfinish : (D.path j).finish ≠ a i := fun he => hn ⟨j, Or.inr he⟩
      simp only [if_neg hstart, if_neg hfinish, Nat.add_zero]
    omega
  choose j hj using hex
  have hmem (i : Fin k) : a i ∈ (D.path (j i)).walk.support := by
    rcases hj i with h | h
    · rw [← h]
      exact (D.path (j i)).walk.start_mem_support
    · rw [← h]
      exact (D.path (j i)).walk.end_mem_support
  have hinj : Function.Injective j := by
    intro i l he
    apply a.injective
    apply B.zeroSeparatedCarrier_anchors_eq hc hA hC (D.path (j i))
      (a i) (a l) (ha i) (ha l) (hmem i)
    rw [he]
    exact hmem l
  refine ⟨⟨j, hinj⟩, ?_⟩
  intro i
  exact ⟨hj i, (D.path (j i)).toward_finish (a i) (hj i)⟩

end Gallai.WholeBowtie
