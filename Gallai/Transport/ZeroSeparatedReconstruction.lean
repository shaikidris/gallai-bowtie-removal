/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ZeroSeparatedSelection
import Gallai.Transport.PunctureReconstruction

/-! # Reconstruction at the sharp three-component zero-syndrome budget -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Three components force the separation needed for simultaneous anchor tails.
All endpoint and carrier choices are derived from the actual graph hypotheses. -/
theorem zeroSeparated_reconstruction (hs : B.syndrome = ∅) (hc : G.Connected)
    (hA : B.anchors.card ≤ 3)
    (hC : Fintype.card B.puncture.ConnectedComponent = 3)
    (D : Decomposition B.puncture) {k : ℕ}
    (a : Fin k ↪ {v : V // v ∉ B.vertices}) (ha : ∀ l, (a l).val ∈ B.anchors)
    (T : Fin k → NonemptyPath G) (ht : ∀ l, (T l).start = (a l).val)
    (hf : ∀ l v, v ∈ (T l).walk.support → v ∈ B.vertices ∨ v ∈ B.anchors)
    {t : ℕ} (N : Fin t → NonemptyPath G)
    (hlocal : ∀ e ∈ G.edgeSet,
      (∑ l, (T l).walk.edges.count e) + (∑ l, (N l).walk.edges.count e) =
        if ∃ v ∈ e, v ∈ B.vertices then 1 else 0) :
    ∃ E : Decomposition G, E.size = D.size + t ∧
      ∀ w : {v // v ∉ B.vertices}, Even (G.degree w.val) →
        D.endpointCount w ≤ E.endpointCount w.val := by
  classical
  obtain ⟨j, hj⟩ := B.zeroSeparatedCarrier_selection hs hc hA hC D a ha
  have hsafe (l) (v : {v : V // v ∉ B.vertices})
      (hv : v.val ∈ (T l).walk.support) :
      v = a l ∨ ¬ B.puncture.Reachable (a l) v := by
    rcases hf l v.val hv with h | h
    · exact (v.property h).elim
    · by_cases he : v = a l
      · exact Or.inl he
      · exact Or.inr (fun hr => he
          (B.zeroPuncture_reachable_anchors_eq hc hA hC (a l) v (ha l) h hr).symm)
  obtain ⟨E, hsize, hends⟩ := B.puncture_reconstruction D j a (fun l => (hj l).1)
    T ht hsafe N hlocal
  refine ⟨E, hsize, ?_⟩
  intro w hw
  apply hends w
  intro l he
  have hodd := B.odd_degree_anchor (ha l)
  exact (Nat.not_even_iff_odd.mpr hodd) (he ▸ hw)

end Gallai.WholeBowtie
