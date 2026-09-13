/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.PunctureReconstruction

/-! # Automatic ordinary zero-syndrome tail selection -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Positive endpoint supply is sufficient for an ordinary core-only tail;
no selected or specially oriented old path is a caller premise. -/
theorem puncture_single_tail_reconstruction (D : Decomposition B.puncture)
    (a : {v : V // v ∉ B.vertices}) (hpos : 0 < D.endpointCount a)
    (T : NonemptyPath G) (ht : T.start = a.val)
    (hf : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices)
    {t : ℕ} (N : Fin t → NonemptyPath G)
    (hlocal : ∀ e ∈ G.edgeSet,
      T.walk.edges.count e + (∑ l, (N l).walk.edges.count e) =
        if ∃ v ∈ e, v ∈ B.vertices then 1 else 0) :
    ∃ E : Decomposition G, E.size = D.size + t ∧
      ∀ w : {v // v ∉ B.vertices}, w ≠ a →
        D.endpointCount w ≤ E.endpointCount w.val := by
  classical
  have hex : ∃ j, (D.path j).start = a ∨ (D.path j).finish = a := by
    by_contra hn
    have hz : D.endpointCount a = 0 := by
      unfold Decomposition.endpointCount
      apply Finset.sum_eq_zero
      intro i _
      have hs : (D.path i).start ≠ a := fun h => hn ⟨i,Or.inl h⟩
      have he : (D.path i).finish ≠ a := fun h => hn ⟨i,Or.inr h⟩
      simp only [if_neg hs, if_neg he, Nat.add_zero]
    omega
  obtain ⟨j, hj⟩ := hex
  let sel : Fin 1 ↪ Fin D.size := ⟨fun _ => j, fun _ _ _ => Subsingleton.elim _ _⟩
  have hsafe (_ : Fin 1) (v : {v : V // v ∉ B.vertices})
      (hv : v.val ∈ T.walk.support) : v = a ∨ ¬ B.puncture.Reachable a v := by
    rcases hf v.val hv with h | h
    · exact Or.inl (Subtype.ext (h.trans ht))
    · exact (v.property h).elim
  obtain ⟨E, hsize, hends⟩ := B.puncture_reconstruction D sel (fun _ => a)
    (fun _ => hj) (fun _ => T) (fun _ => ht) hsafe N (by
      intro e he
      simpa using hlocal e he)
  exact ⟨E, hsize, fun w hw => hends w (fun _ => hw)⟩

end Gallai.WholeBowtie
