/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.PunctureFamily

/-! # Repair-free reconstruction from component-safe tails -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The whole puncture leaves precisely the edges incident with the bowtie. -/
theorem puncture_mapped_count (D : Decomposition B.puncture)
    (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) =
      if ∃ v ∈ e, v ∈ B.vertices then 0 else 1 := by
  classical
  by_cases hl : ∃ v ∈ e, v ∈ B.vertices
  · rw [if_pos hl]
    apply Finset.sum_eq_zero
    intro i _
    apply List.count_eq_zero.mpr
    intro hm
    obtain ⟨f, _, hfe⟩ := List.mem_map.mp hm
    obtain ⟨v, hv, hB⟩ := hl
    rw [← hfe] at hv
    obtain ⟨w, _, rfl⟩ := Sym2.mem_map.mp hv
    exact w.property hB
  · rw [if_neg hl]
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hu : u ∉ B.vertices := fun h => hl ⟨u, by simp, h⟩
      have hv : v ∉ B.vertices := fun h => hl ⟨v, by simp, h⟩
      let f : Sym2 {v // v ∉ B.vertices} := s(⟨u,hu⟩,⟨v,hv⟩)
      change (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count
        (Sym2.map Subtype.val f)) = 1
      simp only [List.count_map_of_injective _ _
        (Sym2.map.injective Subtype.val_injective)]
      exact (D.sum_edge_count f).trans (if_pos he)

/-- Simultaneous tails and a local edge partition yield an actual decomposition
at the exact added-path cost. This covers both ordinary and separated tails. -/
theorem puncture_reconstruction (D : Decomposition B.puncture) {k : ℕ}
    (j : Fin k ↪ Fin D.size) (a : Fin k → {v : V // v ∉ B.vertices})
    (hj : ∀ l, (D.path (j l)).start = a l ∨ (D.path (j l)).finish = a l)
    (T : Fin k → NonemptyPath G) (ht : ∀ l, (T l).start = (a l).val)
    (hf : ∀ l v, v.val ∈ (T l).walk.support →
      v = a l ∨ ¬ B.puncture.Reachable (a l) v)
    {t : ℕ} (N : Fin t → NonemptyPath G)
    (hlocal : ∀ e ∈ G.edgeSet,
      (∑ l, (T l).walk.edges.count e) + (∑ l, (N l).walk.edges.count e) =
        if ∃ v ∈ e, v ∈ B.vertices then 1 else 0) :
    ∃ E : Decomposition G, E.size = D.size + t ∧
      ∀ w : {v // v ∉ B.vertices}, (∀ l, w ≠ a l) →
        D.endpointCount w ≤ E.endpointCount w.val := by
  classical
  obtain ⟨F, hcount, hends⟩ := B.punctureSeparatedFamily D j a hj T ht hf
  let family : Fin D.size ⊕ Fin t → NonemptyPath G := Sum.elim F N
  have hcover (e : Sym2 V) (he : e ∈ G.edgeSet) :
      (∑ i, (family i).walk.edges.count e) = 1 := by
    rw [Fintype.sum_sum_type]
    change (∑ i, (F i).walk.edges.count e) + (∑ l, (N l).walk.edges.count e) = 1
    rw [hcount, B.puncture_mapped_count D e he, Nat.add_assoc, hlocal e he]
    split <;> simp
  let E : Decomposition G := Decomposition.ofEdgeCounts
    (fun i : Fin (D.size + t) => family (finSumFinEquiv.symm i)) (by
      intro e he
      exact ((finSumFinEquiv : Fin D.size ⊕ Fin t ≃ Fin (D.size + t)).symm.sum_comp
        (fun i => (family i).walk.edges.count e)).trans (hcover e he))
  refine ⟨E, rfl, ?_⟩
  intro w hw
  change D.endpointCount w ≤ ∑ i : Fin (D.size + t),
    ((if (family (finSumFinEquiv.symm i)).start = w.val then 1 else 0) +
      (if (family (finSumFinEquiv.symm i)).finish = w.val then 1 else 0))
  rw [(finSumFinEquiv : Fin D.size ⊕ Fin t ≃ Fin (D.size + t)).symm.sum_comp
      (fun i => (if (family i).start = w.val then 1 else 0) +
        (if (family i).finish = w.val then 1 else 0)), Fintype.sum_sum_type]
  exact (hends w hw).trans (Nat.le_add_right _ _)

end Gallai.WholeBowtie
