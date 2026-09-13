/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.InwardStar

/-!
# Prescribed-edge half-star addition

Fan's Lemma 3.6. Positive endpoints at every retained hub neighbour and every
missing-spoke leaf allow the prescribed edge to be restored first. Thereafter
at most one passing neighbour exists, so the inward-subset bound restores at
least half the original missing star. All counts refer to one output witness.
-/

namespace Gallai.Decomposition

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]
  [Fintype V] [DecidableRel G.Adj]

/-- Restore at least half a missing star inward, including any prescribed
spoke. Positivity covers the entire final hub neighbourhood, not just S. -/
theorem prescribed_half_star_addibility (D : Decomposition G) (a : V) (S : Finset V)
    (ha : a ∉ S) (hmissing : ∀ b ∈ S, ¬ G.Adj a b)
    (hpositive : ∀ v, G.Adj a v ∨ v ∈ S → 0 < D.endpointCount v)
    (b : V) (hb : b ∈ S) :
    ∃ B : Finset V, B ⊆ S ∧ b ∈ B ∧ #S ≤ 2 * #B ∧
      ∃ E : Decomposition (G ⊔ B.sup (SimpleGraph.edge a)), E.size = D.size ∧
        ∀ v, E.endpointCount v + (if v ∈ B then 1 else 0) =
          D.endpointCount v + if a = v then #B else 0 := by
  classical
  have hzero : #{v ∈ G.neighborFinset a | D.endpointCount v = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hadj, hz⟩ := Finset.mem_filter.mp hv
    have hp := hpositive v (Or.inl ((G.mem_neighborFinset a v).mp hadj))
    omega
  have hab : a ≠ b := fun h => ha (h.symm ▸ hb)
  obtain ⟨E, hsize, hend⟩ := D.single_edge_addibility a b hab (hmissing b hb)
    (by rw [hzero]; exact hpositive b (Or.inr hb))
  have hrem : ∀ c ∈ S.erase b, ¬ (G ⊔ SimpleGraph.edge a b).Adj a c := by
    intro c hc h
    obtain ⟨hcb, hcS⟩ := Finset.mem_erase.mp hc
    rcases h with h | h
    · exact hmissing c hcS h
    · rw [SimpleGraph.edge_adj] at h
      rcases h.1 with h | h
      · exact hcb h.2
      · exact hab h.1
  have hpos : ∀ c ∈ S.erase b, 0 < E.endpointCount c := by
    intro c hc
    obtain ⟨hcb, hcS⟩ := Finset.mem_erase.mp hc
    have hac : a ≠ c := fun h => ha (h.symm ▸ hcS)
    have he := hend c
    simp only [Ne.symm hcb, hac, if_false, Nat.add_zero] at he
    rw [he]
    exact hpositive c (Or.inr hcS)
  obtain ⟨A, hAS, hcount, Q, hQsize, hQend⟩ :=
    E.inward_star_addibility a (S.erase b)
      (fun h => ha (Finset.mem_of_mem_erase h)) hrem hpos
  have hbA : b ∉ A := fun h => (Finset.mem_erase.mp (hAS h)).1 rfl
  have hcard := Finset.card_erase_add_one hb
  have hpass := D.passing_neighbors_le_add_one a b E hend
  rw [hzero] at hpass
  refine ⟨insert b A, ?_, Finset.mem_insert_self _ _, ?_, ?_⟩
  · exact Finset.insert_subset hb (fun c hc => Finset.mem_of_mem_erase (hAS hc))
  · rw [Finset.card_insert_of_notMem hbA]
    omega
  · have hgraph : (G ⊔ SimpleGraph.edge a b) ⊔ A.sup (SimpleGraph.edge a) =
        G ⊔ (insert b A).sup (SimpleGraph.edge a) := by
      rw [Finset.sup_insert]
      exact sup_assoc _ _ _
    rw [← hgraph]
    refine ⟨Q, hQsize.trans hsize, ?_⟩
    intro v
    have he := hend v
    have hq := hQend v
    rw [Finset.card_insert_of_notMem hbA]
    by_cases hbv : b = v
    · subst v
      simp only [if_true, hab, hbA, if_false, Finset.mem_insert_self,
        Nat.add_zero] at he hq ⊢
      omega
    · have hvb : v ≠ b := Ne.symm hbv
      simp only [hbv, if_false, Nat.add_zero] at he
      simp only [Finset.mem_insert, hvb, false_or]
      by_cases hav : a = v <;> by_cases hvA : v ∈ A <;>
        simp only [hav, hvA, if_true, if_false, Nat.add_zero] at he hq ⊢ <;> omega

end Gallai.Decomposition
