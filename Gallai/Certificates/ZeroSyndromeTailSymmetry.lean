/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromePartitionSymmetry
import Gallai.Certificates.ZeroSyndromeRecord
import Gallai.Certificates.WordRelabel

/-! # Allowed zero-syndrome tails under simultaneous anchor and vertex relabeling -/
namespace Gallai.Certificate.ZeroSyndrome
open CompletedStar

/-- Relabel a source tail and put it at its corresponding target anchor. -/
def mapTails (f : Equiv.Perm Star.Vertex) (σ : Equiv.Perm (Fin 4))
    (tails : Tails) : Tails := fun i => (tails (σ.symm i)).map f

/-- The old-component exclusion is preserved under normalized pullback. -/
theorem TailAllowed.map_pullback (f : Equiv.Perm Star.Vertex)
    (σ : Equiv.Perm (Fin 4))
    (ha : ∀ j, f (anchor j) = anchor (σ j))
    (hf : ∀ v ∈ Star.fresh, f v ∈ Star.fresh)
    {c : Labels} {i : Fin 4} {word : List Star.Vertex}
    (h : TailAllowed (pullLabels σ c) i word) :
    TailAllowed c (σ i) (word.map f) := by
  rcases h with he | ⟨hh, ht⟩
  · exact Or.inl (by simp [he])
  · refine Or.inr ⟨?_, ?_⟩
    · simpa only [List.head?_map, hh, Option.map_some] using congrArg some (ha i)
    · intro v hv
      rw [← List.map_tail] at hv
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
      rcases ht u hu with hu | ⟨j, hj, rfl⟩
      · exact Or.inl (hf _ hu)
      · refine Or.inr ⟨σ j, ?_, ha j⟩
        exact fun he => hj ((pullLabels_eq_iff σ c j i).mpr he)

/-- Every reindexed tail retains the requested target component constraint. -/
theorem mapTails_allowed (f : Equiv.Perm Star.Vertex) (σ : Equiv.Perm (Fin 4))
    (ha : ∀ j, f (anchor j) = anchor (σ j))
    (hf : ∀ v ∈ Star.fresh, f v ∈ Star.fresh)
    {c : Labels} {tails : Tails}
    (h : ∀ i, TailAllowed (pullLabels σ c) i (tails i)) :
    ∀ i, TailAllowed c i (mapTails f σ tails i) := by
  intro i
  simpa only [mapTails, Equiv.apply_symm_apply] using
    (h (σ.symm i)).map_pullback f σ ha hf

/-- The two-credit shared-carrier disjointness survives the same reindexing. -/
theorem mapTails_disjoint (f : Equiv.Perm Star.Vertex) (σ : Equiv.Perm (Fin 4))
    {k : Labels} {tails : Tails}
    (h : ∀ i j, i ≠ j → pullLabels σ k i = pullLabels σ k j →
      (tails i).tail.Disjoint (tails j).tail) :
    ∀ i j, i ≠ j → k i = k j →
      (mapTails f σ tails i).tail.Disjoint (mapTails f σ tails j).tail := by
  intro i j hij hk
  have he : pullLabels σ k (σ.symm i) = pullLabels σ k (σ.symm j) :=
    (pullLabels_eq_iff σ k _ _).mpr (by simpa only [Equiv.apply_symm_apply] using hk)
  have hd := h _ _ (fun heq => hij (σ.symm.injective heq)) he
  simpa only [mapTails, List.map_tail] using (List.Disjoint.map_iff f.injective).mpr hd

/-- The one-credit one-active-tail-per-component condition is invariant. -/
theorem mapTails_separated (f : Equiv.Perm Star.Vertex) (σ : Equiv.Perm (Fin 4))
    {c : Labels} {tails : Tails}
    (h : ∀ i j, i ≠ j → tails i ≠ [] → tails j ≠ [] →
      pullLabels σ c i ≠ pullLabels σ c j) :
    ∀ i j, i ≠ j → mapTails f σ tails i ≠ [] → mapTails f σ tails j ≠ [] →
      c i ≠ c j := by
  intro i j hij hi hj he
  apply h (σ.symm i) (σ.symm j) (fun heq => hij (σ.symm.injective heq))
    (fun hn => hi (by simp [mapTails, hn])) (fun hn => hj (by simp [mapTails, hn]))
  exact (pullLabels_eq_iff σ c _ _).mpr (by simpa only [Equiv.apply_symm_apply] using he)

end Gallai.Certificate.ZeroSyndrome
