/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromePartitions
import Mathlib.Data.Finset.Card

/-! # Normalized pullback of component and carrier interfaces

An anchor permutation changes canonical block names, not the equivalence
relation they encode. Source certificates must be selected at this pulled-back
interface before their words are relabelled to the requested target interface.
-/
namespace Gallai.Certificate.ZeroSyndrome
open scoped Finset

/-- Source-anchor labels for a requested target partition. -/
noncomputable def pullLabels (σ : Equiv.Perm (Fin 4)) (c : Labels) : Labels :=
  normalize (fun i => c (σ i))

/-- Pullback preserves exactly the requested component or carrier relation. -/
theorem pullLabels_eq_iff (σ : Equiv.Perm (Fin 4)) (c : Labels) (i j : Fin 4) :
    pullLabels σ c i = pullLabels σ c j ↔ c (σ i) = c (σ j) :=
  normalize_eq_iff _ _ _

/-- Pulled-back labels satisfy the same canonical normalization contract. -/
theorem pullLabels_normalized (σ : Equiv.Perm (Fin 4)) (c : Labels) :
    Normalized (pullLabels σ c) := normalize_normalized _

/-- Carrier fibers retain their size bound and refine the pulled-back components. -/
theorem Compatible.pullback {c k : Labels} (h : Compatible c k)
    (σ : Equiv.Perm (Fin 4)) : Compatible (pullLabels σ c) (pullLabels σ k) := by
  classical
  constructor
  · intro r
    by_cases he : (Finset.univ.filter fun j => pullLabels σ k j = r).Nonempty
    · obtain ⟨j, hj⟩ := he
      have hjr := (Finset.mem_filter.mp hj).2
      apply le_trans (Finset.card_le_card_of_injOn (t :=
        Finset.univ.filter fun i => k i = k (σ j)) σ ?_ ?_) (h.1 _)
      · intro i hi
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact (pullLabels_eq_iff σ k i j).mp ((Finset.mem_filter.mp hi).2.trans hjr.symm)
      · exact fun _ _ _ _ heq => σ.injective heq
    · rw [Finset.not_nonempty_iff_eq_empty.mp he]
      exact Nat.zero_le _
  · intro i j hij
    exact (pullLabels_eq_iff σ c i j).mpr
      (h.2 _ _ ((pullLabels_eq_iff σ k i j).mp hij))

/-- Every requested legal two-credit interface has a legal source interface. -/
theorem pullLabels_interface (σ : Equiv.Perm (Fin 4)) {c k : Labels}
    (h : (c, k) ∈ interfaces) : (pullLabels σ c, pullLabels σ k) ∈ interfaces := by
  exact (mem_interfaces _ _).mpr ⟨pullLabels_normalized _ _,
    pullLabels_normalized _ _, ((mem_interfaces _ _).mp h).2.2.pullback σ⟩

/-- Normalization and permutation do not reduce the number of component blocks. -/
theorem pullLabels_range_card (σ : Equiv.Perm (Fin 4)) (c : Labels) :
    #(Finset.univ.image c) ≤ #(Finset.univ.image (pullLabels σ c)) := by
  classical
  have he : (Finset.univ.image (pullLabels σ c)).image (fun i => c (σ i)) =
      Finset.univ.image c := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨σ i, Finset.mem_univ _, rfl⟩
    · intro hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      refine Finset.mem_image.mpr ⟨pullLabels σ c (σ.symm i),
        Finset.mem_image.mpr ⟨σ.symm i, Finset.mem_univ _, rfl⟩, ?_⟩
      simpa only [pullLabels, Equiv.apply_symm_apply] using
        (normalize_spec (fun j => c (σ j)) (σ.symm i))
  rw [← he]
  exact Finset.card_image_le

/-- A separated target partition yields a separated normalized source partition. -/
theorem pullLabels_separated (σ : Equiv.Perm (Fin 4)) {c : Labels}
    (h : c ∈ separatedPartitions) : pullLabels σ c ∈ separatedPartitions := by
  classical
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, pullLabels_normalized _ _⟩
  · exact le_trans (Finset.mem_filter.mp h).2 (pullLabels_range_card σ c)

end Gallai.Certificate.ZeroSyndrome
