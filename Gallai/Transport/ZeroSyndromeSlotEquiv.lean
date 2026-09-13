/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ZeroSyndromeOwnership

/-! # Reindexing active tail occurrences by their actual endpoint slots -/

namespace Gallai.WholeBowtie
open Certificate Certificate.CompletedStar Certificate.ZeroSyndrome

/-- Dropping empty word occurrences changes no weight that vanishes at nil. -/
theorem sum_nonempty_words {ι α : Type*} [Fintype ι]
    (words : ι → List α) (weight : List α → ℕ) (hnil : weight [] = 0) :
    (∑ j : {i // words i ≠ []}, weight (words j.val)) =
      ∑ i, weight (words i) := by
  classical
  have hs := Fintype.sum_subtype_add_sum_subtype (fun i => words i ≠ [])
    (fun i => weight (words i))
  have hz : (∑ j : {i // ¬words i ≠ []}, weight (words j.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [not_not.mp j.property, hnil]
  simpa only [hz, Nat.add_zero] using hs

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The occurrence bijection, rather than an equality of sets of words: two
equal words at different input indices must still be accounted for separately. -/
noncomputable def zeroTailSlotEquiv (A : B.AnchorNumbering)
    (D : Decomposition B.puncture) (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (tails : Tails) :
    {j : Fin 4 // tails j ≠ []} ≃
      {s : Fin D.size × Bool //
        B.zeroAssignedWord A D f tails s.1 (B.zeroSlotVertex D s) ≠ []} := by
  classical
  let R (j : Fin 4) (s : Fin D.size × Bool) :=
    B.ZeroTailAt A D f tails s.1 (B.zeroSlotVertex D s) j
  have hs (j : {j : Fin 4 // tails j ≠ []}) : ∃! s, R j.val s :=
    B.zeroTail_unique_slot A D f hf tails j.val j.property
  have hj (s : {s : Fin D.size × Bool //
      B.zeroAssignedWord A D f tails s.1 (B.zeroSlotVertex D s) ≠ []}) :
      ∃! j, R j s.val := B.zeroSlot_unique_tail A D f tails s.val s.property
  let toSlot (j : {j : Fin 4 // tails j ≠ []}) := (hs j).exists.choose
  have hto (j : {j : Fin 4 // tails j ≠ []}) : R j.val (toSlot j) :=
    (hs j).exists.choose_spec
  let toTail (s : {s : Fin D.size × Bool //
      B.zeroAssignedWord A D f tails s.1 (B.zeroSlotVertex D s) ≠ []}) :=
    (hj s).exists.choose
  have hfrom (s : {s : Fin D.size × Bool //
      B.zeroAssignedWord A D f tails s.1 (B.zeroSlotVertex D s) ≠ []}) :
      R (toTail s) s.val := (hj s).exists.choose_spec
  refine
    { toFun := fun j => ⟨toSlot j,
        (B.zeroAssignedWord_ne_nil_iff A D f tails _ _).mpr ⟨j.val, hto j⟩⟩
      invFun := fun s => ⟨toTail s, (hfrom s).2.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro j
    apply Subtype.ext
    exact B.zeroTailAt_unique A D f tails _ _ _ _ (hfrom _) (hto j)
  · intro s
    apply Subtype.ext
    exact (hs ⟨toTail s, (hfrom s).2.2⟩).unique (hto _) (hfrom s)

/-- Reindexing preserves the literal word, not just its edge set. -/
theorem zeroTailSlotEquiv_word (A : B.AnchorNumbering)
    (D : Decomposition B.puncture) (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (tails : Tails) (j : {j : Fin 4 // tails j ≠ []}) :
    B.zeroAssignedWord A D f tails
      (B.zeroTailSlotEquiv A D f hf tails j).val.1
      (B.zeroSlotVertex D (B.zeroTailSlotEquiv A D f hf tails j).val) = tails j.val := by
  apply B.zeroAssignedWord_at
  exact (B.zeroTail_unique_slot A D f hf tails j.val j.property).exists.choose_spec

/-- Any additive accounting weight on active tail words can be transferred
exactly to the active actual slots, preserving occurrence multiplicities. -/
theorem zero_active_word_sum (A : B.AnchorNumbering)
    (D : Decomposition B.puncture) (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (tails : Tails) (weight : List Star.Vertex → ℕ) :
    (∑ j : {j : Fin 4 // tails j ≠ []}, weight (tails j.val)) =
    ∑ s : {s : Fin D.size × Bool //
        B.zeroAssignedWord A D f tails s.1 (B.zeroSlotVertex D s) ≠ []},
      weight (B.zeroAssignedWord A D f tails s.val.1 (B.zeroSlotVertex D s.val)) := by
  classical
  apply Fintype.sum_equiv (B.zeroTailSlotEquiv A D f hf tails)
  intro j
  rw [B.zeroTailSlotEquiv_word]

/-- Exact accounting over all old endpoint slots, with inactive slots
contributing zero. This is the global-tail term in the reconstruction count. -/
theorem zero_all_slot_word_sum (A : B.AnchorNumbering)
    (D : Decomposition B.puncture) (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (tails : Tails) (weight : List Star.Vertex → ℕ) (hnil : weight [] = 0) :
    (∑ s : Fin D.size × Bool,
      weight (B.zeroAssignedWord A D f tails s.1 (B.zeroSlotVertex D s))) =
      ∑ j : Fin 4, weight (tails j) := by
  classical
  calc
    _ = ∑ s : {s : Fin D.size × Bool //
        B.zeroAssignedWord A D f tails s.1 (B.zeroSlotVertex D s) ≠ []},
        weight (B.zeroAssignedWord A D f tails s.val.1 (B.zeroSlotVertex D s.val)) :=
      (sum_nonempty_words _ weight hnil).symm
    _ = ∑ j : {j : Fin 4 // tails j ≠ []}, weight (tails j.val) :=
      (B.zero_active_word_sum A D f hf tails weight).symm
    _ = _ := sum_nonempty_words tails weight hnil

end Gallai.WholeBowtie
