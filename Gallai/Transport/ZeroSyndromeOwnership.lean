/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ZeroSyndromeAssignedCarrier

/-! # Unique endpoint-slot ownership of active tails -/

namespace Gallai.WholeBowtie

open Certificate Certificate.CompletedStar Certificate.ZeroSyndrome
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- False selects the start slot and true the finish slot. -/
def zeroSlotVertex (D : Decomposition B.puncture) (s : Fin D.size × Bool) : V :=
  if s.2 then (D.path s.1).finish.val else (D.path s.1).start.val

omit [DecidableEq V] in
/-- The two slots of a nonempty simple old path are different. -/
theorem zeroSlotVertex_injective (D : Decomposition B.puncture) (k : Fin D.size) :
    Function.Injective (fun b => B.zeroSlotVertex D (k, b)) := by
  intro b c h
  have hn := (D.path k).start_ne_finish B.puncture
  cases b <;> cases c <;> simp_all [zeroSlotVertex, Subtype.ext_iff]

/-- Every nonempty tail has exactly one actual endpoint slot, not merely an
owner path. This prevents double consumption when both endpoints are scanned. -/
theorem zeroTail_unique_slot (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (tails : Tails) (j : Fin 4) (hj : tails j ≠ []) :
    ∃! s : Fin D.size × Bool,
      B.ZeroTailAt A D f tails s.1 (B.zeroSlotVertex D s) j := by
  have hex : ∃ b : Bool, (A j).val = B.zeroSlotVertex D (f (A j), b) := by
    rcases hf (A j) with h | h
    · exact ⟨false, (congrArg Subtype.val h).symm⟩
    · exact ⟨true, (congrArg Subtype.val h).symm⟩
  obtain ⟨b, hb⟩ := hex
  refine ⟨(f (A j), b), ⟨rfl, hb, hj⟩, ?_⟩
  rintro ⟨k, c⟩ hc
  have hk : f (A j) = k := hc.1
  subst k
  have hbc : c = b := B.zeroSlotVertex_injective D (f (A j))
    (hc.2.1.symm.trans hb)
  simp [hbc]

/-- Nonempty assigned words are precisely the active owned tails. -/
theorem zeroAssignedWord_ne_nil_iff (A : B.AnchorNumbering)
    (D : Decomposition B.puncture) (f : B.anchors → Fin D.size)
    (tails : Tails) (k : Fin D.size) (u : V) :
    B.zeroAssignedWord A D f tails k u ≠ [] ↔
      ∃ j, B.ZeroTailAt A D f tails k u j := by
  classical
  by_cases he : ∃ j, B.ZeroTailAt A D f tails k u j
  · rw [B.zeroAssignedWord_at A D f tails k u _ (Classical.choose_spec he)]
    exact iff_of_true (Classical.choose_spec he).2.2 he
  · simp [zeroAssignedWord, he]

/-- Every active output slot recovers exactly one input tail occurrence.
Together with zeroTail_unique_slot this is a bijective ownership relation. -/
theorem zeroSlot_unique_tail (A : B.AnchorNumbering)
    (D : Decomposition B.puncture) (f : B.anchors → Fin D.size)
    (tails : Tails) (s : Fin D.size × Bool)
    (hs : B.zeroAssignedWord A D f tails s.1 (B.zeroSlotVertex D s) ≠ []) :
    ∃! j, B.ZeroTailAt A D f tails s.1 (B.zeroSlotVertex D s) j := by
  obtain ⟨j, hj⟩ := (B.zeroAssignedWord_ne_nil_iff A D f tails _ _).mp hs
  exact ⟨j, hj, fun i hi => B.zeroTailAt_unique A D f tails _ _ i j hi hj⟩

end Gallai.WholeBowtie
