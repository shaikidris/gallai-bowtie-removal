/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ZeroSyndromeAssignment

/-! # Reconstructed old carriers selected by a two-credit record -/

namespace Gallai.WholeBowtie

open Certificate Certificate.CompletedStar Certificate.ZeroSyndrome
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Assigned tails avoid the entire indexed old path after attachment. -/
theorem zeroAssignedTail_avoids (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (tails : Tails) (added : List (List Star.Vertex))
    (h : RecordCore (B.completedStarState A) (B.zeroComponentLabels A) tails added)
    (k : Fin D.size) (u : V) :
    (B.zeroAssignedTail A D f tails added h k u).2.support.tail.Disjoint
      (B.punctureCarrier (D.path k)).walk.support := by
  classical
  rw [B.zeroAssignedTail_support_tail]
  by_cases he : ∃ j, B.ZeroTailAt A D f tails k u j
  · rw [zeroAssignedWord, dif_pos he]
    have hj := Classical.choose_spec he
    have hp := B.allowed_tail_avoids_puncture_carrier D f hf (A (Classical.choose he)) _
      (B.zero_tail_vertices_allowed A tails added h _ hj.2.2)
    rw [hj.1] at hp
    exact hp
  · simp [zeroAssignedWord, he]

/-- Two different endpoint slots on the same carrier receive compatible tails. -/
theorem zeroAssignedTails_disjoint (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size) (tails : Tails) (added : List (List Star.Vertex))
    (h : TwoCreditAccepted (B.completedStarState A) (B.zeroComponentLabels A)
      (B.zeroCarrierLabels A D f) tails added)
    (k : Fin D.size) (u v : V) (huv : u ≠ v) :
    (B.zeroAssignedTail A D f tails added h.2.1 k u).2.support.tail.Disjoint
      (B.zeroAssignedTail A D f tails added h.2.1 k v).2.support.tail := by
  classical
  rw [B.zeroAssignedTail_support_tail, B.zeroAssignedTail_support_tail]
  by_cases hu : ∃ j, B.ZeroTailAt A D f tails k u j
  · by_cases hv : ∃ j, B.ZeroTailAt A D f tails k v j
    · rw [zeroAssignedWord, dif_pos hu, zeroAssignedWord, dif_pos hv]
      have hi := Classical.choose_spec hu
      have hj := Classical.choose_spec hv
      apply B.two_credit_tail_disjoint A D f tails added h
      · intro hij
        apply huv
        exact hi.2.1.symm.trans ((congrArg (fun j => (A j).val) hij).trans hj.2.1)
      · exact hi.1.trans hj.1.symm
    · simp [zeroAssignedWord, hv]
  · simp [zeroAssignedWord, hu]

/-- Each old carrier index now has its actual reconstructed simple path in G.
This retains one output index per old path; added paths are assembled later. -/
noncomputable def zeroRestoredOld (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (tails : Tails) (added : List (List Star.Vertex))
    (h : TwoCreditAccepted (B.completedStarState A) (B.zeroComponentLabels A)
      (B.zeroCarrierLabels A D f) tails added) (k : Fin D.size) : NonemptyPath G := by
  let P := B.punctureCarrier (D.path k)
  let L := B.zeroAssignedTail A D f tails added h.2.1 k P.start
  let R := B.zeroAssignedTail A D f tails added h.2.1 k P.finish
  exact P.endpointTails L.2 R.2
    (B.zeroAssignedTail_isPath A D f tails added h.2.1 k P.start)
    (B.zeroAssignedTail_isPath A D f tails added h.2.1 k P.finish)
    (B.zeroAssignedTail_avoids A D f hf tails added h.2.1 k P.start)
    (B.zeroAssignedTail_avoids A D f hf tails added h.2.1 k P.finish)
    (B.zeroAssignedTails_disjoint A D f tails added h k P.start P.finish (P.start_ne_finish G))

end Gallai.WholeBowtie

namespace Gallai.Certificate.ZeroSyndrome

/-- A one-credit record satisfies the same carrier compatibility used by the
two-credit reconstruction. Its stronger added-path bound remains available
from the original witness and must be retained in final budget accounting. -/
theorem OneCreditAccepted.toTwo {state : CompletedStar.State} {c k : Labels}
    {tails : Tails} {added : List (List Star.Vertex)}
    (h : OneCreditAccepted state c tails added) (hk : (c, k) ∈ interfaces) :
    TwoCreditAccepted state c k tails added := by
  refine ⟨hk, h.2.1, h.2.2.1.trans (by decide), ?_⟩
  intro i j hij howner
  by_cases hi : tails i = []
  · simp [hi]
  by_cases hj : tails j = []
  · simp [hj]
  exact False.elim (h.2.2.2 i j hij hi hj
    (((mem_interfaces c k).mp hk).2.2.2 i j howner))

end Gallai.Certificate.ZeroSyndrome
