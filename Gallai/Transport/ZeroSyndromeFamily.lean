/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ZeroSyndromeOwnership

/-! # Actual old and added paths for zero-syndrome reconstruction

This is a candidate family, not yet a decomposition: unique global edge
coverage is a separate obligation.
-/

namespace Gallai.WholeBowtie

open Certificate Certificate.CompletedStar Certificate.ZeroSyndrome
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Added words are realized as simple nonempty paths using original edges. -/
noncomputable def zeroAddedPath (A : B.AnchorNumbering) (tails : Tails)
    (added : List (List Star.Vertex))
    (h : RecordCore (B.completedStarState A) (B.zeroComponentLabels A) tails added)
    (i : Fin added.length) : NonemptyPath G :=
  B.realizeOriginalMember A (localWords tails added) h.1 added[i]
    (List.mem_append_right _ (List.getElem_mem _))

/-- The output has one index for every old carrier and every added word. -/
noncomputable def zeroCandidateFamily (A : B.AnchorNumbering)
    (D : Decomposition B.puncture) (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (tails : Tails) (added : List (List Star.Vertex))
    (h : TwoCreditAccepted (B.completedStarState A) (B.zeroComponentLabels A)
      (B.zeroCarrierLabels A D f) tails added) :
    Fin D.size ⊕ Fin added.length → NonemptyPath G
  | .inl k => B.zeroRestoredOld A D f hf tails added h k
  | .inr i => B.zeroAddedPath A tails added h.2.1 i

omit [DecidableEq V] in
/-- Exact candidate count; no old carrier index is lost or duplicated. -/
theorem zeroCandidateIndex_card (D : Decomposition B.puncture)
    (added : List (List Star.Vertex)) :
    Fintype.card (Fin D.size ⊕ Fin added.length) = D.size + added.length := by
  simp

end Gallai.WholeBowtie
