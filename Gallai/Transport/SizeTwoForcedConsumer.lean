/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoForcedReconstruction
import Gallai.Transport.ZeroSyndromeAccounting

/-! # Original-graph consumer for forced size-two records

The carrier-family construction and global edge accounting yield one actual
decomposition with the exact record cost and all even outside endpoint reserves.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- A forced record reconstructs G from an actual all-coincident through
profile. No carrier splicing, global coverage, or endpoint reserve is assumed. -/
theorem sizeTwo_forced_reconstruction (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (D : Decomposition B.syndromeStar) (k₀ : Fin D.size)
    (hr : (D.path k₀).start = B.sizeTwoRemoteMarks A 0 ∨
      (D.path k₀).finish = B.sizeTwoRemoteMarks A 0)
    (hsRemote : (D.path k₀).start = B.sizeTwoRemoteMarks A 1 ∨
      (D.path k₀).finish = B.sizeTwoRemoteMarks A 1)
    (hx : B.completedHub ∈ (D.path k₀).walk.support)
    (hs : (D.path k₀).start ≠ B.completedHub)
    (ht : B.completedHub ≠ (D.path k₀).finish)
    (havoid : ∀ k, k ≠ k₀ → B.completedHub ∉ (D.path k).walk.support)
    (j : Fin 2) (connector extra tail : List Star.Vertex) (added : List (List Star.Vertex))
    (h : Forced.AcceptedRecord (B.completedStarState A) j connector extra tail added) :
    ∃ P : Decomposition G, P.size = D.size + added.length ∧ P.size ≤ D.size + 2 ∧
      ∀ w : B.StarSurvivor, w.val ∉ B.vertices → Even (G.degree w.val) →
        D.endpointCount w ≤ P.endpointCount w.val := by
  classical
  obtain ⟨k₁,_,F,hcarrier,hends⟩ := B.sizeTwo_forced_family A hSigma D k₀ hr hsRemote hx hs ht havoid
    j connector extra tail added h
  let P := B.sizeTwoForcedReconstruction A j connector extra tail added h hSigma D k₀ k₁ F hcarrier
  refine ⟨P,rfl,Nat.add_le_add_left h.2.2.2.2.2 _,?_⟩
  intro w hout hw
  have hlabels := B.zero_even_outside_labels A ⟨w.val,hout⟩ hw
  have hend (k : Fin D.size) :
      (if (F k).start = w.val then 1 else 0) + (if (F k).finish = w.val then 1 else 0) =
      (if (D.path k).start = w then 1 else 0) + (if (D.path k).finish = w then 1 else 0 : ℕ) := by
    obtain ⟨hstart,hfinish⟩ := hends k w.val hlabels
    simp only [hstart,hfinish,Subtype.val_inj]
  change D.endpointCount w ≤ ∑ k : Fin (D.size + added.length),
    ((if (Sum.elim F (B.sizeTwoForcedAddedPath A j connector extra tail added h)
      (finSumFinEquiv.symm k)).start = w.val then 1 else 0) +
     (if (Sum.elim F (B.sizeTwoForcedAddedPath A j connector extra tail added h)
      (finSumFinEquiv.symm k)).finish = w.val then 1 else 0))
  rw [(finSumFinEquiv : Fin D.size ⊕ Fin added.length ≃ Fin (D.size + added.length)).symm.sum_comp
    (fun k => (if (Sum.elim F (B.sizeTwoForcedAddedPath A j connector extra tail added h) k).start = w.val
      then 1 else 0) +
      (if (Sum.elim F (B.sizeTwoForcedAddedPath A j connector extra tail added h) k).finish = w.val
      then 1 else 0))]
  rw [Fintype.sum_sum_type]
  change D.endpointCount w ≤ (∑ k : Fin D.size,
    ((if (F k).start = w.val then 1 else 0) + (if (F k).finish = w.val then 1 else 0))) + _
  have he : (∑ k : Fin D.size,
      ((if (F k).start = w.val then 1 else 0) + (if (F k).finish = w.val then 1 else 0))) =
      D.endpointCount w := Finset.sum_congr rfl (fun k _ => hend k)
  rw [he]
  exact Nat.le_add_right _ _

/-- The normalized profile-zero ownership data supplies both remote endpoints
on the hub carrier, so no extra endpoint-location premise is needed. -/
theorem sizeTwo_forced_profile_zero (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (D : Decomposition B.syndromeStar) (f : Fin 4 → Fin D.size)
    (hf : ∀ r : Fin 2,
      (D.path (f (remoteRole 0 r))).start = B.sizeTwoRemoteMarks A r ∨
      (D.path (f (remoteRole 0 r))).finish = B.sizeTwoRemoteMarks A r)
    (howner : ∀ j k, j ≠ 3 → k ≠ 3 → (f j = f k ↔ owner 0 j = owner 0 k))
    (hx : B.completedHub ∈ (D.path (f 0)).walk.support)
    (hs : (D.path (f 0)).start ≠ B.completedHub)
    (ht : B.completedHub ≠ (D.path (f 0)).finish)
    (havoid : ∀ k, k ≠ f 0 → B.completedHub ∉ (D.path k).walk.support)
    (j : Fin 2) (connector extra tail : List Star.Vertex) (added : List (List Star.Vertex))
    (h : Forced.AcceptedRecord (B.completedStarState A) j connector extra tail added) :
    ∃ P : Decomposition G, P.size = D.size + added.length ∧ P.size ≤ D.size + 2 ∧
      ∀ w : B.StarSurvivor, w.val ∉ B.vertices → Even (G.degree w.val) →
        D.endpointCount w ≤ P.endpointCount w.val := by
  have hf₁ : f 1 = f 0 := (howner 1 0 (by decide) (by decide)).mpr (by decide)
  have hf₂ : f 2 = f 0 := (howner 2 0 (by decide) (by decide)).mpr (by decide)
  have hr := hf 0
  have hsRemote := hf 1
  change (D.path (f 1)).start = _ ∨ (D.path (f 1)).finish = _ at hr
  change (D.path (f 2)).start = _ ∨ (D.path (f 2)).finish = _ at hsRemote
  rw [hf₁] at hr
  rw [hf₂] at hsRemote
  exact B.sizeTwo_forced_reconstruction A hSigma D (f 0) hr hsRemote hx hs ht havoid
    j connector extra tail added h

end Gallai.WholeBowtie
