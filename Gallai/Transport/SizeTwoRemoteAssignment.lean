/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRemoteSlots
import Gallai.Transport.SizeTwoAvoidingRecord

/-! # Actual anchor-indexed remote-role dispatch on the syndrome auxiliary -/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The remote marks are the two actual anchors outside the normalized pair. -/
def sizeTwoRemoteMarks (A : B.AnchorNumbering) : Fin 2 ↪ B.StarSurvivor where
  toFun r := B.completedOutside (A ⟨r.val + 2,by omega⟩).val (B.numberedAnchor_not_mem A _)
  inj' := by
    intro r s he
    have hv := congrArg Subtype.val he
    have ha := A.injective (Subtype.ext hv)
    have hi := congrArg Fin.val ha
    apply Fin.ext
    dsimp at hi
    omega

variable (A : B.AnchorNumbering) (i : Fin 13) (D : Decomposition B.syndromeStar)
variable (f : Fin 4 → Fin D.size)
variable (hf : ∀ r : Fin 2,
  (D.path (f (remoteRole i r))).start = B.sizeTwoRemoteMarks A r ∨
  (D.path (f (remoteRole i r))).finish = B.sizeTwoRemoteMarks A r)

/-- This is the actual left/right role selector used by the carrier consumers. -/
noncomputable def sizeTwoEndpointRoles (k : Fin D.size) (side : Bool) : Option (Fin 4) :=
  D.remoteRecordSlot (B.sizeTwoRemoteMarks A) (fun r => f (remoteRole i r)) i (k,side)

include hf in
/-- Every selected role belongs to this actual carrier and attaches at the
actual chosen endpoint, with its literal catalogue boundary. -/
theorem sizeTwoEndpointRoles_spec (k : Fin D.size) (side : Bool) (j : Fin 4)
    (hj : j ∈ B.sizeTwoEndpointRoles A i D f k side) :
    ∃ r : Fin 2, remoteRole i r = j ∧ f j = k ∧
      boundary i j = [CompletedStar.anchor ⟨r.val + 2,by omega⟩] ∧
      (if side then (D.path k).finish.val else (D.path k).start.val) =
        B.completedLabel A (CompletedStar.anchor ⟨r.val + 2,by omega⟩) := by
  obtain ⟨r,hr,hslot⟩ := (D.remoteRecordSlot_mem (B.sizeTwoRemoteMarks A)
    (fun r => f (remoteRole i r)) hf i (k,side) j).mp hj
  have howner := congrArg Prod.fst hslot
  change f (remoteRole i r) = k at howner
  have hv := D.remoteSlot_vertex (B.sizeTwoRemoteMarks A)
    (fun r => f (remoteRole i r)) hf r
  rw [hslot] at hv
  have hv' := congrArg Subtype.val hv
  refine ⟨r,hr,hr ▸ howner,hr ▸ remoteRole_boundary i r,?_⟩
  rw [B.completedLabel_anchor]
  cases side <;> exact hv'

include hf in
theorem sizeTwoEndpointRoles_distinct (k : Fin D.size) (j l : Fin 4)
    (hj : j ∈ B.sizeTwoEndpointRoles A i D f k false)
    (hl : l ∈ B.sizeTwoEndpointRoles A i D f k true) : j ≠ l :=
  D.remoteRecordSlot_ends_disjoint (B.sizeTwoRemoteMarks A)
    (fun r => f (remoteRole i r)) hf i k j l hj hl

include hf in
/-- Instantiated slot sums are already in the actual owner's indexing. -/
theorem sizeTwoEndpointRoles_sum (k : Fin D.size) (weight : Fin 4 → ℕ) :
    (∑ side : Bool, ((B.sizeTwoEndpointRoles A i D f k side).map weight).getD 0) =
      ∑ r : Fin 2, if f (remoteRole i r) = k then weight (remoteRole i r) else 0 :=
  D.remoteRecordSlot_carrier_sum (B.sizeTwoRemoteMarks A)
    (fun r => f (remoteRole i r)) hf i k weight

include hf in
/-- Actual remote endpoint selection discharges all role-selection conditions
of the hub-free consumer. Only the selected carrier's hub avoidance remains. -/
theorem sizeTwo_dispatch_avoiding
    (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
    (h : OrdinaryAccepted (B.completedStarState A) i words added)
    (howners : ∀ r s : Fin 2, f (remoteRole i r) = f (remoteRole i s) →
      owner i (remoteRole i r) = owner i (remoteRole i s))
    (k : Fin D.size) (hx : B.completedHub ∉ (D.path k).walk.support) :
    ∃ N : NonemptyPath G,
      N.start = ((B.sizeTwoAssignedRole A i words added h
        (B.sizeTwoEndpointRoles A i D f k false)).map (·.finish)).getD (D.path k).start.val ∧
      N.finish = ((B.sizeTwoAssignedRole A i words added h
        (B.sizeTwoEndpointRoles A i D f k true)).map (·.finish)).getD (D.path k).finish.val ∧
      ∀ e : Sym2 V, N.walk.edges.count e =
        ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e +
        ∑ r : Fin 2, if f (remoteRole i r) = k then
          ((wordEdges (words (remoteRole i r))).map (Sym2.map (B.completedLabel A))).count e else 0 := by
  let left := B.sizeTwoEndpointRoles A i D f k false
  let right := B.sizeTwoEndpointRoles A i D f k true
  obtain ⟨N,hNs,hNt,hNe⟩ := B.sizeTwo_avoiding_record A i words added h (D.path k) hx left right
    (by
      intro j hj
      obtain ⟨r,_,_,hb,hv⟩ := B.sizeTwoEndpointRoles_spec A i D f hf k false j hj
      exact ⟨_,hb,hv⟩)
    (by
      intro j hj
      obtain ⟨r,_,_,hb,hv⟩ := B.sizeTwoEndpointRoles_spec A i D f hf k true j hj
      exact ⟨_,hb,hv⟩)
    (by
      intro j hj l hl
      obtain ⟨r,hr,hrk,_,_⟩ := B.sizeTwoEndpointRoles_spec A i D f hf k false j hj
      obtain ⟨s,hs,hsk,_,_⟩ := B.sizeTwoEndpointRoles_spec A i D f hf k true l hl
      refine ⟨B.sizeTwoEndpointRoles_distinct A i D f hf k j l hj hl,?_⟩
      subst j l
      exact howners r s (hrk.trans hsk.symm))
  refine ⟨N,hNs,hNt,?_⟩
  intro e
  have hsum := B.sizeTwoEndpointRoles_sum A i D f hf k
    (fun j => ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e)
  simp only [Fintype.sum_bool] at hsum
  have he := hNe e
  change _ + _ = _ at hsum
  dsimp only [left,right] at he
  omega

end Gallai.WholeBowtie
