/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRemoteAssignment
import Gallai.Transport.SizeTwoReconstruction

/-! # Preserving outside endpoint reserves in size-two reconstruction -/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : B.AnchorNumbering) (i : Fin 13)
variable (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
variable (h : OrdinaryAccepted (B.completedStarState A) i words added)

/-- A finite replacement cannot end at a vertex outside all local labels. -/
theorem sizeTwoRole_finish_ne (j : Fin 4) (hj : words j ≠ [])
    (w : V) (hw : ∀ t, B.completedLabel A t ≠ w) :
    (B.sizeTwoRole A i words added h j hj).finish ≠ w := by
  intro he
  have hm := (B.sizeTwoRole A i words added h j hj).walk.end_mem_support
  rw [B.sizeTwoRole_support,he] at hm
  obtain ⟨t,_,ht⟩ := List.mem_map.mp hm
  exact hw t ht

/-- An optional assigned tail changes only a local anchor endpoint into a
local-label endpoint. All outside endpoint occurrences are exactly preserved. -/
theorem sizeTwo_optional_endpoint_iff
    (D : Decomposition B.syndromeStar) (f : Fin 4 → Fin D.size)
    (hf : ∀ r : Fin 2,
      (D.path (f (remoteRole i r))).start = B.sizeTwoRemoteMarks A r ∨
      (D.path (f (remoteRole i r))).finish = B.sizeTwoRemoteMarks A r)
    (k : Fin D.size) (side : Bool) (w : V) (hw : ∀ t, B.completedLabel A t ≠ w) :
    (((B.sizeTwoAssignedRole A i words added h (B.sizeTwoEndpointRoles A i D f k side)).map
      (·.finish)).getD (if side then (D.path k).finish.val else (D.path k).start.val) = w) ↔
      (if side then (D.path k).finish.val else (D.path k).start.val) = w := by
  cases ho : B.sizeTwoAssignedRole A i words added h (B.sizeTwoEndpointRoles A i D f k side) with
  | none => simp [ho]
  | some T =>
    have hT : T ∈ B.sizeTwoAssignedRole A i words added h (B.sizeTwoEndpointRoles A i D f k side) := by
      rw [ho]; simp
    obtain ⟨j,hj,hne,hTeq⟩ := B.sizeTwoAssignedRole_mem A i words added h _ T hT
    have hnew : T.finish ≠ w := by
      rw [hTeq]
      exact B.sizeTwoRole_finish_ne A i words added h j hne w hw
    obtain ⟨r,_,_,_,hv⟩ := B.sizeTwoEndpointRoles_spec A i D f hf k side j hj
    have hold : (if side then (D.path k).finish.val else (D.path k).start.val) ≠ w := by
      intro he
      exact hw _ (hv.symm.trans he)
    simp [ho,hnew,hold]

/-- Passing-style endpoint formulas preserve every outside endpoint incidence
in the SAME candidate path, independently of record coverage or path counts. -/
theorem sizeTwo_optional_endpoint_contribution
    (D : Decomposition B.syndromeStar) (f : Fin 4 → Fin D.size)
    (hf : ∀ r : Fin 2,
      (D.path (f (remoteRole i r))).start = B.sizeTwoRemoteMarks A r ∨
      (D.path (f (remoteRole i r))).finish = B.sizeTwoRemoteMarks A r)
    (k : Fin D.size) (N : NonemptyPath G)
    (hstart : N.start = ((B.sizeTwoAssignedRole A i words added h
      (B.sizeTwoEndpointRoles A i D f k false)).map (·.finish)).getD (D.path k).start.val)
    (hfinish : N.finish = ((B.sizeTwoAssignedRole A i words added h
      (B.sizeTwoEndpointRoles A i D f k true)).map (·.finish)).getD (D.path k).finish.val)
    (w : B.StarSurvivor) (hw : ∀ t, B.completedLabel A t ≠ w.val) :
    (if N.start = w.val then 1 else 0) + (if N.finish = w.val then 1 else 0) =
      (if (D.path k).start = w then 1 else 0) + (if (D.path k).finish = w then 1 else 0 : ℕ) := by
  have hs := B.sizeTwo_optional_endpoint_iff A i words added h D f hf k false w.val hw
  have ht := B.sizeTwo_optional_endpoint_iff A i words added h D f hf k true w.val hw
  simp only [Bool.false_eq_true,ite_false,ite_true] at hs ht
  rw [hstart,hfinish]
  simp only [hs,ht,Subtype.val_inj]

/-- Exact old-carrier endpoint preservation yields a reserve on the actual
global decomposition. Added certificate paths can only increase it. -/
theorem sizeTwoReconstruction_endpoint_reserve
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (D : Decomposition B.syndromeStar) (f : Fin 4 → Fin D.size)
    (F : Fin D.size → NonemptyPath G) (removed : Fin D.size → List (Sym2 V))
    (hcarrier : ∀ k e, (F k).walk.edges.count e + (removed k).count e =
      ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e +
      ∑ j : Fin 4, if f j = k then
        ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e else 0)
    (hremoved : ∀ e, (∑ k : Fin D.size, (removed k).count e) =
      ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e)
    (w : B.StarSurvivor)
    (hends : ∀ k, (if (F k).start = w.val then 1 else 0) + (if (F k).finish = w.val then 1 else 0) =
      (if (D.path k).start = w then 1 else 0) + (if (D.path k).finish = w then 1 else 0 : ℕ)) :
    D.endpointCount w ≤
      (B.sizeTwoReconstruction A hSigma i words added h D f F removed hcarrier hremoved).endpointCount w.val := by
  change D.endpointCount w ≤ ∑ k : Fin (D.size + added.length),
    ((if (Sum.elim F (B.sizeTwoAddedPath A i words added h) (finSumFinEquiv.symm k)).start = w.val then 1 else 0) +
     (if (Sum.elim F (B.sizeTwoAddedPath A i words added h) (finSumFinEquiv.symm k)).finish = w.val then 1 else 0))
  rw [(finSumFinEquiv : Fin D.size ⊕ Fin added.length ≃ Fin (D.size + added.length)).symm.sum_comp
    (fun k => (if (Sum.elim F (B.sizeTwoAddedPath A i words added h) k).start = w.val then 1 else 0) +
      (if (Sum.elim F (B.sizeTwoAddedPath A i words added h) k).finish = w.val then 1 else 0))]
  rw [Fintype.sum_sum_type]
  change D.endpointCount w ≤ (∑ k : Fin D.size,
    ((if (F k).start = w.val then 1 else 0) + (if (F k).finish = w.val then 1 else 0))) + _
  have he : (∑ k : Fin D.size,
      ((if (F k).start = w.val then 1 else 0) + (if (F k).finish = w.val then 1 else 0))) =
      D.endpointCount w := Finset.sum_congr rfl (fun k _ => hends k)
  rw [he]
  exact Nat.le_add_right _ _

end Gallai.WholeBowtie
