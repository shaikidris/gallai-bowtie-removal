/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ReleasedCarrierFootprint
import Gallai.Transport.FreshCarrierOptional

/-! # Release an actual through run and attach optional tails at both ends -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The connector is oriented to the actual released attachments. Optional
remote tails may occur at either or both ends of this same carrier. No
original-edge hypothesis is imposed on the auxiliary hub spokes. -/
theorem syndrome_passing_release_optional (P : NonemptyPath B.syndromeStar)
    (hx : B.completedHub ∈ P.walk.support)
    (hs : P.start ≠ B.completedHub) (ht : B.completedHub ≠ P.finish)
    (M : G.Walk (P.takeTo B.completedHub hx hs).walk.reverse.snd.val
      (P.dropFrom B.completedHub hx ht).walk.snd.val)
    (hM : M.IsPath) (hne : ¬ M.Nil)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = (P.takeTo B.completedHub hx hs).walk.reverse.snd.val ∨
      v.val = (P.dropFrom B.completedHub hx ht).walk.snd.val ∨ v.val = B.label 0)
    (U T : Option (NonemptyPath G))
    (hU : ∀ Q ∈ U, P.start.val = Q.start ∧
      (∀ v ∈ Q.walk.support, v = Q.start ∨ v ∈ B.vertices) ∧
      Disjoint (M.support.toFinset ∩ B.vertices) (Q.freshSupport B.vertices))
    (hT : ∀ Q ∈ T, P.finish.val = Q.start ∧
      (∀ v ∈ Q.walk.support, v = Q.start ∨ v ∈ B.vertices) ∧
      Disjoint (M.support.toFinset ∩ B.vertices) (Q.freshSupport B.vertices))
    (hUT : ∀ Q ∈ U, ∀ R ∈ T,
      Disjoint (Q.freshSupport B.vertices) (R.freshSupport B.vertices)) :
    ∃ N : NonemptyPath G,
      N.start = (U.map (·.finish)).getD P.start.val ∧
      N.finish = (T.map (·.finish)).getD P.finish.val ∧
      ∀ e : Sym2 V, N.walk.edges.count e +
        ([s(B.label 0,(P.takeTo B.completedHub hx hs).walk.reverse.snd.val),
          s(B.label 0,(P.dropFrom B.completedHub hx ht).walk.snd.val)] : List (Sym2 V)).count e =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e + M.edges.count e +
        ((U.map (fun Q => Q.walk.edges)).getD []).count e +
        ((T.map (fun Q => Q.walk.edges)).getD []).count e := by
  let L := P.releaseLeft B.completedHub hx hs
  let R := P.releaseRight B.completedHub hx ht
  have hL := P.releaseLeft_isPath B.completedHub hx hs
  have hR := P.releaseRight_isPath B.completedHub hx ht
  have hLR := P.release_supports_disjoint B.completedHub hx hs ht
  have hxL := P.hub_notMem_releaseLeft B.completedHub hx hs
  have hxR := P.hub_notMem_releaseRight B.completedHub hx ht
  let C := B.retainedThroughCarrier B.syndromeStar B.syndromeStar_le_completedStar
    L R M hL hR hM hne hLR hxL hxR hm
  have hsub : C.freshSupport B.vertices ⊆ M.support.toFinset ∩ B.vertices := by
    intro v hv
    obtain ⟨hvC,hB⟩ := Finset.mem_inter.mp hv
    have hvM := B.completedThroughCarrier_core_support
      (B.retainedLiftWalk B.syndromeStar B.syndromeStar_le_completedStar L)
      (B.retainedLiftWalk B.syndromeStar B.syndromeStar_le_completedStar R) M
      (B.retainedLiftWalk_isPath _ _ L hL) (B.retainedLiftWalk_isPath _ _ R hR)
      hM hne (by simpa only [B.retainedLiftWalk_support] using hLR)
      (by simpa only [B.retainedLiftWalk_support] using hxL)
      (by simpa only [B.retainedLiftWalk_support] using hxR) hm
      v (List.mem_toFinset.mp hvC) hB
    exact Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hvM,hB⟩
  obtain ⟨N,hNs,hNt,hNe⟩ := C.extend_optional_fresh U T B.vertices
    (by intro Q hQ; obtain ⟨hj,hf,hd⟩ := hU Q hQ; exact ⟨hj,hf,hd.mono_left hsub⟩)
    (by intro Q hQ; obtain ⟨hj,hf,hd⟩ := hT Q hQ; exact ⟨hj,hf,hd.mono_left hsub⟩) hUT
  refine ⟨N,hNs,hNt,?_⟩
  intro e
  have hC := congrArg (List.count e)
    (B.retainedThroughCarrier_edges B.syndromeStar B.syndromeStar_le_completedStar
      L R M hL hR hM hne hLR hxL hxR hm)
  have hnew := congrArg (List.count e) hNe
  have hold := congrArg (fun es : List (Sym2 B.StarSurvivor) =>
    (es.map (Sym2.map Subtype.val)).count e) (P.release_edges B.completedHub hx hs ht)
  have hrev : ((U.map (fun Q => Q.walk.edges.reverse)).getD []).count e =
      ((U.map (fun Q => Q.walk.edges)).getD []).count e := by
    cases U <;> simp only [Option.map_none,Option.map_some,Option.getD_none,
      Option.getD_some,List.count_reverse]
  simp only [List.map_append,List.map_cons,List.map_nil,Sym2.map_mk,List.count_append] at hold
  simp only [List.count_append] at hC hnew
  change C.walk.edges.count e = _ at hC
  rw [hrev] at hnew
  change (L.edges.map (Sym2.map Subtype.val)).count e +
    ([s(B.label 0,(P.takeTo B.completedHub hx hs).walk.reverse.snd.val),
      s(B.label 0,(P.dropFrom B.completedHub hx ht).walk.snd.val)] : List (Sym2 V)).count e +
    (R.edges.map (Sym2.map Subtype.val)).count e =
    (P.walk.edges.map (Sym2.map Subtype.val)).count e at hold
  omega

end Gallai.WholeBowtie
