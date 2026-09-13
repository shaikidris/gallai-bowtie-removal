/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoWords
import Gallai.Transport.SyndromePassingOptional

/-! # Checked ordinary records reconstruct a through carrier with optional roles -/
namespace Gallai.NonemptyPath
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Orient a connector without changing its edge multiplicities or footprint. -/
theorem orient_connector (P : NonemptyPath G) (p q : V)
    (hpair : (p = P.start ∧ q = P.finish) ∨ (p = P.finish ∧ q = P.start)) :
    ∃ M : G.Walk p q, M.IsPath ∧ ¬ M.Nil ∧
      (∀ e, M.edges.count e = P.walk.edges.count e) ∧
      M.support.toFinset = P.walk.support.toFinset := by
  rcases hpair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨P.walk,P.isPath,P.nonempty,fun _ => rfl,rfl⟩
  · refine ⟨P.walk.reverse,P.isPath.reverse,?_,?_,?_⟩
    · exact fun hn => P.nonempty (SimpleGraph.Walk.nil_reverse.mp hn)
    · intro e; simp only [SimpleGraph.Walk.edges_reverse,List.count_reverse]
    · simp only [SimpleGraph.Walk.support_reverse,List.toFinset_reverse]

end Gallai.NonemptyPath

namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : B.AnchorNumbering) (i : Fin 13)
variable (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
variable (h : OrdinaryAccepted (B.completedStarState A) i words added)

/-- A role not assigned to this endpoint, or an assigned empty word, is absent. -/
noncomputable def sizeTwoAssignedRole (o : Option (Fin 4)) : Option (NonemptyPath G) :=
  o.bind (fun k => B.sizeTwoOptionalRole A i words added h k)

theorem sizeTwoAssignedRole_mem (o : Option (Fin 4)) (T : NonemptyPath G)
    (ht : T ∈ B.sizeTwoAssignedRole A i words added h o) :
    ∃ k ∈ o, ∃ hk : words k ≠ [], T = B.sizeTwoRole A i words added h k hk := by
  obtain ⟨k,hk,hT⟩ := Option.mem_bind_iff.mp ht
  obtain ⟨hne,he⟩ := B.sizeTwoOptionalRole_mem A i words added h k T hT
  exact ⟨k,hk,hne,he⟩

/-- Assigned roles contribute their literal word edges once, or zero if absent. -/
theorem sizeTwoAssignedRole_count (o : Option (Fin 4)) (e : Sym2 V) :
    (((B.sizeTwoAssignedRole A i words added h o).map (fun T => T.walk.edges)).getD []).count e =
      (o.map (fun k => ((wordEdges (words k)).map
        (Sym2.map (B.completedLabel A))).count e)).getD 0 := by
  cases o with
  | none => rfl
  | some k => exact congrArg (List.count e) (B.sizeTwoOptionalRole_edges A i words added h k)

/-- This consumer orients the finite connector to the actual unordered hub
attachments, leaving all old endpoint-role assignments unchanged. -/
theorem sizeTwo_passing_record (j : Fin 4) (hj : words j ≠ [])
    (u v : Star.Vertex) (hb : boundary i j = [u,v])
    (P : NonemptyPath B.syndromeStar)
    (hx : B.completedHub ∈ P.walk.support)
    (hs : P.start ≠ B.completedHub) (ht : B.completedHub ≠ P.finish)
    (hpair :
      ((P.takeTo B.completedHub hx hs).walk.reverse.snd.val = B.completedLabel A u ∧
       (P.dropFrom B.completedHub hx ht).walk.snd.val = B.completedLabel A v) ∨
      ((P.takeTo B.completedHub hx hs).walk.reverse.snd.val = B.completedLabel A v ∧
       (P.dropFrom B.completedHub hx ht).walk.snd.val = B.completedLabel A u))
    (left right : Option (Fin 4))
    (hleft : ∀ k ∈ left, ∃ a : Star.Vertex, boundary i k = [a] ∧
      P.start.val = B.completedLabel A a ∧ k ≠ j ∧ owner i k = owner i j)
    (hright : ∀ k ∈ right, ∃ a : Star.Vertex, boundary i k = [a] ∧
      P.finish.val = B.completedLabel A a ∧ k ≠ j ∧ owner i k = owner i j)
    (hdist : ∀ k ∈ left, ∀ l ∈ right, k ≠ l) :
    ∃ N : NonemptyPath G,
      N.start = ((B.sizeTwoAssignedRole A i words added h left).map (·.finish)).getD P.start.val ∧
      N.finish = ((B.sizeTwoAssignedRole A i words added h right).map (·.finish)).getD P.finish.val ∧
      ∀ e : Sym2 V, N.walk.edges.count e +
        ([s(B.label 0,(P.takeTo B.completedHub hx hs).walk.reverse.snd.val),
          s(B.label 0,(P.dropFrom B.completedHub hx ht).walk.snd.val)] : List (Sym2 V)).count e =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e +
        ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e +
        (left.map (fun k => ((wordEdges (words k)).map (Sym2.map (B.completedLabel A))).count e)).getD 0 +
        (right.map (fun k => ((wordEdges (words k)).map (Sym2.map (B.completedLabel A))).count e)).getD 0 := by
  let Q := B.sizeTwoRole A i words added h j hj
  obtain ⟨hQs,hQt,hQsupport⟩ := B.sizeTwoRole_pair A i words added h j hj u v hb
  obtain ⟨M,hM,hne,hMe,hMsupport⟩ := Q.orient_connector
    (P.takeTo B.completedHub hx hs).walk.reverse.snd.val
    (P.dropFrom B.completedHub hx ht).walk.snd.val (by
      simpa only [Q,hQs,hQt] using hpair)
  have hm : ∀ z : B.StarSurvivor, z.val ∈ M.support →
      z.val = (P.takeTo B.completedHub hx hs).walk.reverse.snd.val ∨
      z.val = (P.dropFrom B.completedHub hx ht).walk.snd.val ∨ z.val = B.label 0 := by
    intro z hz
    have hz' : z.val ∈ Q.walk.support := by
      have hf : z.val ∈ M.support.toFinset := List.mem_toFinset.mpr hz
      rw [hMsupport] at hf
      exact List.mem_toFinset.mp hf
    rcases hpair with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · rcases hQsupport z hz' with hz | hz | hz
      · exact Or.inl (hz.trans hu.symm)
      · exact Or.inr (Or.inl (hz.trans hv.symm))
      · exact Or.inr (Or.inr hz)
    · rcases hQsupport z hz' with hz | hz | hz
      · exact Or.inr (Or.inl (hz.trans hu.symm))
      · exact Or.inl (hz.trans hv.symm)
      · exact Or.inr (Or.inr hz)
  let U := B.sizeTwoAssignedRole A i words added h left
  let T := B.sizeTwoAssignedRole A i words added h right
  have tails (o : Option (Fin 4)) (b : V)
      (ho : ∀ k ∈ o, ∃ a : Star.Vertex, boundary i k = [a] ∧
        b = B.completedLabel A a ∧ k ≠ j ∧ owner i k = owner i j) :
      ∀ R ∈ B.sizeTwoAssignedRole A i words added h o,
        b = R.start ∧ (∀ z ∈ R.walk.support, z = R.start ∨ z ∈ B.vertices) ∧
        Disjoint (M.support.toFinset ∩ B.vertices) (R.freshSupport B.vertices) := by
    intro R hR
    obtain ⟨k,hk,hkn,rfl⟩ := B.sizeTwoAssignedRole_mem A i words added h o R hR
    obtain ⟨a,hba,hea,hkj,howner⟩ := ho k hk
    obtain ⟨hRs,hRsupport⟩ := B.sizeTwoRole_single A i words added h k hkn a hba
    refine ⟨hea.trans hRs.symm,?_,?_⟩
    · intro z hz
      exact (hRsupport z hz).imp (fun he => he.trans hRs.symm) id
    · rw [hMsupport]
      simpa only [NonemptyPath.freshSupport,Q] using
        B.sizeTwoRole_same_owner_disjoint A i words added h j k hj hkn hkj.symm howner.symm
  have hUT : ∀ R ∈ U, ∀ S ∈ T,
      Disjoint (R.freshSupport B.vertices) (S.freshSupport B.vertices) := by
    intro R hR S hS
    obtain ⟨k,hk,hkn,rfl⟩ := B.sizeTwoAssignedRole_mem A i words added h left R hR
    obtain ⟨l,hl,hln,rfl⟩ := B.sizeTwoAssignedRole_mem A i words added h right S hS
    obtain ⟨_,_,_,_,hko⟩ := hleft k hk
    obtain ⟨_,_,_,_,hlo⟩ := hright l hl
    exact B.sizeTwoRole_same_owner_disjoint A i words added h k l hkn hln
      (hdist k hk l hl) (hko.trans hlo.symm)
  obtain ⟨N,hNs,hNt,hNe⟩ := B.syndrome_passing_release_optional P hx hs ht M hM hne hm
    U T (tails left P.start.val hleft) (tails right P.finish.val hright) hUT
  refine ⟨N,hNs,hNt,?_⟩
  intro e
  have heM : M.edges.count e = ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e :=
    (hMe e).trans (congrArg (List.count e) (B.sizeTwoRole_edges A i words added h j hj))
  simpa only [heM,U,T,B.sizeTwoAssignedRole_count] using hNe e

end Gallai.WholeBowtie
