/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoWords
import Gallai.Transport.TerminalCarrierOptional
import Gallai.Transport.SizeTwoPassingRecord

/-! # A checked ordinary record reconstructs a terminal carrier -/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Consume a nonempty hub role and an optional remote role on the same actual
carrier. Freshness is derived from record acceptance, not assumed of G. -/
theorem sizeTwo_terminal_record (A : B.AnchorNumbering) (i : Fin 13)
    (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
    (h : OrdinaryAccepted (B.completedStarState A) i words added)
    (j k : Fin 4) (hj : words j ≠ []) (hjk : j ≠ k)
    (ho : owner i j = owner i k) (u w : Star.Vertex)
    (hbu : boundary i j = [u]) (hbw : boundary i k = [w])
    (P : NonemptyPath B.syndromeStar) (hx : P.finish = B.completedHub)
    (hu : P.walk.reverse.snd.val = B.completedLabel A u)
    (hw : P.start.val = B.completedLabel A w) :
    ∃ N : NonemptyPath G,
      N.start = ((B.sizeTwoOptionalRole A i words added h k).map (·.finish)).getD
        P.start.val ∧
      N.finish = (B.sizeTwoRole A i words added h j hj).finish ∧
      ∀ e : Sym2 V, N.walk.edges.count e +
        (if s(B.label 0,P.walk.reverse.snd.val) = e then 1 else 0) =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e +
        ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e +
        ((wordEdges (words k)).map (Sym2.map (B.completedLabel A))).count e := by
  let Q := B.sizeTwoRole A i words added h j hj
  obtain ⟨hQs,hQsupport⟩ := B.sizeTwoRole_single A i words added h j hj u hbu
  have ha : Q.start = P.walk.reverse.snd.val := hQs.trans hu.symm
  let M := Q.walk.copy ha rfl
  have hM : M.IsPath := (SimpleGraph.Walk.isPath_copy _ _ _).mpr Q.isPath
  have hne : ¬ M.Nil := by simpa only [M,SimpleGraph.Walk.nil_copy] using Q.nonempty
  have hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = P.walk.reverse.snd.val ∨ v.val = B.label 0 := by
    intro v hv
    rw [SimpleGraph.Walk.support_copy] at hv
    rcases hQsupport v.val hv with hv | hv
    · exact Or.inl (hv.trans hu.symm)
    · exact Or.inr (B.survivor_mem_vertices v hv)
  let U := B.sizeTwoOptionalRole A i words added h k
  have hU : ∀ T ∈ U, P.start.val = T.start ∧
      (∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices) ∧
      Disjoint (M.support.toFinset ∩ B.vertices) (T.freshSupport B.vertices) := by
    intro T ht
    obtain ⟨hk,rfl⟩ := B.sizeTwoOptionalRole_mem A i words added h k T ht
    obtain ⟨hTs,hTsupport⟩ := B.sizeTwoRole_single A i words added h k hk w hbw
    refine ⟨hw.trans hTs.symm,?_,?_⟩
    · intro v hv
      exact (hTsupport v hv).imp (fun hv => hv.trans hTs.symm) id
    · simpa only [M,SimpleGraph.Walk.support_copy,NonemptyPath.freshSupport,Q] using
        B.sizeTwoRole_same_owner_disjoint A i words added h j k hj hk hjk ho
  obtain ⟨N,hNs,hNt,hNe⟩ := B.syndrome_terminal_release_optional P hx M hM hne hm U hU
  refine ⟨N,hNs,hNt,?_⟩
  intro e
  have hMe : M.edges = (wordEdges (words j)).map (Sym2.map (B.completedLabel A)) :=
    (SimpleGraph.Walk.edges_copy Q.walk ha rfl).trans
      (B.sizeTwoRole_edges A i words added h j hj)
  have hUe : ((U.map (fun T => T.walk.edges.reverse)).getD []).count e =
      ((wordEdges (words k)).map (Sym2.map (B.completedLabel A))).count e := by
    have he := congrArg (List.count e) (B.sizeTwoOptionalRole_edges A i words added h k)
    change ((U.map (fun T => T.walk.edges)).getD []).count e = _ at he
    cases hOpt : U <;> rw [hOpt] at he <;>
      simpa only [Option.map_none,Option.getD_none,Option.map_some,
        Option.getD_some,List.count_reverse] using he
  simpa only [hMe,hUe] using hNe e

/-- An absent remote assignment is handled in the same terminal contract as
an assigned nonempty or empty word. This is the dispatcher-facing version. -/
theorem sizeTwo_terminal_assigned (A : B.AnchorNumbering) (i : Fin 13)
    (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
    (h : OrdinaryAccepted (B.completedStarState A) i words added)
    (j : Fin 4) (hj : words j ≠ []) (u : Star.Vertex) (hbu : boundary i j = [u])
    (P : NonemptyPath B.syndromeStar) (hx : P.finish = B.completedHub)
    (hu : P.walk.reverse.snd.val = B.completedLabel A u)
    (left : Option (Fin 4))
    (hleft : ∀ k ∈ left, ∃ symbol : Star.Vertex, boundary i k = [symbol] ∧
      P.start.val = B.completedLabel A symbol ∧ k ≠ j ∧ owner i k = owner i j) :
    ∃ N : NonemptyPath G,
      N.start = ((B.sizeTwoAssignedRole A i words added h left).map (·.finish)).getD P.start.val ∧
      N.finish = (B.sizeTwoRole A i words added h j hj).finish ∧
      ∀ e : Sym2 V, N.walk.edges.count e +
        (if s(B.label 0,P.walk.reverse.snd.val) = e then 1 else 0) =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e +
        ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e +
        (left.map (fun k => ((wordEdges (words k)).map
          (Sym2.map (B.completedLabel A))).count e)).getD 0 := by
  let Q := B.sizeTwoRole A i words added h j hj
  obtain ⟨hQs,hQsupport⟩ := B.sizeTwoRole_single A i words added h j hj u hbu
  have ha : Q.start = P.walk.reverse.snd.val := hQs.trans hu.symm
  let M := Q.walk.copy ha rfl
  have hM : M.IsPath := (SimpleGraph.Walk.isPath_copy _ _ _).mpr Q.isPath
  have hne : ¬ M.Nil := by simpa only [M,SimpleGraph.Walk.nil_copy] using Q.nonempty
  have hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = P.walk.reverse.snd.val ∨ v.val = B.label 0 := by
    intro v hv
    rw [SimpleGraph.Walk.support_copy] at hv
    rcases hQsupport v.val hv with hv | hv
    · exact Or.inl (hv.trans hu.symm)
    · exact Or.inr (B.survivor_mem_vertices v hv)
  let U := B.sizeTwoAssignedRole A i words added h left
  have hU : ∀ T ∈ U, P.start.val = T.start ∧
      (∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices) ∧
      Disjoint (M.support.toFinset ∩ B.vertices) (T.freshSupport B.vertices) := by
    intro T ht
    obtain ⟨k,hk,hkn,rfl⟩ := B.sizeTwoAssignedRole_mem A i words added h left T ht
    obtain ⟨symbol,hb,he,hkj,ho⟩ := hleft k hk
    obtain ⟨hTs,hTv⟩ := B.sizeTwoRole_single A i words added h k hkn symbol hb
    refine ⟨he.trans hTs.symm,?_,?_⟩
    · intro v hv
      exact (hTv v hv).imp (fun hv => hv.trans hTs.symm) id
    · simpa only [M,SimpleGraph.Walk.support_copy,NonemptyPath.freshSupport,Q] using
        B.sizeTwoRole_same_owner_disjoint A i words added h j k hj hkn hkj.symm ho.symm
  obtain ⟨N,hNs,hNt,hNe⟩ := B.syndrome_terminal_release_optional P hx M hM hne hm U hU
  refine ⟨N,hNs,hNt,?_⟩
  intro e
  have hMe : M.edges = (wordEdges (words j)).map (Sym2.map (B.completedLabel A)) :=
    (SimpleGraph.Walk.edges_copy Q.walk ha rfl).trans
    (B.sizeTwoRole_edges A i words added h j hj)
  have hrev : ((U.map (fun T => T.walk.edges.reverse)).getD []).count e =
      ((U.map (fun T => T.walk.edges)).getD []).count e := by
    cases U <;> simp only [Option.map_none,Option.map_some,Option.getD_none,
      Option.getD_some,List.count_reverse]
  simpa only [hMe,hrev,U,B.sizeTwoAssignedRole_count] using hNe e

end Gallai.WholeBowtie
