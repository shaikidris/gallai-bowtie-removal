/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRichOptionalTerminal
import Gallai.Transport.SizeTwoAvoidingRecord

/-! # Optional rich tails on actual remote reserve carriers -/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Extend a hub-free reserve carrier with its accepted optional tail. The
same actual path has exact edge counts and preserves all outside endpoints. -/
theorem sizeTwo_rich_reserve_tail (A : B.AnchorNumbering) (i : Fin 4)
    (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
    (h : Rich.AcceptedRecord (B.completedStarState A) i words added)
    (j : Fin 4) (u : Star.Vertex) (hb : Rich.boundary i j = [u])
    (P : NonemptyPath B.syndromeStar) (hp : B.completedHub ∉ P.walk.support)
    (hw : P.finish.val = B.completedLabel A u) :
    ∃ N : NonemptyPath G,
      (∀ e : Sym2 V, N.walk.edges.count e =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e +
        ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e) ∧
      ∀ v : V, (∀ t, B.completedLabel A t ≠ v) →
        ((if N.start = v then 1 else 0) + (if N.finish = v then 1 else 0 : ℕ)) =
        (if P.start.val = v then 1 else 0) + (if P.finish.val = v then 1 else 0) := by
  let C := B.syndromeAvoidingPath P hp
  let T := B.sizeTwoRichOptionalRole A i words added h j
  have hR : ∀ Q ∈ T, C.finish = Q.start ∧
      (∀ v ∈ Q.walk.support, v = Q.start ∨ v ∈ B.vertices) ∧
      Disjoint (C.freshSupport B.vertices) (Q.freshSupport B.vertices) := by
    intro Q hQ
    obtain ⟨hj,rfl⟩ := B.sizeTwoRichOptionalRole_mem A i words added h j Q hQ
    obtain ⟨hQs,hQv⟩ := B.sizeTwoRichRole_single A i words added h j hj u hb
    refine ⟨hw.trans hQs.symm,?_,?_⟩
    · intro v hv
      simpa only [hQs] using hQv v hv
    · rw [show C.freshSupport B.vertices = ∅ from B.syndromeAvoidingPath_fresh_empty P hp]
      exact Finset.disjoint_empty_left _
  obtain ⟨N,hs,ht,he⟩ := C.extend_optional_fresh none T B.vertices (by simp) hR (by simp)
  refine ⟨N,?_,?_⟩
  · intro e
    have hE := congrArg (List.count e) he
    have hC := B.syndromeAvoidingPath_edges P hp
    have hT := B.sizeTwoRichOptionalRole_edges A i words added h j
    change C.walk.edges = _ at hC
    change (T.map (fun Q => Q.walk.edges)).getD [] = _ at hT
    simpa only [Option.map_none,Option.getD_none,List.nil_append,List.count_append,hC,hT] using hE
  · intro v hv
    have hCv : C.finish ≠ v := fun he => hv u (hw.symm.trans he)
    have hNv : N.finish ≠ v := by
      rw [ht]
      cases hTval : T with
      | none => simpa only [Option.map_none,Option.getD_none] using hCv
      | some Q =>
        have hQ : Q ∈ T := by rw [hTval]; simp
        obtain ⟨hj,rfl⟩ := B.sizeTwoRichOptionalRole_mem A i words added h j Q hQ
        simpa only [Option.map_some,Option.getD_some] using
          B.sizeTwoRichRole_finish_ne A i words added h j hj v hv
    have hs' : N.start = P.start.val := hs
    have hpv : P.finish.val ≠ v := hCv
    simp only [hs',if_neg hNv,if_neg hpv]

end Gallai.WholeBowtie
