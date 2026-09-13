/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoForcedWords
import Gallai.Transport.SizeTwoAvoidingRecord

/-! # Splicing the forced extra tail into its actual carrier

The selected old carrier avoids the released hub. It may contain every other
anchor; freshness, not anchor avoidance, makes the extension simple.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : B.AnchorNumbering) (j : Fin 2)
variable (connector extra tail : List Star.Vertex) (added : List (List Star.Vertex))
variable (h : Forced.AcceptedRecord (B.completedStarState A) j connector extra tail added)

/-- The one mandatory endpoint tail of a forced record. -/
noncomputable def sizeTwoForcedExtra : NonemptyPath G :=
  B.sizeTwoForcedWord A j connector extra tail added h extra
    (by simp [Forced.localWords])

/-- The actual extra carrier receives precisely the extra word's edges.
Its other endpoint is preserved and the selected endpoint moves to the tail's
finish. No disjointness from the central carrier is imposed on the new tail. -/
theorem sizeTwo_forced_extra_splice (P : NonemptyPath B.syndromeStar)
    (hx : B.completedHub ∉ P.walk.support)
    (ha : P.start.val = B.completedLabel A (Forced.extraAnchor j) ∨
      P.finish.val = B.completedLabel A (Forced.extraAnchor j)) :
    ∃ N : NonemptyPath G,
      ((P.start.val = B.completedLabel A (Forced.extraAnchor j) ∧
        N.start = (B.sizeTwoForcedExtra A j connector extra tail added h).finish ∧
        N.finish = P.finish.val) ∨
       (P.finish.val = B.completedLabel A (Forced.extraAnchor j) ∧
        N.start = P.start.val ∧
        N.finish = (B.sizeTwoForcedExtra A j connector extra tail added h).finish)) ∧
      ∀ e : Sym2 V, N.walk.edges.count e =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e +
        ((wordEdges extra).map (Sym2.map (B.completedLabel A))).count e := by
  let C := B.syndromeAvoidingPath P hx
  let T := B.sizeTwoForcedExtra A j connector extra tail added h
  obtain ⟨hTs,hTf⟩ := B.sizeTwoForcedWord_single A j connector extra tail added h
    extra (by simp [Forced.localWords]) (Forced.extraAnchor j) h.2.1
  change T.start = _ at hTs
  have hf : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices := by
    intro v hv
    exact (hTf v hv).imp (fun he => he.trans hTs.symm) id
  have hd : Disjoint (C.freshSupport B.vertices) (T.freshSupport B.vertices) := by
    rw [show C.freshSupport B.vertices = ∅ from B.syndromeAvoidingPath_fresh_empty P hx]
    exact Finset.disjoint_empty_left _
  have hCe := B.syndromeAvoidingPath_edges P hx
  have hTe := B.sizeTwoForcedWord_edges A j connector extra tail added h extra
    (by simp [Forced.localWords])
  change T.walk.edges = _ at hTe
  change C.walk.edges = _ at hCe
  rcases ha with ha | ha
  · obtain ⟨N,hNs,hNt,hNe⟩ := C.extend_optional_fresh (some T) none B.vertices
      (by
        intro Q hQ
        have he : T = Q := by simpa using hQ
        subst Q
        exact ⟨ha.trans hTs.symm,hf,hd⟩)
      (by simp) (by simp)
    refine ⟨N,Or.inl ⟨ha,hNs,hNt⟩,?_⟩
    intro e
    have he := congrArg (List.count e) hNe
    simp only [Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
      List.count_append,List.count_reverse,List.count_nil] at he
    rw [hCe,hTe] at he
    omega
  · obtain ⟨N,hNs,hNt,hNe⟩ := C.extend_optional_fresh none (some T) B.vertices
      (by simp)
      (by
        intro Q hQ
        have he : T = Q := by simpa using hQ
        subst Q
        exact ⟨ha.trans hTs.symm,hf,hd⟩)
      (by simp)
    refine ⟨N,Or.inr ⟨ha,hNs,hNt⟩,?_⟩
    intro e
    have he := congrArg (List.count e) hNe
    simp only [Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
      List.count_append,List.count_nil] at he
    rw [hCe,hTe] at he
    omega

end Gallai.WholeBowtie
