/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRichWords
import Gallai.Transport.SyndromeTerminalTailOption

/-! # Optional rich roles and the unmerged terminal carrier

This consumes the rich certificate's optional single-attachment role, including
an empty word, and returns an optional original-graph carrier. Edge and outside
endpoint accounting are on that same carrier.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : B.AnchorNumbering) (i : Fin 4)
variable (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
variable (h : Rich.AcceptedRecord (B.completedStarState A) i words added)

/-- Empty local tails are absent, not zero-edge paths. -/
noncomputable def sizeTwoRichOptionalRole (j : Fin 4) : Option (NonemptyPath G) :=
  if hj : words j = [] then none else some (B.sizeTwoRichRole A i words added h j hj)

/-- Every present tail is the exact realized certificate word. -/
theorem sizeTwoRichOptionalRole_mem (j : Fin 4) (T : NonemptyPath G)
    (hT : T ∈ B.sizeTwoRichOptionalRole A i words added h j) :
    ∃ hj : words j ≠ [], T = B.sizeTwoRichRole A i words added h j hj := by
  unfold sizeTwoRichOptionalRole at hT
  split at hT
  · simp at hT
  · rename_i hj
    exact ⟨hj,(show _ = T from by simpa only [Option.mem_some_iff] using hT).symm⟩

/-- Uniform edge-list accounting for absent or present local tails. -/
theorem sizeTwoRichOptionalRole_edges (j : Fin 4) :
    ((B.sizeTwoRichOptionalRole A i words added h j).map (fun T => T.walk.edges)).getD [] =
      (wordEdges (words j)).map (Sym2.map (B.completedLabel A)) := by
  unfold sizeTwoRichOptionalRole
  split
  · rename_i hj
    simp [hj,wordEdges]
  · simpa only [Option.map_some,Option.getD_some] using
      B.sizeTwoRichRole_edges A i words added h j ‹words j ≠ []›

/-- Realized rich roles cannot end at a vertex outside all local labels. -/
theorem sizeTwoRichRole_finish_ne (j : Fin 4) (hj : words j ≠ [])
    (v : V) (hv : ∀ t, B.completedLabel A t ≠ v) :
    (B.sizeTwoRichRole A i words added h j hj).finish ≠ v := by
  intro he
  have hm := (B.sizeTwoRichRole A i words added h j hj).walk.end_mem_support
  rw [B.sizeTwoRichRole_support,he] at hm
  obtain ⟨t,_,ht⟩ := List.mem_map.mp hm
  exact hv t ht

include h in
/-- The unmerged terminal hub carrier can consume its optional finite tail.
The output may disappear, but then no outside endpoint is lost. -/
theorem sizeTwo_rich_optional_terminal (j : Fin 4) (u : Star.Vertex)
    (hb : Rich.boundary i j = [u]) (P : NonemptyPath B.syndromeStar)
    (hx : P.finish = B.completedHub)
    (hu : P.walk.reverse.snd.val = B.completedLabel A u) :
    ∃ O : Option (NonemptyPath G),
      (∀ e : Sym2 V, ((O.map (fun N => N.walk.edges)).getD []).count e +
        (if s(B.label 0,P.walk.reverse.snd.val) = e then 1 else 0) =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e +
        ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e) ∧
      ∀ v : V, (∀ t, B.completedLabel A t ≠ v) →
        (O.map (fun N => (if N.start = v then 1 else 0) +
          (if N.finish = v then 1 else 0 : ℕ))).getD 0 =
        (if P.start.val = v then 1 else 0) + (if P.finish.val = v then 1 else 0) := by
  let T := B.sizeTwoRichOptionalRole A i words added h j
  have hT : ∀ Q ∈ T, Q.start = P.walk.reverse.snd.val ∧
      ∀ v : B.StarSurvivor, v.val ∈ Q.walk.support →
        v.val = P.walk.reverse.snd.val ∨ v.val = B.label 0 := by
    intro Q hQ
    obtain ⟨hj,rfl⟩ := B.sizeTwoRichOptionalRole_mem A i words added h j Q hQ
    obtain ⟨hs,hsp⟩ := B.sizeTwoRichRole_single A i words added h j hj u hb
    refine ⟨hs.trans hu.symm,?_⟩
    intro v hv
    rcases hsp v.val hv with he | hf
    · exact Or.inl (he.trans hu.symm)
    · exact Or.inr (B.survivor_mem_vertices v hf)
  obtain ⟨O,he,hend⟩ := B.syndrome_terminal_tail_option P hx T hT
  refine ⟨O,?_,?_⟩
  · intro e
    have hTe := B.sizeTwoRichOptionalRole_edges A i words added h j
    change ((T.map (fun Q => Q.walk.edges)).getD []) = _ at hTe
    simpa only [hTe] using he e
  · intro v hv
    apply hend v
    · exact Ne.symm (hv .x)
    · exact fun he => hv u (hu.symm.trans he.symm)
    · intro Q hQ
      obtain ⟨hj,rfl⟩ := B.sizeTwoRichOptionalRole_mem A i words added h j Q hQ
      exact B.sizeTwoRichRole_finish_ne A i words added h j hj v hv

end Gallai.WholeBowtie
