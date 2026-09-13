/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRichArmMerge

/-! # The joined carrier in the one-credit terminal reconstruction

Trim the terminal hub spoke and join the remaining prefix to a remote reserve
path. The two carriers become one, preserving their other endpoints. A one-edge
terminal carrier is allowed: its trimmed prefix is a nil walk.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Exact terminal merging, including the released-spoke balance. -/
theorem sizeTwo_rich_terminal_merge (w : B.StarSurvivor)
    (hsep : ¬ B.syndromeStar.Reachable B.completedHub w)
    (P Q : NonemptyPath B.syndromeStar)
    (hP : P.finish = B.completedHub) (hQ : Q.finish = w)
    (M : G.Walk P.walk.reverse.snd.val Q.finish.val)
    (hM : M.IsPath) (hne : ¬ M.Nil)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = P.walk.reverse.snd.val ∨ v.val = Q.finish.val ∨ v.val = B.label 0) :
    ∃ N : NonemptyPath G, N.start = P.start.val ∧ N.finish = Q.start.val ∧
      ∀ e : Sym2 V, N.walk.edges.count e +
        ([s(B.label 0, P.walk.reverse.snd.val)] : List (Sym2 V)).count e =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e +
        (Q.walk.edges.map (Sym2.map Subtype.val)).count e + M.edges.count e := by
  have hxL : B.completedHub ∉ P.walk.reverse.tail.reverse.support := by
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse, ← hP]
    exact P.reverse.start_notMem_tail_support
  have hcomp : B.syndromeStar.Reachable B.completedHub P.start :=
    hP ▸ P.walk.reachable.symm
  obtain ⟨N, hs, ht, he⟩ := B.sizeTwo_rich_arm_merge w hsep
    P.walk.reverse.tail.reverse P.isPath.reverse.tail.reverse hxL hcomp Q hQ M hM hne hm
  refine ⟨N, hs, ht, ?_⟩
  intro e
  have hnew := congrArg (fun es : List (Sym2 V) => es.count e) he
  have hold := congrArg (fun es : List (Sym2 B.StarSurvivor) =>
    (es.map (Sym2.map Subtype.val)).count e) P.reverse_tail_edges_append_spoke
  simp only [SimpleGraph.Walk.edges_reverse, List.map_reverse, List.count_reverse,
    List.count_append] at hnew
  simp only [List.map_append, List.map_cons, List.map_nil, Sym2.map_mk,
    List.count_append, hP] at hold
  simp only [SimpleGraph.Walk.edges_reverse, List.map_reverse, List.count_reverse] at hold
  change (P.walk.reverse.tail.edges.map (Sym2.map Subtype.val)).count e +
    ([s(B.label 0, P.walk.reverse.snd.val)] : List (Sym2 V)).count e =
    (P.walk.edges.map (Sym2.map Subtype.val)).count e at hold
  omega

end Gallai.WholeBowtie
