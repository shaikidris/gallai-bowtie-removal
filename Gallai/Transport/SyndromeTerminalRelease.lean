/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SyndromeStarCarrier

/-! # Release a terminal syndrome spoke before inserting its replacement tail -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- A terminal spoke may be synthetic. Trim it first, including when the
whole old carrier was that spoke, then attach the nonempty local replacement. -/
theorem syndrome_terminal_release (P : NonemptyPath B.syndromeStar)
    (hx : P.finish = B.completedHub) {c : V}
    (M : G.Walk P.walk.reverse.snd.val c) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = P.walk.reverse.snd.val ∨ v.val = B.label 0) :
    ∃ N : NonemptyPath G, N.start = P.start.val ∧ N.finish = c ∧
      ∀ e : Sym2 V, N.walk.edges.count e +
        (if s(B.label 0,P.walk.reverse.snd.val) = e then 1 else 0) =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e + M.edges.count e := by
  let L := P.walk.reverse.tail.reverse
  have hL : L.IsPath := P.isPath.reverse.tail.reverse
  have hfree : B.completedHub ∉ L.support := by
    change B.completedHub ∉ P.walk.reverse.tail.reverse.support
    rw [SimpleGraph.Walk.support_reverse,List.mem_reverse]
    have h := P.reverse.start_notMem_tail_support
    change P.finish ∉ P.walk.reverse.tail.support at h
    intro hv
    exact h ((congrArg (fun v => v ∈ P.walk.reverse.tail.support) hx).mpr hv)
  let N := B.retainedTerminalCarrier B.syndromeStar B.syndromeStar_le_completedStar
    L M hL hM hne hfree hm
  refine ⟨N,rfl,rfl,?_⟩
  intro e
  have hnew := congrArg (List.count e)
    (B.retainedTerminalCarrier_edges B.syndromeStar B.syndromeStar_le_completedStar
      L M hL hM hne hfree hm)
  have hold := congrArg (fun es : List (Sym2 B.StarSurvivor) =>
    (es.map (Sym2.map Subtype.val)).count e) P.reverse_tail_edges_append_spoke
  simp only [List.map_append,List.map_cons,List.map_nil,Sym2.map_mk,
    List.count_append,List.count_cons,List.count_nil,hx] at hold
  simp only [List.count_append] at hnew
  change N.walk.edges.count e = _ at hnew
  have hsp : (if (s(B.label 0,P.walk.reverse.snd.val) == e) = true then 1 else 0 : ℕ) =
      (if s(B.label 0,P.walk.reverse.snd.val) = e then 1 else 0) := by simp
  change (L.edges.map (Sym2.map Subtype.val)).count e +
    (0 + if (s(B.label 0,P.walk.reverse.snd.val) == e) = true then 1 else 0) = _ at hold
  rw [hsp] at hold
  omega

end Gallai.WholeBowtie
