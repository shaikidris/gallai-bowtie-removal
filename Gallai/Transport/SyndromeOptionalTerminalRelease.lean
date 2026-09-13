/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SyndromeTerminalRelease

/-! # A terminal spoke can be released without a replacement tail

The one-credit rich terminal records permit an empty tail at the other hub
carrier. Its trimmed prefix can itself be nil. Such a carrier disappears;
it is not counted as a nonempty path. Endpoint counts away from the hub and
the attachment are preserved on the same optional path as the edge identity.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Optional terminal release covers exactly the prefix edges and preserves
every endpoint outside the released edge, including the single-edge case. -/
theorem syndrome_terminal_release_empty (P : NonemptyPath B.syndromeStar)
    (hx : P.finish = B.completedHub) :
    ∃ O : Option (NonemptyPath G),
      ((O.map (fun N => N.walk.edges)).getD [] ++
        [s(B.label 0,P.walk.reverse.snd.val)]) =
          P.walk.edges.map (Sym2.map Subtype.val) ∧
      ∀ v : V, v ≠ B.label 0 → v ≠ P.walk.reverse.snd.val →
        (O.map (fun N => (if N.start = v then 1 else 0) +
          (if N.finish = v then 1 else 0 : ℕ))).getD 0 =
        (if P.start.val = v then 1 else 0) + (if P.finish.val = v then 1 else 0) := by
  classical
  let L := P.walk.reverse.tail.reverse
  have hL : L.IsPath := P.isPath.reverse.tail.reverse
  have hfree : B.completedHub ∉ L.support := by
    change B.completedHub ∉ P.walk.reverse.tail.reverse.support
    rw [SimpleGraph.Walk.support_reverse,List.mem_reverse,← hx]
    exact P.reverse.start_notMem_tail_support
  have hold := congrArg (List.map (Sym2.map (Subtype.val : B.StarSurvivor → V)))
    P.reverse_tail_edges_append_spoke
  simp only [List.map_append,List.map_cons,List.map_nil,Sym2.map_mk,hx] at hold
  change L.edges.map (Sym2.map Subtype.val) ++
    [s(B.label 0,P.walk.reverse.snd.val)] = _ at hold
  by_cases hn : L.Nil
  · refine ⟨none,?_,?_⟩
    · simpa only [SimpleGraph.Walk.edges_eq_nil.mpr hn,List.map_nil,
        List.nil_append,Option.map_none,Option.getD_none] using hold
    · intro v hvx hvq
      have hstart : P.start.val ≠ v := by
        intro he
        exact hvq (he.symm.trans (congrArg Subtype.val hn.eq))
      have hfinish : P.finish.val ≠ v := by
        rw [hx]
        exact Ne.symm hvx
      simp [hstart,hfinish]
  · let T : NonemptyPath B.syndromeStar := ⟨P.start,P.walk.reverse.snd,L,hL,hn⟩
    let N := B.syndromeAvoidingPath T hfree
    refine ⟨some N,?_,?_⟩
    · change N.walk.edges ++ _ = _
      rw [show N.walk.edges = L.edges.map (Sym2.map Subtype.val) from
        B.syndromeAvoidingPath_edges T hfree]
      exact hold
    · intro v hvx hvq
      have hfinish : P.finish.val ≠ v := by
        rw [hx]
        exact Ne.symm hvx
      change (if P.start.val = v then 1 else 0) +
        (if P.walk.reverse.snd.val = v then 1 else 0 : ℕ) = _
      simp only [if_neg (Ne.symm hvq),if_neg hfinish]

end Gallai.WholeBowtie
