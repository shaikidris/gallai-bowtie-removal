/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.FreshCarrierTail

/-! # Both remote tails may belong to the reconstructed hub carrier -/
namespace Gallai.NonemptyPath
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem reverse_freshSupport (P : NonemptyPath G) (F : Finset V) :
    P.reverse.freshSupport F = P.freshSupport F := by
  simp only [freshSupport,reverse,SimpleGraph.Walk.support_reverse,List.toFinset_reverse]

/-- Attach outward tails at both ends of one path. Three pairwise disjoint
core footprints suffice; the resulting path has exact edges and footprint. -/
theorem extend_both_fresh (P L R : NonemptyPath G) (F : Finset V)
    (hl : P.start = L.start) (hr : P.finish = R.start)
    (hL : ∀ v ∈ L.walk.support, v = L.start ∨ v ∈ F)
    (hR : ∀ v ∈ R.walk.support, v = R.start ∨ v ∈ F)
    (hPL : Disjoint (P.freshSupport F) (L.freshSupport F))
    (hPR : Disjoint (P.freshSupport F) (R.freshSupport F))
    (hLR : Disjoint (L.freshSupport F) (R.freshSupport F)) :
    ∃ N : NonemptyPath G, N.start = L.finish ∧ N.finish = R.finish ∧
      N.walk.edges = (L.walk.edges.reverse ++ P.walk.edges) ++ R.walk.edges ∧
      N.freshSupport F = (P.freshSupport F ∪ L.freshSupport F) ∪ R.freshSupport F := by
  have hrev : Disjoint (P.reverse.freshSupport F) (L.freshSupport F) := by
    rwa [reverse_freshSupport]
  let Q := (P.reverse.appendFresh L F hl hL hrev).reverse
  have hQ : Q.freshSupport F = P.freshSupport F ∪ L.freshSupport F :=
    (reverse_freshSupport _ F).trans
      ((P.reverse.appendFresh_support L F hl hL hrev).trans
        (congrArg (fun s => s ∪ L.freshSupport F) (reverse_freshSupport P F)))
  have hQR : Disjoint (Q.freshSupport F) (R.freshSupport F) := by
    rw [hQ]
    exact Finset.disjoint_union_left.mpr ⟨hPR,hLR⟩
  let N := Q.appendFresh R F hr hR hQR
  refine ⟨N,rfl,rfl,?_,?_⟩
  · have hQE : Q.walk.edges = L.walk.edges.reverse ++ P.walk.edges := by
      change (P.reverse.appendFresh L F hl hL hrev).reverse.walk.edges = _
      rw [reverse_edges]
      rw [P.reverse.appendFresh_edges L F hl hL hrev,reverse_edges]
      simp only [List.reverse_append,List.reverse_reverse]
    exact (Q.appendFresh_edges R F hr hR hQR).trans
      (congrArg (fun es => es ++ R.walk.edges) hQE)
  · exact (Q.appendFresh_support R F hr hR hQR).trans
      (congrArg (fun s => s ∪ R.freshSupport F) hQ)

end Gallai.NonemptyPath
