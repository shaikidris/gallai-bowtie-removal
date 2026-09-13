/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.PunctureTail
import Gallai.Operations.FamilyReplace
import Gallai.Operations.Orient

/-! # Simultaneous component-safe terminal extensions

The repair-free puncture supplies the old carriers. Component separation
allows a tail to visit anchors outside its own carrier's component.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Extend injectively selected carriers toward possibly repeated attachment
vertices. Only endpoint reserves at those attachment vertices can be spent. -/
theorem punctureSeparatedFamily (D : Decomposition B.puncture) {k : ℕ} (j : Fin k ↪ Fin D.size)
    (a : Fin k → {v : V // v ∉ B.vertices})
    (hj : ∀ l, (D.path (j l)).start = a l ∨ (D.path (j l)).finish = a l)
    (T : Fin k → NonemptyPath G) (ht : ∀ l, (T l).start = (a l).val)
    (hf : ∀ l v, v.val ∈ (T l).walk.support → v = a l ∨ ¬ B.puncture.Reachable (a l) v) :
    ∃ F : Fin D.size → NonemptyPath G,
      (∀ e, (∑ i, (F i).walk.edges.count e) =
        (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) +
          ∑ l, (T l).walk.edges.count e) ∧
      ∀ w : {v : V // v ∉ B.vertices}, (∀ l, w ≠ a l) → D.endpointCount w ≤
        ∑ i, ((if (F i).start = w.val then 1 else 0) +
          (if (F i).finish = w.val then 1 else 0) : ℕ) := by
  classical
  let P (l) := (D.path (j l)).toward (a l)
  have hfinish (l) : (P l).finish = a l := (D.path (j l)).toward_finish (a l) (hj l)
  have hex (l) : ∃ R : NonemptyPath G, R.start = (P l).start.val ∧
      R.finish = (T l).finish ∧
      R.walk.edges = (P l).walk.edges.map (Sym2.map Subtype.val) ++ (T l).walk.edges := by
    have hjoin : (P l).finish.val = (T l).start :=
      (congrArg Subtype.val (hfinish l)).trans (ht l).symm
    have hsafe : ∀ v : {v : V // v ∉ B.vertices},
        v.val ∈ (T l).walk.support →
          v = (P l).finish ∨ ¬ B.puncture.Reachable (P l).finish v := by
      intro v hv
      simpa only [hfinish] using hf l v hv
    exact ⟨B.punctureSeparatedTail (P l) (T l) hjoin hsafe, rfl, rfl,
      B.punctureSeparatedTail_edges (P l) (T l) hjoin hsafe⟩
  choose R hRs hRt hRe using hex
  let φ : B.puncture →g G := ⟨Subtype.val, fun h => h⟩
  let old (i) := (D.path i).map φ Subtype.val_injective
  refine ⟨replaceFamily old j R, ?_, ?_⟩
  · intro e
    have hR (l) : (R l).walk.edges.count e = (old (j l)).walk.edges.count e +
        (T l).walk.edges.count e := by
      rw [hRe,List.count_append]
      have hold : (old (j l)).walk.edges =
          (D.path (j l)).walk.edges.map (Sym2.map Subtype.val) :=
        SimpleGraph.Walk.edges_map φ (D.path (j l)).walk
      rw [hold]
      congr 1
      dsimp only [P]
      by_cases hs : (D.path (j l)).start = a l
      · rw [(D.path (j l)).toward_of_start_eq (a l) hs,
          NonemptyPath.reverse_edges,List.map_reverse,List.count_reverse]
      · rw [(D.path (j l)).toward_of_start_ne (a l) hs]
    have hsum := sum_replaceFamily old j R (fun Q => Q.walk.edges.count e)
      (fun l => (T l).walk.edges.count e) hR
    have hold : (∑ i, (old i).walk.edges.count e) =
        ∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun es : List (Sym2 V) => es.count e)
        (SimpleGraph.Walk.edges_map φ (D.path i).walk)
    exact hsum.trans (congrArg (fun n => n + ∑ l, (T l).walk.edges.count e) hold)
  · intro w hw
    let measure (Q : NonemptyPath G) :=
      (if Q.start = w.val then 1 else 0) + (if Q.finish = w.val then 1 else 0 : ℕ)
    let delta (l : Fin k) : ℕ := if (T l).finish = w.val then 1 else 0
    have hR (l) : measure (R l) = measure (old (j l)) + delta l := by
      have ho := (D.path (j l)).toward_endpoint_contribution (a l) w
      have ho' : ((if (P l).start = w then 1 else 0) : ℕ) =
          (if (D.path (j l)).start = w then 1 else 0) +
          (if (D.path (j l)).finish = w then 1 else 0) := by
        change ((if (P l).start = w then 1 else 0) +
          (if (P l).finish = w then 1 else 0) : ℕ) = _ at ho
        simpa only [hfinish,if_neg (Ne.symm (hw l)),Nat.add_zero] using ho
      change ((if (R l).start = w.val then 1 else 0) +
        (if (R l).finish = w.val then 1 else 0) : ℕ) = _
      rw [hRs,hRt]
      change _ = ((if (D.path (j l)).start.val = w.val then 1 else 0) +
        (if (D.path (j l)).finish.val = w.val then 1 else 0)) + delta l
      simpa only [Subtype.val_inj,delta] using congrArg (fun n => n + delta l) ho'
    have hsum := sum_replaceFamily old j R measure delta hR
    have hold : (∑ i, measure (old i)) = D.endpointCount w := by
      unfold Decomposition.endpointCount
      apply Finset.sum_congr rfl
      intro i _
      change ((if (D.path i).start.val = w.val then 1 else 0) +
        (if (D.path i).finish.val = w.val then 1 else 0) : ℕ) = _
      simp only [Subtype.val_inj]
    change D.endpointCount w ≤ ∑ i, measure (replaceFamily old j R i)
    rw [hsum,hold]
    exact Nat.le_add_right _ _

end Gallai.WholeBowtie
