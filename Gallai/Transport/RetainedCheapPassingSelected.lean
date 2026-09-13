/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedCheapPassingFamily
import Gallai.Operations.Orient

/-! # Choice-free passing/remote family construction -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Positive remote supply suffices: select its carrier, orient it toward r,
and replace the unique through carrier without changing the family size. -/
theorem retainedCheapPassingSelected (H : SimpleGraph B.StarSurvivor)
    [DecidableRel H.Adj]
    (hOriginal : ∀ u v : B.StarSurvivor, H.Adj u v → G.Adj u.val v.val)
    (p q r : B.StarSurvivor) (hr : ¬ H.Reachable B.completedHub r)
    (hneighbors : ∀ v, H.Adj B.completedHub v → v = p ∨ v = q)
    (D : Decomposition H) (hd : H.degree B.completedHub = 2)
    (hz : D.endpointCount B.completedHub = 0) (hpos : 0 < D.endpointCount r)
    (M : G.Walk p.val q.val) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v = p ∨ v = q ∨ v = B.completedHub ∨ v = r)
    (T : NonemptyPath G) (hT : T.start = r.val)
    (hf : ∀ v : B.StarSurvivor, v.val ∈ T.walk.support →
      v = r ∨ H.Reachable B.completedHub v) :
    ∃ F : Fin D.size → NonemptyPath G,
      (∀ e : Sym2 V, (∑ k, (F k).walk.edges.count e) +
          ([s(B.label 0,p.val),s(B.label 0,q.val)] : List (Sym2 V)).count e =
        (∑ k, ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e) +
          M.edges.count e + T.walk.edges.count e) ∧
      ∀ w : B.StarSurvivor, w ≠ r → D.endpointCount w ≤
        ∑ k, ((if (F k).start = w.val then 1 else 0) +
          (if (F k).finish = w.val then 1 else 0) : ℕ) := by
  classical
  obtain ⟨i,j,_,hx,hs,ht,hj⟩ := B.retainedCheap_passing_selection H r hr D hd hz hpos
  let D' := D.orientToward r
  have hstart : (D.path i).start ≠ r := by
    intro h
    exact B.retained_hub_walk_avoids_remote H r hr (D.path i).walk hx
      (h ▸ (D.path i).walk.start_mem_support)
  have hi : D'.path i = D.path i := (D.path i).toward_of_start_ne r hstart
  obtain ⟨F,hcount,hEnd⟩ := B.retainedCheapPassingFamily H hOriginal p q r hr
    hneighbors D' i j (hi.symm ▸ hx) (hi.symm ▸ hs) (hi.symm ▸ ht)
    (D.orientToward_terminal r j hj) M hM hne hm T hT hf
  refine ⟨F, ?_, ?_⟩
  · intro e
    have hmaps : (∑ k, ((D'.path k).walk.edges.map (Sym2.map Subtype.val)).count e) =
        ∑ k, ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e := by
      apply Finset.sum_congr rfl
      intro k _
      change (((D.path k).toward r).walk.edges.map (Sym2.map Subtype.val)).count e = _
      by_cases hs : (D.path k).start = r
      · rw [(D.path k).toward_of_start_eq r hs, NonemptyPath.reverse_edges,
          List.map_reverse, List.count_reverse]
      · rw [(D.path k).toward_of_start_ne r hs]
    exact (hcount e).trans (congrArg (fun n => n + M.edges.count e + T.walk.edges.count e) hmaps)
  · intro w hw
    have h := hEnd w hw
    rw [D.orientToward_endpointCount r w] at h
    exact h

end Gallai.WholeBowtie
