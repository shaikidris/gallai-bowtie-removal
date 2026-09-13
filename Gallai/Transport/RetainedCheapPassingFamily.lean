/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedCheapThroughNormalized
import Gallai.Transport.RetainedCheapSelection

/-! # Simultaneous through and remote carrier replacement -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Replace the through run and append the remote tail on distinct indices.
The family size is unchanged and only the old endpoint at r may be spent. -/
theorem retainedCheapPassingFamily (H : SimpleGraph B.StarSurvivor)
    [DecidableRel H.Adj]
    (hOriginal : ∀ u v : B.StarSurvivor, H.Adj u v → G.Adj u.val v.val)
    (p q r : B.StarSurvivor) (hr : ¬ H.Reachable B.completedHub r)
    (hneighbors : ∀ v, H.Adj B.completedHub v → v = p ∨ v = q)
    (D : Decomposition H) (i j : Fin D.size)
    (hx : B.completedHub ∈ (D.path i).walk.support)
    (hs : (D.path i).start ≠ B.completedHub) (ht : B.completedHub ≠ (D.path i).finish)
    (hj : (D.path j).finish = r)
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
  have hij := B.retained_remote_index_ne H r hr D i j hx (Or.inr hj)
  obtain ⟨N,hNs,hNt,hN⟩ := B.retainedCheapThrough_normalized H hOriginal p q r hr
    hneighbors (D.path i) hx hs ht M hM hne hm
  obtain ⟨Q,hQs,hQt,hQ⟩ := B.retainedCheap_remote_append H hOriginal r hr
    (D.path j) hj T hT hf
  let φ : H →g G := ⟨Subtype.val, fun {u v} h => hOriginal u v h⟩
  let old (k : Fin D.size) := (D.path k).map φ Subtype.val_injective
  let F (k : Fin D.size) := if k = i then N else if k = j then Q else old k
  have hFi : F i = N := if_pos rfl
  have hFj : F j = Q := by simp only [F, if_neg hij.symm, eq_self, ite_true]
  have hFk (k : Fin D.size) (hi : k ≠ i) (hj : k ≠ j) : F k = old k := by
    simp only [F, if_neg hi, if_neg hj]
  have hold (k : Fin D.size) : (old k).walk.edges =
      (D.path k).walk.edges.map (Sym2.map Subtype.val) :=
    SimpleGraph.Walk.edges_map φ (D.path k).walk
  refine ⟨F, ?_, ?_⟩
  · intro e
    let sp := ([s(B.label 0,p.val),s(B.label 0,q.val)] : List (Sym2 V)).count e
    have per (k : Fin D.size) : (F k).walk.edges.count e + (if k = i then sp else 0) =
        ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e +
          (if k = i then M.edges.count e else 0) +
          (if k = j then T.walk.edges.count e else 0) := by
      by_cases hi : k = i
      · subst k
        rw [hFi]
        simpa only [eq_self,ite_true,if_neg hij,Nat.add_zero,sp] using hN e
      · by_cases hj' : k = j
        · subst k
          rw [hFj]
          have he := congrArg (fun es : List (Sym2 V) => es.count e) hQ
          simpa only [if_neg hi,eq_self,ite_true,Nat.add_zero,List.count_append] using he
        · rw [hFk k hi hj',hold]
          simp only [if_neg hi,if_neg hj',Nat.add_zero]
    have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => per k)
    simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,sp] using hsum
  · intro w hw
    unfold Decomposition.endpointCount
    apply Finset.sum_le_sum
    intro k _
    by_cases hi : k = i
    · subst k
      rw [hFi,hNs,hNt]
      simp only [Subtype.val_inj,le_refl]
    · by_cases hj' : k = j
      · subst k
        rw [hFj,hQs,hQt]
        have hne : (D.path j).finish ≠ w := by rw [hj]; exact Ne.symm hw
        simp only [if_neg hne,Nat.add_zero,Subtype.val_inj]
        exact Nat.le_add_right _ _
      · rw [hFk k hi hj']
        change ((if (D.path k).start = w then 1 else 0) +
          (if (D.path k).finish = w then 1 else 0) : ℕ) ≤
          (if (D.path k).start.val = w.val then 1 else 0) +
          (if (D.path k).finish.val = w.val then 1 else 0)
        simp only [Subtype.val_inj,le_refl]

end Gallai.WholeBowtie
