/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedSyntheticCarrier
import Gallai.Foundations.Endpoints

/-! # Replace exactly the synthetic-edge owner in a retained decomposition -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The synthetic edge has one owner; replacing it preserves the complete
old endpoint vector and adds exactly the private connector's edges. -/
theorem retainedSyntheticFamily (p q : B.StarSurvivor) (hne : p ≠ q)
    (hmissing : ¬ G.Adj p.val q.val) (D : Decomposition (B.retainedHubRepair p q))
    (M : G.Walk p.val q.val) (hM : M.IsPath)
    (hf : ∀ v ∈ M.support, v = p.val ∨ v = q.val ∨ v ∈ (Finset.univ.erase 0).map B.label) :
    ∃ F : Fin D.size → NonemptyPath G,
      (∀ i, (F i).start = (D.path i).start.val ∧ (F i).finish = (D.path i).finish.val) ∧
      ∀ e, (∑ i, (F i).walk.edges.count e) + (if s(p.val,q.val) = e then 1 else 0) =
        (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) + M.edges.count e := by
  classical
  have ha : (B.retainedHubRepair p q).Adj p q := by
    change (toggleEdge B.retainedHubGraph p q).Adj p q
    rw [toggleEdge, if_neg (show ¬ B.retainedHubGraph.Adj p q from hmissing)]
    exact Or.inr ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩, hne⟩)
  obtain ⟨j, hj, huniq⟩ := D.covers s(p,q) ha
  obtain ⟨Q, hQs, hQt, hQc⟩ := B.restore_retainedRepairCarrier p q (D.path j) hj M hM hf
  have hother (i : Fin D.size) (hij : i ≠ j) : s(p,q) ∉ (D.path i).walk.edges :=
    fun hi => hij (huniq i hi)
  let F : Fin D.size → NonemptyPath G := fun i =>
    if hij : i = j then Q else B.unchangedRetainedRepairCarrier p q (D.path i) (hother i hij)
  have hFj : F j = Q := dif_pos rfl
  have hFi (i : Fin D.size) (hi : i ≠ j) :
      F i = B.unchangedRetainedRepairCarrier p q (D.path i) (hother i hi) := dif_neg hi
  refine ⟨F, ?_, ?_⟩
  · intro i
    by_cases hi : i = j
    · subst i
      rw [hFj]
      exact ⟨hQs,hQt⟩
    · rw [hFi i hi]
      exact ⟨rfl,rfl⟩
  · intro e
    have hpoint (i : Fin D.size) :
        (F i).walk.edges.count e + (if i = j then (if s(p.val,q.val) = e then 1 else 0) else 0) =
        ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e +
          (if i = j then M.edges.count e else 0) := by
      by_cases hi : i = j
      · subst i
        rw [hFj]
        simpa only [eq_self, ite_true, B.retainedRepairCarrier_edges] using hQc e
      · rw [hFi i hi]
        simp only [if_neg hi, unchangedRetainedRepairCarrier,
          NonemptyPath.transfer_edges, B.retainedRepairCarrier_edges, Nat.add_zero]
    have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hpoint i)
    simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hsum

end Gallai.WholeBowtie
