/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedSyntheticFamily
import Gallai.Transport.RetainedSyntheticWords
import Gallai.Transport.RetainedEndingAccounting
import Gallai.Transport.RetainedEdgePartition
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Sum

/-! # Global reconstruction for retained synthetic repair certificates -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Strict-private synthetic certificates reconstruct the original graph with
both spokes retained and all survivor endpoint reserves preserved. -/
theorem retainedSynthetic_reconstruction
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
    (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)
    (hmissing : ¬ G.Adj (A 1).val (A 2).val)
    (D : Decomposition (B.retainedHubRepair (B.retainedSlot A 1) (B.retainedSlot A 2)))
    (connector : List Vertex) (added : List (List Vertex))
    (h : Retained.SyntheticAccepted s connector added) :
    ∃ E : Decomposition G, E.size = D.size + added.length ∧ E.size ≤ D.size + 2 ∧
      ∀ w : B.StarSurvivor, D.endpointCount w ≤ E.endpointCount w.val := by
  classical
  have hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true → (A j).val ∈ B.row i :=
    fun i j hj => (hrows i _).mpr ⟨j,hj,rfl⟩
  obtain ⟨M,hM,hMe,hMf⟩ := B.retainedSyntheticConnector A s hrow connector added h
  have hne : B.retainedSlot A 1 ≠ B.retainedSlot A 2 := by
    intro he
    have hi : (1 : Fin 3) = 2 := A.injective
      (Subtype.ext (congrArg (fun w : B.StarSurvivor => w.val) he))
    exact (by decide : (1 : Fin 3) ≠ 2) hi
  obtain ⟨F,hEnds,hF⟩ := B.retainedSyntheticFamily (B.retainedSlot A 1) (B.retainedSlot A 2)
    hne hmissing D M hM hMf
  let N (i : Fin added.length) := B.realizeRetainedSyntheticMember A s hrow connector added h
    added[i] (List.mem_cons_of_mem _ (List.getElem_mem _))
  let Q : Fin D.size ⊕ Fin added.length → NonemptyPath G := Sum.elim F N
  have hN (i : Fin added.length) : (N i).walk.edges =
      (wordEdges added[i]).map (Sym2.map (B.threeLabel A)) :=
    B.realizeRetainedSyntheticMember_edges A s hrow connector added h _ _
  have hAdj : ∀ u v : B.StarSurvivor, G.Adj u.val v.val →
      ((B.retainedHubRepair (B.retainedSlot A 1) (B.retainedSlot A 2)).Adj u v ↔
        ¬ ((false : Bool) = true ∧ s(u.val,v.val) = s((A 1).val,(A 2).val))) := by
    intro u v huv
    change (toggleEdge B.retainedHubGraph (B.retainedSlot A 1) (B.retainedSlot A 2)).Adj u v ↔ _
    rw [toggleEdge, if_neg (show ¬ B.retainedHubGraph.Adj
      (B.retainedSlot A 1) (B.retainedSlot A 2) from hmissing)]
    exact iff_of_true (Or.inl huv) (by simp)
  have hacc : Accepted ((targetEdges s \ {s(0,anchor 0),s(0,anchor 1)}) ∪ retainedRepair false)
      (connector :: added) := by simpa only [retainedRepair, Bool.false_eq_true, ite_false,
        Finset.union_empty] using h.2.2.2.2.2.1
  have hcover (e : Sym2 V) (he : e ∈ G.edgeSet) : (∑ i, (Q i).walk.edges.count e) = 1 := by
    have hr : s((A 1).val,(A 2).val) ≠ e := by
      intro hh
      apply hmissing
      change s((A 1).val,(A 2).val) ∈ G.edgeSet
      rw [hh]
      exact he
    have hc := hF e
    change (∑ i, (F i).walk.edges.count e) +
      (if s((A 1).val,(A 2).val) = e then 1 else 0) = _ at hc
    rw [if_neg hr, Nat.add_zero] at hc
    have hc' : (∑ i, (F i).walk.edges.count e) =
        (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) +
          ((wordEdges connector).map (Sym2.map (B.threeLabel A))).count e :=
      hc.trans (congrArg (fun t : List (Sym2 V) =>
        (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) + t.count e) hMe)
    have hl := B.retainedWords_local_count A s false connector added h.1 hacc e
    have hb := B.retained_edge_balance_of_original A s hrows _ false hAdj D h.1 e he
    rw [Fintype.sum_sum_type]
    simp only [Q, Sum.elim_inl, Sum.elim_inr, hN]
    omega
  let E : Decomposition G := Decomposition.ofEdgeCounts
    (fun i : Fin (D.size + added.length) => Q (finSumFinEquiv.symm i)) (by
      intro e he
      exact ((finSumFinEquiv : Fin D.size ⊕ Fin added.length ≃
        Fin (D.size + added.length)).symm.sum_comp
          (fun i => (Q i).walk.edges.count e)).trans (hcover e he))
  refine ⟨E,rfl,Nat.add_le_add_left h.2.2.2.2.2.2 _,?_⟩
  intro w
  have hEnd : (∑ i, ((if (F i).start = w.val then 1 else 0) +
      (if (F i).finish = w.val then 1 else 0) : ℕ)) = D.endpointCount w := by
    unfold Decomposition.endpointCount
    apply Finset.sum_congr rfl
    intro i _
    rw [(hEnds i).1,(hEnds i).2]
    simp only [Subtype.val_inj]
  change D.endpointCount w ≤ ∑ i : Fin (D.size + added.length),
    ((if (Q (finSumFinEquiv.symm i)).start = w.val then 1 else 0) +
      (if (Q (finSumFinEquiv.symm i)).finish = w.val then 1 else 0))
  rw [(finSumFinEquiv : Fin D.size ⊕ Fin added.length ≃ Fin (D.size + added.length)).symm.sum_comp
    (fun i => (if (Q i).start = w.val then 1 else 0) +
      (if (Q i).finish = w.val then 1 else 0)), Fintype.sum_sum_type]
  change D.endpointCount w ≤
    (∑ i, ((if (F i).start = w.val then 1 else 0) + (if (F i).finish = w.val then 1 else 0))) + _
  rw [hEnd]
  exact Nat.le_add_right _ _

/-- Both checked synthetic representative rows have actual arbitrary-order
reconstruction. This does not yet assert relabeling coverage of every row. -/
theorem retainedSynthetic_representative
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 6) (hi : i = 1 ∨ i = 4)
    (hrows : ∀ j v, v ∈ B.row j ↔
      ∃ k, (rowMask (Retained.state i j)).val.testBit k.val = true ∧ (A k).val = v)
    (hmissing : ¬ G.Adj (A 1).val (A 2).val)
    (D : Decomposition (B.retainedHubRepair (B.retainedSlot A 1) (B.retainedSlot A 2))) :
    ∃ E : Decomposition G, E.size ≤ D.size + 2 ∧
      ∀ w : B.StarSurvivor, D.endpointCount w ≤ E.endpointCount w.val := by
  rcases hi with rfl | rfl
  · obtain ⟨E,_,hb,he⟩ := B.retainedSynthetic_reconstruction A (Retained.state 1) hrows
      hmissing D [6,3,4,7] [[3,5,1,6,2,0,4],[3,0,1,2,5,4]] Retained.synthetic_one
    exact ⟨E,hb,he⟩
  · obtain ⟨E,_,hb,he⟩ := B.retainedSynthetic_reconstruction A (Retained.state 4) hrows
      hmissing D [6,1,2,7] [[1,5,2,0,3,4,7],[1,0,4,5,3,7]] Retained.synthetic_four
    exact ⟨E,hb,he⟩

end Gallai.WholeBowtie
