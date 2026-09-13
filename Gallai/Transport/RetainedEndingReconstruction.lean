/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedEndingAccounting
import Gallai.Transport.RetainedTerminalFamily
import Gallai.Transport.RetainedEdgePartition
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Sum

/-! # Actual one-tail retained ending reconstruction -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrows : ∀ i v, v ∈ B.row i ↔
  ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)

include hrows in
/-- Any positive hub endpoint supply supports the one-tail ending identity.
No degree hypothesis or selection oracle is required. -/
theorem retainedEnding_reconstruction
    (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj] (repair : Bool)
    (hAdj : ∀ u v, H.Adj u v ↔ G.Adj u.val v.val ∧
      ¬ (repair = true ∧ s(u.val,v.val) = s((A 1).val,(A 2).val)))
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (D : Decomposition H) (hpos : 0 < D.endpointCount B.completedHub)
    (tail : List Vertex) (added : List (List Vertex))
    (h : RetainedEndingAccepted s repair [tail] added) :
    ∃ E : Decomposition G, E.size = D.size + added.length ∧
      E.size ≤ D.size + 2 ∧ ∀ w : B.StarSurvivor, w ≠ B.completedHub →
        D.endpointCount w ≤ E.endpointCount w.val := by
  classical
  have hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true → (A j).val ∈ B.row i := by
    intro i j hj
    exact (hrows i _).mpr ⟨j, hj, rfl⟩
  obtain ⟨T, ht, hte, hf⟩ := B.retainedEndingTail A s hrow repair hp [tail] added h tail (by simp)
  obtain ⟨F, hF, hEnd⟩ := B.retainedTerminalSelected H
    (fun u v ha => ((hAdj u v).mp ha).1) D hpos T ht hf
  let N (i : Fin added.length) := B.realizeRetainedEndingMember A s hrow repair hp
    [tail] added h added[i] (List.mem_append_right _ (List.getElem_mem _))
  let Q : Fin D.size ⊕ Fin added.length → NonemptyPath G := Sum.elim F N
  have hN (i : Fin added.length) : (N i).walk.edges =
      (wordEdges added[i]).map (Sym2.map (B.threeLabel A)) :=
    B.realizeRetainedEndingMember_edges A s hrow repair hp _ _ h _ _
  have hcover (e : Sym2 V) (he : e ∈ G.edgeSet) :
      (∑ i, (Q i).walk.edges.count e) = 1 := by
    have hc := hF e
    rw [hte] at hc
    have hl := B.retainedEnding_local_count A s repair tail added h e
    have hb := B.retained_edge_balance A s hrows H repair hAdj D h.1 e he
    rw [Fintype.sum_sum_type]
    simp only [Q, Sum.elim_inl, Sum.elim_inr, hN]
    omega
  let E : Decomposition G := Decomposition.ofEdgeCounts
    (fun i : Fin (D.size + added.length) => Q (finSumFinEquiv.symm i)) (by
      intro e he
      exact ((finSumFinEquiv : Fin D.size ⊕ Fin added.length ≃
        Fin (D.size + added.length)).symm.sum_comp
          (fun i => (Q i).walk.edges.count e)).trans (hcover e he))
  refine ⟨E, rfl, Nat.add_le_add_left h.2.2.2.2.2 _, ?_⟩
  intro w hw
  change D.endpointCount w ≤ ∑ i : Fin (D.size + added.length),
    ((if (Q (finSumFinEquiv.symm i)).start = w.val then 1 else 0) +
      (if (Q (finSumFinEquiv.symm i)).finish = w.val then 1 else 0))
  rw [(finSumFinEquiv : Fin D.size ⊕ Fin added.length ≃
    Fin (D.size + added.length)).symm.sum_comp
      (fun i => (if (Q i).start = w.val then 1 else 0) +
        (if (Q i).finish = w.val then 1 else 0)), Fintype.sum_sum_type]
  change D.endpointCount w ≤
    (∑ i, ((if (F i).start = w.val then 1 else 0) + (if (F i).finish = w.val then 1 else 0))) + _
  rw [hEnd w hw]
  exact Nat.le_add_right _ _

end Gallai.WholeBowtie
