/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedCheapPassingAccounting
import Gallai.Transport.RetainedEdgePartition

/-! # One-credit reconstruction in the retained passing profile -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrows : ∀ i v, v ∈ B.row i ↔
  ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)

include hrows in
/-- A separated retained passing auxiliary and its accepted cheap record
reconstruct G within one extra path. No global edge-cover oracle is assumed. -/
theorem retainedCheapPassing_reconstruction
    (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj] (repair : Bool)
    (hAdj : ∀ u v, H.Adj u v ↔ G.Adj u.val v.val ∧
      ¬ (repair = true ∧ s(u.val,v.val) = s((A 1).val,(A 2).val)))
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (hpq : H.Adj B.completedHub (B.retainedSlot A 0) ∧
      H.Adj B.completedHub (B.retainedSlot A 1))
    (hr : ¬ H.Reachable B.completedHub (B.retainedSlot A 2))
    (D : Decomposition H) (hd : H.degree B.completedHub = 2)
    (hz : D.endpointCount B.completedHub = 0)
    (hpos : 0 < D.endpointCount (B.retainedSlot A 2))
    (connector remote : List Vertex) (added : List (List Vertex))
    (h : Retained.CheapPassingAccepted s repair connector remote added) :
    ∃ E : Decomposition G, E.size = D.size + added.length ∧
      E.size ≤ D.size + 1 ∧ ∀ w : B.StarSurvivor, w ≠ B.retainedSlot A 2 →
        D.endpointCount w ≤ E.endpointCount w.val := by
  classical
  have hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true → (A j).val ∈ B.row i := by
    intro i j hj
    exact (hrows i _).mpr ⟨j,hj,rfl⟩
  have hOriginal : ∀ u v, H.Adj u v → G.Adj u.val v.val :=
    fun u v ha => ((hAdj u v).mp ha).1
  have hneighbors : ∀ v, H.Adj B.completedHub v →
      v = B.retainedSlot A 0 ∨ v = B.retainedSlot A 1 := by
    intro v ha
    exact (B.retainedHub_normalized_neighbors A s hrows h.1 v).mp
      (hOriginal B.completedHub v ha)
  obtain ⟨Q,hQ,hEnd⟩ := B.retainedCheapPassing_candidate A s hrow H hOriginal hpq
    hneighbors hr D hd hz hpos repair hp connector remote added h
  have hcover (e : Sym2 V) (he : e ∈ G.edgeSet) : (∑ i, (Q i).walk.edges.count e) = 1 := by
    have hc := hQ e
    have hb := B.retained_edge_balance A s hrows H repair hAdj D h.1 e he
    omega
  let E : Decomposition G := Decomposition.ofEdgeCounts
    (fun i : Fin (D.size + added.length) => Q (finSumFinEquiv.symm i)) (by
      intro e he
      exact ((finSumFinEquiv : Fin D.size ⊕ Fin added.length ≃
        Fin (D.size + added.length)).symm.sum_comp
          (fun i => (Q i).walk.edges.count e)).trans (hcover e he))
  refine ⟨E,rfl,Nat.add_le_add_left h.2.2.2.2.2.2.2 _,?_⟩
  intro w hw
  change D.endpointCount w ≤ ∑ i : Fin (D.size + added.length),
    ((if (Q (finSumFinEquiv.symm i)).start = w.val then 1 else 0) +
      (if (Q (finSumFinEquiv.symm i)).finish = w.val then 1 else 0))
  rw [(finSumFinEquiv : Fin D.size ⊕ Fin added.length ≃
    Fin (D.size + added.length)).symm.sum_comp
      (fun i => (if (Q i).start = w.val then 1 else 0) +
        (if (Q i).finish = w.val then 1 else 0))]
  exact hEnd w hw

end Gallai.WholeBowtie
