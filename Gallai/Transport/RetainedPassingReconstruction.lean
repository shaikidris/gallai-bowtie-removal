/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedPassingAccounting
import Gallai.Transport.RetainedEdgePartition

/-! # Actual reconstruction from retained passing certificates -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrows : ∀ i v, v ∈ B.row i ↔
  ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)

include hrows in
/-- At a passing degree-two retained hub, the finite record reconstructs G
within two added paths and preserves every survivor's endpoint reserve. -/
theorem retainedPassing_reconstruction
    (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj] (repair : Bool)
    (hAdj : ∀ u v, H.Adj u v ↔ G.Adj u.val v.val ∧
      ¬ (repair = true ∧ s(u.val,v.val) = s((A 1).val,(A 2).val)))
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (D : Decomposition H)
    (hzero : D.endpointCount B.completedHub = 0)
    (connector : List Vertex) (added : List (List Vertex))
    (h : RetainedPassingAccepted s repair connector added) :
    ∃ E : Decomposition G, E.size = D.size + added.length ∧
      E.size ≤ D.size + 2 ∧ ∀ w : B.StarSurvivor,
        D.endpointCount w ≤ E.endpointCount w.val := by
  classical
  have hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true → (A j).val ∈ B.row i := by
    intro i j hj
    exact (hrows i _).mpr ⟨j, hj, rfl⟩
  have hOriginal : ∀ u v, H.Adj u v → G.Adj u.val v.val := fun u v ha => (hAdj u v).mp ha |>.1
  have hle : H ≤ B.completedStar := fun u v ha => Or.inl (hOriginal u v ha)
  have hneighbors : ∀ v, H.Adj B.completedHub v →
      v = B.retainedSlot A 0 ∨ v = B.retainedSlot A 1 := by
    intro v ha
    exact (B.retainedHub_normalized_neighbors A s hrows h.1 v).mp
      (hOriginal B.completedHub v ha)
  have hneighborSet : H.neighborFinset B.completedHub =
      {B.retainedSlot A 0, B.retainedSlot A 1} := by
    ext v
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨hneighbors v, ?_⟩
    intro hv
    have ha := (B.retainedHub_normalized_neighbors A s hrows h.1 v).mpr hv
    apply (hAdj B.completedHub v).mpr
    refine ⟨ha, ?_⟩
    rintro ⟨_, heq⟩
    have hubB : B.label 0 ∈ B.vertices := Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩
    rcases Sym2.eq_iff.mp heq with heq | heq
    · exact (A 1).property (heq.1 ▸ hubB)
    · exact (A 2).property (heq.1 ▸ hubB)
  have hd : H.degree B.completedHub = 2 := by
    change (H.neighborFinset B.completedHub).card = 2
    rw [hneighborSet, Finset.card_pair]
    intro heq
    have hi : (0 : Fin 3) = 1 := A.injective
      (Subtype.ext (congrArg (fun w : B.StarSurvivor => w.val) heq))
    exact (by decide : (0 : Fin 3) ≠ 1) hi
  obtain ⟨Q, hQ, hEnd⟩ := B.retainedPassing_candidate A s hrow H hle hOriginal
    hneighbors D hd hzero repair hp connector added h
  have hcover (e : Sym2 V) (he : e ∈ G.edgeSet) :
      (∑ i, (Q i).walk.edges.count e) = 1 := by
    have hc := hQ e
    have hb := B.retained_edge_balance A s hrows H repair hAdj D h.1 e he
    omega
  let E : Decomposition G := Decomposition.ofEdgeCounts
    (fun i : Fin (D.size + added.length) => Q (finSumFinEquiv.symm i)) (by
      intro e he
      exact ((finSumFinEquiv : Fin D.size ⊕ Fin added.length ≃
        Fin (D.size + added.length)).symm.sum_comp
          (fun i => (Q i).walk.edges.count e)).trans (hcover e he))
  refine ⟨E, rfl, Nat.add_le_add_left h.2.2.2.2.2.2 _, ?_⟩
  intro w
  change D.endpointCount w ≤ ∑ i : Fin (D.size + added.length),
    ((if (Q (finSumFinEquiv.symm i)).start = w.val then 1 else 0) +
      (if (Q (finSumFinEquiv.symm i)).finish = w.val then 1 else 0))
  rw [(finSumFinEquiv : Fin D.size ⊕ Fin added.length ≃
    Fin (D.size + added.length)).symm.sum_comp
      (fun i => (if (Q i).start = w.val then 1 else 0) +
        (if (Q i).finish = w.val then 1 else 0))]
  exact hEnd w

include hrows in
/-- No-repair passing records act directly on private deletion. -/
theorem retainedPassing_noRepair (D : Decomposition B.retainedHubGraph)
    (hzero : D.endpointCount B.completedHub = 0)
    (connector : List Vertex) (added : List (List Vertex))
    (h : RetainedPassingAccepted s false connector added) :
    ∃ E : Decomposition G, E.size = D.size + added.length ∧
      E.size ≤ D.size + 2 ∧ ∀ w : B.StarSurvivor,
        D.endpointCount w ≤ E.endpointCount w.val := by
  apply B.retainedPassing_reconstruction A s hrows B.retainedHubGraph false
    (fun u v => by simp) (by simp) D hzero connector added h

include hrows in
/-- Original-repair passing records act on the actual toggled auxiliary.
All adjacency, degree and global coverage conditions are discharged here. -/
theorem retainedPassing_originalRepair
    (hpq : G.Adj (A 1).val (A 2).val)
    (D : Decomposition (B.retainedHubRepair (B.retainedSlot A 1) (B.retainedSlot A 2)))
    (hzero : D.endpointCount B.completedHub = 0)
    (connector : List Vertex) (added : List (List Vertex))
    (h : RetainedPassingAccepted s true connector added) :
    ∃ E : Decomposition G, E.size = D.size + added.length ∧
      E.size ≤ D.size + 2 ∧ ∀ w : B.StarSurvivor,
        D.endpointCount w ≤ E.endpointCount w.val := by
  have hAdj : ∀ u v,
      (B.retainedHubRepair (B.retainedSlot A 1) (B.retainedSlot A 2)).Adj u v ↔
      G.Adj u.val v.val ∧ ¬ (true = true ∧ s(u.val,v.val) = s((A 1).val,(A 2).val)) := by
    intro u v
    change (toggleEdge B.retainedHubGraph (B.retainedSlot A 1) (B.retainedSlot A 2)).Adj u v ↔ _
    rw [toggleEdge, if_pos (show B.retainedHubGraph.Adj
      (B.retainedSlot A 1) (B.retainedSlot A 2) from hpq), SimpleGraph.deleteEdges_adj]
    simp only [Set.mem_singleton_iff, true_and]
    apply and_congr_right
    intro _
    apply not_congr
    exact (Sym2.map.injective Subtype.val_injective).eq_iff.symm
  exact B.retainedPassing_reconstruction A s hrows _ true hAdj
    (fun _ => hpq) D hzero connector added h

end Gallai.WholeBowtie
