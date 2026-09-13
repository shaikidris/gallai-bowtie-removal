/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedCheapPassingReconstruction
import Gallai.Transport.RetainedCheapEndingReconstruction

/-! # Profile-independent reconstruction of all cheap retained representatives -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The normalized row and exact original-edge repair contract determine the
two retained spokes and degree two, without a separate degree premise. -/
theorem retainedNormalized_spokes_degree
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
    (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)
    (hs : s 0 = 1) (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj]
    (repair : Bool)
    (hAdj : ∀ u v, H.Adj u v ↔ G.Adj u.val v.val ∧
      ¬ (repair = true ∧ s(u.val,v.val) = s((A 1).val,(A 2).val))) :
    (H.Adj B.completedHub (B.retainedSlot A 0) ∧
      H.Adj B.completedHub (B.retainedSlot A 1)) ∧ H.degree B.completedHub = 2 := by
  classical
  have hadj (v) : H.Adj B.completedHub v ↔
      v = B.retainedSlot A 0 ∨ v = B.retainedSlot A 1 := by
    constructor
    · intro ha
      exact (B.retainedHub_normalized_neighbors A s hrows hs v).mp
        ((hAdj B.completedHub v).mp ha).1
    · intro hv
      apply (hAdj B.completedHub v).mpr
      refine ⟨(B.retainedHub_normalized_neighbors A s hrows hs v).mpr hv,?_⟩
      rintro ⟨_,heq⟩
      have hx : B.label 0 ∈ B.vertices := Finset.mem_map.mpr ⟨0,Finset.mem_univ _,rfl⟩
      rcases Sym2.eq_iff.mp heq with heq | heq
      · exact (A 1).property (heq.1 ▸ hx)
      · exact (A 2).property (heq.1 ▸ hx)
  refine ⟨⟨(hadj _).mpr (Or.inl rfl),(hadj _).mpr (Or.inr rfl)⟩,?_⟩
  have hset : H.neighborFinset B.completedHub = {B.retainedSlot A 0,B.retainedSlot A 1} := by
    ext v
    simpa only [SimpleGraph.mem_neighborFinset,Finset.mem_insert,Finset.mem_singleton] using hadj v
  change (H.neighborFinset B.completedHub).card = 2
  rw [hset,Finset.card_pair]
  intro heq
  have hi : (0 : Fin 3) = 1 := A.injective
    (Subtype.ext (congrArg (fun w : B.StarSurvivor => w.val) heq))
  exact (by decide : (0 : Fin 3) ≠ 1) hi

/-- Every stored cheap representative has two hub tails, as required by the
terminal-profile consumer. -/
theorem retainedCheap_two_tails (i : Fin 5) :
    ∃ u v, Retained.cheapEnding i = [u,v] := by
  fin_cases i <;> exact ⟨_,_,rfl⟩

/-- All five normalized cheap records reconstruct G independently of the hub
endpoint profile. Separation follows from two components and anchor coverage. -/
theorem retainedCheap_representative
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 5)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (Retained.state (Retained.cheapIndex i) j)).val.testBit k.val = true ∧ (A k).val = v)
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj]
    (hAdj : ∀ u v, H.Adj u v ↔ G.Adj u.val v.val ∧
      ¬ (Retained.repair (Retained.cheapIndex i) = true ∧ s(u.val,v.val) = s((A 1).val,(A 2).val)))
    (hp : Retained.repair (Retained.cheapIndex i) = true → G.Adj (A 1).val (A 2).val)
    (hcover : ∀ C : H.ConnectedComponent, ∃ u : B.StarSurvivor, u ∈ C.supp ∧ u.val ∈ B.anchors)
    (hc : Fintype.card H.ConnectedComponent = 2)
    (D : Decomposition H) (hpos : 0 < D.endpointCount (B.retainedSlot A 2)) :
    ∃ E : Decomposition G, E.size ≤ D.size + 1 ∧
      ∀ w : B.StarSurvivor, w ≠ B.completedHub → w ≠ B.retainedSlot A 2 →
        D.endpointCount w ≤ E.endpointCount w.val := by
  have passing := Retained.cheapPassing_checked i
  obtain ⟨hpq,hd⟩ := B.retainedNormalized_spokes_degree A _ hrows passing.1 H _ hAdj
  have hr := B.retained_remote_not_reachable A H
    (B.retained_reachable_slot A H hA hcover) hpq.1 hpq.2 hc
  by_cases hz : D.endpointCount B.completedHub = 0
  · obtain ⟨E,_,hb,he⟩ := B.retainedCheapPassing_reconstruction A _ hrows H _ hAdj hp
      hpq hr D hd hz hpos _ _ _ passing
    exact ⟨E,hb,fun w _ hw => he w hw⟩
  · have ending := Retained.cheapEnding_checked i
    obtain ⟨u,v,huv⟩ := retainedCheap_two_tails i
    rw [huv] at ending
    obtain ⟨E,_,hb,he⟩ := B.retainedCheapEnding_reconstruction A _ hrows H _ hAdj hp
      hpq hr D hd (Nat.pos_of_ne_zero hz) hpos u v _ _ ending
    exact ⟨E,hb,he⟩

end Gallai.WholeBowtie
