/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedCheapAuxiliary
import Gallai.Transport.RetainedOrdinaryReconstruction

/-! # One-credit reconstruction from the actual retained auxiliary -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- When the indicated repair edge is original, the actual auxiliary has
exactly the original retained edges minus that optional edge. -/
theorem retainedCheapAuxiliary_original_adj
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 5)
    (hp : Retained.repair (Retained.cheapIndex i) = true → G.Adj (A 1).val (A 2).val)
    (u v : B.StarSurvivor) :
    (B.retainedCheapAuxiliary A i).Adj u v ↔ G.Adj u.val v.val ∧
      ¬ (Retained.repair (Retained.cheapIndex i) = true ∧
        s(u.val,v.val) = s((A 1).val,(A 2).val)) := by
  by_cases hr : Retained.repair (Retained.cheapIndex i) = true
  · simp only [retainedCheapAuxiliary, hr, if_true, true_and]
    change (toggleEdge B.retainedHubGraph (B.retainedSlot A 1)
      (B.retainedSlot A 2)).Adj u v ↔ _
    rw [toggleEdge, if_pos (show B.retainedHubGraph.Adj
      (B.retainedSlot A 1) (B.retainedSlot A 2) from hp hr), SimpleGraph.deleteEdges_adj]
    simp only [Set.mem_singleton_iff]
    apply and_congr_right
    intro _
    apply not_congr
    exact (Sym2.map.injective Subtype.val_injective).eq_iff.symm
  · simp [retainedCheapAuxiliary, hr]

/-- Every decomposition of a two-component actual cheap auxiliary lifts at
cost at most one. Degree, separation, component coverage and remote exposure
are derived, rather than supplied by the caller. -/
theorem retainedCheap_actual_reconstruction
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 5)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (Retained.state (Retained.cheapIndex i) j)).val.testBit k.val = true ∧
        (A k).val = v)
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hG : G.Connected)
    (hp : Retained.repair (Retained.cheapIndex i) = true → G.Adj (A 1).val (A 2).val)
    (hc : Fintype.card (B.retainedCheapAuxiliary A i).ConnectedComponent = 2)
    (D : Decomposition (B.retainedCheapAuxiliary A i)) :
    ∃ E : Decomposition G, E.size ≤ D.size + 1 ∧
      ∀ w : B.StarSurvivor, w ≠ B.completedHub → w ≠ B.retainedSlot A 2 →
        D.endpointCount w ≤ E.endpointCount w.val := by
  have hs := (Retained.cheapPassing_checked i).1
  have hrow (k : Fin 3) (hk : k = 0 ∨ k = 1) : (A k).val ∈ B.row 0 := by
    apply (hrows 0 _).mpr
    refine ⟨k,?_,rfl⟩
    rw [hs]
    rcases hk with rfl | rfl <;> decide
  have ha0 := (B.mem_anchors _).mpr ⟨0,hrow 0 (Or.inl rfl)⟩
  have ha1 := (B.mem_anchors _).mpr ⟨0,hrow 1 (Or.inr rfl)⟩
  have ha2 := B.retainedCheap_remote_anchor A i hrows
  have hadj := B.retainedCheapAuxiliary_original_adj A i hp
  obtain ⟨hpq,_⟩ := B.retainedNormalized_spokes_degree A _ hrows hs _ _ hadj
  have hcover := B.retained_component_anchor_of_edges (B.retainedCheapAuxiliary A i) hG
    ⟨B.retainedSlot A 0,hpq.1,ha0⟩ (fun u v hu huv => by
      apply (hadj u v).mpr
      refine ⟨huv,?_⟩
      rintro ⟨_,he⟩
      rcases Sym2.eq_iff.mp he with he | he
      · exact hu (he.1.symm ▸ ha1)
      · exact hu (he.1.symm ▸ ha2))
  exact B.retainedCheap_representative A i hrows hA _ hadj hp hcover hc D
    (B.retainedCheapAuxiliary_remote_positive A i hrows hA D)

/-- Both actual credit alternatives now give the ceiling bound and preserve
the designated even vertex's exposure. The remote anchor cannot be that vertex. -/
theorem retainedCheap_actual_budget
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 5)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (Retained.state (Retained.cheapIndex i) j)).val.testBit k.val = true ∧
        (A k).val = v)
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hG : G.Connected)
    (hp : Retained.repair (Retained.cheapIndex i) = true → G.Adj (A 1).val (A 2).val)
    (D : Decomposition (B.retainedCheapAuxiliary A i))
    (y : B.StarSurvivor) (hx : y.val ≠ B.label 0) (hy : Even (G.degree y.val))
    (he : 2 ≤ D.endpointCount y)
    (hb : D.size + 2 ≤ (Fintype.card V + 1) / 2 ∨
      (D.size + 1 ≤ (Fintype.card V + 1) / 2 ∧
        Fintype.card (B.retainedCheapAuxiliary A i).ConnectedComponent = 2)) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y.val := by
  have hx' : y ≠ B.completedHub := fun h => hx (congrArg Subtype.val h)
  rcases hb with hb | ⟨hb,hc⟩
  · obtain ⟨E,hsize,hend⟩ := B.retainedOrdinary_representative A _ hrows _
      (B.retainedCheapAuxiliary_original_adj A i hp) hp D
    exact ⟨E,hsize.trans hb,he.trans (hend y hx')⟩
  · have hyr : y ≠ B.retainedSlot A 2 := by
      intro h
      subst y
      have ho := B.odd_degree_anchor (B.retainedCheap_remote_anchor A i hrows)
      exact (Nat.not_even_iff_odd.mpr ho) hy
    obtain ⟨E,hsize,hend⟩ := B.retainedCheap_actual_reconstruction A i hrows hA hG hp hc D
    exact ⟨E,hsize.trans hb,he.trans (hend y hx' hyr)⟩

end Gallai.WholeBowtie
