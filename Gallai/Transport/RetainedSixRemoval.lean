/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedSyntheticRemoval

/-! # Removal for all six normalized retained representatives -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Representative zero uses only two anchors; private deletion keeps them
joined through the hub and therefore has no sharp two-component obstruction. -/
theorem retainedZero_removal
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices})
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (Retained.state 0 j)).val.testBit k.val = true ∧ (A k).val = v)
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hG : G.Connected)
    (y : B.StarSurvivor) (hx : y.val ≠ B.label 0) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y.val := by
  classical
  have hs0 : Retained.state 0 0 = 1 := by decide
  have hpair (v : V) (hv : v ∈ B.anchors) : v = (A 0).val ∨ v = (A 1).val := by
    obtain ⟨j,hj⟩ := (B.mem_anchors v).mp hv
    obtain ⟨k,hk,rfl⟩ := (hrows j v).mp hj
    have hj1 : Retained.state 0 j = 1 := (by decide : ∀ j : Fin 5, Retained.state 0 j = 1) j
    rw [hj1] at hk
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (Bool.false_ne_true hk).elim
  have ha : B.anchors.card ≤ 3 := by
    have hsub : B.anchors ⊆ {(A 0).val,(A 1).val} := by
      intro v hv
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hpair v hv
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two.trans (by decide))
  obtain ⟨hpq,hd⟩ := B.retainedNormalized_spokes_degree A _ hrows hs0 B.retainedHubGraph false
    (fun u v => by simp)
  have hr : (B.row 0).card = 2 := B.retainedHub_degree.symm.trans hd
  have hnon : (B.row 0).Nonempty := Finset.card_pos.mp (by omega)
  have all (v : B.StarSurvivor) : B.retainedHubGraph.Reachable v B.completedHub := by
    obtain ⟨u,hu,ha⟩ := B.retainedHub_component_anchor hG hnon
      (B.retainedHubGraph.connectedComponentMk v)
    have hreach := (B.retainedHubGraph.connectedComponentMk v).reachable_of_mem_supp
      (show v ∈ (B.retainedHubGraph.connectedComponentMk v).supp from rfl) hu
    rcases hpair u.val ha with hp | hq
    · have he : u = B.retainedSlot A 0 := Subtype.ext hp
      exact (he ▸ hreach).trans hpq.1.reachable.symm
    · have he : u = B.retainedSlot A 1 := Subtype.ext hq
      exact (he ▸ hreach).trans hpq.2.reachable.symm
  have hc : Fintype.card B.retainedHubGraph.ConnectedComponent ≤ 1 := by
    have he (C : B.retainedHubGraph.ConnectedComponent) :
        C = B.retainedHubGraph.connectedComponentMk B.completedHub := by
      induction C using SimpleGraph.ConnectedComponent.ind with
      | h v => exact SimpleGraph.ConnectedComponent.sound (all v)
    exact Fintype.card_le_one_iff.mpr (fun C D => (he C).trans (he D).symm)
  have hs := B.threeAnchor_private_empty A _ hrows hA
    (by decide : privateSyndrome (Retained.state 0) = ∅)
  obtain ⟨D,he,hb⟩ := B.retainedHub_endpoint_credit hs hr ha hG y hx hy hcap
  have hb2 : D.size + 2 ≤ (Fintype.card V + 1) / 2 := by
    rcases hb with hb | ⟨_,hc2,_⟩
    · exact hb
    · omega
  obtain ⟨E,hsize,hend⟩ := B.retainedOrdinary_representative A 0 hrows B.retainedHubGraph
    (fun u v => by simp [Retained.repair]) (by simp [Retained.repair]) D
  exact ⟨E,hsize.trans hb2,he.trans (hend y (fun h => hx (congrArg Subtype.val h)))⟩

/-- All six normalized retained types satisfy removal without a supplied
auxiliary decomposition, repair-edge status, or carrier interface. Exhaustive
relabeling into these types remains a separate finite-universe obligation. -/
theorem retainedSix_removal
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 6)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (Retained.state i j)).val.testBit k.val = true ∧ (A k).val = v)
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hG : G.Connected)
    (y : B.StarSurvivor) (hx : y.val ≠ B.label 0) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y.val := by
  by_cases hi : i = 0
  · subst i
    exact B.retainedZero_removal A hrows hA hG y hx hy hcap
  · obtain ⟨j,hj⟩ := (by decide : ∀ i : Fin 6, i ≠ 0 →
        ∃ j : Fin 5, Retained.cheapIndex j = i) i hi
    subst i
    exact B.retainedFive_removal A j hrows hA hG y hx hy hcap

end Gallai.WholeBowtie
