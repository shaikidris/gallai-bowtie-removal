/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.CompositionRetainedFive

/-! # Fixed-witness lift for the zero retained representative -/
namespace Gallai.Composition
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The two anchors of representative zero stay connected through the retained hub. -/
theorem retained_zero_components (B : WholeBowtie G)
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices})
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (Retained.state 0 j)).val.testBit k.val = true ∧ (A k).val = v)
    (hG : G.Connected) : Fintype.card B.retainedHubGraph.ConnectedComponent ≤ 1 := by
  classical
  have hs0 : Retained.state 0 0 = 1 := by decide
  have hpair (v : V) (hv : v ∈ B.anchors) : v = (A 0).val ∨ v = (A 1).val := by
    obtain ⟨j, hj⟩ := (B.mem_anchors v).mp hv
    obtain ⟨k, hk, rfl⟩ := (hrows j v).mp hj
    have hj1 : Retained.state 0 j = 1 := (by decide : ∀ j : Fin 5, Retained.state 0 j = 1) j
    rw [hj1] at hk
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (Bool.false_ne_true hk).elim
  obtain ⟨hpq, hd⟩ := B.retainedNormalized_spokes_degree A _ hrows hs0 B.retainedHubGraph false
    (fun u v => by simp)
  have hr : (B.row 0).card = 2 := B.retainedHub_degree.symm.trans hd
  have hnon : (B.row 0).Nonempty := Finset.card_pos.mp (by omega)
  have all (v : B.StarSurvivor) : B.retainedHubGraph.Reachable v B.completedHub := by
    obtain ⟨u, hu, ha⟩ := B.retainedHub_component_anchor hG hnon
      (B.retainedHubGraph.connectedComponentMk v)
    have hreach := (B.retainedHubGraph.connectedComponentMk v).reachable_of_mem_supp
      (show v ∈ (B.retainedHubGraph.connectedComponentMk v).supp from rfl) hu
    rcases hpair u.val ha with hp | hq
    · have he : u = B.retainedSlot A 0 := Subtype.ext hp
      exact (he ▸ hreach).trans hpq.1.reachable.symm
    · have he : u = B.retainedSlot A 1 := Subtype.ext hq
      exact (he ▸ hreach).trans hpq.2.reachable.symm
  have he (C : B.retainedHubGraph.ConnectedComponent) :
      C = B.retainedHubGraph.connectedComponentMk B.completedHub := by
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h v => exact SimpleGraph.ConnectedComponent.sound (all v)
  exact Fintype.card_le_one_iff.mpr (fun C D => (he C).trans (he D).symm)

/-- Any component-sum witness lifts, preserving all nonhub endpoint counts.
No one-exception theorem is applied to the remaining family. -/
theorem retained_zero_lift (B : WholeBowtie G)
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices})
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (Retained.state 0 j)).val.testBit k.val = true ∧ (A k).val = v)
    (hc : G.Connected) (D : Decomposition B.retainedHubGraph)
    (hb : D.size ≤ ∑ K : B.retainedHubGraph.ConnectedComponent,
      (Fintype.card K.supp + 1) / 2) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      ∀ w : B.StarSurvivor, w.val ≠ B.label 0 →
        D.endpointCount w ≤ E.endpointCount w.val := by
  have hcomp := retained_zero_components B A hrows hc
  have hcredit := B.retained_credit_of_component_budget _ D hb (by omega)
  have htwo : D.size + 2 ≤ (Fintype.card V + 1) / 2 := by
    rcases hcredit with htwo | ⟨_, hC, _⟩
    · exact htwo
    · omega
  obtain ⟨E, hsize, hends⟩ := B.retainedOrdinary_representative A 0 hrows B.retainedHubGraph
    (fun u v => by simp [Retained.repair]) (by simp [Retained.repair]) D
  exact ⟨E, hsize.trans htwo, fun w hw =>
    hends w (fun h => hw (congrArg Subtype.val h))⟩

end Gallai.Composition
