/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedCheapRemoval
import Gallai.Transport.RetainedSyntheticReconstruction

/-! # Synthetic retained repairs have two reconstruction credits -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- A missing repair edge joins the remote anchor to the retained hub's
component. Anchor coverage then excludes a two-component credit obstruction. -/
theorem retainedSynthetic_components_le_one
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (s j)).val.testBit k.val = true ∧ (A k).val = v)
    (hs0 : s 0 = 1)
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hs : B.privateDeletionSyndrome = {B.retainedSlot A 1,B.retainedSlot A 2})
    (hG : G.Connected) (hm : ¬ G.Adj (A 1).val (A 2).val) :
    Fintype.card (B.retainedHubRepair (B.retainedSlot A 1)
      (B.retainedSlot A 2)).ConnectedComponent ≤ 1 := by
  classical
  let H := B.retainedHubRepair (B.retainedSlot A 1) (B.retainedSlot A 2)
  have keep {u v : B.StarSurvivor} (h : B.retainedHubGraph.Adj u v) : H.Adj u v := by
    change (toggleEdge B.retainedHubGraph _ _).Adj u v
    rw [toggleEdge,if_neg (show ¬ B.retainedHubGraph.Adj
      (B.retainedSlot A 1) (B.retainedSlot A 2) from hm)]
    exact Or.inl h
  have hp : H.Adj B.completedHub (B.retainedSlot A 0) := keep
    ((B.retainedHub_normalized_neighbors A s hrows hs0 _).mpr (Or.inl rfl))
  have hq : H.Adj B.completedHub (B.retainedSlot A 1) := keep
    ((B.retainedHub_normalized_neighbors A s hrows hs0 _).mpr (Or.inr rfl))
  have hqr : H.Adj (B.retainedSlot A 1) (B.retainedSlot A 2) := by
    change (toggleEdge B.retainedHubGraph _ _).Adj _ _
    rw [toggleEdge,if_neg (show ¬ B.retainedHubGraph.Adj
      (B.retainedSlot A 1) (B.retainedSlot A 2) from hm)]
    apply Or.inr
    simp only [SimpleGraph.edge_adj]
    refine ⟨by simp,?_⟩
    intro he
    have hi : (1 : Fin 3) = 2 := A.injective
      (Subtype.ext (congrArg (fun w : B.StarSurvivor => w.val) he))
    exact (by decide : (1 : Fin 3) ≠ 2) hi
  have hr : (B.row 0).Nonempty := ⟨(A 0).val,(hrows 0 _).mpr
    ⟨0,by rw [hs0]; decide,rfl⟩⟩
  have cover := B.retained_reachable_slot A H hA
    (B.retainedHubRepair_component_anchor _ _ hs hG hr)
  have all (v : B.StarSurvivor) : H.Reachable v B.completedHub := by
    obtain ⟨j,hj⟩ := cover v
    fin_cases j
    · exact hj.trans hp.reachable.symm
    · exact hj.trans hq.reachable.symm
    · exact hj.trans (hq.reachable.trans hqr.reachable).symm
  have he (C : H.ConnectedComponent) : C = H.connectedComponentMk B.completedHub := by
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h v => exact SimpleGraph.ConnectedComponent.sound (all v)
  exact Fintype.card_le_one_iff.mpr (fun C D => (he C).trans (he D).symm)

/-- Both normalized synthetic representatives satisfy removal at all orders,
with a supplied designated even vertex exposed at least twice. -/
theorem retainedSynthetic_removal
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 6) (hi : i = 1 ∨ i = 4)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (Retained.state i j)).val.testBit k.val = true ∧ (A k).val = v)
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hG : G.Connected) (hm : ¬ G.Adj (A 1).val (A 2).val)
    (y : B.StarSurvivor) (hx : y.val ≠ B.label 0) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y.val := by
  classical
  have hs0 : Retained.state i 0 = 1 := by rcases hi with rfl | rfl <;> decide
  have hsfin : privateSyndrome (Retained.state i) = {1,2} := by
    rcases hi with rfl | rfl <;> decide
  have hs := B.threeAnchor_private_pair A _ hrows hA 1 2 hsfin
  have hne : B.retainedSlot A 1 ≠ B.retainedSlot A 2 := by
    intro h
    have he : (1 : Fin 3) = 2 := A.injective
      (Subtype.ext (congrArg (fun w : B.StarSurvivor => w.val) h))
    exact (by decide : (1 : Fin 3) ≠ 2) he
  have hr : (B.row 0).card = 2 := by
    rw [← B.retainedHub_degree]
    exact (B.retainedNormalized_spokes_degree A _ hrows hs0 B.retainedHubGraph false
      (fun u v => by simp)).2
  have ha : B.anchors.card ≤ 3 := by
    have hsub : B.anchors ⊆ Finset.univ.image (fun j : Fin 3 => (A j).val) := by
      intro v hv
      obtain ⟨j,hj⟩ := hA v hv
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩
    exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by decide))
  obtain ⟨D,he,hb⟩ := B.retainedHubRepair_endpoint_credit _ _ hne hs hr ha hG y hx hy hcap
  have hc := B.retainedSynthetic_components_le_one A _ hrows hs0 hA hs hG hm
  have hb2 : D.size + 2 ≤ (Fintype.card V + 1) / 2 := by
    rcases hb with hb | ⟨_,hc2,_⟩
    · exact hb
    · omega
  obtain ⟨E,hsize,hend⟩ := B.retainedSynthetic_representative A i hi hrows hm D
  exact ⟨E,hsize.trans hb2,he.trans (hend y)⟩

/-- The five cheap normalized representatives are removable for every actual
repair-edge status. No repair-status, auxiliary, budget or profile assumption
is exported by this combined result. -/
theorem retainedFive_removal
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 5)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (Retained.state (Retained.cheapIndex i) j)).val.testBit k.val = true ∧
        (A k).val = v)
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hG : G.Connected)
    (y : B.StarSurvivor) (hx : y.val ≠ B.label 0) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y.val := by
  by_cases hp : Retained.repair (Retained.cheapIndex i) = true →
      G.Adj (A 1).val (A 2).val
  · exact B.retainedCheap_original_removal A i hrows hA hG hp y hx hy hcap
  · have hr : Retained.repair (Retained.cheapIndex i) = true := by
      by_contra hn
      exact hp (fun h => (hn h).elim)
    have hm : ¬ G.Adj (A 1).val (A 2).val := fun h => hp (fun _ => h)
    have hi : Retained.cheapIndex i = 1 ∨ Retained.cheapIndex i = 4 :=
      (by decide : ∀ j : Fin 5, Retained.repair (Retained.cheapIndex j) = true →
        Retained.cheapIndex j = 1 ∨ Retained.cheapIndex j = 4) i hr
    exact B.retainedSynthetic_removal A _ hi hrows hA hG hm y hx hy hcap

end Gallai.WholeBowtie
