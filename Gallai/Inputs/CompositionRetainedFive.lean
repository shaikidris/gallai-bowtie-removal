/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.CompositionRetainedCheap
import Gallai.Transport.RetainedSyntheticRemoval

/-! # Fixed-witness lifting for all five nonzero retained representatives -/
namespace Gallai.Composition
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Synthetic retained repair is connected and hence affords two reconstruction paths. -/
theorem retained_synthetic_lift (B : WholeBowtie G)
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 6) (hi : i = 1 ∨ i = 4)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (Retained.state i j)).val.testBit k.val = true ∧ (A k).val = v)
    (hcover : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hc : G.Connected) (hm : ¬ G.Adj (A 1).val (A 2).val)
    (D : Decomposition (B.retainedHubRepair (B.retainedSlot A 1) (B.retainedSlot A 2)))
    (hb : D.size ≤ ∑ K :
      (B.retainedHubRepair (B.retainedSlot A 1) (B.retainedSlot A 2)).ConnectedComponent,
      (Fintype.card K.supp + 1) / 2) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      ∀ w : B.StarSurvivor, D.endpointCount w ≤ E.endpointCount w.val := by
  have hs0 : Retained.state i 0 = 1 := by rcases hi with rfl | rfl <;> decide
  have hsfin : privateSyndrome (Retained.state i) = {1, 2} := by
    rcases hi with rfl | rfl <;> decide
  have hs := B.threeAnchor_private_pair A _ hrows hcover 1 2 hsfin
  have hcomp := B.retainedSynthetic_components_le_one A _ hrows hs0 hcover hs hc hm
  have hcredit := B.retained_credit_of_component_budget _ D hb (by omega)
  have htwo : D.size + 2 ≤ (Fintype.card V + 1) / 2 := by
    rcases hcredit with htwo | ⟨_, hC, _⟩
    · exact htwo
    · omega
  obtain ⟨E, hsize, hends⟩ := B.retainedSynthetic_representative A i hi hrows hm D
  exact ⟨E, hsize.trans htwo, hends⟩

/-- All actual repair-edge statuses lift a fixed component-sum witness. -/
theorem retained_five_lift (B : WholeBowtie G)
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 5)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (Retained.state (Retained.cheapIndex i) j)).val.testBit k.val = true ∧
        (A k).val = v)
    (hcover : ∀ v ∈ B.anchors, ∃ j, (A j).val = v) (hc : G.Connected) :
    ∀ D : Decomposition (B.retainedCheapAuxiliary A i),
      D.size ≤ ∑ K : (B.retainedCheapAuxiliary A i).ConnectedComponent,
        (Fintype.card K.supp + 1) / 2 →
      ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
        ∀ w : B.StarSurvivor, w.val ≠ B.label 0 → Even (G.degree w.val) →
          D.endpointCount w ≤ E.endpointCount w.val := by
  by_cases hp : Retained.repair (Retained.cheapIndex i) = true → G.Adj (A 1).val (A 2).val
  · exact fun D hb => retained_cheap_original_lift B A i hrows hcover hc hp D hb
  · have hr : Retained.repair (Retained.cheapIndex i) = true := by
      by_contra hn
      exact hp (fun h => (hn h).elim)
    have hm : ¬ G.Adj (A 1).val (A 2).val := fun h => hp (fun _ => h)
    have hi : Retained.cheapIndex i = 1 ∨ Retained.cheapIndex i = 4 :=
      (by decide : ∀ j : Fin 5, Retained.repair (Retained.cheapIndex j) = true →
        Retained.cheapIndex j = 1 ∨ Retained.cheapIndex j = 4) i hr
    have hcases : i = 0 ∨ i = 3 :=
      (by decide : ∀ j : Fin 5, Retained.repair (Retained.cheapIndex j) = true →
        j = 0 ∨ j = 3) i hr
    rcases hcases with rfl | rfl
    · intro D hb
      obtain ⟨E, hE, hends⟩ := retained_synthetic_lift B A _ hi hrows hcover hc hm D hb
      exact ⟨E, hE, fun w _ _ => hends w⟩
    · intro D hb
      obtain ⟨E, hE, hends⟩ := retained_synthetic_lift B A _ hi hrows hcover hc hm D hb
      exact ⟨E, hE, fun w _ _ => hends w⟩

end Gallai.Composition
