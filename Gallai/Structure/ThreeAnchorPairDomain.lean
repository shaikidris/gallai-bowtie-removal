/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ThreeAnchorSlots
import Gallai.Certificates.ThreeAnchorStateCode

/-! # Actual pair-syndrome graphs enter the exhaustive finite route partition -/

namespace Gallai.WholeBowtie

open Certificate.ThreeAnchor Certificate.ThreeAnchor.Orbits
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The graph supplies slots, exact rows and a classified finite state.
No auxiliary connectedness or preselected certificate is assumed. -/
theorem threeAnchor_pair_domain (hc : G.Connected) (hA : B.anchors.card ≤ 3)
    (y : {v : V // v ∉ B.vertices}) (hy : Even (G.degree y.val))
    (ha : 3 ≤ B.activity) (hs : B.syndrome.card = 2) :
    ∃ (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State),
      (∀ v ∈ B.anchors, ∃ j, (A j).val = v) ∧
      (∀ i v, v ∈ B.row i ↔
        ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v) ∧
      (encode s ∈ syntheticCodes ∨ encode s ∈ retainedCodes) := by
  obtain ⟨A, s, hcover, hrows⟩ := B.exists_threeAnchorSlots_state_connected hc hA y hy
  have hcard := Finset.card_image_of_injective (Certificate.ThreeAnchor.syndrome s)
    (Subtype.val_injective.comp A.injective)
  change ((Certificate.ThreeAnchor.syndrome s).image (fun j => (A j).val)).card =
    (Certificate.ThreeAnchor.syndrome s).card at hcard
  rw [B.threeAnchor_syndrome_image A hcover s hrows, hs] at hcard
  refine ⟨A, s, hcover, hrows, state_pair_partition s ?_ hcard.symm⟩
  rw [B.threeAnchor_activity A s hrows]
  exact ha

end Gallai.WholeBowtie
