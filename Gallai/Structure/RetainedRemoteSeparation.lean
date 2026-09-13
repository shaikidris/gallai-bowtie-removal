/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.RetainedHubComponents
import Gallai.Structure.ThreeAnchorRetainedRows

/-! # The remote anchor in a two-component retained auxiliary

Component coverage and the two retained spokes force the third anchor into
the other component. This supplies avoidance for the cheap retained tails.
-/

namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Anchor coverage expressed as reachability to the three labelled slots. -/
theorem retained_reachable_slot
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices})
    (H : SimpleGraph B.StarSurvivor)
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hcover : ∀ C : H.ConnectedComponent,
      ∃ u : B.StarSurvivor, u ∈ C.supp ∧ u.val ∈ B.anchors)
    (v : B.StarSurvivor) : ∃ j, H.Reachable v (B.retainedSlot A j) := by
  obtain ⟨u, hu, ha⟩ := hcover (H.connectedComponentMk v)
  obtain ⟨j, hj⟩ := hA u.val ha
  have he : B.retainedSlot A j = u := Subtype.ext hj
  refine ⟨j, he.symm ▸ ?_⟩
  exact (H.connectedComponentMk v).reachable_of_mem_supp (show v ∈
    (H.connectedComponentMk v).supp from rfl) hu

/-- With two components, the third anchor cannot reach the retained hub. -/
theorem retained_remote_not_reachable
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices})
    (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj]
    (hcover : ∀ v, ∃ j, H.Reachable v (B.retainedSlot A j))
    (hp : H.Adj B.completedHub (B.retainedSlot A 0))
    (hq : H.Adj B.completedHub (B.retainedSlot A 1))
    (hc : Fintype.card H.ConnectedComponent = 2) :
    ¬ H.Reachable B.completedHub (B.retainedSlot A 2) := by
  intro hr
  have all (v : B.StarSurvivor) : H.Reachable v B.completedHub := by
    obtain ⟨j, hj⟩ := hcover v
    fin_cases j
    · exact hj.trans hp.reachable.symm
    · exact hj.trans hq.reachable.symm
    · exact hj.trans hr.symm
  have he (C : H.ConnectedComponent) : C = H.connectedComponentMk B.completedHub := by
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h v => exact SimpleGraph.ConnectedComponent.sound (all v)
  have hle : Fintype.card H.ConnectedComponent ≤ 1 :=
    Fintype.card_le_one_iff.mpr (fun C D => (he C).trans (he D).symm)
  omega

/-- Any old walk visiting the hub avoids the remote anchor. No simplicity
assumption is needed for this component-level fact. -/
theorem retained_hub_walk_avoids_remote
    (H : SimpleGraph B.StarSurvivor) (r : B.StarSurvivor)
    (hr : ¬ H.Reachable B.completedHub r)
    {u v : B.StarSurvivor} (P : H.Walk u v)
    (hx : B.completedHub ∈ P.support) : r ∉ P.support := by
  intro hm
  exact hr ((P.takeUntil B.completedHub hx).reachable.symm.trans
    (P.takeUntil r hm).reachable)

/-- A remote endpoint carrier avoids every vertex reachable from the hub. -/
theorem retained_remote_walk_avoids_hub_component
    (H : SimpleGraph B.StarSurvivor) (r : B.StarSurvivor)
    (hr : ¬ H.Reachable B.completedHub r)
    {u v : B.StarSurvivor} (P : H.Walk u v) (hend : v = r)
    (w : B.StarSurvivor) (hw : H.Reachable B.completedHub w) :
    w ∉ P.support := by
  intro hm
  subst v
  exact hr (hw.trans (P.dropUntil w hm).reachable)

end Gallai.WholeBowtie
