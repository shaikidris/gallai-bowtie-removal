/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.RetainedHubCap
import Gallai.Inputs.ZeroSyndromeAssembly

/-! # Componentwise endpoint supply for retained-hub auxiliaries -/
namespace Gallai

private theorem retained_endpoint_sum_of_cap {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (y : W)
    (hp : 0 < H.degree y) (hy : Even (H.degree y))
    (hcap : ∀ v, Even (H.degree v) → v ≠ y → eDegree H v ≤ 3) :
    ∃ D : Decomposition H,
      D.size ≤ ∑ C : H.ConnectedComponent, (Fintype.card C.supp + 1) / 2 ∧
      2 ≤ D.endpointCount y := by
  classical
  obtain ⟨D, hb, he⟩ := component_endpoint_of_cap H y (H.connectedComponentMk y)
    rfl hp hy hcap
  apply endpoint_budget_of_components H y
    (fun C => (Fintype.card C.supp + 1) / 2) D hb he
  intro C hC
  apply other_component_ceiling H y C _ hcap
  intro hyC
  exact hC (SimpleGraph.ConnectedComponent.eq_of_common_vertex hyC rfl)

namespace WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Non-hub even survivors have no incidence with deleted private vertices. -/
theorem retainedHub_degree_of_even (v : B.StarSurvivor)
    (hx : v.val ≠ B.label 0) (hv : Even (G.degree v.val)) :
    B.retainedHubGraph.degree v = G.degree v.val := by
  have hz : G.neighborFinset v.val ∩ (Finset.univ.erase 0).map B.label = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨ha, hm⟩ := Finset.mem_inter.mp hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hm
    have hA := (B.mem_anchors _).mpr ⟨i, (B.mem_row i _).mpr
      ⟨((G.mem_neighborFinset _ _).mp ha).symm,
        fun h => hx (B.survivor_mem_vertices v h)⟩⟩
    exact (Nat.not_even_iff_odd.mpr (B.odd_degree_anchor hA)) hv
  have hd := B.privateDeletion_degree_add_deleted (Finset.univ.erase 0) v
  simpa only [hz, Finset.card_empty, Nat.add_zero] using hd

/-- Odd repair ends cannot change a non-hub even survivor's degree. -/
theorem retainedHubRepair_degree_of_even (p q : B.StarSurvivor)
    (hs : B.privateDeletionSyndrome = {p,q}) (v : B.StarSurvivor)
    (hx : v.val ≠ B.label 0) (hv : Even (G.degree v.val)) :
    (B.retainedHubRepair p q).degree v = G.degree v.val := by
  have hp : v ≠ p := by
    intro he
    subst v
    exact (Nat.not_even_iff_odd.mpr (B.odd_degree_anchor
      (B.privateDeletionSyndrome_anchor p (by simp [hs])))) hv
  have hq : v ≠ q := by
    intro he
    subst v
    exact (Nat.not_even_iff_odd.mpr (B.odd_degree_anchor
      (B.privateDeletionSyndrome_anchor q (by simp [hs])))) hv
  exact (toggleEdge_degree_of_ne B.retainedHubGraph p q v hp hq).trans
    (B.retainedHub_degree_of_even v hx hv)

/-- Pair repair supplies the exact component-ceiling sum and exposes y twice. -/
theorem retainedHubRepair_endpoint_sum (p q : B.StarSurvivor) (hne : p ≠ q)
    (hs : B.privateDeletionSyndrome = {p,q}) (hrow : (B.row 0).card ≤ 3)
    (hc : G.Connected) (y : B.StarSurvivor) (hx : y.val ≠ B.label 0)
    (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ D : Decomposition (B.retainedHubRepair p q),
      D.size ≤ ∑ C : (B.retainedHubRepair p q).ConnectedComponent,
        (Fintype.card C.supp + 1) / 2 ∧ 2 ≤ D.endpointCount y := by
  have : Nontrivial V := ⟨⟨y.val, B.label 0, hx⟩⟩
  apply retained_endpoint_sum_of_cap
  · rw [B.retainedHubRepair_degree_of_even p q hs y hx hy]
    exact hc.preconnected.degree_pos_of_nontrivial y.val
  · exact (B.retainedHubRepair_even_iff p q hne hs y).mpr hy
  · exact B.retainedHubRepair_cap p q hne hs hrow y hcap

/-- Empty syndrome has the same componentwise endpoint supply without a toggle. -/
theorem retainedHub_endpoint_sum (hs : B.privateDeletionSyndrome = ∅)
    (hrow : (B.row 0).card ≤ 3) (hc : G.Connected)
    (y : B.StarSurvivor) (hx : y.val ≠ B.label 0) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ D : Decomposition B.retainedHubGraph,
      D.size ≤ ∑ C : B.retainedHubGraph.ConnectedComponent,
        (Fintype.card C.supp + 1) / 2 ∧ 2 ≤ D.endpointCount y := by
  have : Nontrivial V := ⟨⟨y.val, B.label 0, hx⟩⟩
  apply retained_endpoint_sum_of_cap
  · rw [B.retainedHub_degree_of_even y hx hy]
    exact hc.preconnected.degree_pos_of_nontrivial y.val
  · exact (B.retainedHub_even_iff hs y).mpr hy
  · exact B.retainedHub_cap hs hrow y hcap

end WholeBowtie
end Gallai
