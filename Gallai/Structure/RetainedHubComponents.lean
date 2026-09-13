/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.RetainedHubCap
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-! # Anchor coverage of retained auxiliary components -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- A retained auxiliary changing only anchor incidences cannot acquire an
anchor-free component, provided the retained hub reaches an anchor. -/
theorem retained_component_anchor_of_edges
    (H : SimpleGraph B.StarSurvivor) (hc : G.Connected)
    (hh : ∃ a, H.Adj B.completedHub a ∧ a.val ∈ B.anchors)
    (hkeep : ∀ u v : B.StarSurvivor, u.val ∉ B.anchors →
      G.Adj u.val v.val → H.Adj u v) (C : H.ConnectedComponent) :
    ∃ u : B.StarSurvivor, u ∈ C.supp ∧ u.val ∈ B.anchors := by
  classical
  by_contra hn
  push Not at hn
  have hhub : B.completedHub ∉ C.supp := by
    intro h
    obtain ⟨a, ha, hA⟩ := hh
    exact hn a (C.mem_supp_of_adj_mem_supp h ha) hA
  have step (u : B.StarSurvivor) (hu : u ∈ C.supp) (w : V)
      (ha : G.Adj u.val w) :
      ∃ hw : w ∉ (Finset.univ.erase 0).map B.label,
        (⟨w, hw⟩ : B.StarSurvivor) ∈ C.supp := by
    have hu0 : u.val ≠ B.label 0 := by
      intro he
      have he' : u = B.completedHub := Subtype.ext he
      exact hhub (he' ▸ hu)
    have hw : w ∉ (Finset.univ.erase 0).map B.label := by
      intro hm
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hm
      exact hn u hu ((B.mem_anchors _).mpr ⟨i, (B.mem_row i _).mpr
        ⟨ha.symm, fun h => hu0 (B.survivor_mem_vertices u h)⟩⟩)
    exact ⟨hw, C.mem_supp_of_adj_mem_supp hu (hkeep u ⟨w, hw⟩ (hn u hu) ha)⟩
  have along {v w : V} (walk : G.Walk v w) :
      (∃ hv : v ∉ (Finset.univ.erase 0).map B.label,
        (⟨v, hv⟩ : B.StarSurvivor) ∈ C.supp) →
      (∃ hw : w ∉ (Finset.univ.erase 0).map B.label,
        (⟨w, hw⟩ : B.StarSurvivor) ∈ C.supp) := by
    induction walk with
    | nil => exact id
    | @cons v w t hvw walk ih =>
      rintro ⟨hv, hvC⟩
      exact ih (step ⟨v, hv⟩ hvC w hvw)
  obtain ⟨u, hu⟩ := C.nonempty_supp
  obtain ⟨walk⟩ := hc u.val (B.label 0)
  obtain ⟨_, h⟩ := along walk ⟨u.property, hu⟩
  exact hhub h

/-- Private deletion with a nonempty hub row has no anchor-free component. -/
theorem retainedHub_component_anchor (hc : G.Connected) (hr : (B.row 0).Nonempty)
    (C : B.retainedHubGraph.ConnectedComponent) :
    ∃ u : B.StarSurvivor, u ∈ C.supp ∧ u.val ∈ B.anchors := by
  apply B.retained_component_anchor_of_edges B.retainedHubGraph hc _ (fun _ _ _ h => h) C
  obtain ⟨a, ha⟩ := hr
  have hA := (B.mem_anchors _).mpr ⟨0, ha⟩
  exact ⟨⟨a, B.anchor_survives hA⟩, (B.retainedHub_adj _).mpr ha, hA⟩

/-- Toggling an actual syndrome pair preserves anchor coverage of components. -/
theorem retainedHubRepair_component_anchor (p q : B.StarSurvivor)
    (hs : B.privateDeletionSyndrome = {p,q})
    (hc : G.Connected) (hr : (B.row 0).Nonempty)
    (C : (B.retainedHubRepair p q).ConnectedComponent) :
    ∃ u : B.StarSurvivor, u ∈ C.supp ∧ u.val ∈ B.anchors := by
  have hpA := B.privateDeletionSyndrome_anchor p (by simp [hs])
  have hqA := B.privateDeletionSyndrome_anchor q (by simp [hs])
  have keep (u v : B.StarSurvivor) (hu : u.val ∉ B.anchors)
      (ha : G.Adj u.val v.val) : (B.retainedHubRepair p q).Adj u v := by
    have hup : u ≠ p := fun he => hu (he ▸ hpA)
    have huq : u ≠ q := fun he => hu (he ▸ hqA)
    exact ((toggleEdge_adj_of_ne B.retainedHubGraph p q v u hup huq).mpr ha.symm).symm
  apply B.retained_component_anchor_of_edges _ hc _ keep C
  obtain ⟨a, ha⟩ := hr
  have hA := (B.mem_anchors _).mpr ⟨0, ha⟩
  exact ⟨⟨a, B.anchor_survives hA⟩,
    keep B.completedHub _ B.hub_not_mem_anchors ((B.mem_row 0 _).mp ha).1, hA⟩

/-- Three anchors cover at most two components when two distinct row anchors
remain joined through the retained hub. -/
theorem retained_components_le_two_of_coverage
    (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj]
    (hA : B.anchors.card ≤ 3) (hr : 2 ≤ (B.row 0).card)
    (hcover : ∀ C : H.ConnectedComponent,
      ∃ u : B.StarSurvivor, u ∈ C.supp ∧ u.val ∈ B.anchors)
    (hspoke : ∀ u : B.StarSurvivor, u.val ∈ B.row 0 → H.Adj B.completedHub u) :
    Fintype.card H.ConnectedComponent ≤ 2 := by
  classical
  let f : B.anchors → H.ConnectedComponent := fun a =>
    H.connectedComponentMk ⟨a.val, B.anchor_survives a.property⟩
  have hf : Function.Surjective f := by
    intro C
    obtain ⟨u, hu, ha⟩ := hcover C
    exact ⟨⟨u.val, ha⟩, (SimpleGraph.ConnectedComponent.eq_of_common_vertex hu
      (show u ∈ (f ⟨u.val, ha⟩).supp from rfl)).symm⟩
  by_contra hn
  have hle := Fintype.card_le_of_surjective f hf
  have hcard : Fintype.card B.anchors = Fintype.card H.ConnectedComponent := by
    rw [Fintype.card_coe] at hle ⊢
    omega
  have hi := hf.injective_of_finite (Fintype.equivOfCardEq hcard)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < (B.row 0).card by omega)
  have haA := (B.mem_anchors _).mpr ⟨0, ha⟩
  have hbA := (B.mem_anchors _).mpr ⟨0, hb⟩
  have he : f ⟨a, haA⟩ = f ⟨b, hbA⟩ := SimpleGraph.ConnectedComponent.sound
    ((hspoke ⟨a, B.anchor_survives haA⟩ ha).symm.reachable.trans
      (hspoke ⟨b, B.anchor_survives hbA⟩ hb).reachable)
  exact hab (congrArg (fun z : B.anchors => z.val) (hi he))

/-- The unmodified retained star has at most two components. -/
theorem retainedHub_components_le_two (hc : G.Connected)
    (hA : B.anchors.card ≤ 3) (hr : 2 ≤ (B.row 0).card) :
    Fintype.card B.retainedHubGraph.ConnectedComponent ≤ 2 := by
  have hne := Finset.card_pos.mp (show 0 < (B.row 0).card by omega)
  exact B.retained_components_le_two_of_coverage _ hA hr
    (B.retainedHub_component_anchor hc hne) (fun u hu => (B.retainedHub_adj u).mpr hu)

/-- Original and synthetic anchor repairs both preserve the two-component bound. -/
theorem retainedHubRepair_components_le_two (p q : B.StarSurvivor)
    (hs : B.privateDeletionSyndrome = {p,q}) (hc : G.Connected)
    (hA : B.anchors.card ≤ 3) (hr : 2 ≤ (B.row 0).card) :
    Fintype.card (B.retainedHubRepair p q).ConnectedComponent ≤ 2 := by
  have hne := Finset.card_pos.mp (show 0 < (B.row 0).card by omega)
  apply B.retained_components_le_two_of_coverage _ hA hr
    (B.retainedHubRepair_component_anchor p q hs hc hne)
  intro u hu
  have hp : B.completedHub ≠ p := by
    intro h
    exact B.retainedHub_not_syndrome (by simp [hs, h])
  have hq : B.completedHub ≠ q := by
    intro h
    exact B.retainedHub_not_syndrome (by simp [hs, h])
  exact ((toggleEdge_adj_of_ne B.retainedHubGraph p q u B.completedHub hp hq).mpr
    ((B.retainedHub_adj u).mpr hu).symm).symm

end Gallai.WholeBowtie
