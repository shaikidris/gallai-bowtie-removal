/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.SyndromeStarCap
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-! # Component coverage and the three-component bound for syndrome spokes -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- A retained auxiliary changing only anchor incidences cannot acquire an
anchor-free component, provided the retained hub reaches an anchor. -/
theorem retained_component_anchor_of_off_hub_edges
    (H : SimpleGraph B.StarSurvivor) (hc : G.Connected)
    (hh : ∃ a, H.Adj B.completedHub a ∧ a.val ∈ B.anchors)
    (hkeep : ∀ u v : B.StarSurvivor, u.val ≠ B.label 0 → u.val ∉ B.anchors →
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
    exact ⟨hw, C.mem_supp_of_adj_mem_supp hu (hkeep u ⟨w, hw⟩ hu0 (hn u hu) ha)⟩
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


/-- A nonempty syndrome ensures that every component still meets an anchor. -/
theorem syndromeStar_component_anchor (hc : G.Connected) (hs : B.syndrome.Nonempty)
    (C : B.syndromeStar.ConnectedComponent) :
    ∃ u : B.StarSurvivor, u ∈ C.supp ∧ u.val ∈ B.anchors := by
  apply B.retained_component_anchor_of_off_hub_edges B.syndromeStar hc ?_ ?_ C
  · obtain ⟨a,ha⟩ := hs
    have hA := B.syndrome_subset_anchors ha
    exact ⟨⟨a,B.anchor_survives hA⟩,(B.syndromeStar_hub_adj _).mpr ha,hA⟩
  · intro u v hu hn ha
    have hv : v.val ≠ B.label 0 := by
      intro he
      have hrow : u.val ∈ B.row 0 := (B.mem_row 0 _).mpr
        ⟨he ▸ ha.symm,fun h => hu (B.survivor_mem_vertices u h)⟩
      exact hn (B.row_subset_anchors 0 hrow)
    exact (B.syndromeStar_away_adj u v hu hv).mpr ha

/-- With at most four anchors, the two joined syndrome anchors save at least
one component. This includes disconnected auxiliaries and isolated anchors. -/
theorem syndromeStar_components_le_three (hc : G.Connected)
    (hA : B.anchors.card ≤ 4) (hs : B.syndrome.card = 2) :
    Fintype.card B.syndromeStar.ConnectedComponent ≤ 3 := by
  classical
  have hnon : B.syndrome.Nonempty := Finset.card_pos.mp (by omega)
  let f : B.anchors → B.syndromeStar.ConnectedComponent := fun a =>
    B.syndromeStar.connectedComponentMk ⟨a.val,B.anchor_survives a.property⟩
  have hf : Function.Surjective f := by
    intro C
    obtain ⟨u,hu,ha⟩ := B.syndromeStar_component_anchor hc hnon C
    exact ⟨⟨u.val,ha⟩,(SimpleGraph.ConnectedComponent.eq_of_common_vertex hu
      (show u ∈ (f ⟨u.val,ha⟩).supp from rfl)).symm⟩
  by_contra hn
  have hle := Fintype.card_le_of_surjective f hf
  have hcard : Fintype.card B.anchors =
      Fintype.card B.syndromeStar.ConnectedComponent := by
    rw [Fintype.card_coe] at hle ⊢
    omega
  have hi := hf.injective_of_finite (Fintype.equivOfCardEq hcard)
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < B.syndrome.card by omega)
  have haA := B.syndrome_subset_anchors ha
  have hbA := B.syndrome_subset_anchors hb
  have he : f ⟨a,haA⟩ = f ⟨b,hbA⟩ := SimpleGraph.ConnectedComponent.sound
    (((B.syndromeStar_hub_adj ⟨a,B.anchor_survives haA⟩).mpr ha).symm.reachable.trans
      ((B.syndromeStar_hub_adj ⟨b,B.anchor_survives hbA⟩).mpr hb).reachable)
  exact hab (congrArg (fun z : B.anchors => z.val) (hi he))

end Gallai.WholeBowtie
