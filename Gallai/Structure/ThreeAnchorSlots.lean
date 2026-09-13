/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ThreeAnchorRows
import Mathlib.Data.Fintype.EquivFin

/-! # Existing-vertex slots for an at-most-three-anchor boundary -/

namespace Gallai.WholeBowtie

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Extend the actual boundary to three existing retained slots, never new vertices. -/
theorem exists_threeAnchorSlots (hA : B.anchors.card ≤ 3)
    (hn : 3 ≤ Fintype.card {v : V // v ∉ B.vertices}) :
    ∃ A : Fin 3 ↪ {v : V // v ∉ B.vertices},
      ∀ v ∈ B.anchors, ∃ j, (A j).val = v := by
  classical
  let f : B.anchors ↪ {v : V // v ∉ B.vertices} :=
    ⟨B.anchorPunctureVertex, fun a b h => Subtype.ext
      (congrArg (fun z : {v : V // v ∉ B.vertices} => z.val) h)⟩
  let S := Finset.univ.map f
  have hS : S.card ≤ 3 := by simpa only [S, Finset.card_map, Finset.card_univ,
    Fintype.card_coe] using hA
  obtain ⟨T, hST, _, hT⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ S) hS (by simpa only [Finset.card_univ] using hn)
  let e : Fin 3 ≃ T := (Fintype.equivFinOfCardEq
    (by simpa only [Fintype.card_coe] using hT)).symm
  let A : Fin 3 ↪ {v : V // v ∉ B.vertices} :=
    e.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨A, ?_⟩
  intro v hv
  have ht : f ⟨v, hv⟩ ∈ T := hST (Finset.mem_map.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩)
  obtain ⟨j, hj⟩ := e.surjective ⟨f ⟨v, hv⟩, ht⟩
  refine ⟨j, ?_⟩
  exact congrArg (fun u : T => u.val.val) hj

/-- Two distinct odd anchors and the designated even retained vertex already
provide the three existing vertices needed for an unused slot. -/
theorem three_retained_of_anchor_pair (p q y : {v : V // v ∉ B.vertices})
    (hp : p.val ∈ B.anchors) (hq : q.val ∈ B.anchors) (hpq : p ≠ q)
    (hy : Even (G.degree y.val)) :
    3 ≤ Fintype.card {v : V // v ∉ B.vertices} := by
  classical
  have hpy : p ≠ y := by
    intro h
    subst y
    exact Nat.not_even_iff_odd.mpr (B.odd_degree_anchor hp) hy
  have hqy : q ≠ y := by
    intro h
    subst y
    exact Nat.not_even_iff_odd.mpr (B.odd_degree_anchor hq) hy
  have hc : ({p, q, y} : Finset {v : V // v ∉ B.vertices}).card = 3 := by
    simp [hpq, hpy, hqy]
  calc
    3 = ({p, q, y} : Finset {v : V // v ∉ B.vertices}).card := hc.symm
    _ ≤ (Finset.univ : Finset {v : V // v ∉ B.vertices}).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = _ := Finset.card_univ

/-- In the pair-syndrome branch, all slot and exact-state assumptions are produced. -/
theorem exists_threeAnchorSlots_state (hA : B.anchors.card ≤ 3)
    (p q y : {v : V // v ∉ B.vertices}) (hpq : p ≠ q)
    (hs : B.syndrome = {p.val, q.val}) (hy : Even (G.degree y.val)) :
    ∃ (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : Certificate.ThreeAnchor.State),
      (∀ v ∈ B.anchors, ∃ j, (A j).val = v) ∧
      ∀ i v, v ∈ B.row i ↔
        ∃ j, (Certificate.ThreeAnchor.rowMask (s i)).val.testBit j.val = true ∧
          (A j).val = v := by
  have hp := B.syndrome_subset_anchors (show p.val ∈ B.syndrome by simp [hs])
  have hq := B.syndrome_subset_anchors (show q.val ∈ B.syndrome by simp [hs])
  obtain ⟨A, hcover⟩ := B.exists_threeAnchorSlots hA
    (B.three_retained_of_anchor_pair p q y hp hq hpq hy)
  obtain ⟨s, hrows⟩ := B.exists_threeAnchorState A hcover
  exact ⟨A, s, hcover, hrows⟩

/-- Connectedness and one retained even vertex force two odd anchors, hence at
least three retained vertices. This also covers the zero-syndrome branch. -/
theorem three_retained_of_connected (hc : G.Connected)
    (y : {v : V // v ∉ B.vertices}) (hy : Even (G.degree y.val)) :
    3 ≤ Fintype.card {v : V // v ∉ B.vertices} := by
  obtain ⟨u, _, hu⟩ := B.puncture_component_anchor hc (B.puncture.connectedComponentMk y)
  obtain ⟨i, hi⟩ := (B.mem_anchors u.val).mp hu
  have hpos : 0 < (B.row i).card := Finset.card_pos.mpr ⟨u.val, hi⟩
  have hev := B.even_card_row i
  have htwo : 1 < (B.row i).card := by
    rw [Nat.even_iff] at hev
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp htwo
  have hpA := B.row_subset_anchors i hp
  have hqA := B.row_subset_anchors i hq
  exact B.three_retained_of_anchor_pair
    (B.anchorPunctureVertex ⟨p, hpA⟩) (B.anchorPunctureVertex ⟨q, hqA⟩) y hpA hqA
    (fun h => hpq (congrArg (fun z : {v : V // v ∉ B.vertices} => z.val) h)) hy

/-- Complete existing-slot and exact-row production for every connected
at-most-three-anchor instance with a retained designated even vertex. -/
theorem exists_threeAnchorSlots_state_connected (hc : G.Connected)
    (hA : B.anchors.card ≤ 3) (y : {v : V // v ∉ B.vertices})
    (hy : Even (G.degree y.val)) :
    ∃ (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : Certificate.ThreeAnchor.State),
      (∀ v ∈ B.anchors, ∃ j, (A j).val = v) ∧
      ∀ i v, v ∈ B.row i ↔
        ∃ j, (Certificate.ThreeAnchor.rowMask (s i)).val.testBit j.val = true ∧
          (A j).val = v := by
  obtain ⟨A, hcover⟩ := B.exists_threeAnchorSlots hA (B.three_retained_of_connected hc y hy)
  obtain ⟨s, hrows⟩ := B.exists_threeAnchorState A hcover
  exact ⟨A, s, hcover, hrows⟩

end Gallai.WholeBowtie
