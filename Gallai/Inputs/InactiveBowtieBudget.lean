/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.InactiveBowtieDeletion
import Gallai.Inputs.OneException

/-! # Endpoint budget of the actual inactive-pair auxiliary

Deleting two inactive private vertices produces no new even vertex, leaves
hub E-degree at most two, and preserves the external designated vertex.
The proved one-exception theorem therefore supplies a decomposition with
one full path of slack for restoration. No auxiliary witness is assumed.
-/

namespace Gallai.WholeBowtie

open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Empty deleted rows ensure that a retained even vertex was originally even. -/
theorem privateDeletion_even_original (I : Finset (Fin 5))
    (hi : ∀ i ∈ I, B.row i = ∅) (v : {v : V // v ∉ I.map B.label})
    (hv : Even ((B.privateDeletion I).degree v)) : Even (G.degree v.val) := by
  by_cases hb : v.val ∈ B.vertices
  · obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hb
    change B.label j = v.val at hj
    exact hj ▸ B.even_degree_label j
  · rwa [B.privateDeletion_degree_outside I hi v hb] at hv

/-- Partial inactive deletion cannot increase the E-degree of a retained vertex. -/
theorem privateDeletion_eDegree_le (I : Finset (Fin 5))
    (hi : ∀ i ∈ I, B.row i = ∅) (v : {v : V // v ∉ I.map B.label}) :
    eDegree (B.privateDeletion I) v ≤ eDegree G v.val := by
  have hsub : (evenNeighbors (B.privateDeletion I) v).map
      (Function.Embedding.subtype _) ⊆ evenNeighbors G v.val := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨ha, he⟩ := (mem_evenNeighbors v q).mp hq
    exact (mem_evenNeighbors v.val q.val).mpr
      ⟨ha, B.privateDeletion_even_original I hi q he⟩
  simpa only [Finset.card_map, eDegree] using Finset.card_le_card hsub

/-- The retained hub has at most the number of undeleted private even neighbours. -/
theorem privateDeletion_hub_cap (I : Finset (Fin 5)) (h0 : 0 ∉ I)
    (hi : ∀ i ∈ I, B.row i = ∅) :
    eDegree (B.privateDeletion I) ⟨B.label 0, by simpa using h0⟩ ≤ 4 - #I := by
  let x : {v : V // v ∉ I.map B.label} := ⟨B.label 0, by simpa using h0⟩
  have hsub : (evenNeighbors (B.privateDeletion I) x).map
      (Function.Embedding.subtype _) ⊆ ((Finset.univ.erase 0) \ I).map B.label := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨ha, he⟩ := (mem_evenNeighbors x q).mp hq
    have heG := B.privateDeletion_even_original I hi q he
    have hB : q.val ∈ B.vertices := (B.mem_vertices q.val).mpr
      (mem_evenComponent_of_adj B.component (B.label_mem_component 0) ha heG)
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hB
    have hj0 : j ≠ 0 := by
      intro hj0
      have heq : x = q := Subtype.ext (by simpa only [x, hj0] using hj)
      exact ha.ne heq
    have hjI : j ∉ I := by
      intro hji
      exact q.property (Finset.mem_map.mpr ⟨j, hji, hj⟩)
    exact Finset.mem_map.mpr ⟨j,
      Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hj0, Finset.mem_univ _⟩, hjI⟩, hj⟩
  have hI : I ⊆ (Finset.univ.erase (0 : Fin 5)) := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨fun h => h0 (h ▸ hj), Finset.mem_univ _⟩
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_map, Finset.card_sdiff_of_subset hI,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin 5)), Finset.card_univ,
    Fintype.card_fin, eDegree, x] using hc

/-- An actual inactive-pair deletion has an endpoint-rich decomposition and
one path of restoration slack under the manuscript's original hypotheses. -/
theorem privateDeletion_endpoint_budget (I : Finset (Fin 5)) (h0 : 0 ∉ I)
    (hI : #I = 2) (hi : ∀ i ∈ I, B.row i = ∅) (hc : G.Connected)
    (y : V) (hy : y ∉ B.vertices) (hyEven : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y → eDegree G v ≤ 3) :
    ∃ D : Decomposition (B.privateDeletion I),
      D.size + 1 ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount ⟨y, by
        intro h
        obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp h
        exact hy (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩)⟩ := by
  classical
  have hyI : y ∉ I.map B.label := by
    intro h
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp h
    exact hy (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  let Y : {v : V // v ∉ I.map B.label} := ⟨y, hyI⟩
  let X : {v : V // v ∉ I.map B.label} := ⟨B.label 0, by simpa using h0⟩
  have hXY : X ≠ Y := by
    intro h
    have hv : B.label 0 = y := congrArg Subtype.val h
    exact hy (hv ▸ Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩)
  have : Nontrivial {v : V // v ∉ I.map B.label} := ⟨⟨X, Y, hXY⟩⟩
  have hconn := B.privateDeletion_connected I h0 hi hc
  have hYEven : Even ((B.privateDeletion I).degree Y) := by
    rw [B.privateDeletion_degree_outside I hi Y hy]
    exact hyEven
  have hcaps : ∀ v, Even ((B.privateDeletion I).degree v) → v ≠ Y →
      eDegree (B.privateDeletion I) v ≤ 3 := by
    intro v hv hvY
    by_cases hvX : v = X
    · subst v
      have hb := B.privateDeletion_hub_cap I h0 hi
      change eDegree (B.privateDeletion I) X ≤ 4 - #I at hb
      omega
    · exact (B.privateDeletion_eDegree_le I hi v).trans
        (hcap v.val (B.privateDeletion_even_original I hi v hv)
          (fun h => hvX (Subtype.ext h)) (fun h => hvY (Subtype.ext h)))
  obtain ⟨D, hD, hDY⟩ := one_exception_endpoint (B.privateDeletion I) Y hconn
    (hconn.preconnected.degree_pos_of_nontrivial Y) hYEven hcaps
  have hn := B.privateDeletion_card I
  exact ⟨D, by omega, hDY⟩

/-- Literal low activity supplies both the deleted pair and its endpoint-rich
auxiliary decomposition, with one path left for the restoration consumer. -/
theorem low_activity_auxiliary_budget (ha : B.activity ≤ 2) (hc : G.Connected)
    (y : V) (hy : y ∉ B.vertices) (hyEven : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y → eDegree G v ≤ 3) :
    ∃ I : Finset (Fin 5), #I = 2 ∧ 0 ∉ I ∧ (∀ i ∈ I, B.row i = ∅) ∧
      ∃ D : Decomposition (B.privateDeletion I),
        D.size + 1 ≤ (Fintype.card V + 1) / 2 ∧
        ∀ hyI : y ∉ I.map B.label, 2 ≤ D.endpointCount ⟨y, hyI⟩ := by
  obtain ⟨I, hI, h0, hi⟩ := B.exists_inactive_pair ha
  obtain ⟨D, hD, hDy⟩ := B.privateDeletion_endpoint_budget I h0 hI hi hc y hy hyEven hcap
  exact ⟨I, hI, h0, hi, D, hD, fun _ => hDy⟩

end Gallai.WholeBowtie
