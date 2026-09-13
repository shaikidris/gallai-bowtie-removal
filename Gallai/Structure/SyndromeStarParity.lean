/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.SyndromeStar
import Gallai.Structure.Incidence

/-! # Exact degree and parity of the syndrome-spoke auxiliary -/
namespace Gallai.WholeBowtie
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- A non-hub survivor keeps all old outside neighbours and exactly one hub
neighbour when it is an anchor. No anchor-anchor edges are toggled. -/
theorem syndromeStar_neighbors (v : B.StarSurvivor) (hv : v.val ≠ B.label 0) :
    (B.syndromeStar.neighborFinset v).map (Function.Embedding.subtype _) =
      (G.neighborFinset v.val \ B.vertices) ∪
        (if v.val ∈ B.syndrome then {B.label 0} else ∅) := by
  ext w
  constructor
  · intro hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hw
    have ha := (B.syndromeStar.mem_neighborFinset v q).mp hq
    by_cases hq0 : q.val = B.label 0
    · have hhub : q = B.completedHub := Subtype.ext hq0
      have hA := (B.syndromeStar_hub_adj v).mp (hhub ▸ ha.symm)
      exact Finset.mem_union_right _ (by simp [hA, hq0])
    · apply Finset.mem_union_left
      apply Finset.mem_sdiff.mpr
      refine ⟨(G.mem_neighborFinset _ _).mpr
        ((B.syndromeStar_away_adj v q hv hq0).mp ha), ?_⟩
      exact fun h => hq0 (B.survivor_mem_vertices q h)
  · intro hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨ha, hout⟩ := Finset.mem_sdiff.mp hw
      have hs : w ∉ (Finset.univ.erase 0).map B.label := by
        intro h
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp h
        exact hout (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      refine Finset.mem_map.mpr ⟨⟨w, hs⟩, ?_, rfl⟩
      exact (B.syndromeStar.mem_neighborFinset _ _).mpr
        ((B.syndromeStar_away_adj v ⟨w,hs⟩ hv (fun he =>
          hout (Finset.mem_map.mpr ⟨0,Finset.mem_univ _,he.symm⟩))).mpr
          ((G.mem_neighborFinset _ _).mp ha))
    · split_ifs at hw with hA
      · have hw0 : w = B.label 0 := Finset.mem_singleton.mp hw
        subst w
        exact Finset.mem_map.mpr ⟨B.completedHub,
          (B.syndromeStar.mem_neighborFinset _ _).mpr
            ((B.syndromeStar_hub_adj v).mpr hA).symm, rfl⟩
      · exact (Finset.notMem_empty _ hw).elim

/-- Exact parity-restoring degree accounting at every non-hub survivor. -/
theorem syndromeStar_degree_balance (v : B.StarSurvivor) (hv : v.val ≠ B.label 0) :
    B.syndromeStar.degree v + #(G.neighborFinset v.val ∩ B.vertices) =
      G.degree v.val + if v.val ∈ B.syndrome then 1 else 0 := by
  have hd : Disjoint (G.neighborFinset v.val \ B.vertices)
      (if v.val ∈ B.syndrome then {B.label 0} else ∅) := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    split_ifs at hw' with hA
    · have hw0 := Finset.mem_singleton.mp hw'
      exact (Finset.mem_sdiff.mp hw).2 (hw0 ▸
        Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩)
    · exact Finset.notMem_empty _ hw'
  have h := congrArg Finset.card (B.syndromeStar_neighbors v hv)
  rw [Finset.card_map, Finset.card_union_of_disjoint hd] at h
  have hp := Finset.card_sdiff_add_card_inter (G.neighborFinset v.val) B.vertices
  have hs : #(if v.val ∈ B.syndrome then {B.label 0} else ∅) =
      if v.val ∈ B.syndrome then 1 else 0 := by split_ifs <;> simp
  rw [hs] at h
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h hp
  omega

/-- Replacing deleted incidences by syndrome spokes restores every parity,
including the retained hub, since the syndrome has even cardinality. -/
theorem syndromeStar_even_iff (v : B.StarSurvivor) :
    Even (B.syndromeStar.degree v) ↔ Even (G.degree v.val) := by
  by_cases hv : v.val = B.label 0
  · have he : v = B.completedHub := Subtype.ext hv
    rw [he, B.syndromeStar_hub_degree]
    exact iff_of_true B.even_card_syndrome (B.even_degree_label 0)
  · have hout : v.val ∉ B.vertices := fun h => hv (B.survivor_mem_vertices v h)
    have h := B.syndromeStar_degree_balance v hv
    have hm : v.val ∈ B.syndrome ↔
        Odd #(G.neighborFinset v.val ∩ B.vertices) := by
      rw [B.mem_syndrome_iff_odd_column, B.columnCount_eq_deleted_degree v.val hout]
    by_cases hs : v.val ∈ B.syndrome
    · have ho := Nat.odd_iff.mp (hm.mp hs)
      rw [if_pos hs] at h
      simp only [Nat.even_iff]
      omega
    · have ho : ¬ Odd #(G.neighborFinset v.val ∩ B.vertices) := fun hh => hs (hm.mpr hh)
      rw [Nat.odd_iff] at ho
      rw [if_neg hs] at h
      simp only [Nat.even_iff]
      omega

end Gallai.WholeBowtie
