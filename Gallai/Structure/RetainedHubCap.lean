/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.RetainedHubAuxiliary

/-! # One-exception degree caps after retained-hub repair -/

namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The hub loses four edges, so it never belongs to the private syndrome. -/
theorem retainedHub_not_syndrome : B.completedHub ∉ B.privateDeletionSyndrome := by
  apply (B.retainedHub_parity_eq_iff B.completedHub).mp
  rw [B.retainedHub_degree, (Nat.even_iff.mp (B.even_card_row 0))]
  exact (Nat.even_iff.mp (B.even_degree_label 0)).symm

/-- Every actual repair end is an original odd anchor. -/
theorem privateDeletionSyndrome_anchor (v : B.StarSurvivor)
    (hv : v ∈ B.privateDeletionSyndrome) : v.val ∈ B.anchors := by
  have hn : v.val ≠ B.label 0 := by
    intro h
    have he : v = B.completedHub := Subtype.ext h
    exact B.retainedHub_not_syndrome (he ▸ hv)
  have ho : Odd (G.neighborFinset v.val ∩
      (Finset.univ.erase 0).map B.label).card := (Finset.mem_filter.mp hv).2
  have hp : 0 < (G.neighborFinset v.val ∩
      (Finset.univ.erase 0).map B.label).card := by
    have := Nat.odd_iff.mp ho
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hp
  obtain ⟨ha, hm⟩ := Finset.mem_inter.mp hw
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hm
  exact (B.mem_anchors _).mpr ⟨i, (B.mem_row i _).mpr
    ⟨((G.mem_neighborFinset _ _).mp ha).symm,
      fun h => hn (B.survivor_mem_vertices v h)⟩⟩

/-- Toggling odd anchor ends cannot introduce an even neighbour. -/
theorem retainedHubRepair_eDegree_le (p q : B.StarSurvivor) (hne : p ≠ q)
    (hs : B.privateDeletionSyndrome = {p,q}) (v : B.StarSurvivor) :
    eDegree (B.retainedHubRepair p q) v ≤ eDegree G v.val := by
  have hp := B.odd_degree_anchor (B.privateDeletionSyndrome_anchor p (by simp [hs]))
  have hq := B.odd_degree_anchor (B.privateDeletionSyndrome_anchor q (by simp [hs]))
  have hsub : (evenNeighbors (B.retainedHubRepair p q) v).map
      (Function.Embedding.subtype _) ⊆ evenNeighbors G v.val := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨ha, he⟩ := (mem_evenNeighbors _ _).mp hu
    have he' := (B.retainedHubRepair_even_iff p q hne hs u).mp he
    have hup : u ≠ p := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hp) he'
    have huq : u ≠ q := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hq) he'
    exact (mem_evenNeighbors _ _).mpr
      ⟨(toggleEdge_adj_of_ne B.retainedHubGraph p q v u hup huq).mp ha, he'⟩
  simpa only [Finset.card_map, eDegree] using Finset.card_le_card hsub

/-- Pair repair leaves the hub degree unchanged. -/
theorem retainedHubRepair_degree (p q : B.StarSurvivor)
    (hs : B.privateDeletionSyndrome = {p,q}) :
    (B.retainedHubRepair p q).degree B.completedHub = (B.row 0).card := by
  have hp : B.completedHub ≠ p := by
    intro h
    exact B.retainedHub_not_syndrome (by simp [hs, h])
  have hq : B.completedHub ≠ q := by
    intro h
    exact B.retainedHub_not_syndrome (by simp [hs, h])
  exact (toggleEdge_degree_of_ne B.retainedHubGraph p q B.completedHub hp hq).trans
    B.retainedHub_degree

/-- With a two-spoke retained hub only the designated exception remains. -/
theorem retainedHubRepair_cap (p q : B.StarSurvivor) (hne : p ≠ q)
    (hs : B.privateDeletionSyndrome = {p,q}) (hrow : (B.row 0).card ≤ 3)
    (y : B.StarSurvivor)
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∀ v, Even ((B.retainedHubRepair p q).degree v) → v ≠ y →
      eDegree (B.retainedHubRepair p q) v ≤ 3 := by
  intro v he hny
  by_cases hx : v.val = B.label 0
  · have hv : v = B.completedHub := Subtype.ext hx
    subst v
    apply (eDegree_le_degree _).trans
    rw [B.retainedHubRepair_degree p q hs]
    exact hrow
  · exact (B.retainedHubRepair_eDegree_le p q hne hs v).trans
      (hcap v.val ((B.retainedHubRepair_even_iff p q hne hs v).mp he) hx
        (fun h => hny (Subtype.ext h)))

/-- Empty-syndrome private deletion also introduces no even neighbour. -/
theorem retainedHub_eDegree_le (hs : B.privateDeletionSyndrome = ∅)
    (v : B.StarSurvivor) : eDegree B.retainedHubGraph v ≤ eDegree G v.val := by
  have hsub : (evenNeighbors B.retainedHubGraph v).map
      (Function.Embedding.subtype _) ⊆ evenNeighbors G v.val := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨ha, he⟩ := (mem_evenNeighbors _ _).mp hu
    exact (mem_evenNeighbors _ _).mpr ⟨ha, (B.retainedHub_even_iff hs u).mp he⟩
  simpa only [Finset.card_map, eDegree] using Finset.card_le_card hsub

/-- The one-exception cap when no anchor repair is needed. -/
theorem retainedHub_cap (hs : B.privateDeletionSyndrome = ∅)
    (hrow : (B.row 0).card ≤ 3) (y : B.StarSurvivor)
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∀ v, Even (B.retainedHubGraph.degree v) → v ≠ y →
      eDegree B.retainedHubGraph v ≤ 3 := by
  intro v he hny
  by_cases hx : v.val = B.label 0
  · have hv : v = B.completedHub := Subtype.ext hx
    subst v
    apply (eDegree_le_degree _).trans
    rw [B.retainedHub_degree]
    exact hrow
  · exact (B.retainedHub_eDegree_le hs v).trans
      (hcap v.val ((B.retainedHub_even_iff hs v).mp he) hx
        (fun h => hny (Subtype.ext h)))

end Gallai.WholeBowtie
