/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.EdgeToggle
import Gallai.Structure.Incidence

/-! # Whole-bowtie deletion repaired at a two-vertex syndrome

The repair toggles the actual anchor edge, so both original-edge deletion and
synthetic-edge insertion are covered without assuming either status.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The whole-deletion auxiliary with its actual syndrome-pair edge toggled. -/
abbrev pairRepairedPuncture (p q : {v : V // v ∉ B.vertices}) :
    SimpleGraph {v : V // v ∉ B.vertices} := toggleEdge B.puncture p q

/-- Every retained vertex recovers its original parity, in either repair status. -/
theorem pairRepairedPuncture_even_iff (p q : {v : V // v ∉ B.vertices})
    (hne : p ≠ q) (hs : B.syndrome = {p.val, q.val})
    (v : {v : V // v ∉ B.vertices}) :
    Even ((B.pairRepairedPuncture p q).degree v) ↔ Even (G.degree v.val) := by
  have hp : B.puncture.degree v % 2 = G.degree v.val % 2 ↔ ¬ (v = p ∨ v = q) := by
    simpa only [hs, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] using
      B.puncture_parity_eq_iff v
  rw [toggleEdge_even_iff B.puncture p q hne v]
  by_cases hv : v = p ∨ v = q
  · have hn : B.puncture.degree v % 2 ≠ G.degree v.val % 2 := fun he => hp.mp he hv
    simp only [if_pos hv, Nat.even_iff]
    omega
  · have he := hp.mpr hv
    simp only [if_neg hv, Nat.even_iff]
    omega

/-- Parity repair introduces no even neighbour: the repair ends are original odd anchors. -/
theorem pairRepairedPuncture_eDegree_le (p q : {v : V // v ∉ B.vertices})
    (hne : p ≠ q) (hs : B.syndrome = {p.val, q.val})
    (v : {v : V // v ∉ B.vertices}) :
    eDegree (B.pairRepairedPuncture p q) v ≤ eDegree G v.val := by
  have hp : Odd (G.degree p.val) := B.odd_degree_anchor
    (B.syndrome_subset_anchors (by simp [hs]))
  have hq : Odd (G.degree q.val) := B.odd_degree_anchor
    (B.syndrome_subset_anchors (by simp [hs]))
  have hsub : (evenNeighbors (B.pairRepairedPuncture p q) v).map
      (Function.Embedding.subtype _) ⊆ evenNeighbors G v.val := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨hadj, heven⟩ := (mem_evenNeighbors _ _).mp hu
    have he := (B.pairRepairedPuncture_even_iff p q hne hs u).mp heven
    have hup : u ≠ p := by
      intro h
      subst u
      exact (Nat.not_even_iff_odd.mpr hp) he
    have huq : u ≠ q := by
      intro h
      subst u
      exact (Nat.not_even_iff_odd.mpr hq) he
    exact (mem_evenNeighbors _ _).mpr
      ⟨(toggleEdge_adj_of_ne B.puncture p q v u hup huq).mp hadj, he⟩
  simpa only [Finset.card_map, eDegree] using Finset.card_le_card hsub

/-- Only the designated outside exception can remain after syndrome-pair repair. -/
theorem pairRepairedPuncture_cap (p q : {v : V // v ∉ B.vertices})
    (hne : p ≠ q) (hs : B.syndrome = {p.val, q.val})
    (y : {v : V // v ∉ B.vertices})
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∀ v, Even ((B.pairRepairedPuncture p q).degree v) → v ≠ y →
      eDegree (B.pairRepairedPuncture p q) v ≤ 3 := by
  intro v hv hvy
  apply (B.pairRepairedPuncture_eDegree_le p q hne hs v).trans
  apply hcap v.val ((B.pairRepairedPuncture_even_iff p q hne hs v).mp hv)
  · intro hx
    apply v.property
    rw [hx]
    exact (B.mem_vertices _).mpr (B.label_mem_component 0)
  · exact fun h => hvy (Subtype.ext h)

end Gallai.WholeBowtie
