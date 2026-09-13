/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.PairRepairedPuncture
import Gallai.Inputs.ZeroSyndromeComponents

/-! # Componentwise decomposition supply after actual syndrome-pair repair -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Original even vertices lose no edges and are not ends of the repair edge. -/
theorem pairRepairedPuncture_degree_of_even (p q : {v : V // v ∉ B.vertices})
    (hs : B.syndrome = {p.val, q.val}) (v : {v : V // v ∉ B.vertices})
    (hv : Even (G.degree v.val)) :
    (B.pairRepairedPuncture p q).degree v = G.degree v.val := by
  have hp : v ≠ p := by
    intro he
    subst v
    exact Nat.not_even_iff_odd.mpr (B.odd_degree_anchor
      (B.syndrome_subset_anchors (by simp [hs]))) hv
  have hq : v ≠ q := by
    intro he
    subst v
    exact Nat.not_even_iff_odd.mpr (B.odd_degree_anchor
      (B.syndrome_subset_anchors (by simp [hs]))) hv
  exact (toggleEdge_degree_of_ne B.puncture p q v hp hq).trans
    (B.puncture_degree_of_even v hv)

/-- The designated component has a ceiling decomposition exposing y twice. -/
theorem pairRepaired_component_endpoint (p q : {v : V // v ∉ B.vertices})
    (hne : p ≠ q) (hs : B.syndrome = {p.val, q.val}) (hc : G.Connected)
    (y : {v : V // v ∉ B.vertices}) (hy : Even (G.degree y.val))
    (C : (B.pairRepairedPuncture p q).ConnectedComponent) (hyC : y ∈ C.supp)
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ D : Decomposition ((B.pairRepairedPuncture p q).induce C.supp),
      D.size ≤ (Fintype.card C.supp + 1) / 2 ∧ 2 ≤ D.endpointCount ⟨y, hyC⟩ := by
  classical
  have hyx : y.val ≠ B.label 0 := by
    intro he
    apply y.property
    rw [he]
    exact (B.mem_vertices _).mpr (B.label_mem_component 0)
  have : Nontrivial V := ⟨⟨y.val, B.label 0, hyx⟩⟩
  have hp : 0 < (B.pairRepairedPuncture p q).degree y := by
    rw [B.pairRepairedPuncture_degree_of_even p q hs y hy]
    exact hc.preconnected.degree_pos_of_nontrivial y.val
  exact component_endpoint_of_cap (B.pairRepairedPuncture p q) y C hyC hp
    ((B.pairRepairedPuncture_even_iff p q hne hs y).mpr hy)
    (B.pairRepairedPuncture_cap p q hne hs y hcap)

/-- Every other component has its ceiling budget, including a SET alternative. -/
theorem pairRepaired_other_ceiling (p q : {v : V // v ∉ B.vertices})
    (hne : p ≠ q) (hs : B.syndrome = {p.val, q.val})
    (y : {v : V // v ∉ B.vertices})
    (C : (B.pairRepairedPuncture p q).ConnectedComponent) (hyC : y ∉ C.supp)
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    HasPathBudget ((B.pairRepairedPuncture p q).induce C.supp)
      ((Fintype.card C.supp + 1) / 2) :=
  other_component_ceiling (B.pairRepairedPuncture p q) y C hyC
    (B.pairRepairedPuncture_cap p q hne hs y hcap)

end Gallai.WholeBowtie
