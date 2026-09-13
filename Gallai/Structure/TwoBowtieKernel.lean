/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.BowtieEvenDegree
import Gallai.Structure.OrderParity

/-! # The two-whole-bowtie kernel and its exception dictionary -/
namespace Gallai.TwoBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Two disjoint whole bowties, with subcubic residual even vertices. -/
def Kernel (X Y : WholeBowtie G) : Prop :=
  Disjoint X.vertices Y.vertices ∧
  ∀ v, Even (G.degree v) → v ∉ X.vertices → v ∉ Y.vertices → eDegree G v ≤ 3

/-- The original odd-degree vertices. -/
def oddVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => Odd (G.degree v)

variable {X Y : WholeBowtie G}

omit [DecidableEq V] in
/-- The kernel hypotheses are symmetric in the two bowties. -/
theorem Kernel.symm (h : Kernel X Y) : Kernel Y X :=
  ⟨h.1.symm, fun v hv hy hx => h.2 v hv hx hy⟩

omit [DecidableEq V] in
/-- The second centre lies outside the first bowtie. -/
theorem Kernel.hub_out (h : Kernel X Y) : Y.label 0 ∉ X.vertices := by
  intro hx
  exact Finset.disjoint_left.mp h.1 hx
    ((Y.mem_vertices _).mpr (Y.label_mem_component 0))

/-- Every whole-bowtie anchor is among the original odd vertices. -/
theorem anchors_subset_odd (X : WholeBowtie G) : X.anchors ⊆ oddVertices G := by
  intro v hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, X.odd_degree_anchor hv⟩

/-- Away from its hub, a whole bowtie has E-degree two. -/
theorem private_cap (X : WholeBowtie G) {v : V}
    (hv : v ∈ X.vertices) (hne : v ≠ X.label 0) : eDegree G v ≤ 3 := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
  have hi : i ≠ 0 := fun hi => hne (congrArg X.label hi)
  rw [X.eDegree_label, if_neg hi]
  omega

/-- The kernel gives precisely the cap required by the two-exception theorem. -/
theorem Kernel.exception_cap (h : Kernel X Y) (v : V)
    (hv : Even (G.degree v)) (hx : v ≠ X.label 0) (hy : v ≠ Y.label 0) :
    eDegree G v ≤ 3 := by
  by_cases hm : v ∈ X.vertices
  · exact private_cap X hm hx
  by_cases hn : v ∈ Y.vertices
  · exact private_cap Y hn hy
  exact h.2 v hv hm hn

end Gallai.TwoBowtie
