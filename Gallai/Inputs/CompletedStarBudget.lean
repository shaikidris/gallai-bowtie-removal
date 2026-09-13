/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.CompletedStarAuxiliary
import Gallai.Structure.Incidence
import Gallai.Inputs.OneException

/-! # The actual four-anchor, full-syndrome auxiliary budget

The hypothesis is equality of the original incidence syndrome with the
actual anchor set. Connectivity, parity, E-degree caps and the endpoint-rich
decomposition are derived, not supplied by an encoding or lifting oracle.
-/

namespace Gallai.WholeBowtie

open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Full original syndrome supplies exactly the odd incidences required by
star completion. -/
theorem full_syndrome_columns (hfull : B.syndrome = B.anchors) :
    ∀ w ∈ B.anchors, Odd #(G.neighborFinset w ∩ B.vertices) := by
  intro w hw
  have hs : w ∈ B.syndrome := hfull ▸ hw
  have ho := (B.mem_syndrome_iff_odd_column w).mp hs
  rwa [B.columnCount_eq_deleted_degree w (B.anchor_not_mem_vertices hw)] at ho

/-- Every vertex outside the whole bowtie is retained in the star auxiliary. -/
def completedOutside (y : V) (hy : y ∉ B.vertices) : B.StarSurvivor :=
  ⟨y, by
    intro h
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp h
    exact hy (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩

/-- The full-syndrome branch has two paths available for reconstruction and
two endpoints at the original other exception, for either order parity. -/
theorem completedStar_endpoint_budget (hfour : #B.anchors = 4)
    (hfull : B.syndrome = B.anchors) (hc : G.Connected)
    (y : V) (hy : y ∉ B.vertices) (hyEven : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y → eDegree G v ≤ 3) :
    ∃ D : Decomposition B.completedStar,
      D.size + 2 ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount (B.completedOutside y hy) := by
  classical
  have hcard : Even #B.anchors := by rw [hfour]; decide
  have hcols := B.full_syndrome_columns hfull
  let Y := B.completedOutside y hy
  have hXY : B.completedHub ≠ Y := by
    intro h
    have he : B.label 0 = y := congrArg Subtype.val h
    exact hy (he ▸ Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩)
  have : Nontrivial B.StarSurvivor := ⟨⟨B.completedHub, Y, hXY⟩⟩
  have hconn := B.completedStar_connected hc
  have he : Even (B.completedStar.degree Y) :=
    (B.completedStar_even_iff hcard hcols Y).mpr hyEven
  have hcaps : ∀ v, Even (B.completedStar.degree v) → v ≠ Y →
      eDegree B.completedStar v ≤ 3 := by
    intro v hv hvY
    by_cases hx : v = B.completedHub
    · subst v
      rw [B.completedHub_eDegree hcard hcols]
      omega
    · have hxval : v.val ≠ B.label 0 := fun h => hx (Subtype.ext h)
      have hvG := (B.completedStar_even_iff hcard hcols v).mp hv
      exact (B.completedStar_eDegree_le hcard hcols v hxval hvG).trans
        (hcap v.val hvG hxval (fun h => hvY (Subtype.ext h)))
  obtain ⟨D, hD, hDy⟩ := one_exception_endpoint B.completedStar Y hconn
    (hconn.preconnected.degree_pos_of_nontrivial Y) he hcaps
  have hn := B.completedStar_card
  exact ⟨D, by omega, hDy⟩

end Gallai.WholeBowtie
