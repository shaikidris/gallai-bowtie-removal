/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.PeelingConclusion
import Gallai.Structure.BowtieEvenDegree

/-! # The fourth Theorem A alternative: peeling at a whole bowtie -/

namespace Gallai.WholeBowtie

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- An external neighbour of the whole-bowtie hub whose even contacts are
limited to the two exceptions yields the original ceiling budget exposing y.
No anchor bound, activity bound, parity or puncture-connectedness is assumed. -/
theorem peeling_endpoint (hc : G.Connected) (y : V) (hy : y ∉ B.vertices)
    (hyEven : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y → eDegree G v ≤ 3)
    (hpeel : ∃ w ∈ B.row 0,
      ∀ v, G.Adj w v → Even (G.degree v) → v = B.label 0 ∨ v = y) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y := by
  obtain ⟨w, hw, hcontact⟩ := hpeel
  have hxy : B.label 0 ≠ y := fun heq => hy
    (heq ▸ (B.mem_vertices (B.label 0)).mpr (B.label_mem_component 0))
  have hxw : G.Adj (B.label 0) w := ((B.mem_row 0 w).mp hw).1
  have hwOdd : Odd (G.degree w) := B.odd_degree_anchor ((B.mem_anchors w).mpr ⟨0, hw⟩)
  exact odd_neighbor_peeling (B.label 0) y w hc hxy hxw (B.even_degree_label 0)
    hyEven hwOdd hcontact hcap (Or.inr (by simp [B.eDegree_label]))

end Gallai.WholeBowtie
