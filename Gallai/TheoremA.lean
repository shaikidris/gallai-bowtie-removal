/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.BoundedAnchorConclusion
import Gallai.Inputs.BowtiePeeling
import Gallai.OddOrder

/-! # Manuscript Theorem A: whole-bowtie removal

All four alternatives have the original-graph ceiling conclusion. Odd order
is handled first to expose both exceptions on the SAME decomposition witness.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Literal four-alternative bowtie-removal theorem, with simultaneous hub
exposure on odd order. No restriction on the odd-anchor graph, the designated
exception's E-degree, or connectedness after deletion is imposed. -/
theorem theoremA (hc : G.Connected) (y : V) (hyout : y ∉ B.vertices)
    (hy : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y → eDegree G v ≤ 3)
    (hcase : B.anchors.card ≤ 4 ∨ B.activity ≤ 2 ∨
      (∃ w ∈ B.row 0, ∀ v, G.Adj w v → Even (G.degree v) → v = B.label 0 ∨ v = y) ∨
      Odd (Fintype.card V)) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount y ∧
      (Odd (Fintype.card V) → 2 ≤ P.endpointCount (B.label 0)) := by
  by_cases hodd : Odd (Fintype.card V)
  · obtain ⟨m,hm⟩ := hodd
    have horder : Fintype.card V = 2 * m + 1 := by omega
    have hxy : B.label 0 ≠ y := fun he => hyout
      (he ▸ (B.mem_vertices (B.label 0)).mpr (B.label_mem_component 0))
    have hmissing : ¬ G.Adj (B.label 0) y := by
      intro hadj
      exact hyout ((B.mem_vertices y).mpr
        (mem_evenComponent_of_adj B.component (B.label_mem_component 0) hadj hy))
    obtain ⟨P,hP,hPx,hPy⟩ := Gallai.odd_order_two_exception_of_cap m horder hc
      (B.label 0) y hxy hmissing (B.even_degree_label 0) hy hcap
    exact ⟨P,by omega,hPy,fun _ => hPx⟩
  · have solved : ∃ P : Decomposition G,
        P.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ P.endpointCount y := by
      rcases hcase with hA | ha | hp | ho
      · exact B.bounded_anchor_endpoint hA hc y hyout hy hcap
      · exact B.low_activity_endpoint ha hc y hyout hy hcap
      · exact B.peeling_endpoint hc y hyout hy hcap hp
      · exact (hodd ho).elim
    obtain ⟨P,hP,hPy⟩ := solved
    exact ⟨P,hP,hPy,fun ho => (hodd ho).elim⟩

end Gallai.WholeBowtie
