/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ThreeAnchorLabels

/-! # Exhaustive original local boundary for three-anchor words -/

namespace Gallai.WholeBowtie

open Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrows : ∀ i v, v ∈ B.row i ↔
  ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)

include hrows in
/-- Exact rows place every edge at a core vertex into the finite target. -/
theorem threeLabel_target_covers (i : Fin 5) (v : V) (ha : G.Adj (B.label i) v) :
    ∃ e ∈ targetEdges s, Sym2.map (B.threeLabel A) e = s(B.label i, v) := by
  by_cases hv : v ∈ B.vertices
  · obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hv
    have hj := (B.adj_iff i j).mp ha
    have hc : s(i.castAdd 3, j.castAdd 3) ∈
        ({s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(0, 4), s(3, 4)} : Finset (Sym2 Vertex)) :=
      (by decide : ∀ i j : Fin 5, bowtieGraph.Adj i j → s(i.castAdd 3, j.castAdd 3) ∈
        ({s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(0, 4), s(3, 4)} : Finset (Sym2 Vertex))) i j hj
    refine ⟨s(i.castAdd 3, j.castAdd 3), Finset.mem_union_left _ hc, ?_⟩
    change s(B.threeLabel A (i.castAdd 3), B.threeLabel A (j.castAdd 3)) = _
    rw [B.threeLabel_core, B.threeLabel_core]
  · obtain ⟨j, hj, hjv⟩ := (hrows i v).mp ((B.mem_row i v).mpr ⟨ha, hv⟩)
    refine ⟨s(i.castAdd 3, anchor j), Finset.mem_union_right _ ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩
    · change s(B.threeLabel A (i.castAdd 3), B.threeLabel A (anchor j)) = _
      rw [B.threeLabel_core, B.threeLabel_anchor, hjv]

/-- Every mapped local edge is incident with a deleted vertex. -/
theorem threeLabel_target_incident (e : Sym2 Vertex) (he : e ∈ targetEdges s) :
    ∃ v ∈ Sym2.map (B.threeLabel A) e, v ∈ B.vertices := by
  have hcore : ∃ v ∈ e, v.val < 5 := by
    rw [targetEdges, Finset.mem_union] at he
    rcases he with he | he
    · exact (by decide : ∀ e : Sym2 Vertex,
        e ∈ ({s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(0, 4), s(3, 4)} : Finset _) →
        ∃ v ∈ e, v.val < 5) e he
    · obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp he
      exact ⟨i.castAdd 3, by simp, i.isLt⟩
  obtain ⟨v, hv, hvc⟩ := hcore
  exact ⟨B.threeLabel A v, Sym2.mem_map.mpr ⟨v, hv, rfl⟩, B.threeLabel_fresh A v hvc⟩

include hrows in
/-- The mapped target is exactly the original graph's local edge boundary. -/
theorem threeLabel_target_iff (e : Sym2 V) :
    (∃ f ∈ targetEdges s, Sym2.map (B.threeLabel A) f = e) ↔
      e ∈ G.edgeSet ∧ ∃ v ∈ e, v ∈ B.vertices := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨B.threeLabel_target_edge A s ?_ f hf, B.threeLabel_target_incident A s f hf⟩
    intro i j hj
    exact (hrows i _).mpr ⟨j, hj, rfl⟩
  · rintro ⟨he, v, hv, hvB⟩
    induction e using Sym2.inductionOn with
    | hf u w =>
      change G.Adj u w at he
      have h : v = u ∨ v = w := by simpa using hv
      rcases h with rfl | rfl
      · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hvB
        exact B.threeLabel_target_covers A s hrows i w he
      · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hvB
        obtain ⟨f, hf, hfe⟩ := B.threeLabel_target_covers A s hrows i u he.symm
        exact ⟨f, hf, hfe.trans Sym2.eq_swap⟩

end Gallai.WholeBowtie
