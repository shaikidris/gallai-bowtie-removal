/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.PairRepairedCoverage

/-! # Original-repair deletion embeds directly and has one explicit edge deficit -/

namespace Gallai.WholeBowtie

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- When repair deletes an original edge, every auxiliary edge is already in G. -/
def originalPairHom (p q : {v : V // v ∉ B.vertices}) (he : G.Adj p.val q.val) :
    B.pairRepairedPuncture p q →g G where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    change (toggleEdge B.puncture p q).Adj u v at huv
    simp only [toggleEdge, show B.puncture.Adj p q from he, if_true] at huv
    exact huv.1

/-- An unchanged auxiliary carrier is an actual original-graph path. -/
def originalPairCarrier (p q : {v : V // v ∉ B.vertices}) (he : G.Adj p.val q.val)
    (P : NonemptyPath (B.pairRepairedPuncture p q)) : NonemptyPath G :=
  P.map (B.originalPairHom p q he) Subtype.val_injective

/-- Direct embedding preserves the exact mapped edge occurrence list. -/
theorem originalPairCarrier_edges (p q : {v : V // v ∉ B.vertices})
    (he : G.Adj p.val q.val) (P : NonemptyPath (B.pairRepairedPuncture p q)) :
    (B.originalPairCarrier p q he P).walk.edges = P.walk.edges.map (Sym2.map Subtype.val) :=
  SimpleGraph.Walk.edges_map (B.originalPairHom p q he) P.walk

/-- The deleted original repair edge occurs on no surviving carrier. -/
theorem originalPair_count_repair (p q : {v : V // v ∉ B.vertices})
    (he : G.Adj p.val q.val) (D : Decomposition (B.pairRepairedPuncture p q)) :
    (∑ i, (B.originalPairCarrier p q he (D.path i)).walk.edges.count s(p.val,q.val)) = 0 := by
  change (∑ i, (B.originalPairCarrier p q he (D.path i)).walk.edges.count
    (Sym2.map Subtype.val s(p,q))) = 0
  simp only [B.originalPairCarrier_edges,
    List.count_map_of_injective _ _ (Sym2.map.injective Subtype.val_injective)]
  rw [D.sum_edge_count]
  have hn : s(p,q) ∉ (B.pairRepairedPuncture p q).edgeSet := by
    simp [pairRepairedPuncture, toggleEdge, he]
  exact if_neg hn

/-- Every other surviving original edge keeps multiplicity one. -/
theorem originalPair_count_outside (p q : {v : V // v ∉ B.vertices})
    (hpq : G.Adj p.val q.val) (D : Decomposition (B.pairRepairedPuncture p q))
    (e : Sym2 V) (he : e ∈ G.edgeSet) (hl : ¬ ∃ v ∈ e, v ∈ B.vertices)
    (hne : e ≠ s(p.val,q.val)) :
    (∑ i, (B.originalPairCarrier p q hpq (D.path i)).walk.edges.count e) = 1 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hu : u ∉ B.vertices := fun h => hl ⟨u, by simp, h⟩
    have hv : v ∉ B.vertices := fun h => hl ⟨v, by simp, h⟩
    let f : Sym2 {v // v ∉ B.vertices} := s(⟨u,hu⟩,⟨v,hv⟩)
    have hfne : f ≠ s(p,q) := by
      intro h
      exact hne (congrArg (Sym2.map Subtype.val) h)
    have hf : f ∈ (B.pairRepairedPuncture p q).edgeSet := by
      change (toggleEdge B.puncture p q).Adj ⟨u,hu⟩ ⟨v,hv⟩
      simp only [toggleEdge, show B.puncture.Adj p q from hpq, if_true]
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨he, by simpa only [Set.mem_singleton_iff] using hfne⟩
    change (∑ i, (B.originalPairCarrier p q hpq (D.path i)).walk.edges.count
      (Sym2.map Subtype.val f)) = 1
    simp only [B.originalPairCarrier_edges,
      List.count_map_of_injective _ _ (Sym2.map.injective Subtype.val_injective)]
    exact (D.sum_edge_count f).trans (if_pos hf)

/-- Original deletion leaves the entire local boundary uncovered. -/
theorem originalPair_count_local (p q : {v : V // v ∉ B.vertices})
    (hpq : G.Adj p.val q.val) (D : Decomposition (B.pairRepairedPuncture p q))
    (e : Sym2 V) (hl : ∃ v ∈ e, v ∈ B.vertices) :
    (∑ i, (B.originalPairCarrier p q hpq (D.path i)).walk.edges.count e) = 0 := by
  simpa only [B.originalPairCarrier_edges, B.pairRepairedCarrier_edges] using
    B.pairRepaired_count_local p q D e hl

/-- Complete surviving-edge accounting for the original-repair branch. -/
theorem originalPair_edge_count (p q : {v : V // v ∉ B.vertices})
    (hpq : G.Adj p.val q.val) (D : Decomposition (B.pairRepairedPuncture p q))
    (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (∑ i, (B.originalPairCarrier p q hpq (D.path i)).walk.edges.count e) =
      if (∃ v ∈ e, v ∈ B.vertices) ∨ e = s(p.val,q.val) then 0 else 1 := by
  classical
  by_cases hl : ∃ v ∈ e, v ∈ B.vertices
  · rw [if_pos (Or.inl hl)]
    exact B.originalPair_count_local p q hpq D e hl
  · by_cases hr : e = s(p.val,q.val)
    · rw [if_pos (Or.inr hr), hr]
      exact B.originalPair_count_repair p q hpq D
    · rw [if_neg (not_or.mpr ⟨hl,hr⟩)]
      exact B.originalPair_count_outside p q hpq D e he hl hr

end Gallai.WholeBowtie
