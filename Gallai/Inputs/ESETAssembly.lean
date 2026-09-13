/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ESET
import Gallai.Inputs.ESETReserve

/-! # Literal ESET reserves and hanging absorption

This module consumes the structural two-case predicate, deriving the actual
decompositions for both cases. It does not assume the floor-or-SET theorem.
-/

namespace Gallai

universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {z : V}

/-- The literal ESET connection has a ceiling-budget decomposition exposing it twice. -/
theorem IsESETAt.endpoint_reserve (h : IsESETAt G z) :
    ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount z := by
  classical
  rcases h with h | ⟨h, x, y, hx, hy, hG⟩
  · exact h.endpoint_reserve z
  · have hz : z ∉ Set.range (Function.Embedding.subtype (fun v : V => v ≠ z)) := by
      rintro ⟨w, hw⟩
      exact w.property hw
    have hr := h.extension_ceiling_reserve (Function.Embedding.subtype _) z hz x y hx hy
    change ∃ D : Decomposition (((G.induce {v | v ≠ z}).map
      (Function.Embedding.subtype _) ⊔ SimpleGraph.edge z x.val) ⊔
        SimpleGraph.edge z y.val), D.size ≤ (Fintype.card V + 1) / 2 ∧
          2 ≤ D.endpointCount z at hr
    rw [← hG] at hr
    exact hr

variable {W : Type v} [DecidableEq W]

/-- Every non-SET ESET already satisfies the floor path bound.
Its deleted SET core has odd order, so its own order is even. -/
theorem IsESETAt.floor_or_set (h : IsESETAt G z) :
    HasPathBudget G (Fintype.card V / 2) ∨ IsSET G := by
  classical
  rcases h with hs | ht
  · exact Or.inr hs
  · have ho := ht.1.odd_order
    have hc : Fintype.card {v : V // v ≠ z} = Fintype.card V - 1 := by
      simpa only [Fintype.card_subtype_eq] using
        (Fintype.card_subtype_compl (fun v : V => v = z))
    have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨z⟩
    have hc' : Fintype.card ↥({v : V | v ≠ z}) = Fintype.card V - 1 := by
      simpa only [Fintype.card_subtype, Set.mem_ofPred_eq] using hc
    obtain ⟨D, hD, _⟩ := (show IsESETAt G z from Or.inr ht).endpoint_reserve
    have he : (Fintype.card V + 1) / 2 = Fintype.card V / 2 := by
      rw [hc'] at ho
      obtain ⟨k, hk⟩ := ho
      omega
    exact Or.inl ⟨D, by simpa only [he] using hD⟩

/-- A literal ESET connection has a genuine incident edge. -/
theorem IsESETAt.connection_adj (h : IsESETAt G z) : ∃ w, G.Adj z w := by
  obtain ⟨D, _, hz⟩ := h.endpoint_reserve
  exact (G.degree_pos_iff_exists_adj z).mp
    (by have := D.endpointCount_le_degree z; omega)

/-- A path meeting an embedded ESET only at its connection is absorbed for free. -/
theorem IsESETAt.absorb_embedded_path (h : IsESETAt G z) (f : V ↪ W)
    {H : SimpleGraph W} {a b : W} (p : H.Walk a b) (hp : p.IsPath)
    (hz : f z ∈ p.support) (hle : G.map f ≤ H)
    (hedges : ∀ e, e ∈ H.edgeSet ↔ e ∈ (G.map f).edgeSet ∨ e ∈ p.edges)
    (hmeet : ∀ w ∈ p.support, w ∈ Set.range f → w = f z) :
    ∃ E : Decomposition H, E.size ≤ (Fintype.card V + 1) / 2 := by
  obtain ⟨D, hD, hzD⟩ := h.endpoint_reserve
  obtain ⟨E, hs⟩ := (D.map f).absorb_walk_of_vertex_intersection p hp (f z) hz
    (by simpa using hzD) hle hedges (by
      intro w hw hadj
      obtain ⟨t, ht⟩ := hadj
      obtain ⟨r, s, _, hr, _⟩ := (SimpleGraph.map_adj f G w t).mp ht
      exact hmeet w hw ⟨r, hr⟩)
  exact ⟨E, hs.le.trans hD⟩

/-- Either type of hanging ESET saves one path from the remainder decomposition.
Positive joint degree ensures a nonempty remainder carrier exists. -/
theorem IsESETAt.absorb_hanging (h : IsESETAt G z) (f : V ↪ W)
    {J : SimpleGraph W} (D : Decomposition J)
    (hpos : ∃ t, J.Adj (f z) t)
    (hmeet : ∀ w, (∃ t, J.Adj w t) → w ∈ Set.range f → w = f z) :
    ∃ E : Decomposition (G.map f ⊔ J),
      E.size ≤ (Fintype.card V + 1) / 2 + D.size - 1 := by
  classical
  obtain ⟨t, ht⟩ := hpos
  obtain ⟨i, hi, _⟩ := D.covers s(f z, t) ht
  let P := D.path i
  let K := G.map f ⊔ P.walk.toSubgraph.spanningCoe
  have heK (e : Sym2 W) : e ∈ K.edgeSet ↔ e ∈ (G.map f).edgeSet ∨ e ∈ P.walk.edges := by
    simp only [K, SimpleGraph.edgeSet_sup, Set.mem_union,
      SimpleGraph.Subgraph.edgeSet_spanningCoe, SimpleGraph.Walk.mem_edges_toSubgraph]
  let Q := P.transfer K (fun e he => (heK e).mpr (Or.inr he))
  obtain ⟨A, hA⟩ := h.absorb_embedded_path f Q.walk Q.isPath
    (by simpa [Q] using P.walk.fst_mem_support_of_mem_edges hi)
    le_sup_left (by simpa only [Q, NonemptyPath.transfer_edges] using heK) (by
      intro w hw hr
      have hw' : w ∈ P.walk.support := by simpa [Q] using hw
      obtain ⟨t, _, ht⟩ := SimpleGraph.adj_of_mem_walk_support P.walk P.nonempty hw'
      exact hmeet w ⟨t, ht⟩ hr)
  have hdis : Disjoint (G.map f).edgeSet J.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro hg hj
      have hab : J.Adj a b := hj
      obtain ⟨r, s, _, hr, hs⟩ := (SimpleGraph.map_adj f G a b).mp hg
      have ha := hmeet a ⟨b, hab⟩ ⟨r, hr⟩
      have hb := hmeet b ⟨a, hab.symm⟩ ⟨s, hs⟩
      exact hab.ne (ha.trans hb.symm)
  obtain ⟨E, hs⟩ := D.replace_carrier_union i A heK hdis
  exact ⟨E, by omega⟩

end Gallai
