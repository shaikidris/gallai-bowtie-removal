/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.CarrierSplice
import Gallai.Operations.Transport
import Mathlib.Combinatorics.SimpleGraph.Operations

/-! # Restore a synthetic repair edge by a fresh connector

The old carrier lives in the auxiliary graph H, whereas its replacement lives
in G. In particular, the removed synthetic edge is not required to belong to G.
The connector may meet the old carrier only at its two attachment vertices.
-/

namespace Gallai

variable {V : Type*} {G H : SimpleGraph V} {a b x y : V}

/-- Locate a used unordered edge as an oriented run, retaining both outer pieces. -/
theorem walk_edge_run (P : H.Walk a b) (e : Sym2 V) (he : e ∈ P.edges) :
    ∃ (u v : V) (h : H.Adj u v) (L : H.Walk a u) (R : H.Walk v b),
      s(u, v) = e ∧ P = L.append (.cons h R) := by
  induction P with
  | nil => simp at he
  | @cons a c b hac P ih =>
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · exact ⟨a, c, hac, .nil, P, he.symm, rfl⟩
    · obtain ⟨u, v, h, L, R, heq, hP⟩ := ih he
      exact ⟨u, v, h, .cons hac L, R, heq, by rw [hP]; rfl⟩

/-- Decomposition coverage supplies the run and proves all other carriers avoid it. -/
theorem Decomposition.repairEdge_carrier (D : Decomposition H)
    (e : Sym2 V) (he : e ∈ H.edgeSet) :
    ∃ (i : Fin D.size) (u v : V) (h : H.Adj u v)
      (L : H.Walk (D.path i).start u) (R : H.Walk v (D.path i).finish),
      s(u, v) = e ∧ (D.path i).walk = L.append (.cons h R) ∧
      ∀ j, j ≠ i → e ∉ (D.path j).walk.edges := by
  obtain ⟨i, hi, huniq⟩ := D.covers e he
  obtain ⟨u, v, h, L, R, heq, hP⟩ := walk_edge_run (D.path i).walk e hi
  exact ⟨i, u, v, h, L, R, heq, hP, fun j hji hj => hji (huniq j hj)⟩

/-- Removing one displayed edge separates a simple carrier into disjoint supports. -/
theorem edgeRun_supports_disjoint (L : H.Walk a x) (R : H.Walk y b)
    (hxy : H.Adj x y) (hp : (L.append (.cons hxy R)).IsPath) :
    L.support.Disjoint R.support := by
  have hn := hp.support_nodup
  simp only [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons,
    List.tail_cons] at hn
  exact hn.disjoint

/-- Neither retained outer piece still uses the released repair edge. -/
theorem edgeRun_edges_avoid (L : H.Walk a x) (R : H.Walk y b)
    (hxy : H.Adj x y) (hp : (L.append (.cons hxy R)).IsPath) :
    s(x, y) ∉ L.edges ∧ s(x, y) ∉ R.edges := by
  have hn := hp.isTrail.edges_nodup
  simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons] at hn
  exact ⟨fun he => hn.disjoint he (by simp),
    (List.nodup_cons.mp hn.of_append_right).1⟩

/-- In a one-edge supergraph, releasing that edge leaves only original edges. -/
theorem edgeRun_original_edges {u v : V}
    (L : (G ⊔ SimpleGraph.edge x y).Walk a u)
    (R : (G ⊔ SimpleGraph.edge x y).Walk v b)
    (hxy : (G ⊔ SimpleGraph.edge x y).Adj u v)
    (hp : (L.append (.cons hxy R)).IsPath) (heq : s(u, v) = s(x, y)) :
    (∀ e ∈ L.edges, e ∈ G.edgeSet) ∧ (∀ e ∈ R.edges, e ∈ G.edgeSet) := by
  have hn := edgeRun_edges_avoid L R hxy hp
  rw [heq] at hn
  constructor
  · intro e he
    have hm := L.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_sup] at hm
    rcases hm with hg | hx
    · exact hg
    · have heq : e = s(x, y) := SimpleGraph.edgeSet_edge_subset hx
      exact (hn.1 (heq ▸ he)).elim
  · intro e he
    have hm := R.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_sup] at hm
    rcases hm with hg | hx
    · exact hg
    · have heq : e = s(x, y) := SimpleGraph.edgeSet_edge_subset hx
      exact (hn.2 (heq ▸ he)).elim

/-- Replace a synthetic edge without changing the carrier endpoints. -/
def NonemptyPath.restoreRepairEdge (L : H.Walk a x) (R : H.Walk y b)
    (hxy : H.Adj x y) (hp : (L.append (.cons hxy R)).IsPath)
    (hL : ∀ e ∈ L.edges, e ∈ G.edgeSet)
    (hR : ∀ e ∈ R.edges, e ∈ G.edgeSet)
    (M : G.Walk x y) (hM : M.IsPath)
    (hfresh : ∀ v, v ∈ M.support → v ∈ (L.append (.cons hxy R)).support →
      v = x ∨ v = y) : NonemptyPath G :=
  NonemptyPath.splice (L.transfer G hL) M (R.transfer G hR)
    (hp.of_append_left.transfer hL) hM (hp.of_append_right.of_cons.transfer hR)
    (SimpleGraph.Walk.not_nil_of_ne hxy.ne)
    (by
      simpa only [SimpleGraph.Walk.support_transfer] using
        edgeRun_supports_disjoint L R hxy hp)
    (by
      intro v hvL hvM
      rw [SimpleGraph.Walk.support_transfer] at hvL
      have hvOld : v ∈ (L.append (.cons hxy R)).support := by
        rw [SimpleGraph.Walk.mem_support_append_iff]
        exact Or.inl hvL
      rcases hfresh v hvM hvOld with hx | hy
      · exact hx
      · exact False.elim (edgeRun_supports_disjoint L R hxy hp hvL
          (hy ▸ R.start_mem_support)))
    (by
      intro v hvM hvR
      rw [SimpleGraph.Walk.support_transfer] at hvR
      have hvOld : v ∈ (L.append (.cons hxy R)).support := by
        rw [SimpleGraph.Walk.mem_support_append_iff]
        right
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
        exact Or.inr hvR
      rcases hfresh v hvM hvOld with hx | hy
      · exact False.elim (edgeRun_supports_disjoint L R hxy hp
          (hx ▸ L.end_mem_support) hvR)
      · exact hy)

/-- Exact edge accounting: the connector replaces, rather than retains, xy. -/
theorem NonemptyPath.restoreRepairEdge_edge_count [DecidableEq V]
    (L : H.Walk a x) (R : H.Walk y b)
    (hxy : H.Adj x y) (hp : (L.append (.cons hxy R)).IsPath)
    (hL : ∀ e ∈ L.edges, e ∈ G.edgeSet)
    (hR : ∀ e ∈ R.edges, e ∈ G.edgeSet)
    (M : G.Walk x y) (hM : M.IsPath)
    (hfresh : ∀ v, v ∈ M.support → v ∈ (L.append (.cons hxy R)).support →
      v = x ∨ v = y) (e : Sym2 V) :
    (NonemptyPath.restoreRepairEdge L R hxy hp hL hR M hM hfresh).walk.edges.count e +
      (if s(x, y) = e then 1 else 0) =
    (L.append (.cons hxy R)).edges.count e + M.edges.count e := by
  simp only [restoreRepairEdge, splice, SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_transfer, SimpleGraph.Walk.edges_cons,
    List.count_append, List.count_cons]
  split <;> simp_all <;> omega

/-- A used repair edge can be restored in either orientation; the full old
carrier and connector are the only inputs, not a preselected splitting. -/
theorem NonemptyPath.restoreMissingEdge [DecidableEq V]
    (P : NonemptyPath (G ⊔ SimpleGraph.edge x y))
    (he : s(x, y) ∈ P.walk.edges) (M : G.Walk x y) (hM : M.IsPath)
    (hfresh : ∀ v, v ∈ M.support → v ∈ P.walk.support → v = x ∨ v = y) :
    ∃ Q : NonemptyPath G, Q.start = P.start ∧ Q.finish = P.finish ∧
      ∀ e, Q.walk.edges.count e + (if s(x, y) = e then 1 else 0) =
        P.walk.edges.count e + M.edges.count e := by
  obtain ⟨u, v, h, L, R, heq, hP⟩ := walk_edge_run P.walk s(x, y) he
  have hp : (L.append (.cons h R)).IsPath := hP ▸ P.isPath
  obtain ⟨hL, hR⟩ := edgeRun_original_edges L R h hp heq
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hf : ∀ w, w ∈ M.support → w ∈ (L.append (.cons h R)).support →
        w = u ∨ w = v := by simpa only [hP] using hfresh
    refine ⟨restoreRepairEdge L R h hp hL hR M hM hf, rfl, rfl, ?_⟩
    intro e
    simpa only [hP] using restoreRepairEdge_edge_count L R h hp hL hR M hM hf e
  · have hf : ∀ w, w ∈ M.reverse.support → w ∈ (L.append (.cons h R)).support →
        w = u ∨ w = v := by
      intro w hw ho
      have hw' : w ∈ M.support := by simpa using hw
      exact (hfresh w hw' (hP ▸ ho)).symm
    refine ⟨restoreRepairEdge L R h hp hL hR M.reverse hM.reverse hf, rfl, rfl, ?_⟩
    intro e
    simpa only [hP, Sym2.eq_swap, SimpleGraph.Walk.edges_reverse, List.count_reverse] using
      restoreRepairEdge_edge_count L R h hp hL hR M.reverse hM.reverse hf e

end Gallai
