/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Expansion.Assignment

/-!
# Separating retained edges from the local reconstruction

The old contribution of each altered carrier is precisely its edges not
incident with the hub. Exact edge multisets, rather than only adjacency,
will let the global family inherit old edge ownership.
-/

namespace Gallai.Star

universe u

variable {V : Type u} {H : SimpleGraph V} [DecidableEq V]

/-- Filtering out hub spokes changes no edge of a hub-free walk. -/
theorem hubFree_filter {a b : V} (W : H.Walk a b) (x : V) (hx : x ∉ W.support) :
    W.edges.filter (fun e => decide (x ∉ e)) = W.edges := by
  apply List.filter_eq_self.mpr
  intro e he
  exact decide_eq_true (fun hxe => hx (SimpleGraph.Walk.mem_support_of_mem_edges he hxe))

/-- Through release retains exactly the original nonspoke edges in their order. -/
theorem through_nonspoke_edges (P : NonemptyPath H) (x : V)
    (hx : x ∈ P.walk.support) (hs : P.start ≠ x) (ht : x ≠ P.finish) :
    P.walk.edges.filter (fun e => decide (x ∉ e)) =
      (P.releaseLeft x hx hs).edges ++ (P.releaseRight x hx ht).edges := by
  rw [← P.release_edges x hx hs ht, List.filter_append, List.filter_append,
    hubFree_filter _ x (P.hub_notMem_releaseLeft x hx hs),
    hubFree_filter _ x (P.hub_notMem_releaseRight x hx ht)]
  simp

/-- Orientation changes the edge order but not its multiset. -/
theorem toward_edges_perm (P : NonemptyPath H) (x : V) :
    (P.toward x).walk.edges.Perm P.walk.edges := by
  by_cases hs : P.start = x
  · rw [P.toward_of_start_eq x hs, NonemptyPath.reverse_edges]
    exact List.reverse_perm _
  · rw [P.toward_of_start_ne x hs]

/-- A released terminal prefix has exactly the old carrier's nonspoke multiset. -/
theorem terminal_nonspoke_edges (P : NonemptyPath H) (x : V)
    (hx : P.start = x ∨ P.finish = x) :
    P.walk.edges.filter (fun e => decide (x ∉ e)) |>.Perm
      (P.toward x).walk.reverse.tail.reverse.edges := by
  let Q := P.toward x
  have hf : Q.finish = x := P.toward_finish x hx
  have hfilter : Q.walk.edges.filter (fun e => decide (x ∉ e)) =
      Q.walk.reverse.tail.reverse.edges := by
    rw [← Q.reverse_tail_edges_append_spoke, List.filter_append,
      hubFree_filter _ x (hf ▸ released_terminal_hub_absent Q)]
    simp [hf]
  exact ((toward_edges_perm P x).filter _).symm.trans (List.Perm.of_eq hfilter)

variable [Fintype V] [DecidableRel H.Adj]

/-- Automatic terminal restoration partitions into retained edges and its assigned word. -/
theorem assignedTerminal_edge_partition (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : D.TerminalIndex x) :
    (assignedTerminal D x hd i).walk.edges.Perm
      (((D.path i.val).walk.edges.filter (fun e => decide (x ∉ e))).map
        (Sym2.map (oldHom H x)) ++
      (wordEdges ((profileOf D x).terminalWord (terminalNumber D x hd i))).map
        (Sym2.map (label H x (D.fourNeighborEquiv x hd)))) := by
  unfold assignedTerminal
  rw [restoreTerminal_edges]
  exact ((terminal_nonspoke_edges (D.path i.val) x
    (Finset.mem_filter.mp i.property).2).symm.map _).append_right _

/-- Automatic through restoration partitions into retained edges and its assigned word. -/
theorem assignedThrough_edge_partition (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : D.ThroughIndex x) :
    (assignedThrough D x hd i).walk.edges.Perm
      (((D.path i.val).walk.edges.filter (fun e => decide (x ∉ e))).map
        (Sym2.map (oldHom H x)) ++
      (wordEdges ((profileOf D x).throughWord (throughNumber D x hd i))).map
        (Sym2.map (label H x (D.fourNeighborEquiv x hd)))) := by
  have hi := (Finset.mem_filter.mp i.property).2
  let p := profileOf D x
  let n := throughNumber D x hd i
  have hm := p.throughWord_mem n
  have hc := p.valid.2.2.1 _ hm
  have he : (assignedThrough D x hd i).walk.edges =
      (((D.path i.val).releaseLeft x hi.1 hi.2.1).edges.map (Sym2.map (oldHom H x)) ++
        (wordEdges (p.throughWord n)).map
          (Sym2.map (label H x (D.fourNeighborEquiv x hd)))) ++
      ((D.path i.val).releaseRight x hi.1 hi.2.2.symm).edges.map
        (Sym2.map (oldHom H x)) :=
    restoreThrough_edges (D.path i.val) x hi.1 hi.2.1 hi.2.2.symm
      (D.fourNeighborEquiv x hd) (p.throughWord n) hc.1 hc.2 (p.valid.word_edges _ hm)
      (anchor (p.throughAnchor n 0)) (anchor (p.throughAnchor n 1))
      (through_attachment D x hd i 0) (through_attachment D x hd i 1)
      (p.throughWord_compatible n)
  rw [he, through_nonspoke_edges _ x hi.1 hi.2.1 hi.2.2.symm,
    List.map_append, List.append_assoc, List.append_assoc]
  exact List.perm_append_comm.append_left _

end Gallai.Star
