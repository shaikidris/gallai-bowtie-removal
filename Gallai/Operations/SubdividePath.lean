/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.Transport
import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega

/-! # Insert a fresh vertex into an actual edge run -/

namespace Gallai

universe u
variable {V : Type u} {G : SimpleGraph V} {a b x y z : V}

/-- Subdivision preserves simplicity when the inserted vertex is absent from
the entire old carrier, including both possibly empty outer pieces. -/
theorem isPath_subdivide (L : G.Walk a x) (R : G.Walk y b)
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hzy : G.Adj z y)
    (hp : (L.append (.cons hxy R)).IsPath)
    (hz : z ∉ (L.append (.cons hxy R)).support) :
    (L.append (.cons hxz (.cons hzy R))).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  have hn := hp.support_nodup
  simp only [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons,
    List.tail_cons] at hn hz ⊢
  have hzL : z ∉ L.support := fun h => hz (List.mem_append_left _ h)
  have hzR : z ∉ R.support := fun h => hz (List.mem_append_right _ h)
  exact List.nodup_append'.mpr ⟨hn.of_append_left,
    List.nodup_cons.mpr ⟨hzR, hn.of_append_right⟩,
    List.disjoint_cons_right.mpr ⟨hzL, hn.disjoint⟩⟩

/-- Replace one displayed edge with its two fresh-vertex incidences, without
changing either endpoint of the nonempty path. -/
def NonemptyPath.subdivide (L : G.Walk a x) (R : G.Walk y b)
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hzy : G.Adj z y)
    (hp : (L.append (.cons hxy R)).IsPath)
    (hz : z ∉ (L.append (.cons hxy R)).support) : NonemptyPath G where
  start := a
  finish := b
  walk := L.append (.cons hxz (.cons hzy R))
  isPath := isPath_subdivide L R hxy hxz hzy hp hz
  nonempty := by
    intro hn
    have h := hn.length_eq_zero
    simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons] at h
    omega

/-- Exact edge balance for subdivision: one old edge is exchanged for two. -/
theorem NonemptyPath.subdivide_edge_count [DecidableEq V]
    (L : G.Walk a x) (R : G.Walk y b)
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hzy : G.Adj z y)
    (hp : (L.append (.cons hxy R)).IsPath)
    (hz : z ∉ (L.append (.cons hxy R)).support) (e : Sym2 V) :
    (NonemptyPath.subdivide L R hxy hxz hzy hp hz).walk.edges.count e +
      (if s(x, y) = e then 1 else 0) =
    (L.append (.cons hxy R)).edges.count e +
      (if s(x, z) = e then 1 else 0) + (if s(z, y) = e then 1 else 0) := by
  simp only [subdivide, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons,
    List.count_append, List.count_cons]
  split <;> split <;> split <;> simp_all <;> omega

end Gallai
