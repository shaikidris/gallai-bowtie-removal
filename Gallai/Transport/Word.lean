/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Foundations.Decomposition
import Lean.Elab.Tactic.Omega

/-!
# From a checked vertex word to an actual simple path

Consecutive-edge membership, rather than a bare certificate flag, supplies
adjacency in the ambient graph. Vertex distinctness and positive edge length
remain explicit. This bridge does not assert compatibility with old carriers.
-/

namespace Gallai

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- A vertex word whose consecutive edges belong to the graph is an adjacency chain. -/
theorem isChain_of_word_edges (word : List V)
    (hedges : ∀ e ∈ List.zipWith (fun u v => s(u, v)) word word.tail, e ∈ G.edgeSet) :
    word.IsChain G.Adj := by
  induction word with
  | nil => exact .nil
  | cons a word ih =>
    cases word with
    | nil => exact .singleton a
    | cons b rest =>
      apply List.IsChain.cons
      · apply ih
        intro e he
        exact hedges e (by simpa only [List.tail_cons, List.zipWith_cons_cons,
          List.mem_cons] using Or.inr he)
      · simpa using hedges s(a, b) (by simp)

/-- Interpret a nonrepeating word with at least one edge as an ambient path. -/
def NonemptyPath.ofWord (word : List V) (hlen : 2 ≤ word.length)
    (hnodup : word.Nodup)
    (hedges : ∀ e ∈ List.zipWith (fun u v => s(u, v)) word word.tail, e ∈ G.edgeSet) :
    NonemptyPath G where
  start := word.head (by intro h; simp [h] at hlen)
  finish := word.getLast (by intro h; simp [h] at hlen)
  walk := .ofSupport word (by intro h; simp [h] at hlen) (isChain_of_word_edges word hedges)
  isPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    simpa only [SimpleGraph.Walk.support_ofSupport] using hnodup
  nonempty := by
    intro hn
    have hzero := hn.length_eq_zero
    rw [SimpleGraph.Walk.length_ofSupport] at hzero
    omega

/-- Word interpretation preserves the entire support list. -/
theorem NonemptyPath.ofWord_support (word : List V) (hlen : 2 ≤ word.length)
    (hnodup : word.Nodup)
    (hedges : ∀ e ∈ List.zipWith (fun u v => s(u, v)) word word.tail, e ∈ G.edgeSet) :
    (NonemptyPath.ofWord word hlen hnodup hedges).walk.support = word := by
  exact SimpleGraph.Walk.support_ofSupport _ _

/-- Word interpretation preserves the edge list, including its multiplicities. -/
theorem NonemptyPath.ofWord_edges (word : List V) (hlen : 2 ≤ word.length)
    (hnodup : word.Nodup)
    (hedges : ∀ e ∈ List.zipWith (fun u v => s(u, v)) word word.tail, e ∈ G.edgeSet) :
    (NonemptyPath.ofWord word hlen hnodup hedges).walk.edges =
      List.zipWith (fun u v => s(u, v)) word word.tail := by
  rw [SimpleGraph.Walk.edges_eq_zipWith_support, NonemptyPath.ofWord_support]

end Gallai
