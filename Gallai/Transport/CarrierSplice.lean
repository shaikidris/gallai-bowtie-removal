/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.Concatenate

/-!
# Replacing a through segment inside one carrier

The two old pieces may be nil. Their supports must be disjoint, and the
connector may meet each only at its own attachment. This is a local-to-carrier
soundness statement, not a global decomposition or interface-selection theorem.
-/

namespace Gallai

universe u

variable {V : Type u} {G : SimpleGraph V} {a b c d : V}

/-- A compatible connector splices two disjoint old pieces into a simple path. -/
theorem isPath_splice (L : G.Walk a b) (M : G.Walk b c) (R : G.Walk c d)
    (hL : L.IsPath) (hM : M.IsPath) (hR : R.IsPath)
    (hLR : L.support.Disjoint R.support)
    (hLM : ∀ w, w ∈ L.support → w ∈ M.support → w = b)
    (hMR : ∀ w, w ∈ M.support → w ∈ R.support → w = c) :
    ((L.append M).append R).IsPath := by
  apply isPath_append_of_intersection _ _
    (isPath_append_of_intersection L M hL hM hLM) hR
  intro w hw hwR
  rw [SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hw with hwL | hwM
  · exact False.elim (hLR hwL hwR)
  · exact hMR w hwM hwR

/-- Build a nonempty carrier even when one or both old pieces have no edges. -/
def NonemptyPath.splice (L : G.Walk a b) (M : G.Walk b c) (R : G.Walk c d)
    (hL : L.IsPath) (hM : M.IsPath) (hR : R.IsPath) (hMne : ¬ M.Nil)
    (hLR : L.support.Disjoint R.support)
    (hLM : ∀ w, w ∈ L.support → w ∈ M.support → w = b)
    (hMR : ∀ w, w ∈ M.support → w ∈ R.support → w = c) : NonemptyPath G where
  start := a
  finish := d
  walk := (L.append M).append R
  isPath := isPath_splice L M R hL hM hR hLR hLM hMR
  nonempty := by
    intro hn
    exact hMne (SimpleGraph.Walk.nil_append_iff.mp
      (SimpleGraph.Walk.nil_append_iff.mp hn).1).2

/-- A splice uses exactly the old-left, connector, and old-right edges. -/
theorem NonemptyPath.splice_edges (L : G.Walk a b) (M : G.Walk b c) (R : G.Walk c d)
    (hL : L.IsPath) (hM : M.IsPath) (hR : R.IsPath) (hMne : ¬ M.Nil)
    (hLR : L.support.Disjoint R.support)
    (hLM : ∀ w, w ∈ L.support → w ∈ M.support → w = b)
    (hMR : ∀ w, w ∈ M.support → w ∈ R.support → w = c) :
    (NonemptyPath.splice L M R hL hM hR hMne hLR hLM hMR).walk.edges =
      (L.edges ++ M.edges) ++ R.edges := by
  exact (SimpleGraph.Walk.edges_append (L.append M) R).trans
    (congrArg (· ++ R.edges) (SimpleGraph.Walk.edges_append L M))

end Gallai
