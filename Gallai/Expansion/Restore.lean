/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Expansion.Carrier

/-!
# Restore an actual carrier from a compatible star word

These constructors release the input carrier themselves. Simplicity and
connector avoidance are derived from the input path and finite word contract,
not supplied as arbitrary ambient compatibility witnesses. The choice of word
and attachment labels must still come from the profile-specific global family.
-/

namespace Gallai.Star

universe u

variable {V : Type u} {H : SimpleGraph V} [DecidableEq V]

/-- Replace an actual internal hub run by a compatible checked through word. -/
def restoreThrough (P : NonemptyPath H) (x : V)
    (hx : x ∈ P.walk.support) (hs : P.start ≠ x) (ht : x ≠ P.finish)
    (A : Fin 4 ≃ H.neighborSet x) (word : List Vertex)
    (hlen : 2 ≤ word.length) (hnodup : word.Nodup)
    (hedges : ∀ e ∈ wordEdges word, e ∈ activeEdges) (u v : Vertex)
    (hu : label H x A u = Sum.inl (P.takeTo x hx hs).walk.reverse.snd)
    (hv : label H x A v = Sum.inl (P.dropFrom x hx ht).walk.snd)
    (hcompat : compatible [u, .x, v] word) : NonemptyPath (expansion H x) := by
  let M := realizeWord H x A word hlen hnodup hedges
  have hstart : M.start = Sum.inl (P.takeTo x hx hs).walk.reverse.snd :=
    (realizeWord_start H x A word hlen hnodup hedges u hcompat.1).trans hu
  have hlast : word.getLast? = some v := by
    have h := hcompat.2
    simpa using h.1
  have hfinish : M.finish = Sum.inl (P.dropFrom x hx ht).walk.snd :=
    (realizeWord_finish H x A word hlen hnodup hedges v hlast).trans hv
  exact throughCarrier (P.releaseLeft x hx hs) (P.releaseRight x hx ht)
    (M.walk.copy hstart hfinish) (P.releaseLeft_isPath x hx hs)
    (P.releaseRight_isPath x hx ht) ((M.walk.isPath_copy hstart hfinish).mpr M.isPath)
    (SimpleGraph.Walk.not_nil_of_ne (fun he =>
      P.release_attachments_ne x hx hs ht (Sum.inl_injective he)))
    (P.release_supports_disjoint x hx hs ht) (P.hub_notMem_releaseLeft x hx hs)
    (P.hub_notMem_releaseRight x hx ht)
    (by
      intro w hw
      have hw' : Sum.inl w ∈ M.walk.support := by
        simpa only [SimpleGraph.Walk.support_copy] using hw
      exact realizeWord_through_old_support H x _ _ A word hlen hnodup hedges u v hu hv
        hcompat w hw')

/-- Through restoration keeps both outside endpoints of the original carrier. -/
theorem restoreThrough_endpoints (P : NonemptyPath H) (x : V)
    (hx : x ∈ P.walk.support) (hs : P.start ≠ x) (ht : x ≠ P.finish)
    (A : Fin 4 ≃ H.neighborSet x) (word : List Vertex)
    (hlen : 2 ≤ word.length) (hnodup : word.Nodup)
    (hedges : ∀ e ∈ wordEdges word, e ∈ activeEdges) (u v : Vertex)
    (hu : label H x A u = Sum.inl (P.takeTo x hx hs).walk.reverse.snd)
    (hv : label H x A v = Sum.inl (P.dropFrom x hx ht).walk.snd)
    (hcompat : compatible [u, .x, v] word) :
    (restoreThrough P x hx hs ht A word hlen hnodup hedges u v hu hv hcompat).start =
        Sum.inl P.start ∧
      (restoreThrough P x hx hs ht A word hlen hnodup hedges u v hu hv hcompat).finish =
        Sum.inl P.finish := ⟨rfl, rfl⟩

omit [DecidableEq V] in
/-- Releasing a terminal carrier makes its former final vertex absent from the old prefix. -/
theorem released_terminal_hub_absent (P : NonemptyPath H) :
    P.finish ∉ P.walk.reverse.tail.reverse.support := by
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
  exact P.reverse.start_notMem_tail_support

/-- Replace the terminal spoke of an actual carrier by a compatible checked tail. -/
def restoreTerminal (P : NonemptyPath H) (x : V)
    (hx : P.start = x ∨ P.finish = x) (A : Fin 4 ≃ H.neighborSet x)
    (word : List Vertex) (hlen : 2 ≤ word.length) (hnodup : word.Nodup)
    (hedges : ∀ e ∈ wordEdges word, e ∈ activeEdges) (u : Vertex)
    (hu : label H x A u = Sum.inl (P.toward x).walk.reverse.snd)
    (hcompat : compatible [u, .x] word) : NonemptyPath (expansion H x) := by
  let Q := P.toward x
  let M := realizeWord H x A word hlen hnodup hedges
  have hstart : M.start = Sum.inl Q.walk.reverse.snd :=
    (realizeWord_start H x A word hlen hnodup hedges u hcompat.1).trans hu
  have hQfinish : Q.finish = x := P.toward_finish x hx
  have hhub : x ∉ Q.walk.reverse.tail.reverse.support :=
    hQfinish ▸ released_terminal_hub_absent Q
  exact terminalCarrier Q.walk.reverse.tail.reverse (M.walk.copy hstart rfl)
    Q.isPath.reverse.tail.reverse ((M.walk.isPath_copy hstart rfl).mpr M.isPath)
    (SimpleGraph.Walk.not_nil_of_ne (fun he => M.start_ne_finish _ (hstart.trans he))) hhub
    (by
      intro v hv
      have hv' : Sum.inl v ∈ M.walk.support := by
        simpa only [SimpleGraph.Walk.support_copy] using hv
      exact realizeWord_terminal_old_support H x _ A word hlen hnodup hedges u hu hcompat v hv')

/-- Terminal restoration retains the outside endpoint and ends at the new word's finish. -/
theorem restoreTerminal_endpoints (P : NonemptyPath H) (x : V)
    (hx : P.start = x ∨ P.finish = x) (A : Fin 4 ≃ H.neighborSet x)
    (word : List Vertex) (hlen : 2 ≤ word.length) (hnodup : word.Nodup)
    (hedges : ∀ e ∈ wordEdges word, e ∈ activeEdges) (u : Vertex)
    (hu : label H x A u = Sum.inl (P.toward x).walk.reverse.snd)
    (hcompat : compatible [u, .x] word) :
    (restoreTerminal P x hx A word hlen hnodup hedges u hu hcompat).start =
        Sum.inl (P.toward x).start ∧
      (restoreTerminal P x hx A word hlen hnodup hedges u hu hcompat).finish =
        (realizeWord H x A word hlen hnodup hedges).finish := ⟨rfl, rfl⟩

/-- Actual through restoration replaces precisely the two released spokes by the word edges. -/
theorem restoreThrough_edges (P : NonemptyPath H) (x : V)
    (hx : x ∈ P.walk.support) (hs : P.start ≠ x) (ht : x ≠ P.finish)
    (A : Fin 4 ≃ H.neighborSet x) (word : List Vertex)
    (hlen : 2 ≤ word.length) (hnodup : word.Nodup)
    (hedges : ∀ e ∈ wordEdges word, e ∈ activeEdges) (u v : Vertex)
    (hu : label H x A u = Sum.inl (P.takeTo x hx hs).walk.reverse.snd)
    (hv : label H x A v = Sum.inl (P.dropFrom x hx ht).walk.snd)
    (hcompat : compatible [u, .x, v] word) :
    (restoreThrough P x hx hs ht A word hlen hnodup hedges u v hu hv hcompat).walk.edges =
      ((P.releaseLeft x hx hs).edges.map (Sym2.map (oldHom H x)) ++
        (wordEdges word).map (Sym2.map (label H x A))) ++
          (P.releaseRight x hx ht).edges.map (Sym2.map (oldHom H x)) := by
  simp only [restoreThrough, throughCarrier_edges, SimpleGraph.Walk.edges_copy, realizeWord_edges]

/-- Actual terminal restoration replaces precisely the terminal spoke by the word edges. -/
theorem restoreTerminal_edges (P : NonemptyPath H) (x : V)
    (hx : P.start = x ∨ P.finish = x) (A : Fin 4 ≃ H.neighborSet x)
    (word : List Vertex) (hlen : 2 ≤ word.length) (hnodup : word.Nodup)
    (hedges : ∀ e ∈ wordEdges word, e ∈ activeEdges) (u : Vertex)
    (hu : label H x A u = Sum.inl (P.toward x).walk.reverse.snd)
    (hcompat : compatible [u, .x] word) :
    (restoreTerminal P x hx A word hlen hnodup hedges u hu hcompat).walk.edges =
      (P.toward x).walk.reverse.tail.reverse.edges.map (Sym2.map (oldHom H x)) ++
        (wordEdges word).map (Sym2.map (label H x A)) := by
  simp only [restoreTerminal, terminalCarrier_edges, SimpleGraph.Walk.edges_copy, realizeWord_edges]

end Gallai.Star
