/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeRecord
import Gallai.Transport.CompletedStarWords
import Gallai.Transport.ZeroSyndromePartitionRealization
import Gallai.Transport.ZeroSyndromeTails

/-! # Realizing accepted whole-deletion tails in the original graph

Use only original row edges. The retained-star word embedding is reusable
without a retained-star hypothesis: it is the injective original local label
map. Carrier assignment remains separate from local word realization.
-/

namespace Gallai.WholeBowtie

open Certificate Certificate.CompletedStar Certificate.ZeroSyndrome
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Realize any member of an accepted local family directly in G. -/
noncomputable def realizeOriginalMember (A : B.AnchorNumbering)
    (words : List (List Star.Vertex))
    (h : Accepted (targetEdges (B.completedStarState A)) words)
    (word : List Star.Vertex) (hw : word ∈ words) : NonemptyPath G := by
  let P : NonemptyPath (graph (B.completedStarState A)) :=
    NonemptyPath.ofWord word (h.1 word hw).1 (h.1 word hw).2 (fun e he => by
      apply (graph_edges _ e).mp
      change e ∈ (targetEdges (B.completedStarState A)).val
      rw [← h.2]
      exact List.mem_flatMap.mpr ⟨word, hw, he⟩)
  exact P.map (B.completedLocalHom A) (B.completedLabel_injective A)

/-- No old ambient vertex is hidden by symbolic word interpretation. -/
theorem realizeOriginalMember_support (A : B.AnchorNumbering)
    (words : List (List Star.Vertex))
    (h : Accepted (targetEdges (B.completedStarState A)) words)
    (word : List Star.Vertex) (hw : word ∈ words) :
    (B.realizeOriginalMember A words h word hw).walk.support =
      word.map (B.completedLabel A) := by
  simp only [realizeOriginalMember, NonemptyPath.map,
    SimpleGraph.Walk.support_map, NonemptyPath.ofWord_support]
  rfl

/-- Original edge multiplicities are retained under realization. -/
theorem realizeOriginalMember_edges (A : B.AnchorNumbering)
    (words : List (List Star.Vertex))
    (h : Accepted (targetEdges (B.completedStarState A)) words)
    (word : List Star.Vertex) (hw : word ∈ words) :
    (B.realizeOriginalMember A words h word hw).walk.edges =
      (Certificate.wordEdges word).map (Sym2.map (B.completedLabel A)) := by
  simp only [realizeOriginalMember, NonemptyPath.map,
    SimpleGraph.Walk.edges_map, NonemptyPath.ofWord_edges]
  rfl

/-- A used tail occurs in the local family, regardless of empty sibling tails. -/
theorem zero_tail_mem (tails : Tails) (added : List (List Star.Vertex))
    (i : Fin 4) (hi : tails i ≠ []) : tails i ∈ localWords tails added := by
  apply List.mem_append_left
  apply List.mem_filter.mpr
  exact ⟨List.mem_ofFn.mpr ⟨i, rfl⟩, by simpa using hi⟩

/-- Realize one nonempty accepted tail; empty tails are handled by nil walks. -/
noncomputable def realizeZeroTail (A : B.AnchorNumbering) (c : Labels)
    (tails : Tails) (added : List (List Star.Vertex))
    (h : RecordCore (B.completedStarState A) c tails added)
    (i : Fin 4) (hi : tails i ≠ []) : NonemptyPath G :=
  B.realizeOriginalMember A (localWords tails added) h.1 (tails i)
    (zero_tail_mem tails added i hi)

/-- A realized tail has exactly the anchor prescribed by the record as its start. -/
theorem realizeZeroTail_start (A : B.AnchorNumbering) (c : Labels)
    (tails : Tails) (added : List (List Star.Vertex))
    (h : RecordCore (B.completedStarState A) c tails added)
    (i : Fin 4) (hi : tails i ≠ []) :
    (B.realizeZeroTail A c tails added h i hi).start = (A i).val := by
  have hs := B.realizeOriginalMember_support A (localWords tails added) h.1
    (tails i) (zero_tail_mem tails added i hi)
  have hh := (h.2 i).resolve_left hi
  have hp := congrArg List.head? hs
  rw [List.head?_map, hh.1] at hp
  have hstart : (B.realizeZeroTail A c tails added h i hi).walk.support.head? =
      some (B.realizeZeroTail A c tails added h i hi).start := by
    rw [← (B.realizeZeroTail A c tails added h i hi).walk.cons_tail_support]
    rfl
  change (B.realizeZeroTail A c tails added h i hi).walk.support.head? = _ at hp
  rw [hstart] at hp
  exact (Option.some.inj hp).trans (B.completedLabel_anchor A i)

end Gallai.WholeBowtie
