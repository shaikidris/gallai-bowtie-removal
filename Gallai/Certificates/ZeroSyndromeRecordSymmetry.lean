/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeTailSymmetry
import Gallai.Certificates.WordOrientation
import Mathlib.Data.List.FinRange

/-! # Exact zero-syndrome record transport -/
namespace Gallai.Certificate.ZeroSyndrome
open CompletedStar

/-- Mapping words commutes with omission of empty tails. -/
theorem localWords_map (f : Equiv.Perm Star.Vertex) (tails : Tails)
    (added : List (List Star.Vertex)) :
    localWords (fun i => (tails i).map f) (added.map (List.map f)) =
      (localWords tails added).map (List.map f) := by
  have ho : List.ofFn (fun i => (tails i).map f) =
      (List.ofFn tails).map (List.map f) := List.map_ofFn.symm
  unfold localWords
  rw [ho, List.filter_map, List.map_append]
  simp only [Function.comp_def, List.isEmpty_map]

/-- Reindexing tails changes only the order of local word occurrences. -/
theorem localWords_reindex (σ : Equiv.Perm (Fin 4)) (tails : Tails)
    (added : List (List Star.Vertex)) :
    (localWords (fun i => tails (σ i)) added).Perm (localWords tails added) := by
  exact ((σ.ofFn_comp_perm tails).filter (fun w => !w.isEmpty)).append_right added

/-- Mapped and reindexed words have the exact mapped edge partition. -/
theorem accepted_mapTails (f : Equiv.Perm Star.Vertex) (σ : Equiv.Perm (Fin 4))
    {edges : Finset (Sym2 Star.Vertex)} {tails : Tails} {added : List (List Star.Vertex)}
    (h : Accepted edges (localWords tails added)) :
    Accepted (edges.map f.toEmbedding.sym2Map)
      (localWords (mapTails f σ tails) (added.map (List.map f))) := by
  have hm := h.map f.toEmbedding
  change Accepted (edges.map f.toEmbedding.sym2Map)
    ((localWords tails added).map (List.map f)) at hm
  rw [← localWords_map f tails added] at hm
  exact hm.perm (localWords_reindex σ.symm (fun i => (tails i).map f)
    (added.map (List.map f))).symm

/-- Full shared acceptance transports when the vertex action realizes the target rows. -/
theorem RecordCore.map_pullback (f : Equiv.Perm Star.Vertex) (σ : Equiv.Perm (Fin 4))
    (ha : ∀ j, f (anchor j) = anchor (σ j))
    (hf : ∀ v ∈ Star.fresh, f v ∈ Star.fresh)
    {s t : State} (he : (targetEdges s).map f.toEmbedding.sym2Map = targetEdges t)
    {c : Labels} {tails : Tails} {added : List (List Star.Vertex)}
    (h : RecordCore s (pullLabels σ c) tails added) :
    RecordCore t c (mapTails f σ tails) (added.map (List.map f)) := by
  refine ⟨?_, mapTails_allowed f σ ha hf h.2⟩
  rw [← he]
  exact accepted_mapTails f σ h.1

/-- Both the two-credit budget and shared-carrier safety are transported. -/
theorem TwoCreditAccepted.map_pullback (f : Equiv.Perm Star.Vertex)
    (σ : Equiv.Perm (Fin 4)) (ha : ∀ j, f (anchor j) = anchor (σ j))
    (hf : ∀ v ∈ Star.fresh, f v ∈ Star.fresh)
    {s t : State} (he : (targetEdges s).map f.toEmbedding.sym2Map = targetEdges t)
    {c k : Labels} (hi : (c, k) ∈ interfaces) {tails : Tails}
    {added : List (List Star.Vertex)}
    (h : TwoCreditAccepted s (pullLabels σ c) (pullLabels σ k) tails added) :
    TwoCreditAccepted t c k (mapTails f σ tails) (added.map (List.map f)) := by
  exact ⟨hi, h.2.1.map_pullback f σ ha hf he,
    by simpa only [List.length_map] using h.2.2.1, mapTails_disjoint f σ h.2.2.2⟩

/-- The one-credit budget and separated-tail condition are transported. -/
theorem OneCreditAccepted.map_pullback (f : Equiv.Perm Star.Vertex)
    (σ : Equiv.Perm (Fin 4)) (ha : ∀ j, f (anchor j) = anchor (σ j))
    (hf : ∀ v ∈ Star.fresh, f v ∈ Star.fresh)
    {s t : State} (he : (targetEdges s).map f.toEmbedding.sym2Map = targetEdges t)
    {c : Labels} (hi : c ∈ separatedPartitions) {tails : Tails}
    {added : List (List Star.Vertex)}
    (h : OneCreditAccepted s (pullLabels σ c) tails added) :
    OneCreditAccepted t c (mapTails f σ tails) (added.map (List.map f)) := by
  exact ⟨hi, h.2.1.map_pullback f σ ha hf he,
    by simpa only [List.length_map] using h.2.2.1, mapTails_separated f σ h.2.2.2⟩

end Gallai.Certificate.ZeroSyndrome
