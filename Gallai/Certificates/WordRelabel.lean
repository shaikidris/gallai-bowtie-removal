/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.RecordSoundness

/-! # Relabelling local carrier roles

Relabelling transports the literal ordered boundary. Reversing a connector
exchanges its attachments; it is not treated as an unchanged ordered role.
These operations supply the role interface for completed-star symmetry.
-/

namespace Gallai.Certificate

variable {V W : Type*}

/-- Relabelling retains every edge occurrence, including its multiplicity. -/
theorem wordEdges_map (f : V → W) (word : List V) :
    wordEdges (word.map f) = (wordEdges word).map (Sym2.map f) := by
  simp only [wordEdges, ← List.map_tail, List.zipWith_map, List.map_zipWith]
  rfl

/-- Allowed vertices and ordered attachments are transported together. -/
theorem Compatible.map [DecidableEq W] {boundary word : List V}
    {allowed : Finset V} (h : Compatible boundary allowed word) (f : V → W) :
    Compatible (boundary.map f) (allowed.image f) (word.map f) := by
  cases boundary with
  | nil => simp [Compatible] at h
  | cons a rest =>
    cases rest with
    | nil =>
      refine ⟨?_, ?_⟩
      · simp only [List.head?_map, h.1, Option.map_some]
      · intro v hv
        rw [← List.map_tail] at hv
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
        exact Finset.mem_image.mpr ⟨u, h.2 u hu, rfl⟩
    | cons b rest =>
      cases rest with
      | nil =>
        refine ⟨?_, ?_, ?_⟩
        · simp only [List.head?_map, h.1, Option.map_some]
        · simp only [List.getLast?_map, h.2.1, Option.map_some]
        · intro v hv
          rw [← List.map_tail, ← List.map_dropLast] at hv
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
          exact Finset.mem_image.mpr ⟨u, h.2.2 u hu, rfl⟩
      | cons c rest => simp [Compatible] at h

/-- A connector may be reversed exactly when its ordered attachments are reversed. -/
theorem Compatible.reverse_pair {a b : V} {allowed : Finset V} {word : List V}
    (h : Compatible [a, b] allowed word) : Compatible [b, a] allowed word.reverse := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.head?_reverse] using h.2.1
  · simpa only [List.getLast?_reverse] using h.1
  · intro v hv
    rw [List.tail_reverse, List.dropLast_reverse, List.tail_dropLast,
      List.mem_reverse] at hv
    exact h.2.2 v hv

/-- Relabelling the family retains the complete edge-occurrence list. -/
theorem familyEdges_map (f : V → W) (words : List (List V)) :
    familyEdges (words.map (List.map f)) = (familyEdges words).map (Sym2.map f) := by
  simp only [familyEdges, List.flatMap_map, List.map_flatMap,
    wordEdges_map]

/-- Injective relabelling preserves the endpoint count at the relabelled vertex. -/
theorem endpoints_map [DecidableEq V] [DecidableEq W] (f : V → W)
    (hf : Function.Injective f) (words : List (List V)) (v : V) :
    endpoints (words.map (List.map f)) (f v) = endpoints words v := by
  have hoption (o : Option V) : o.map f = some (f v) ↔ o = some v := by
    cases o <;> simp [hf.eq_iff]
  simp only [endpoints, List.map_map, Function.comp_def, List.head?_map,
    List.getLast?_map, hoption]

/-- An injective relabelling preserves simplicity and exact edge multiplicities. -/
theorem Accepted.map {edges : Finset (Sym2 V)} {words : List (List V)}
    (h : Accepted edges words) (f : V ↪ W) :
    Accepted (edges.map f.sym2Map) (words.map (List.map f)) := by
  refine ⟨?_, ?_⟩
  · intro word hw
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hw
    exact ⟨by simpa only [List.length_map] using (h.1 old ho).1,
      List.Nodup.map f.injective (h.1 old ho).2⟩
  · rw [familyEdges_map]
    exact congrArg (Multiset.map (Sym2.map f)) h.2

/-- A complete record transports to relabelled edges, roles and endpoint demands. -/
theorem RecordAccepted.map [DecidableEq V] [DecidableEq W]
    {edges : Finset (Sym2 V)} {roles : List (List V × Finset V)}
    {replacements added : List (List V)} {budget : ℕ}
    {marked : Finset V} {required : V → ℕ}
    (h : RecordAccepted edges roles replacements added budget marked required)
    (f : V ≃ W) :
    RecordAccepted (edges.map f.toEmbedding.sym2Map)
      (roles.map (fun role => (role.1.map f, role.2.image f)))
      (replacements.map (List.map f)) (added.map (List.map f)) budget
      (marked.image f) (fun v => required (f.symm v)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.map_append, Equiv.toEmbedding, Function.Embedding.coeFn_mk]
      using h.1.map f.toEmbedding
  · have hr := h.2.1
    clear h
    induction hr with
    | nil => exact List.Forall₂.nil
    | cons hab _ ih => exact List.Forall₂.cons (hab.map f) ih
  · simpa only [List.length_map] using h.2.2.1
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    rw [← List.map_append, endpoints_map f f.injective]
    simpa only [Equiv.symm_apply_apply] using h.2.2.2 u hu

end Gallai.Certificate
