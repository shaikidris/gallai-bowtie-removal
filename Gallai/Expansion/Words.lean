/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Expansion.Graph
import Gallai.Transport.Word

/-!
# Realizing star certificate words in the expanded graph

Each replacement and added word is interpreted as an actual nonempty simple
path. This step verifies its ambient adjacency; compatibility with released
old pieces and simultaneous decomposition coverage are separate obligations.
-/

namespace Gallai.Star

universe u

variable {V : Type u}

/-- Relabelling a word relabels exactly its consecutive unordered edges. -/
theorem word_edges_map (f : Vertex → V) (word : List Vertex) :
    List.zipWith (fun u v => s(u, v)) (word.map f) (word.map f).tail =
      (wordEdges word).map (Sym2.map f) := by
  simp only [wordEdges, ← List.map_tail, List.zipWith_map, List.map_zipWith, Sym2.map_mk]

/-- A symbol available after release can label an old vertex only at the hub. -/
theorem fresh_label_old (H : SimpleGraph V) (x : V) (A : Fin 4 ≃ H.neighborSet x)
    (w : Vertex) (hw : w ∈ fresh) (v : V) (hv : label H x A w = Sum.inl v) : v = x := by
  simp only [fresh, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact (Sum.inl_injective hv).symm
  all_goals simp [label] at hv

/-- A checked word is an actual simple path in the literal star expansion. -/
def realizeWord (H : SimpleGraph V) (x : V) (A : Fin 4 ≃ H.neighborSet x)
    (word : List Vertex) (hlen : 2 ≤ word.length) (hnodup : word.Nodup)
    (hedges : ∀ e ∈ wordEdges word, e ∈ activeEdges) : NonemptyPath (expansion H x) :=
  NonemptyPath.ofWord (word.map (label H x A))
    (by simpa only [List.length_map] using hlen)
    (List.Nodup.map (label_injective H x A) hnodup)
    (by
      intro e he
      rw [word_edges_map] at he
      rcases List.mem_map.mp he with ⟨a, ha, rfl⟩
      exact active_edge_mem H x A a (hedges a ha))

/-- Word realization preserves the entire labelled vertex sequence. -/
theorem realizeWord_support (H : SimpleGraph V) (x : V)
    (A : Fin 4 ≃ H.neighborSet x) (word : List Vertex)
    (hlen : 2 ≤ word.length) (hnodup : word.Nodup)
    (hedges : ∀ e ∈ wordEdges word, e ∈ activeEdges) :
    (realizeWord H x A word hlen hnodup hedges).walk.support =
      word.map (label H x A) := by
  exact NonemptyPath.ofWord_support _ _ _ _

/-- Word realization preserves all edge multiplicities, not only edge membership. -/
theorem realizeWord_edges (H : SimpleGraph V) (x : V)
    (A : Fin 4 ≃ H.neighborSet x) (word : List Vertex)
    (hlen : 2 ≤ word.length) (hnodup : word.Nodup)
    (hedges : ∀ e ∈ wordEdges word, e ∈ activeEdges) :
    (realizeWord H x A word hlen hnodup hedges).walk.edges =
      (wordEdges word).map (Sym2.map (label H x A)) := by
  change (NonemptyPath.ofWord _ _ _ _).walk.edges = _
  rw [NonemptyPath.ofWord_edges, word_edges_map]

/-- A prescribed first symbol becomes the start of the realized path. -/
theorem realizeWord_start (H : SimpleGraph V) (x : V)
    (A : Fin 4 ≃ H.neighborSet x) (word : List Vertex)
    (hlen : 2 ≤ word.length) (hnodup : word.Nodup)
    (hedges : ∀ e ∈ wordEdges word, e ∈ activeEdges) (u : Vertex)
    (hu : word.head? = some u) :
    (realizeWord H x A word hlen hnodup hedges).start = label H x A u := by
  apply List.head_of_head?_eq_some
  simp only [List.head?_map, hu, Option.map_some]

/-- A prescribed last symbol becomes the finish of the realized path. -/
theorem realizeWord_finish (H : SimpleGraph V) (x : V)
    (A : Fin 4 ≃ H.neighborSet x) (word : List Vertex)
    (hlen : 2 ≤ word.length) (hnodup : word.Nodup)
    (hedges : ∀ e ∈ wordEdges word, e ∈ activeEdges) (u : Vertex)
    (hu : word.getLast? = some u) :
    (realizeWord H x A word hlen hnodup hedges).finish = label H x A u := by
  apply List.getLast_of_getLast?_eq_some
  simp only [List.getLast?_map, hu, Option.map_some]

/-- Terminal-word compatibility supplies the actual old-support restriction. -/
theorem realizeWord_terminal_old_support (H : SimpleGraph V) (x b : V)
    (A : Fin 4 ≃ H.neighborSet x) (word : List Vertex)
    (hlen : 2 ≤ word.length) (hnodup : word.Nodup)
    (hedges : ∀ e ∈ wordEdges word, e ∈ activeEdges) (u : Vertex)
    (hu : label H x A u = Sum.inl b) (hcompat : compatible [u, .x] word) :
    ∀ v, Sum.inl v ∈ (realizeWord H x A word hlen hnodup hedges).walk.support →
      v = b ∨ v = x := by
  intro v hv
  rw [realizeWord_support] at hv
  rcases List.mem_map.mp hv with ⟨w, hw, he⟩
  rcases compatible_terminal_support u word hcompat w hw with rfl | hf
  · exact Or.inl (Sum.inl_injective (hu.symm.trans he)).symm
  · exact Or.inr (fresh_label_old H x A w hf v he)

/-- Through-word compatibility supplies the actual two-attachment old-support restriction. -/
theorem realizeWord_through_old_support (H : SimpleGraph V) (x b c : V)
    (A : Fin 4 ≃ H.neighborSet x) (word : List Vertex)
    (hlen : 2 ≤ word.length) (hnodup : word.Nodup)
    (hedges : ∀ e ∈ wordEdges word, e ∈ activeEdges) (u v : Vertex)
    (hu : label H x A u = Sum.inl b) (hv : label H x A v = Sum.inl c)
    (hcompat : compatible [u, .x, v] word) :
    ∀ w, Sum.inl w ∈ (realizeWord H x A word hlen hnodup hedges).walk.support →
      w = b ∨ w = c ∨ w = x := by
  intro w hw
  rw [realizeWord_support] at hw
  rcases List.mem_map.mp hw with ⟨symbol, hsymbol, he⟩
  rcases compatible_through_support u v word hcompat symbol hsymbol with rfl | rfl | hf
  · exact Or.inl (Sum.inl_injective (hu.symm.trans he)).symm
  · exact Or.inr (Or.inl (Sum.inl_injective (hv.symm.trans he)).symm)
  · exact Or.inr (Or.inr (fresh_label_old H x A symbol hf w he))

/-- A valid local family supplies adjacency for every one of its words. -/
theorem Valid.word_edges {old replacements added : List (List Vertex)} {out : ℕ}
    (h : Valid old replacements added out) (word : List Vertex)
    (hw : word ∈ replacements ++ added) :
    ∀ e ∈ wordEdges word, e ∈ activeEdges := by
  intro e he
  apply h.2.2.2.2.2.1.mem_iff.mp
  exact List.mem_flatMap.mpr ⟨word, hw, he⟩

/-- Consume the actual finite contract to realize any replacement or added word. -/
def Valid.realize {old replacements added : List (List Vertex)} {out : ℕ}
    (h : Valid old replacements added out) (H : SimpleGraph V) (x : V)
    (A : Fin 4 ≃ H.neighborSet x) (word : List Vertex)
    (hw : word ∈ replacements ++ added) : NonemptyPath (expansion H x) :=
  realizeWord H x A word (h.2.2.1 word hw).1 (h.2.2.1 word hw).2
    (h.word_edges word hw)

/-- The finite family consumer preserves its exact word, without a path-choice premise. -/
theorem Valid.realize_support {old replacements added : List (List Vertex)} {out : ℕ}
    (h : Valid old replacements added out) (H : SimpleGraph V) (x : V)
    (A : Fin 4 ≃ H.neighborSet x) (word : List Vertex)
    (hw : word ∈ replacements ++ added) :
    (h.realize H x A word hw).walk.support = word.map (label H x A) :=
  realizeWord_support H x A word _ _ _

/-- The finite family consumer preserves the exact local edge list. -/
theorem Valid.realize_edges {old replacements added : List (List Vertex)} {out : ℕ}
    (h : Valid old replacements added out) (H : SimpleGraph V) (x : V)
    (A : Fin 4 ≃ H.neighborSet x) (word : List Vertex)
    (hw : word ∈ replacements ++ added) :
    (h.realize H x A word hw).walk.edges =
      (wordEdges word).map (Sym2.map (label H x A)) :=
  realizeWord_edges H x A word _ _ _

/-- Realize every local word in its original order, including the two added paths. -/
def Valid.realizedFamily {old replacements added : List (List Vertex)} {out : ℕ}
    (h : Valid old replacements added out) (H : SimpleGraph V) (x : V)
    (A : Fin 4 ≃ H.neighborSet x) : List (NonemptyPath (expansion H x)) :=
  (replacements ++ added).attach.map (fun w => h.realize H x A w.val w.property)

/-- The local family has one path per replacement and exactly two added paths. -/
theorem Valid.realizedFamily_length {old replacements added : List (List Vertex)} {out : ℕ}
    (h : Valid old replacements added out) (H : SimpleGraph V) (x : V)
    (A : Fin 4 ≃ H.neighborSet x) :
    (h.realizedFamily H x A).length = old.length + 2 := by
  simp only [realizedFamily, List.length_map, List.length_attach, List.length_append,
    h.1, h.2.1]

/-- The list of realized edge lists is exactly the mapped list of certificate edge lists. -/
theorem Valid.realizedFamily_edges {old replacements added : List (List Vertex)} {out : ℕ}
    (h : Valid old replacements added out) (H : SimpleGraph V) (x : V)
    (A : Fin 4 ≃ H.neighborSet x) :
    (h.realizedFamily H x A).map (fun P => P.walk.edges) =
      (replacements ++ added).map (fun w => (wordEdges w).map (Sym2.map (label H x A))) := by
  simp only [realizedFamily, List.map_map, Function.comp_def, h.realize_edges]
  exact List.attach_map_val
    (f := fun w => (wordEdges w).map (Sym2.map (label H x A)))

/-- The actual local paths partition the mapped active-edge multilist exactly. -/
theorem Valid.realizedFamily_partition {old replacements added : List (List Vertex)} {out : ℕ}
    (h : Valid old replacements added out) (H : SimpleGraph V) (x : V)
    (A : Fin 4 ≃ H.neighborSet x) :
    ((h.realizedFamily H x A).map (fun P => P.walk.edges)).flatten.Perm
      (activeEdges.map (Sym2.map (label H x A))) := by
  rw [h.realizedFamily_edges]
  have hm := h.2.2.2.2.2.1.map (Sym2.map (label H x A))
  simp only [familyEdges, List.map_flatMap] at hm
  exact hm

end Gallai.Star
