/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.Word
import Gallai.Foundations.EdgeCounts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Multiset.Count

/-! # Decidable local edge-partition certificates

The alphabet is arbitrary. Acceptance checks word simplicity and exact edge
multiplicity, but does not assert compatibility with any old ambient carrier.
-/

namespace Gallai.Certificate

variable {V : Type*}

/-- Consecutive unordered edges of a vertex word, with multiplicities retained. -/
def wordEdges (word : List V) : List (Sym2 V) :=
  List.zipWith (fun a b => s(a, b)) word word.tail

/-- All edge occurrences, without collapsing equal words or equal edges. -/
def familyEdges (words : List (List V)) : List (Sym2 V) := words.flatMap wordEdges

/-- The shared local acceptance contract of the reconstruction record families. -/
def Accepted (edges : Finset (Sym2 V)) (words : List (List V)) : Prop :=
  (∀ word ∈ words, 2 ≤ word.length ∧ word.Nodup) ∧
    (familyEdges words : Multiset (Sym2 V)) = edges.val

instance [DecidableEq V] (edges : Finset (Sym2 V)) (words : List (List V)) :
    Decidable (Accepted edges words) := by
  unfold Accepted
  infer_instance

/-- Executable acceptance, checked by Lean's ordinary decision reduction. -/
def check [DecidableEq V] (edges : Finset (Sym2 V)) (words : List (List V)) : Bool :=
  decide (Accepted edges words)

/-- A successful computation proves exactly the declared finite contract. -/
theorem check_eq_true [DecidableEq V] (edges : Finset (Sym2 V)) (words : List (List V)) :
    check edges words = true ↔ Accepted edges words := by
  simp [check]

/-- The checked edge multiplicity at the literal word-occurrence indices. -/
theorem Accepted.edge_count [DecidableEq V] {edges : Finset (Sym2 V)}
    {words : List (List V)} (h : Accepted edges words) (e : Sym2 V) :
    (∑ i : Fin words.length, (wordEdges words[i]).count e) =
      if e ∈ edges then 1 else 0 := by
  have hsum : (familyEdges words).count e =
      ∑ i : Fin words.length, (wordEdges words[i]).count e := by
    rw [familyEdges, List.count_flatMap, ← List.ofFn_getElem_eq_map, List.sum_ofFn]
    rfl
  have hcount := congrArg (Multiset.count e) h.2
  simp only [Multiset.coe_count] at hcount
  rw [← hsum, hcount]
  split_ifs with he
  · exact Multiset.count_eq_one_of_mem edges.nodup he
  · exact Multiset.count_eq_zero_of_notMem he

variable [DecidableEq V] {edges : Finset (Sym2 V)} {words : List (List V)}

/-- Interpret one accepted occurrence in a graph containing the specified local edges. -/
def Accepted.realize (h : Accepted edges words) (G : SimpleGraph V)
    (hG : ∀ e ∈ edges, e ∈ G.edgeSet) (i : Fin words.length) : NonemptyPath G :=
  NonemptyPath.ofWord words[i] (h.1 _ (List.getElem_mem _)).1
    (h.1 _ (List.getElem_mem _)).2 (fun e he => hG e (by
      change e ∈ edges.val
      rw [← h.2]
      exact List.mem_flatMap.mpr ⟨words[i], List.getElem_mem _, he⟩))

omit [DecidableEq V] in
/-- Every support vertex of a realized occurrence is a vertex of its checked word. -/
theorem Accepted.realize_support (h : Accepted edges words) (G : SimpleGraph V)
    (hG : ∀ e ∈ edges, e ∈ G.edgeSet) (i : Fin words.length) :
    (h.realize G hG i).walk.support = words[i] :=
  NonemptyPath.ofWord_support _ _ _ _

omit [DecidableEq V] in
/-- Realization preserves the checked complete edge list at each occurrence. -/
theorem Accepted.realize_edges (h : Accepted edges words) (G : SimpleGraph V)
    (hG : ∀ e ∈ edges, e ∈ G.edgeSet) (i : Fin words.length) :
    (h.realize G hG i).walk.edges = wordEdges words[i] :=
  NonemptyPath.ofWord_edges _ _ _ _

/-- Accepted local words give a decomposition when the specified edges are
exactly those of the target graph. No unique-owner assumption is supplied. -/
def Accepted.toDecomposition (h : Accepted edges words) (G : SimpleGraph V)
    (hG : ∀ e, e ∈ edges ↔ e ∈ G.edgeSet) : Decomposition G :=
  Decomposition.ofEdgeCounts (h.realize G (fun e he => (hG e).mp he)) (by
    intro e he
    simp only [h.realize_edges]
    rw [h.edge_count e, if_pos ((hG e).mpr he)])

/-- The decomposition retains the number of word occurrences exactly. -/
@[simp] theorem Accepted.toDecomposition_size (h : Accepted edges words) (G : SimpleGraph V)
    (hG : ∀ e, e ∈ edges ↔ e ∈ G.edgeSet) :
    (h.toDecomposition G hG).size = words.length := rfl

/-- Endpoint incidences of the word occurrences, in the same format as the
finite certificate verifiers. -/
def endpoints (words : List (List V)) (v : V) : ℕ :=
  (words.map (fun word => (if word.head? = some v then 1 else 0) +
    (if word.getLast? = some v then 1 else 0))).sum

/-- The local decomposition has exactly the checked endpoint vector, not
merely the same path budget or edge set. -/
theorem Accepted.toDecomposition_endpointCount (h : Accepted edges words) (G : SimpleGraph V)
    (hG : ∀ e, e ∈ edges ↔ e ∈ G.edgeSet) (v : V) :
    (h.toDecomposition G hG).endpointCount v = endpoints words v := by
  change (∑ i : Fin words.length,
    ((if (h.realize G (fun e he => (hG e).mp he) i).start = v then 1 else 0) +
      (if (h.realize G (fun e he => (hG e).mp he) i).finish = v then 1 else 0))) = _
  unfold endpoints
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  have hne : words[i.val] ≠ [] := by
    intro heq
    have hl := (h.1 _ (List.getElem_mem i.isLt)).1
    simp [heq] at hl
  rw [List.head?_eq_some_head hne, List.getLast?_eq_some_getLast hne]
  simp only [Option.some.injEq]
  rfl

end Gallai.Certificate
