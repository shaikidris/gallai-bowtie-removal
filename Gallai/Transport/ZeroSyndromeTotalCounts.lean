/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ZeroSyndromeAccounting
import Gallai.Transport.ZeroSyndromeSlotEquiv

/-! # Combining old and local edge-count contributions -/

namespace Gallai.Certificate.ZeroSyndrome

/-- The record's filtered word list has the same accounting as all four
tails followed by the added occurrences, whenever empty words have weight zero. -/
theorem localWords_weight_sum (tails : Tails) (added : List (List Star.Vertex))
    (weight : List Star.Vertex → ℕ) (hnil : weight [] = 0) :
    ((localWords tails added).map weight).sum =
      (∑ j : Fin 4, weight (tails j)) +
        ∑ i : Fin added.length, weight added[i] := by
  have hfilter (L : List (List Star.Vertex)) :
      ((L.filter (fun w => !w.isEmpty)).map weight).sum = (L.map weight).sum := by
    induction L with
    | nil => rfl
    | cons w L ih => cases w <;> simp [ih, hnil]
  rw [localWords, List.map_append, List.sum_append, hfilter,
    List.map_ofFn, List.sum_ofFn, ← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

end Gallai.Certificate.ZeroSyndrome

namespace Gallai.WholeBowtie
open Certificate Certificate.CompletedStar Certificate.ZeroSyndrome
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Acceptance accounts for mapped original local edges with multiplicity. -/
theorem zero_local_edge_sum (A : B.AnchorNumbering) (tails : Tails)
    (added : List (List Star.Vertex))
    (h : RecordCore (B.completedStarState A) (B.zeroComponentLabels A) tails added)
    (e : Sym2 V) :
    (∑ j : Fin 4,
      ((wordEdges (tails j)).map (Sym2.map (B.completedLabel A))).count e) +
    (∑ i : Fin added.length,
      ((wordEdges added[i]).map (Sym2.map (B.completedLabel A))).count e) =
    ((targetEdges (B.completedStarState A)).val.map
      (Sym2.map (B.completedLabel A))).count e := by
  have hc := congrArg (fun m : Multiset (Sym2 Star.Vertex) =>
    (m.map (Sym2.map (B.completedLabel A))).count e) h.1.2
  simp only [Multiset.map_coe, Multiset.coe_count] at hc
  rw [familyEdges, List.map_flatMap, List.count_flatMap] at hc
  dsimp only [Function.comp_def] at hc
  rw [localWords_weight_sum tails added
    (fun w => ((wordEdges w).map (Sym2.map (B.completedLabel A))).count e)
    (by simp [wordEdges])] at hc
  exact hc

/-- Exact total count before classifying an edge as puncture or local. -/
theorem zeroCandidateFamily_total_count (A : B.AnchorNumbering)
    (D : Decomposition B.puncture) (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (tails : Tails) (added : List (List Star.Vertex))
    (h : TwoCreditAccepted (B.completedStarState A) (B.zeroComponentLabels A)
      (B.zeroCarrierLabels A D f) tails added) (e : Sym2 V) :
    (∑ i : Fin D.size ⊕ Fin added.length,
      (B.zeroCandidateFamily A D f hf tails added h i).walk.edges.count e) =
    (∑ k : Fin D.size, (B.punctureCarrier (D.path k)).walk.edges.count e) +
      ((targetEdges (B.completedStarState A)).val.map
        (Sym2.map (B.completedLabel A))).count e := by
  let weight := fun w => ((wordEdges w).map (Sym2.map (B.completedLabel A))).count e
  have hs := B.zero_all_slot_word_sum A D f hf tails weight (by simp [weight, wordEdges])
  rw [Fintype.sum_prod_type] at hs
  simp only [Fintype.sum_bool, zeroSlotVertex, Bool.false_eq_true, ite_false, ite_true] at hs
  have ho := fun k => B.zeroRestoredOld_edge_count A D f hf tails added h k e
  rw [Fintype.sum_sum_type]
  simp only [zeroCandidateFamily, ho, B.zeroAddedPath_edges, Finset.sum_add_distrib]
  have hl := B.zero_local_edge_sum A tails added h.2.1 e
  dsimp only [weight] at hs
  rw [Finset.sum_add_distrib] at hs
  omega

end Gallai.WholeBowtie
