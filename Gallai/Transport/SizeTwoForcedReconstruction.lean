/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoForcedFamily
import Gallai.Transport.SizeTwoBoundaryCounts

/-! # Global edge coverage for forced size-two reconstruction

The checked local partition and actual old-carrier equations imply unique
coverage of every original edge. Synthetic auxiliary spokes are canceled,
not assumed to have been edges of the original graph.
-/
namespace Gallai.Certificate.SizeTwo.Forced

/-- Empty optional tails have zero weight and are never counted as paths. -/
theorem localWords_weight_sum (connector extra tail : List Star.Vertex)
    (added : List (List Star.Vertex)) (weight : List Star.Vertex → ℕ)
    (hnil : weight [] = 0) :
    ((localWords connector extra tail added).map weight).sum =
      weight connector + weight extra + weight tail +
        ∑ k : Fin added.length, weight added[k] := by
  have ha : (added.map weight).sum = ∑ k : Fin added.length, weight added[k] := by
    rw [← List.ofFn_getElem_eq_map,List.sum_ofFn]
    rfl
  rw [localWords,List.map_append,List.sum_append,List.map_append,List.sum_append,ha]
  by_cases ht : tail = []
  · simp only [ht,↓reduceIte,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hnil,Nat.add_zero]
  · simp only [if_neg ht,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]

end Gallai.Certificate.SizeTwo.Forced

namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : B.AnchorNumbering) (j : Fin 2)
variable (connector extra tail : List Star.Vertex) (added : List (List Star.Vertex))
variable (h : Forced.AcceptedRecord (B.completedStarState A) j connector extra tail added)

include h in
/-- The forced record covers the original local edge multiset exactly once. -/
theorem sizeTwo_forced_local_edge_sum (e : Sym2 V) :
    ((wordEdges connector).map (Sym2.map (B.completedLabel A))).count e +
    ((wordEdges extra).map (Sym2.map (B.completedLabel A))).count e +
    ((wordEdges tail).map (Sym2.map (B.completedLabel A))).count e +
    (∑ k : Fin added.length, ((wordEdges added[k]).map (Sym2.map (B.completedLabel A))).count e) =
      ((CompletedStar.targetEdges (B.completedStarState A)).val.map
        (Sym2.map (B.completedLabel A))).count e := by
  have hc := congrArg (fun m : Multiset (Sym2 Star.Vertex) =>
    (m.map (Sym2.map (B.completedLabel A))).count e) h.2.2.2.2.1.2
  simp only [Multiset.map_coe,Multiset.coe_count] at hc
  rw [familyEdges,List.map_flatMap,List.count_flatMap] at hc
  dsimp only [Function.comp_def] at hc
  rw [Forced.localWords_weight_sum connector extra tail added
    (fun w => ((wordEdges w).map (Sym2.map (B.completedLabel A))).count e)
    (by simp [wordEdges])] at hc
  exact hc

/-- Added certificate paths are actual nonempty simple paths in G. -/
noncomputable def sizeTwoForcedAddedPath (k : Fin added.length) : NonemptyPath G :=
  B.sizeTwoForcedWord A j connector extra tail added h added[k]
    (List.mem_append_right _ (List.getElem_mem _))

variable (hSigma : B.syndrome = {(A 0).val,(A 1).val})
variable (D : Decomposition B.syndromeStar) (k₀ k₁ : Fin D.size)
variable (F : Fin D.size → NonemptyPath G)
variable (hcarrier : ∀ k e, (F k).walk.edges.count e +
  (if k = k₀ then
    ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e else 0) =
  ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e +
  (if k = k₀ then
    ((wordEdges connector).map (Sym2.map (B.completedLabel A))).count e +
    ((wordEdges tail).map (Sym2.map (B.completedLabel A))).count e else 0) +
  (if k = k₁ then ((wordEdges extra).map (Sym2.map (B.completedLabel A))).count e else 0))

include hSigma hcarrier in
/-- Summing the actual local balances and canceling auxiliary spokes proves
global multiplicity one; global coverage is not an input hypothesis. -/
theorem sizeTwo_forced_reconstructed_edge_count (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (∑ k : Fin D.size, (F k).walk.edges.count e) +
      (∑ k : Fin added.length,
        (B.sizeTwoForcedAddedPath A j connector extra tail added h k).walk.edges.count e) = 1 := by
  classical
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => hcarrier k e)
  simp only [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte] at hs
  have ha : (∑ k : Fin added.length,
      (B.sizeTwoForcedAddedPath A j connector extra tail added h k).walk.edges.count e) =
      ∑ k : Fin added.length, ((wordEdges added[k]).map (Sym2.map (B.completedLabel A))).count e := by
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (List.count e)
      (B.sizeTwoForcedWord_edges A j connector extra tail added h added[k] _)
  have hl := B.sizeTwo_forced_local_edge_sum A j connector extra tail added h e
  have hg := B.sizeTwo_original_edge_balance A hSigma D e he
  omega

/-- The candidate family plus added paths is an actual decomposition of G. -/
noncomputable def sizeTwoForcedReconstruction : Decomposition G :=
  Decomposition.ofEdgeCounts
    (fun k : Fin (D.size + added.length) =>
      Sum.elim F (B.sizeTwoForcedAddedPath A j connector extra tail added h) (finSumFinEquiv.symm k))
    (by
      intro e he
      rw [(finSumFinEquiv : Fin D.size ⊕ Fin added.length ≃ Fin (D.size + added.length)).symm.sum_comp
        (fun k => (Sum.elim F (B.sizeTwoForcedAddedPath A j connector extra tail added h) k).walk.edges.count e)]
      rw [Fintype.sum_sum_type]
      exact B.sizeTwo_forced_reconstructed_edge_count A j connector extra tail added h
        hSigma D k₀ k₁ F hcarrier e he)

/-- The reconstruction has exactly the old count plus the stored added count. -/
theorem sizeTwoForcedReconstruction_size :
    (B.sizeTwoForcedReconstruction A j connector extra tail added h hSigma D k₀ k₁ F hcarrier).size =
      D.size + added.length := rfl

/-- Every forced record uses at most two additional paths. -/
theorem sizeTwoForcedReconstruction_budget :
    (B.sizeTwoForcedReconstruction A j connector extra tail added h hSigma D k₀ k₁ F hcarrier).size ≤
      D.size + 2 := Nat.add_le_add_left h.2.2.2.2.2 _

end Gallai.WholeBowtie
