/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRichWords
import Gallai.Transport.SizeTwoBoundaryCounts
import Gallai.Transport.ZeroSyndromeTotalCounts
import Gallai.Operations.OptionalFamilyAppend

/-! # Original-graph assembly for an accounted rich carrier family

Finite record acceptance, the actual old-family balance and the original
auxiliary-edge dictionary imply unique coverage. Coverage is proved here,
not assumed. The family balance and absent merged slot remain explicit
inputs supplied by the through/terminal carrier consumers.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : B.AnchorNumbering) (i : Fin 4)
variable (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
variable (h : Rich.AcceptedRecord (B.completedStarState A) i words added)

include h in
/-- Rich record acceptance partitions the original local edge multiset. -/
theorem sizeTwo_rich_local_edge_sum (e : Sym2 V) :
    (∑ j : Fin 4, ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e) +
    (∑ k : Fin added.length, ((wordEdges added[k]).map (Sym2.map (B.completedLabel A))).count e) =
    ((CompletedStar.targetEdges (B.completedStarState A)).val.map
      (Sym2.map (B.completedLabel A))).count e := by
  have hc := congrArg (fun m : Multiset (Sym2 Star.Vertex) =>
    (m.map (Sym2.map (B.completedLabel A))).count e) h.2.1.2
  simp only [Multiset.map_coe,Multiset.coe_count] at hc
  rw [familyEdges,List.map_flatMap,List.count_flatMap] at hc
  dsimp only [Function.comp_def] at hc
  have hs := ZeroSyndrome.localWords_weight_sum words added
    (fun w => ((wordEdges w).map (Sym2.map (B.completedLabel A))).count e)
    (by simp [wordEdges])
  exact hs.symm.trans hc

/-- Each additional word is an actual nonempty simple path in original G. -/
noncomputable def sizeTwoRichAddedPath (k : Fin added.length) : NonemptyPath G :=
  B.realizeOriginalMember A (activeWords words ++ added) h.2.1 added[k]
    (List.mem_append_right _ (List.getElem_mem _))

include h in
/-- An accounted rich family yields an actual decomposition within one extra
path. Its endpoint totals dominate those of the SAME reconstructed family.
The carrier balance is still an explicit consumer obligation, not hidden
behind a presumed edge-cover or favourable decomposition hypothesis. -/
theorem sizeTwo_rich_assemble
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (D : Decomposition B.syndromeStar) (F : Fin D.size → Option (NonemptyPath G))
    (k : Fin D.size) (hk : F k = none)
    (hbalance : ∀ e : Sym2 V,
      (∑ l, ((F l).map (fun P => P.walk.edges.count e)).getD 0) +
        ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e =
      (∑ l, ((D.path l).walk.edges.map (Sym2.map Subtype.val)).count e) +
        ∑ j : Fin 4, ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e) :
    ∃ P : Decomposition G, P.size ≤ D.size + 1 ∧
      ∀ v : V, (∑ l, ((F l).map (fun Q => (if Q.start = v then 1 else 0) +
        (if Q.finish = v then 1 else 0 : ℕ))).getD 0) ≤ P.endpointCount v := by
  have hc : ∀ e ∈ G.edgeSet,
      (∑ l, ((F l).map (fun P => P.walk.edges.count e)).getD 0) +
      (∑ l : Fin added.length, (B.sizeTwoRichAddedPath A i words added h l).walk.edges.count e) = 1 := by
    intro e he
    have ha : (∑ l : Fin added.length,
        (B.sizeTwoRichAddedPath A i words added h l).walk.edges.count e) =
        ∑ l : Fin added.length, ((wordEdges added[l]).map (Sym2.map (B.completedLabel A))).count e := by
      apply Finset.sum_congr rfl
      intro l _
      exact congrArg (List.count e) (B.realizeOriginalMember_edges A _ h.2.1 added[l] _)
    have hf := hbalance e
    have hl := B.sizeTwo_rich_local_edge_sum A i words added h e
    have hg := B.sizeTwo_original_edge_balance A hSigma D e he
    omega
  obtain ⟨P,hsize,hend⟩ := Decomposition.optional_append_one_credit F
    (B.sizeTwoRichAddedPath A i words added h) k hk hc
  refine ⟨P,by have := h.2.2; omega,?_⟩
  intro v
  rw [hend]
  exact Nat.le_add_right _ _

end Gallai.WholeBowtie
