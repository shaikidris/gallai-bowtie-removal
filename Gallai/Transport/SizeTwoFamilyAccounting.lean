/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoWords
import Gallai.Transport.ZeroSyndromeTotalCounts
import Gallai.Structure.SyndromeStar

/-! # Ordinary size-two family accounting

The balance theorem consumes per-carrier reconstruction equations. It does
not assume or claim that the candidate is already a decomposition of G.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : B.AnchorNumbering) (i : Fin 13)
variable (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
variable (h : OrdinaryAccepted (B.completedStarState A) i words added)

include h in
/-- Acceptance partitions the original local edge multiset exactly once. -/
theorem sizeTwo_local_edge_sum (e : Sym2 V) :
    (∑ j : Fin 4, ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e) +
    (∑ k : Fin added.length, ((wordEdges added[k]).map (Sym2.map (B.completedLabel A))).count e) =
    ((CompletedStar.targetEdges (B.completedStarState A)).val.map
      (Sym2.map (B.completedLabel A))).count e := by
  have hc := congrArg (fun m : Multiset (Sym2 Star.Vertex) =>
    (m.map (Sym2.map (B.completedLabel A))).count e) h.2.2.1.2
  simp only [Multiset.map_coe,Multiset.coe_count] at hc
  rw [familyEdges,List.map_flatMap,List.count_flatMap] at hc
  dsimp only [Function.comp_def] at hc
  have hs := ZeroSyndrome.localWords_weight_sum words added
    (fun w => ((wordEdges w).map (Sym2.map (B.completedLabel A))).count e)
    (by simp [wordEdges])
  exact hs.symm.trans hc

/-- Added local words become actual simple paths independently of old carriers. -/
noncomputable def sizeTwoAddedPath (k : Fin added.length) : NonemptyPath G :=
  B.realizeOriginalMember A (activeWords words ++ added) h.2.2.1 added[k]
    (List.mem_append_right _ (List.getElem_mem _))

/-- Sum the local carrier equations with each role assigned to one actual
carrier. Released spokes remain on the left until the auxiliary/original
edge comparison cancels them. No original-spoke assumption is made. -/
theorem sizeTwo_family_balance (D : Decomposition B.syndromeStar)
    (f : Fin 4 → Fin D.size) (F : Fin D.size → NonemptyPath G)
    (removed : Fin D.size → List (Sym2 V))
    (hcarrier : ∀ k e, (F k).walk.edges.count e + (removed k).count e =
      ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e +
      ∑ j : Fin 4, if f j = k then
        ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e else 0)
    (e : Sym2 V) :
    (∑ k : Fin D.size, (F k).walk.edges.count e) +
      (∑ k : Fin D.size, (removed k).count e) +
      (∑ k : Fin added.length, (B.sizeTwoAddedPath A i words added h k).walk.edges.count e) =
    (∑ k : Fin D.size, ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e) +
      ((CompletedStar.targetEdges (B.completedStarState A)).val.map
        (Sym2.map (B.completedLabel A))).count e := by
  classical
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => hcarrier k e)
  simp only [Finset.sum_add_distrib] at hs
  have hroles : (∑ k : Fin D.size, ∑ j : Fin 4, if f j = k then
      ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e else 0) =
      ∑ j : Fin 4, ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e := by
    rw [Finset.sum_comm]
    simp
  rw [hroles] at hs
  have hadded : (∑ k : Fin added.length, (B.sizeTwoAddedPath A i words added h k).walk.edges.count e) =
      ∑ k : Fin added.length, ((wordEdges added[k]).map (Sym2.map (B.completedLabel A))).count e := by
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (List.count e) (B.realizeOriginalMember_edges A _ h.2.2.1 _ _)
  have hl := B.sizeTwo_local_edge_sum A i words added h e
  omega

end Gallai.WholeBowtie
