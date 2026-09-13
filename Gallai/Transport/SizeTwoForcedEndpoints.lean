/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoForcedCentral
import Gallai.Transport.SizeTwoForcedExtra

/-! # Outside endpoint preservation for the two forced carrier splices

Both endpoints are tracked on the same reconstructed paths that carry the
edge equations. No independently selected endpoint witness is substituted.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : B.AnchorNumbering) (j : Fin 2)
variable (connector extra tail : List Star.Vertex) (added : List (List Star.Vertex))
variable (h : Forced.AcceptedRecord (B.completedStarState A) j connector extra tail added)

/-- Realized finite words cannot finish at a vertex outside all local labels. -/
theorem sizeTwoForcedWord_finish_ne (word : List Star.Vertex)
    (hw : word ∈ Forced.localWords connector extra tail added)
    (v : V) (hv : ∀ t, B.completedLabel A t ≠ v) :
    (B.sizeTwoForcedWord A j connector extra tail added h word hw).finish ≠ v := by
  intro he
  have hm := (B.sizeTwoForcedWord A j connector extra tail added h word hw).walk.end_mem_support
  rw [B.sizeTwoForcedWord_support,he] at hm
  obtain ⟨t,_,ht⟩ := List.mem_map.mp hm
  exact hv t ht

/-- An optional tail at s preserves each outside endpoint predicate. -/
theorem sizeTwoForcedTail_endpoint_iff (endpoint v : V)
    (he : endpoint = B.completedLabel A .s) (hv : ∀ t, B.completedLabel A t ≠ v) :
    (((B.sizeTwoForcedTail A j connector extra tail added h).map (·.finish)).getD endpoint = v) ↔
      endpoint = v := by
  cases ho : B.sizeTwoForcedTail A j connector extra tail added h with
  | none => simp
  | some T =>
    have hT : T ∈ B.sizeTwoForcedTail A j connector extra tail added h := by rw [ho]; simp
    obtain ⟨ht,hTeq⟩ := B.sizeTwoForcedTail_mem A j connector extra tail added h T hT
    have hnew : T.finish ≠ v := by
      rw [hTeq]
      exact B.sizeTwoForcedWord_finish_ne A j connector extra tail added h tail _ v hv
    have hold : endpoint ≠ v := fun hh => hv .s (he.symm.trans hh)
    simp [hnew,hold]

/-- The central carrier's explicit endpoint formulas preserve all outside
endpoint occurrences, including when the optional tail is empty. -/
theorem sizeTwo_forced_central_endpoints (P : NonemptyPath B.syndromeStar)
    (N : NonemptyPath G) (atStart : Bool)
    (ha : (if atStart then P.start.val else P.finish.val) = B.completedLabel A .s)
    (hstart : N.start = (if atStart then
      ((B.sizeTwoForcedTail A j connector extra tail added h).map (·.finish)).getD P.start.val
      else P.start.val))
    (hfinish : N.finish = (if atStart then P.finish.val else
      ((B.sizeTwoForcedTail A j connector extra tail added h).map (·.finish)).getD P.finish.val))
    (v : V) (hv : ∀ t, B.completedLabel A t ≠ v) :
    (N.start = v ↔ P.start.val = v) ∧ (N.finish = v ↔ P.finish.val = v) := by
  rw [hstart,hfinish]
  cases atStart
  · exact ⟨Iff.rfl,B.sizeTwoForcedTail_endpoint_iff A j connector extra tail added h
      P.finish.val v ha hv⟩
  · exact ⟨B.sizeTwoForcedTail_endpoint_iff A j connector extra tail added h
      P.start.val v ha hv,Iff.rfl⟩

/-- The extra splice now retains which old endpoint was replaced. This links
its endpoint preservation to its actual reconstruction witness. -/
theorem sizeTwo_forced_extra_endpoints (P : NonemptyPath B.syndromeStar)
    (N : NonemptyPath G)
    (hend :
      (P.start.val = B.completedLabel A (Forced.extraAnchor j) ∧
       N.start = (B.sizeTwoForcedExtra A j connector extra tail added h).finish ∧
       N.finish = P.finish.val) ∨
      (P.finish.val = B.completedLabel A (Forced.extraAnchor j) ∧
       N.start = P.start.val ∧
       N.finish = (B.sizeTwoForcedExtra A j connector extra tail added h).finish))
    (v : V) (hv : ∀ t, B.completedLabel A t ≠ v) :
    (N.start = v ↔ P.start.val = v) ∧ (N.finish = v ↔ P.finish.val = v) := by
  have hnew : (B.sizeTwoForcedExtra A j connector extra tail added h).finish ≠ v :=
    B.sizeTwoForcedWord_finish_ne A j connector extra tail added h extra _ v hv
  rcases hend with ⟨ha,hNs,hNt⟩ | ⟨ha,hNs,hNt⟩
  · have hold : P.start.val ≠ v := fun hh => hv _ (ha.symm.trans hh)
    simp [hNs,hNt,hnew,hold]
  · have hold : P.finish.val ≠ v := fun hh => hv _ (ha.symm.trans hh)
    simp [hNs,hNt,hnew,hold]

end Gallai.WholeBowtie
