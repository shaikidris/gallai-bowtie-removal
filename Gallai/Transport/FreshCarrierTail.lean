/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.Concatenate

/-! # Appending a tail while tracking consumed fresh vertices -/
namespace Gallai.NonemptyPath
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Vertices of the reusable local core already consumed by one carrier. -/
def freshSupport (P : NonemptyPath G) (F : Finset V) : Finset V :=
  P.walk.support.toFinset ∩ F

/-- A tail using only its attachment and unconsumed fresh vertices is safe,
even when the old carrier has already received a connector or another tail. -/
def appendFresh (P T : NonemptyPath G) (F : Finset V)
    (hj : P.finish = T.start)
    (ht : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ F)
    (hd : Disjoint (P.freshSupport F) (T.freshSupport F)) : NonemptyPath G :=
  P.append T hj (by
    intro v hv hvt
    rcases ht v hvt with he | hf
    · exact he.trans hj.symm
    · exact (Finset.disjoint_left.mp hd
        (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hv,hf⟩)
        (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hvt,hf⟩)).elim)

theorem appendFresh_edges (P T : NonemptyPath G) (F : Finset V)
    (hj : P.finish = T.start)
    (ht : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ F)
    (hd : Disjoint (P.freshSupport F) (T.freshSupport F)) :
    (P.appendFresh T F hj ht hd).walk.edges = P.walk.edges ++ T.walk.edges :=
  P.append_edges T hj _

/-- The updated footprint is exact, so another disjoint tail can be added. -/
theorem appendFresh_support (P T : NonemptyPath G) (F : Finset V)
    (hj : P.finish = T.start)
    (ht : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ F)
    (hd : Disjoint (P.freshSupport F) (T.freshSupport F)) :
    (P.appendFresh T F hj ht hd).freshSupport F = P.freshSupport F ∪ T.freshSupport F := by
  ext v
  simp only [freshSupport,Finset.mem_inter,List.mem_toFinset,Finset.mem_union]
  change (v ∈ (P.walk.append (T.walk.copy hj.symm rfl)).support ∧ _) ↔ _
  rw [SimpleGraph.Walk.mem_support_append_iff,SimpleGraph.Walk.support_copy]
  tauto

/-- Endpoint bookkeeping for the whole-family budget calculation. -/
theorem appendFresh_endpoint (P T : NonemptyPath G) (F : Finset V)
    (hj : P.finish = T.start)
    (ht : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ F)
    (hd : Disjoint (P.freshSupport F) (T.freshSupport F)) (v : V) :
    ((if (P.appendFresh T F hj ht hd).start = v then 1 else 0) +
      (if (P.appendFresh T F hj ht hd).finish = v then 1 else 0)) +
      (if P.finish = v then 2 else 0 : ℕ) =
    ((if P.start = v then 1 else 0) + (if P.finish = v then 1 else 0)) +
      ((if T.start = v then 1 else 0) + (if T.finish = v then 1 else 0)) :=
  P.append_endpoint_contribution T hj _ v

end Gallai.NonemptyPath
