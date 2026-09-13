/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.FreshCarrierBothEnds

/-! # Optional tails preserve one carrier, including empty certificate roles -/
namespace Gallai.NonemptyPath
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Uniform optional-tail transport. None means no edge and no new path;
the old endpoint is retained rather than represented by a trivial path. -/
theorem extend_optional_fresh (P : NonemptyPath G)
    (L R : Option (NonemptyPath G)) (F : Finset V)
    (hL : ∀ T ∈ L, P.start = T.start ∧
      (∀ v ∈ T.walk.support, v = T.start ∨ v ∈ F) ∧
      Disjoint (P.freshSupport F) (T.freshSupport F))
    (hR : ∀ T ∈ R, P.finish = T.start ∧
      (∀ v ∈ T.walk.support, v = T.start ∨ v ∈ F) ∧
      Disjoint (P.freshSupport F) (T.freshSupport F))
    (hLR : ∀ U ∈ L, ∀ T ∈ R, Disjoint (U.freshSupport F) (T.freshSupport F)) :
    ∃ N : NonemptyPath G,
      N.start = (L.map (·.finish)).getD P.start ∧
      N.finish = (R.map (·.finish)).getD P.finish ∧
      N.walk.edges = (((L.map (fun T => T.walk.edges.reverse)).getD []) ++
        P.walk.edges) ++ ((R.map (fun T => T.walk.edges)).getD []) := by
  cases L with
  | none =>
    cases R with
    | none => exact ⟨P,rfl,rfl,by simp⟩
    | some T =>
      obtain ⟨hj,ht,hd⟩ := hR T (by simp)
      refine ⟨P.appendFresh T F hj ht hd,rfl,rfl,?_⟩
      simpa only [Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
        List.nil_append] using P.appendFresh_edges T F hj ht hd
  | some U =>
    obtain ⟨hj,ht,hd⟩ := hL U (by simp)
    cases R with
    | none =>
      have hd' : Disjoint (P.reverse.freshSupport F) (U.freshSupport F) := by
        rwa [reverse_freshSupport]
      let N := (P.reverse.appendFresh U F hj ht hd').reverse
      refine ⟨N,rfl,rfl,?_⟩
      have he := congrArg List.reverse (P.reverse.appendFresh_edges U F hj ht hd')
      simpa only [N,reverse_edges,List.reverse_append,List.reverse_reverse,
        Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,List.append_nil] using he
    | some T =>
      obtain ⟨hjT,htT,hdT⟩ := hR T (by simp)
      obtain ⟨N,hNs,hNt,hNe,_⟩ := P.extend_both_fresh U T F hj hjT ht htT hd hdT
        (hLR U (by simp) T (by simp))
      exact ⟨N,hNs,hNt,hNe⟩

end Gallai.NonemptyPath
