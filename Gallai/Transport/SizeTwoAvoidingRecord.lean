/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoPassingRecord

/-! # Ordinary remote-only and untouched carriers -/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Every unchanged old piece avoids the entire local core after embedding. -/
theorem syndromeAvoidingPath_fresh_empty (P : NonemptyPath B.syndromeStar)
    (hx : B.completedHub ∉ P.walk.support) :
    (B.syndromeAvoidingPath P hx).freshSupport B.vertices = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hp,hB⟩ := Finset.mem_inter.mp hv
  have hs : (B.syndromeAvoidingPath P hx).walk.support = P.walk.support.map Subtype.val := by
    unfold syndromeAvoidingPath completedAvoidingPath
    rw [B.completedMapWalk_support]
    simp only [NonemptyPath.map,SimpleGraph.Walk.support_map,List.map_map]
    rfl
  have hp' := List.mem_toFinset.mp hp
  rw [hs] at hp'
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hp'
  have hux : u = B.completedHub := Subtype.ext (B.survivor_mem_vertices u hB)
  exact hx (hux ▸ hu)

/-- Hub-free carriers receive zero, one or two remote roles. The same contract
covers an entirely untouched old path, with both assigned roles absent. -/
theorem sizeTwo_avoiding_record (A : B.AnchorNumbering) (i : Fin 13)
    (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
    (h : OrdinaryAccepted (B.completedStarState A) i words added)
    (P : NonemptyPath B.syndromeStar) (hx : B.completedHub ∉ P.walk.support)
    (left right : Option (Fin 4))
    (hleft : ∀ k ∈ left, ∃ symbol : Star.Vertex, boundary i k = [symbol] ∧
      P.start.val = B.completedLabel A symbol)
    (hright : ∀ k ∈ right, ∃ symbol : Star.Vertex, boundary i k = [symbol] ∧
      P.finish.val = B.completedLabel A symbol)
    (howners : ∀ k ∈ left, ∀ l ∈ right, k ≠ l ∧ owner i k = owner i l) :
    ∃ N : NonemptyPath G,
      N.start = ((B.sizeTwoAssignedRole A i words added h left).map (·.finish)).getD P.start.val ∧
      N.finish = ((B.sizeTwoAssignedRole A i words added h right).map (·.finish)).getD P.finish.val ∧
      ∀ e : Sym2 V, N.walk.edges.count e =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e +
        (left.map (fun k => ((wordEdges (words k)).map (Sym2.map (B.completedLabel A))).count e)).getD 0 +
        (right.map (fun k => ((wordEdges (words k)).map (Sym2.map (B.completedLabel A))).count e)).getD 0 := by
  let C := B.syndromeAvoidingPath P hx
  let U := B.sizeTwoAssignedRole A i words added h left
  let T := B.sizeTwoAssignedRole A i words added h right
  have tails (o : Option (Fin 4)) (endpoint : V)
      (ho : ∀ k ∈ o, ∃ symbol : Star.Vertex, boundary i k = [symbol] ∧
        endpoint = B.completedLabel A symbol) :
      ∀ R ∈ B.sizeTwoAssignedRole A i words added h o,
        endpoint = R.start ∧ (∀ v ∈ R.walk.support, v = R.start ∨ v ∈ B.vertices) ∧
        Disjoint (C.freshSupport B.vertices) (R.freshSupport B.vertices) := by
    intro R hR
    obtain ⟨k,hk,hkn,rfl⟩ := B.sizeTwoAssignedRole_mem A i words added h o R hR
    obtain ⟨symbol,hb,he⟩ := ho k hk
    obtain ⟨hRs,hRv⟩ := B.sizeTwoRole_single A i words added h k hkn symbol hb
    refine ⟨he.trans hRs.symm,?_,?_⟩
    · intro v hv
      exact (hRv v hv).imp (fun hv => hv.trans hRs.symm) id
    · rw [show C.freshSupport B.vertices = ∅ from B.syndromeAvoidingPath_fresh_empty P hx]
      exact Finset.disjoint_empty_left _
  have hUT : ∀ R ∈ U, ∀ S ∈ T,
      Disjoint (R.freshSupport B.vertices) (S.freshSupport B.vertices) := by
    intro R hR S hS
    obtain ⟨k,hk,hkn,rfl⟩ := B.sizeTwoAssignedRole_mem A i words added h left R hR
    obtain ⟨l,hl,hln,rfl⟩ := B.sizeTwoAssignedRole_mem A i words added h right S hS
    obtain ⟨hne,ho⟩ := howners k hk l hl
    exact B.sizeTwoRole_same_owner_disjoint A i words added h k l hkn hln hne ho
  obtain ⟨N,hNs,hNt,hNe⟩ := C.extend_optional_fresh U T B.vertices
    (tails left P.start.val hleft) (tails right P.finish.val hright) hUT
  refine ⟨N,hNs,hNt,?_⟩
  intro e
  have he := congrArg (List.count e) hNe
  have hrev : ((U.map (fun R => R.walk.edges.reverse)).getD []).count e =
      ((U.map (fun R => R.walk.edges)).getD []).count e := by
    cases U <;> simp only [Option.map_none,Option.map_some,Option.getD_none,
      Option.getD_some,List.count_reverse]
  simp only [List.count_append,hrev] at he
  have hC := congrArg (List.count e) (B.syndromeAvoidingPath_edges P hx)
  have hU := B.sizeTwoAssignedRole_count A i words added h left e
  have hT := B.sizeTwoAssignedRole_count A i words added h right e
  change C.walk.edges.count e = _ at hC
  change ((U.map (fun R => R.walk.edges)).getD []).count e = _ at hU
  change ((T.map (fun R => R.walk.edges)).getD []).count e = _ at hT
  omega

end Gallai.WholeBowtie
