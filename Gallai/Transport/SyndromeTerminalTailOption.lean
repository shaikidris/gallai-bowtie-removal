/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SyndromeOptionalTerminalRelease

/-! # Uniform optional-tail reconstruction at a released terminal spoke

The output is zero or one nonempty paths. Absence is permitted only through
the empty-prefix branch; no nil carrier is smuggled into a decomposition.
Exact edge counts and outside endpoints are supplied by the same output.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Both empty and present tails fit a single optional-carrier interface. -/
theorem syndrome_terminal_tail_option (P : NonemptyPath B.syndromeStar)
    (hx : P.finish = B.completedHub) (T : Option (NonemptyPath G))
    (hT : ∀ Q ∈ T, Q.start = P.walk.reverse.snd.val ∧
      ∀ v : B.StarSurvivor, v.val ∈ Q.walk.support →
        v.val = P.walk.reverse.snd.val ∨ v.val = B.label 0) :
    ∃ O : Option (NonemptyPath G),
      (∀ e : Sym2 V, ((O.map (fun N => N.walk.edges)).getD []).count e +
        (if s(B.label 0,P.walk.reverse.snd.val) = e then 1 else 0) =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e +
        ((T.map (fun Q => Q.walk.edges)).getD []).count e) ∧
      ∀ v : V, v ≠ B.label 0 → v ≠ P.walk.reverse.snd.val →
        (∀ Q ∈ T, Q.finish ≠ v) →
        (O.map (fun N => (if N.start = v then 1 else 0) +
          (if N.finish = v then 1 else 0 : ℕ))).getD 0 =
        (if P.start.val = v then 1 else 0) + (if P.finish.val = v then 1 else 0) := by
  classical
  cases T with
  | none =>
    obtain ⟨O,he,hend⟩ := B.syndrome_terminal_release_empty P hx
    refine ⟨O,?_,?_⟩
    · intro e
      have hc := congrArg (List.count e) he
      simpa only [List.count_append,List.count_cons,List.count_nil,
        Nat.zero_add,beq_iff_eq,Option.map_none,Option.getD_none,Nat.add_zero] using hc
    · intro v hvx hvq _
      exact hend v hvx hvq
  | some Q =>
    obtain ⟨ha,hQ⟩ := hT Q (by simp)
    let M := Q.walk.copy ha rfl
    have hM : M.IsPath := (SimpleGraph.Walk.isPath_copy _ _ _).mpr Q.isPath
    have hne : ¬ M.Nil := by simpa only [M,SimpleGraph.Walk.nil_copy] using Q.nonempty
    have hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
        v.val = P.walk.reverse.snd.val ∨ v.val = B.label 0 := by
      intro v hv
      exact hQ v (by simpa only [M,SimpleGraph.Walk.support_copy] using hv)
    obtain ⟨N,hs,ht,he⟩ := B.syndrome_terminal_release P hx M hM hne hm
    refine ⟨some N,?_,?_⟩
    · intro e
      simpa only [Option.map_some,Option.getD_some,M,SimpleGraph.Walk.edges_copy] using he e
    · intro v hvx _ hvT
      have hvQ := hvT Q (by simp)
      have hvP : P.finish.val ≠ v := by
        rw [hx]
        exact Ne.symm hvx
      simp only [Option.map_some,Option.getD_some,hs,ht,if_neg hvQ,if_neg hvP]

end Gallai.WholeBowtie
