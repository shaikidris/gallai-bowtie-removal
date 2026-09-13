/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoForcedWords
import Gallai.Transport.SizeTwoPassingRecord

/-! # Reconstructing the central carrier of a forced size-two record

The connector replaces the released run through the hub. The optional s-tail
is inserted at its actual endpoint. Their checked fresh supports are disjoint;
no disjointness with the separate extra carrier is required.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : B.AnchorNumbering) (j : Fin 2)
variable (connector extra tail : List Star.Vertex) (added : List (List Star.Vertex))
variable (h : Forced.AcceptedRecord (B.completedStarState A) j connector extra tail added)

/-- An empty stored s-tail contributes no path. -/
noncomputable def sizeTwoForcedTail : Option (NonemptyPath G) :=
  if ht : tail = [] then none else
    some (B.sizeTwoForcedWord A j connector extra tail added h tail
      (by simp [Forced.localWords,ht]))

/-- A present optional tail is precisely the realized stored word. -/
theorem sizeTwoForcedTail_mem (T : NonemptyPath G)
    (hT : T ∈ B.sizeTwoForcedTail A j connector extra tail added h) :
    ∃ ht : tail ≠ [], T = B.sizeTwoForcedWord A j connector extra tail added h tail
      (by simp [Forced.localWords,ht]) := by
  unfold sizeTwoForcedTail at hT
  split at hT
  · simp at hT
  · rename_i ht
    exact ⟨ht,(show _ = T from by simpa only [Option.mem_some_iff] using hT).symm⟩

/-- Absent and present tails have uniform literal edge accounting. -/
theorem sizeTwoForcedTail_edges :
    (((B.sizeTwoForcedTail A j connector extra tail added h).map
      (fun T => T.walk.edges)).getD []) =
      (wordEdges tail).map (Sym2.map (B.completedLabel A)) := by
  unfold sizeTwoForcedTail
  split
  · rename_i ht
    simp [ht,wordEdges]
  · simpa only [Option.map_some,Option.getD_some] using
      B.sizeTwoForcedWord_edges A j connector extra tail added h tail
        (by simp [Forced.localWords,‹tail ≠ []›])

/-- Both orientations of the actual through run and either location of its
s-endpoint are allowed. The two removed spokes are recorded explicitly. -/
theorem sizeTwo_forced_central_splice (P : NonemptyPath B.syndromeStar)
    (hx : B.completedHub ∈ P.walk.support)
    (hs : P.start ≠ B.completedHub) (ht : B.completedHub ≠ P.finish)
    (hpair :
      ((P.takeTo B.completedHub hx hs).walk.reverse.snd.val = B.completedLabel A .p ∧
       (P.dropFrom B.completedHub hx ht).walk.snd.val = B.completedLabel A .q) ∨
      ((P.takeTo B.completedHub hx hs).walk.reverse.snd.val = B.completedLabel A .q ∧
       (P.dropFrom B.completedHub hx ht).walk.snd.val = B.completedLabel A .p))
    (atStart : Bool)
    (ha : (if atStart then P.start.val else P.finish.val) = B.completedLabel A .s) :
    ∃ N : NonemptyPath G,
      N.start = (if atStart then
        ((B.sizeTwoForcedTail A j connector extra tail added h).map (·.finish)).getD P.start.val
        else P.start.val) ∧
      N.finish = (if atStart then P.finish.val else
        ((B.sizeTwoForcedTail A j connector extra tail added h).map (·.finish)).getD P.finish.val) ∧
      ∀ e : Sym2 V, N.walk.edges.count e +
        ([s(B.label 0,(P.takeTo B.completedHub hx hs).walk.reverse.snd.val),
          s(B.label 0,(P.dropFrom B.completedHub hx ht).walk.snd.val)] : List (Sym2 V)).count e =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e +
        ((wordEdges connector).map (Sym2.map (B.completedLabel A))).count e +
        ((wordEdges tail).map (Sym2.map (B.completedLabel A))).count e := by
  let Q := B.sizeTwoForcedWord A j connector extra tail added h connector
    (by simp [Forced.localWords])
  obtain ⟨hQs,hQt,hQsupport⟩ := B.sizeTwoForcedWord_pair A j connector extra tail added h
    connector (by simp [Forced.localWords]) .p .q h.1
  obtain ⟨M,hM,hne,hMe,hMsupport⟩ := Q.orient_connector
    (P.takeTo B.completedHub hx hs).walk.reverse.snd.val
    (P.dropFrom B.completedHub hx ht).walk.snd.val (by
      simpa only [Q,hQs,hQt] using hpair)
  have hm : ∀ z : B.StarSurvivor, z.val ∈ M.support →
      z.val = (P.takeTo B.completedHub hx hs).walk.reverse.snd.val ∨
      z.val = (P.dropFrom B.completedHub hx ht).walk.snd.val ∨ z.val = B.label 0 := by
    intro z hz
    have hz' : z.val ∈ Q.walk.support := by
      have hf := List.mem_toFinset.mpr hz
      rw [hMsupport] at hf
      exact List.mem_toFinset.mp hf
    rcases hpair with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · rcases hQsupport z hz' with hz | hz | hz
      · exact Or.inl (hz.trans hu.symm)
      · exact Or.inr (Or.inl (hz.trans hv.symm))
      · exact Or.inr (Or.inr hz)
    · rcases hQsupport z hz' with hz | hz | hz
      · exact Or.inr (Or.inl (hz.trans hu.symm))
      · exact Or.inl (hz.trans hv.symm)
      · exact Or.inr (Or.inr hz)
  let O := B.sizeTwoForcedTail A j connector extra tail added h
  have tails (endpoint : V) (he : endpoint = B.completedLabel A .s) :
      ∀ R ∈ O, endpoint = R.start ∧
        (∀ v ∈ R.walk.support, v = R.start ∨ v ∈ B.vertices) ∧
        Disjoint (M.support.toFinset ∩ B.vertices) (R.freshSupport B.vertices) := by
    intro R hR
    obtain ⟨htail,rfl⟩ := B.sizeTwoForcedTail_mem A j connector extra tail added h R hR
    obtain ⟨hRs,hRv⟩ := B.sizeTwoForcedWord_single A j connector extra tail added h
      tail (by simp [Forced.localWords,htail]) .s (h.2.2.1.resolve_left htail)
    refine ⟨he.trans hRs.symm,?_,?_⟩
    · intro v hv
      exact (hRv v hv).imp (fun hv => hv.trans hRs.symm) id
    · rw [hMsupport]
      simpa only [NonemptyPath.freshSupport,Q] using
        B.sizeTwoForcedWord_disjoint A j connector extra tail added h connector tail
          (by simp [Forced.localWords]) (by simp [Forced.localWords,htail]) h.2.2.2.1
  let U := if atStart then O else none
  let T := if atStart then none else O
  have hU : ∀ R ∈ U, P.start.val = R.start ∧
      (∀ v ∈ R.walk.support, v = R.start ∨ v ∈ B.vertices) ∧
      Disjoint (M.support.toFinset ∩ B.vertices) (R.freshSupport B.vertices) := by
    cases atStart
    · simp [U]
    · exact tails P.start.val ha
  have hT : ∀ R ∈ T, P.finish.val = R.start ∧
      (∀ v ∈ R.walk.support, v = R.start ∨ v ∈ B.vertices) ∧
      Disjoint (M.support.toFinset ∩ B.vertices) (R.freshSupport B.vertices) := by
    cases atStart
    · exact tails P.finish.val ha
    · simp [T]
  have hUT : ∀ R ∈ U, ∀ S ∈ T,
      Disjoint (R.freshSupport B.vertices) (S.freshSupport B.vertices) := by
    cases atStart <;> simp [U,T]
  obtain ⟨N,hNs,hNt,hNe⟩ := B.syndrome_passing_release_optional P hx hs ht
    M hM hne hm U T hU hT hUT
  refine ⟨N,?_,?_,?_⟩
  · cases atStart <;> simpa [U,O] using hNs
  · cases atStart <;> simpa [T,O] using hNt
  · intro e
    have heM : M.edges.count e =
        ((wordEdges connector).map (Sym2.map (B.completedLabel A))).count e :=
      (hMe e).trans (congrArg (List.count e)
        (B.sizeTwoForcedWord_edges A j connector extra tail added h connector
          (by simp [Forced.localWords])))
    have heO := congrArg (List.count e)
      (B.sizeTwoForcedTail_edges A j connector extra tail added h)
    change ((O.map (fun R => R.walk.edges)).getD []).count e = _ at heO
    have he := hNe e
    cases atStart <;>
      simp only [U,T,Bool.false_eq_true,↓reduceIte,Option.map_none,
        Option.getD_none,List.count_nil,heM,heO,Nat.add_zero] at he ⊢ <;>
      exact he

end Gallai.WholeBowtie
