/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRichSeparatedMerge
import Gallai.Transport.SizeTwoRichSeparatedWords
import Gallai.Transport.SizeTwoPassingDispatch

/-! # Certificate-driven two-carrier replacement in either attachment order -/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

theorem sizeTwo_separated_pair (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (i : Fin 4) (connector tail : List Star.Vertex) (added : List (List Star.Vertex))
    (h : Rich.SeparatedAccepted (B.completedStarState A) i connector tail added)
    (w : B.StarSurvivor) (hwlabel : w.val = B.completedLabel A (Rich.reserve i))
    (hsep : ¬ B.syndromeStar.Reachable B.completedHub w)
    (P : NonemptyPath B.syndromeStar) (hx : B.completedHub ∈ P.walk.support)
    (hs : P.start ≠ B.completedHub) (ht : B.completedHub ≠ P.finish)
    (Q : NonemptyPath B.syndromeStar) (hQ : Q.finish = w) :
    ∃ N₀ N₁ : NonemptyPath G,
      (∀ e : Sym2 V, N₀.walk.edges.count e + N₁.walk.edges.count e +
        ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e +
        (Q.walk.edges.map (Sym2.map Subtype.val)).count e +
        ((wordEdges connector).map (Sym2.map (B.completedLabel A))).count e +
        ((wordEdges tail).map (Sym2.map (B.completedLabel A))).count e) ∧
      ∀ v : V, (∀ t, B.completedLabel A t ≠ v) →
        ((if N₀.start = v then 1 else 0) + (if N₀.finish = v then 1 else 0 : ℕ)) +
        ((if N₁.start = v then 1 else 0) + (if N₁.finish = v then 1 else 0 : ℕ)) =
        ((if P.start.val = v then 1 else 0) + (if P.finish.val = v then 1 else 0 : ℕ)) +
        ((if Q.start.val = v then 1 else 0) + (if Q.finish.val = v then 1 else 0 : ℕ)) := by
  classical
  obtain ⟨C,T,hCs,hCt,hTs,hCv,hTv,hCe,hTe,hTend⟩ :=
    B.sizeTwo_separated_words A i connector tail added h
  have hQl : Q.finish.val = B.completedLabel A (Rich.reserve i) :=
    (congrArg Subtype.val hQ).trans hwlabel
  let ca (b : B.StarSurvivor) (hb : b.val = B.completedLabel A .p) :=
    C.walk.copy (hCs.trans hb.symm) (hCt.trans hQl.symm)
  let ta (b : B.StarSurvivor) (hb : b.val = B.completedLabel A .q) :=
    T.walk.copy (hTs.trans hb.symm) rfl
  have caProps (b : B.StarSurvivor) (hb : b.val = B.completedLabel A .p) :
      (ca b hb).IsPath ∧ ¬ (ca b hb).Nil ∧
      ∀ v : B.StarSurvivor, v.val ∈ (ca b hb).support →
        v.val = b.val ∨ v.val = Q.finish.val ∨ v.val = B.label 0 := by
    refine ⟨(SimpleGraph.Walk.isPath_copy _ _ _).mpr C.isPath,?_,?_⟩
    · simpa only [ca,SimpleGraph.Walk.nil_copy] using C.nonempty
    · intro v hv
      have hh := hCv v (by simpa only [ca,SimpleGraph.Walk.support_copy] using hv)
      simpa only [hb,hQl] using hh
  have taProps (b : B.StarSurvivor) (hb : b.val = B.completedLabel A .q) :
      (ta b hb).IsPath ∧ ¬ (ta b hb).Nil ∧
      ∀ v : B.StarSurvivor, v.val ∈ (ta b hb).support →
        v.val = b.val ∨ v.val = B.label 0 := by
    refine ⟨(SimpleGraph.Walk.isPath_copy _ _ _).mpr T.isPath,?_,?_⟩
    · simpa only [ta,SimpleGraph.Walk.nil_copy] using T.nonempty
    · intro v hv
      have hh := hTv v (by simpa only [ta,SimpleGraph.Walk.support_copy] using hv)
      simpa only [hb] using hh
  let b := (P.takeTo B.completedHub hx hs).walk.reverse.snd
  let c := (P.dropFrom B.completedHub hx ht).walk.snd
  have hpair := B.sizeTwo_passing_attachment_pair A hSigma P hx hs ht
  have out : ∃ N₀ N₁ : NonemptyPath G,
      ((N₀.start = P.start.val ∧ N₁.start = P.finish.val) ∨
       (N₀.start = P.finish.val ∧ N₁.start = P.start.val)) ∧
      N₀.finish = Q.start.val ∧ N₁.finish = T.finish ∧
      ∀ e : Sym2 V, N₀.walk.edges.count e + N₁.walk.edges.count e +
        ([s(B.label 0,b.val),s(B.label 0,c.val)] : List (Sym2 V)).count e =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e +
        (Q.walk.edges.map (Sym2.map Subtype.val)).count e +
        C.walk.edges.count e + T.walk.edges.count e := by
    rcases hpair with ⟨hb,hc⟩ | ⟨hb,hc⟩
    · obtain ⟨hm,hn,hmv⟩ := caProps b hb
      obtain ⟨htp,htn,htv⟩ := taProps c hc
      obtain ⟨N₀,N₁,h₀,h₁,h₂,h₃,he⟩ := B.sizeTwo_separated_merge w hsep P hx hs ht Q hQ
        (ca b hb) (ta c hc) hm hn htp htn hmv htv
      refine ⟨N₀,N₁,Or.inl ⟨h₀,h₂⟩,h₁,h₃,?_⟩
      intro e
      simpa only [ca,ta,SimpleGraph.Walk.edges_copy] using he e
    · obtain ⟨hm,hn,hmv⟩ := caProps c hc
      obtain ⟨htp,htn,htv⟩ := taProps b hb
      obtain ⟨N₀,N₁,h₀,h₁,h₂,h₃,he⟩ := B.sizeTwo_separated_merge_right w hsep P hx hs ht Q hQ
        (ca c hc) (ta b hb) hm hn htp htn hmv htv
      refine ⟨N₀,N₁,Or.inr ⟨h₀,h₂⟩,h₁,h₃,?_⟩
      intro e
      simpa only [ca,ta,SimpleGraph.Walk.edges_copy] using he e
  obtain ⟨N₀,N₁,hstarts,hf₀,hf₁,he⟩ := out
  refine ⟨N₀,N₁,?_,?_⟩
  · intro e
    have hh := he e
    rw [hCe,hTe] at hh
    have hremoved : ([s(B.label 0,b.val),s(B.label 0,c.val)] : List (Sym2 V)).count e =
        ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e := by
      rcases hpair with ⟨hb,hc⟩ | ⟨hb,hc⟩
      · rw [hb,hc]; rfl
      · rw [hb,hc]
        simp only [completedLabel,List.count_cons,List.count_nil,Nat.zero_add]
        exact Nat.add_comm _ _
    rw [hremoved] at hh
    exact hh
  · intro v hv
    have hQt : Q.finish.val ≠ v := fun he => hv (Rich.reserve i) (hQl.symm.trans he)
    have hTt : T.finish ≠ v := hTend v hv
    rcases hstarts with ⟨h₀,h₁⟩ | ⟨h₀,h₁⟩ <;>
      simp only [h₀,h₁,hf₀,hf₁,if_neg hQt,if_neg hTt,Nat.add_zero] <;> omega

end Gallai.WholeBowtie
