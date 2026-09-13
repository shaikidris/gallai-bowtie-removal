/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRichReconstruction
import Gallai.Transport.SizeTwoRichTerminalMerge
import Gallai.Transport.SizeTwoRichReserveTail
import Gallai.Operations.FamilyBalance

/-! # Complete rich terminal reconstruction on selected actual carriers

Merge the p-terminal carrier with one remote carrier, restore the q-terminal
carrier optionally, and extend the other two reserve carriers. Five old slots
produce at most four paths; the accepted additional paths use that credit.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The rich terminal certificate constructs a genuine original-graph
decomposition, including empty q-prefix/tail cases, preserving outside reserves. -/
theorem sizeTwo_rich_terminal_consumer (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (i : Fin 4) (hi : Rich.isThrough i = false)
    (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
    (h : Rich.AcceptedRecord (B.completedStarState A) i words added)
    (D : Decomposition B.syndromeStar) (j : Fin 5 ↪ Fin D.size)
    (w : B.StarSurvivor) (hwlabel : w.val = B.completedLabel A (Rich.reserve i))
    (hsep : ¬ B.syndromeStar.Reachable B.completedHub w)
    (hx₀ : (D.path (j 0)).finish = B.completedHub)
    (hx₁ : (D.path (j 1)).finish = B.completedHub)
    (hp : (D.path (j 0)).walk.reverse.snd.val = B.completedLabel A .p)
    (hq : (D.path (j 1)).walk.reverse.snd.val = B.completedLabel A .q)
    (havoid : ∀ k, k ≠ j 0 → k ≠ j 1 → B.completedHub ∉ (D.path k).walk.support)
    (hw : ∀ l : Fin 3, (D.path (j l.succ.succ)).finish = w) :
    ∃ P : Decomposition G, P.size ≤ D.size + 1 ∧
      ∀ v : B.StarSurvivor, (∀ t, B.completedLabel A t ≠ v.val) →
        D.endpointCount v ≤ P.endpointCount v.val := by
  classical
  have hw₂ : (D.path (j 2)).finish = w := hw 0
  have hw₃ : (D.path (j 3)).finish = w := hw 1
  have hw₄ : (D.path (j 4)).finish = w := hw 2
  have hn : words 0 ≠ [] := by
    intro he
    exact Rich.mandatory_nonempty i 0 (Or.inl rfl) (he ▸ h.1 0)
  have hb₀ : Rich.boundary i 0 = [.p,Rich.reserve i] := by simp [Rich.boundary,hi]
  have hb₁ : Rich.boundary i 1 = [.q] := by simp [Rich.boundary,hi]
  have hb₂ : Rich.boundary i 2 = [Rich.reserve i] := by simp [Rich.boundary,hi]
  have hb₃ : Rich.boundary i 3 = [Rich.reserve i] := by simp [Rich.boundary,hi]
  let C := B.sizeTwoRichRole A i words added h 0 hn
  obtain ⟨hCs,hCt,hCv⟩ := B.sizeTwoRichRole_pair A i words added h 0 hn .p (Rich.reserve i) hb₀
  have hCs' : C.start = (D.path (j 0)).walk.reverse.snd.val := hCs.trans hp.symm
  have hCt' : C.finish = (D.path (j 2)).finish.val :=
    hCt.trans (hwlabel.symm.trans (congrArg Subtype.val hw₂).symm)
  let M := C.walk.copy hCs' hCt'
  have hM : M.IsPath := (SimpleGraph.Walk.isPath_copy _ _ _).mpr C.isPath
  have hne : ¬ M.Nil := by simpa only [M,SimpleGraph.Walk.nil_copy] using C.nonempty
  have hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = (D.path (j 0)).walk.reverse.snd.val ∨
      v.val = (D.path (j 2)).finish.val ∨ v.val = B.label 0 := by
    intro v hv
    simp only [M,SimpleGraph.Walk.support_copy] at hv
    simpa only [← hp,← hwlabel,hw₂] using hCv v hv
  obtain ⟨N,hsN,htN,heN⟩ := B.sizeTwo_rich_terminal_merge w hsep
    (D.path (j 0)) (D.path (j 2)) hx₀ hw₂ M hM hne hm
  obtain ⟨O,heO,hendO⟩ := B.sizeTwo_rich_optional_terminal A i words added h 1 .q hb₁
    (D.path (j 1)) hx₁ hq
  have hfree₃ : B.completedHub ∉ (D.path (j 3)).walk.support :=
    havoid (j 3) (fun he => (by decide : (3 : Fin 5) ≠ 0) (j.injective he))
      (fun he => (by decide : (3 : Fin 5) ≠ 1) (j.injective he))
  have hfree₄ : B.completedHub ∉ (D.path (j 4)).walk.support :=
    havoid (j 4) (fun he => (by decide : (4 : Fin 5) ≠ 0) (j.injective he))
      (fun he => (by decide : (4 : Fin 5) ≠ 1) (j.injective he))
  obtain ⟨R,heR,hendR⟩ := B.sizeTwo_rich_reserve_tail A i words added h 2 (Rich.reserve i)
    hb₂ (D.path (j 3)) hfree₃ ((congrArg Subtype.val hw₃).trans hwlabel)
  obtain ⟨S,heS,hendS⟩ := B.sizeTwo_rich_reserve_tail A i words added h 3 (Rich.reserve i)
    hb₃ (D.path (j 4)) hfree₄ ((congrArg Subtype.val hw₄).trans hwlabel)
  let base : Fin D.size → Option (NonemptyPath G) := fun k =>
    if hk : B.completedHub ∈ (D.path k).walk.support then none
    else some (B.syndromeAvoidingPath (D.path k) hk)
  let outs : Fin 5 → Option (NonemptyPath G) := ![some N,O,none,some R,some S]
  let F := replaceFamily base j outs
  have hselected (l : Fin 5) : F (j l) = outs l := replaceFamily_selected base j outs l
  have hother (k : Fin D.size) (hk : ∀ l, j l ≠ k) :
      ∃ hf : B.completedHub ∉ (D.path k).walk.support,
        F k = some (B.syndromeAvoidingPath (D.path k) hf) := by
    have hf := havoid k (hk 0).symm (hk 1).symm
    refine ⟨hf,?_⟩
    change replaceFamily base j outs k = _
    rw [replaceFamily_unselected base j outs k (by rintro ⟨l,hl⟩; exact hk l hl)]
    exact dif_neg hf
  have five (f : Fin 5 → ℕ) : (∑ l, f l) = f 0 + f 1 + f 2 + f 3 + f 4 := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + 0)))) = _
    omega
  have four (f : Fin 4 → ℕ) : (∑ l, f l) = f 0 + f 1 + f 2 + f 3 := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
    change f 0 + (f 1 + (f 2 + (f 3 + 0))) = _
    omega
  have hmeasure (measure : NonemptyPath G → ℕ) :
      (∑ l : Fin 5, ((F (j l)).map measure).getD 0) =
        measure N + (O.map measure).getD 0 + measure R + measure S := by
    simp_rw [hselected]
    simp [outs,Fin.sum_univ_succ,Nat.add_assoc]
  have hbalance (e : Sym2 V) :
      (∑ k, ((F k).map (fun Q => Q.walk.edges.count e)).getD 0) +
        ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e =
      (∑ k, ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e) +
        ∑ l : Fin 4, ((wordEdges (words l)).map (Sym2.map (B.completedLabel A))).count e := by
    apply sum_grouped_balance _ _ j
    · rw [hmeasure,five,four]
      have hN := heN e
      have hO := heO e
      have hR := heR e
      have hS := heS e
      have hMcount : M.edges.count e =
          ((wordEdges (words 0)).map (Sym2.map (B.completedLabel A))).count e := by
        change (C.walk.copy hCs' hCt').edges.count e = _
        rw [SimpleGraph.Walk.edges_copy]
        exact congrArg (List.count e) (B.sizeTwoRichRole_edges A i words added h 0 hn)
      have hOc : ((O.map (fun Q => Q.walk.edges)).getD []).count e =
          (O.map (fun Q => Q.walk.edges.count e)).getD 0 := by cases O <;> rfl
      rw [hMcount,hp] at hN
      rw [hq,hOc] at hO
      change N.walk.edges.count e + ([s(B.label 0,(A 0).val)] : List (Sym2 V)).count e = _ at hN
      change (O.map (fun Q => Q.walk.edges.count e)).getD 0 +
        (if s(B.label 0,(A 1).val) = e then 1 else 0) = _ at hO
      simp only [List.count_cons,List.count_nil,Nat.zero_add,beq_iff_eq] at hN ⊢
      omega
    · intro k hk
      obtain ⟨hfree,hF⟩ := hother k hk
      rw [hF]
      exact congrArg (List.count e) (B.syndromeAvoidingPath_edges (D.path k) hfree)
  obtain ⟨P,hsize,hend⟩ := B.sizeTwo_rich_assemble A i words added h hSigma D F
    (j 2) (by simpa [outs] using hselected 2) hbalance
  refine ⟨P,hsize,?_⟩
  intro v hv
  let endpoint : NonemptyPath G → ℕ := fun Q =>
    (if Q.start = v.val then 1 else 0) + (if Q.finish = v.val then 1 else 0)
  let old : Fin D.size → ℕ := fun k =>
    (if (D.path k).start.val = v.val then 1 else 0) +
      (if (D.path k).finish.val = v.val then 1 else 0)
  have hNend : endpoint N = old (j 0) + old (j 2) := by
    have hxv : (D.path (j 0)).finish.val ≠ v.val := by
      rw [hx₀]; exact hv .x
    have hwv : (D.path (j 2)).finish.val ≠ v.val := by
      rw [hw₂]; exact fun he => hv (Rich.reserve i) (hwlabel.symm.trans he)
    simp only [endpoint,old,hsN,htN,if_neg hxv,if_neg hwv,Nat.add_zero]
  have hends : (∑ k, ((F k).map endpoint).getD 0) = ∑ k, old k := by
    have hh := sum_grouped_balance old (fun k => ((F k).map endpoint).getD 0) j 0 0
    suffices htotal : (∑ k, ((F k).map endpoint).getD 0) + 0 = (∑ k, old k) + 0 by
      simpa only [Nat.add_zero] using htotal
    apply hh
    · rw [hmeasure,five]
      have hO := hendO v.val hv
      have hR := hendR v.val hv
      have hS := hendS v.val hv
      change (O.map endpoint).getD 0 = old (j 1) at hO
      change endpoint R = old (j 3) at hR
      change endpoint S = old (j 4) at hS
      rw [hNend,hO,hR,hS]
      omega
    · intro k hk
      obtain ⟨hfree,hF⟩ := hother k hk
      rw [hF]
      rfl
  have hold : (∑ k, old k) = D.endpointCount v := by
    simp only [old,Decomposition.endpointCount,Subtype.val_inj]
  exact (hends.trans hold).symm.trans_le (hend v.val)

end Gallai.WholeBowtie
