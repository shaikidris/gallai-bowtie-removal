/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.RetainedHubAuxiliary
import Gallai.Operations.Concatenate
import Gallai.Operations.Orient
import Gallai.Foundations.EdgeCounts

/-! # Extend a retained terminal carrier into the deleted private vertices -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- A fresh private tail extends one selected terminal carrier without losing
any survivor endpoints except the spent hub occurrence. Both old spokes stay. -/
theorem retainedTerminalFamily (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj]
    (hOriginal : ∀ u v : B.StarSurvivor, H.Adj u v → G.Adj u.val v.val)
    (D : Decomposition H) (j : Fin D.size) (hj : (D.path j).finish = B.completedHub)
    (T : NonemptyPath G) (ht : T.start = B.label 0)
    (hf : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ (Finset.univ.erase 0).map B.label) :
    ∃ F : Fin D.size → NonemptyPath G,
      (∀ e, (∑ i, (F i).walk.edges.count e) =
        (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) +
          T.walk.edges.count e) ∧
      ∀ w : B.StarSurvivor, w ≠ B.completedHub →
        (∑ i, ((if (F i).start = w.val then 1 else 0) +
          (if (F i).finish = w.val then 1 else 0) : ℕ)) = D.endpointCount w := by
  classical
  let φ : H →g G := ⟨Subtype.val, fun {u v} h => hOriginal u v h⟩
  let old (i : Fin D.size) := (D.path i).map φ Subtype.val_injective
  have hjoin : (old j).finish = T.start := (congrArg Subtype.val hj).trans ht.symm
  have hinter : ∀ v, v ∈ (old j).walk.support → v ∈ T.walk.support → v = (old j).finish := by
    intro v hv htv
    rcases hf v htv with hvx | hdel
    · exact hvx.trans hjoin.symm
    · change v ∈ ((D.path j).walk.map φ).support at hv
      rw [SimpleGraph.Walk.support_map] at hv
      obtain ⟨u, _, hu⟩ := List.mem_map.mp hv
      change u.val = v at hu
      exact (u.property (hu.symm ▸ hdel)).elim
  let N := (old j).append T hjoin hinter
  let F : Fin D.size → NonemptyPath G := fun i => if i = j then N else old i
  have hFj : F j = N := if_pos rfl
  have hFi (i : Fin D.size) (hi : i ≠ j) : F i = old i := if_neg hi
  have hold (i : Fin D.size) : (old i).walk.edges =
      (D.path i).walk.edges.map (Sym2.map Subtype.val) := SimpleGraph.Walk.edges_map φ _
  have hN : N.walk.edges = (old j).walk.edges ++ T.walk.edges :=
    NonemptyPath.append_edges _ _ _ _
  refine ⟨F, ?_, ?_⟩
  · intro e
    have hp (i : Fin D.size) : (F i).walk.edges.count e =
        ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e +
          (if i = j then T.walk.edges.count e else 0) := by
      by_cases hi : i = j
      · subst i
        rw [hFj, hN, List.count_append, hold]
        simp only [eq_self, ite_true]
      · rw [hFi i hi, hold, if_neg hi, Nat.add_zero]
    have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hp i)
    simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hs
  · intro w hw
    have hwx : w.val ≠ B.label 0 := fun he => hw (Subtype.ext he)
    have htw : T.finish ≠ w.val := by
      intro he
      rcases hf T.finish T.walk.end_mem_support with hx | hdel
      · exact T.nonempty (T.isPath.nil_iff_eq.mpr hx.symm)
      · exact w.property (he ▸ hdel)
    have hpw : (D.path j).finish ≠ w := fun he => hw (he.symm.trans hj)
    unfold Decomposition.endpointCount
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = j
    · subst i
      rw [hFj]
      change ((if (D.path j).start.val = w.val then 1 else 0) +
        (if T.finish = w.val then 1 else 0)) = _
      simp only [if_neg htw, Subtype.val_inj, if_neg hpw]
    · rw [hFi i hi]
      change ((if (D.path i).start.val = w.val then 1 else 0) +
        (if (D.path i).finish.val = w.val then 1 else 0)) = _
      simp only [Subtype.val_inj]

/-- Positive endpoint supply selects and orients a terminal carrier; no
favourable carrier choice is required for a private tail. -/
theorem retainedTerminalSelected (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj]
    (hOriginal : ∀ u v : B.StarSurvivor, H.Adj u v → G.Adj u.val v.val)
    (D : Decomposition H) (hpos : 0 < D.endpointCount B.completedHub)
    (T : NonemptyPath G) (ht : T.start = B.label 0)
    (hf : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ (Finset.univ.erase 0).map B.label) :
    ∃ F : Fin D.size → NonemptyPath G,
      (∀ e, (∑ i, (F i).walk.edges.count e) =
        (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) +
          T.walk.edges.count e) ∧
      ∀ w : B.StarSurvivor, w ≠ B.completedHub →
        (∑ i, ((if (F i).start = w.val then 1 else 0) +
          (if (F i).finish = w.val then 1 else 0) : ℕ)) = D.endpointCount w := by
  classical
  have hex : ∃ j, (D.path j).start = B.completedHub ∨ (D.path j).finish = B.completedHub := by
    by_contra hn
    have hz : D.endpointCount B.completedHub = 0 := by
      unfold Decomposition.endpointCount
      apply Finset.sum_eq_zero
      intro i _
      have hs : (D.path i).start ≠ B.completedHub := fun he => hn ⟨i, Or.inl he⟩
      have ht : (D.path i).finish ≠ B.completedHub := fun he => hn ⟨i, Or.inr he⟩
      simp only [if_neg hs, if_neg ht, Nat.add_zero]
    omega
  obtain ⟨j, hj⟩ := hex
  let D' := D.orientToward B.completedHub
  obtain ⟨F, hcount, hEnd⟩ := B.retainedTerminalFamily H hOriginal D' j
    (D.orientToward_terminal B.completedHub j hj) T ht hf
  refine ⟨F, ?_, ?_⟩
  · intro e
    have hmaps : (∑ i, ((D'.path i).walk.edges.map (Sym2.map Subtype.val)).count e) =
        ∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e := by
      apply Finset.sum_congr rfl
      intro i _
      change (((D.path i).toward B.completedHub).walk.edges.map (Sym2.map Subtype.val)).count e = _
      by_cases hs : (D.path i).start = B.completedHub
      · rw [(D.path i).toward_of_start_eq B.completedHub hs,
          NonemptyPath.reverse_edges, List.map_reverse, List.count_reverse]
      · rw [(D.path i).toward_of_start_ne B.completedHub hs]
    exact (hcount e).trans (congrArg (· + T.walk.edges.count e) hmaps)
  · intro w hw
    exact (hEnd w hw).trans (D.orientToward_endpointCount B.completedHub w)

end Gallai.WholeBowtie
