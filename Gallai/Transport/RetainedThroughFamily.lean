/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedThroughReplacement
import Gallai.Foundations.DegreeTwoCarriers

/-! # Whole-family replacement of the unique retained through-carrier -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Selecting and replacing the through-carrier preserves every old endpoint
and exchanges the retained spokes for the connector in the entire family. -/
theorem retainedThroughFamily (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj]
    (hle : H ≤ B.completedStar)
    (hOriginal : ∀ u v : B.StarSurvivor, H.Adj u v → G.Adj u.val v.val)
    (p q : B.StarSurvivor)
    (hneighbors : ∀ v, H.Adj B.completedHub v → v = p ∨ v = q)
    (D : Decomposition H) (hd : H.degree B.completedHub = 2)
    (hzero : D.endpointCount B.completedHub = 0)
    (M : G.Walk p.val q.val) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = p.val ∨ v.val = q.val ∨ v.val = B.label 0) :
    ∃ F : Fin D.size → NonemptyPath G,
      (∀ e : Sym2 V, (∑ i, (F i).walk.edges.count e) +
          ([s(B.label 0, p.val), s(B.label 0, q.val)] : List (Sym2 V)).count e =
        (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) + M.edges.count e) ∧
      ∀ w : B.StarSurvivor,
        (∑ i, ((if (F i).start = w.val then 1 else 0) +
          (if (F i).finish = w.val then 1 else 0) : ℕ)) = D.endpointCount w := by
  classical
  let φ : H →g G := ⟨Subtype.val, fun {u v} h => hOriginal u v h⟩
  let old : Fin D.size → NonemptyPath G := fun i => (D.path i).map φ Subtype.val_injective
  have old_edges (i : Fin D.size) : (old i).walk.edges =
      (D.path i).walk.edges.map (Sym2.map Subtype.val) :=
    SimpleGraph.Walk.edges_map φ (D.path i).walk
  obtain ⟨j, hx, hs, ht, _⟩ := D.degree_two_through_carrier B.completedHub hd hzero
  obtain ⟨N, hNs, hNt, hN⟩ := B.retainedThroughReplacement H hle p q hneighbors
    (D.path j) hx hs ht M hM hne hm
  let b := ((D.path j).takeTo B.completedHub hx hs).walk.reverse.snd
  let c := ((D.path j).dropFrom B.completedHub hx ht).walk.snd
  have hadj := (D.path j).release_attachments_adj B.completedHub hx hs ht
  have hbc := (D.path j).release_attachments_ne B.completedHub hx hs ht
  have hpair : (b = p ∧ c = q) ∨ (b = q ∧ c = p) := by
    rcases hneighbors b hadj.1 with hb | hb <;>
      rcases hneighbors c hadj.2 with hc | hc
    · exact False.elim (hbc (hb.trans hc.symm))
    · exact Or.inl ⟨hb, hc⟩
    · exact Or.inr ⟨hb, hc⟩
    · exact False.elim (hbc (hb.trans hc.symm))
  have hspokes (e : Sym2 V) :
      ([s(B.label 0, b.val), s(B.label 0, c.val)] : List (Sym2 V)).count e =
      ([s(B.label 0, p.val), s(B.label 0, q.val)] : List (Sym2 V)).count e := by
    rcases hpair with ⟨hb, hc⟩ | ⟨hb, hc⟩ <;>
      simp [hb, hc, List.count_cons, Nat.add_comm]
  let F : Fin D.size → NonemptyPath G := fun i => if i = j then N else old i
  have hFj : F j = N := if_pos rfl
  refine ⟨F, ?_, ?_⟩
  · intro e
    let sp := ([s(B.label 0, p.val), s(B.label 0, q.val)] : List (Sym2 V)).count e
    have hp (i : Fin D.size) : (F i).walk.edges.count e + (if i = j then sp else 0) =
        ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e +
          (if i = j then M.edges.count e else 0) := by
      by_cases hi : i = j
      · subst i
        rw [hFj]
        have hn := hN e
        change N.walk.edges.count e +
          ([s(B.label 0, b.val), s(B.label 0, c.val)] : List (Sym2 V)).count e = _ at hn
        rw [hspokes] at hn
        simpa only [eq_self, ite_true, sp] using hn
      · change (if i = j then N else old i).walk.edges.count e +
          (if i = j then sp else 0) = _
        rw [if_neg hi, if_neg hi, if_neg hi]
        simpa only [Nat.add_zero] using congrArg (List.count e) (old_edges i)
    have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hp i)
    simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hsum
  · intro w
    unfold Decomposition.endpointCount
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = j
    · subst i
      simp only [F, if_pos rfl, hNs, hNt, Subtype.val_inj]
    · simp only [F, if_neg hi]
      change ((if (D.path i).start.val = w.val then 1 else 0) +
        (if (D.path i).finish.val = w.val then 1 else 0)) = _
      simp only [Subtype.val_inj]

end Gallai.WholeBowtie
