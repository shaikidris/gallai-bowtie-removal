/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.OriginalPairExtension
import Gallai.Operations.Orient

/-! # Replace one terminal carrier by its fresh extension in the whole family -/

namespace Gallai.WholeBowtie

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Extending a selected carrier leaves the family size unchanged and adds
exactly the tail edges. All retained endpoint reserves away from its attachment
are preserved. -/
theorem originalPairExtensionFamily (p q : {v : V // v ∉ B.vertices})
    (hpq : G.Adj p.val q.val) (D : Decomposition (B.pairRepairedPuncture p q))
    (j : Fin D.size) (T : NonemptyPath G) (hj : (D.path j).finish.val = T.start)
    (hf : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices) :
    ∃ F : Fin D.size → NonemptyPath G,
      (∀ e, (∑ i, (F i).walk.edges.count e) =
        (∑ i, (B.originalPairCarrier p q hpq (D.path i)).walk.edges.count e) +
          T.walk.edges.count e) ∧
      ∀ w : {v // v ∉ B.vertices}, w.val ≠ T.start →
        (∑ i, ((if (F i).start = w.val then 1 else 0) +
          (if (F i).finish = w.val then 1 else 0) : ℕ)) = D.endpointCount w := by
  classical
  let Q := B.originalPairExtension p q hpq (D.path j) T hj hf
  let F : Fin D.size → NonemptyPath G := fun i =>
    if i = j then Q else B.originalPairCarrier p q hpq (D.path i)
  have hFj : F j = Q := by simp only [F, if_pos rfl]
  have hFi (i : Fin D.size) (hi : i ≠ j) :
      F i = B.originalPairCarrier p q hpq (D.path i) := by simp only [F, if_neg hi]
  refine ⟨F, ?_, ?_⟩
  · intro e
    have hpoint (i : Fin D.size) : (F i).walk.edges.count e =
        (B.originalPairCarrier p q hpq (D.path i)).walk.edges.count e +
          (if i = j then T.walk.edges.count e else 0) := by
      by_cases hi : i = j
      · subst i
        rw [hFj]
        change (B.originalPairExtension p q hpq (D.path j) T hj hf).walk.edges.count e = _
        rw [B.originalPairExtension_edges, B.originalPairCarrier_edges, List.count_append]
        simp only [if_true]
      · rw [hFi i hi]
        simp only [if_neg hi, Nat.add_zero]
    have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hpoint i)
    simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hsum
  · intro w hw
    unfold Decomposition.endpointCount
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = j
    · subst i
      rw [hFj]
      have hends := B.originalPairExtension_endpoints p q hpq (D.path j) T hj hf w hw
      simpa only [Subtype.ext_iff] using hends
    · rw [hFi i hi]
      change ((if (D.path i).start.val = w.val then 1 else 0) +
        (if (D.path i).finish.val = w.val then 1 else 0)) = _
      simp only [Subtype.ext_iff]

/-- Positive endpoint supply selects and orients the carrier automatically.
The returned family has a complete original-edge deficit formula. -/
theorem originalPairSelectedFamily (p q : {v : V // v ∉ B.vertices})
    (hpq : G.Adj p.val q.val) (D : Decomposition (B.pairRepairedPuncture p q))
    (a : {v : V // v ∉ B.vertices}) (hpos : 0 < D.endpointCount a)
    (T : NonemptyPath G) (ht : T.start = a.val)
    (hf : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices) :
    ∃ F : Fin D.size → NonemptyPath G,
      (∀ e ∈ G.edgeSet, (∑ i, (F i).walk.edges.count e) =
        (if (∃ v ∈ e, v ∈ B.vertices) ∨ e = s(p.val,q.val) then 0 else 1) +
          T.walk.edges.count e) ∧
      ∀ w : {v // v ∉ B.vertices}, w ≠ a →
        (∑ i, ((if (F i).start = w.val then 1 else 0) +
          (if (F i).finish = w.val then 1 else 0) : ℕ)) = D.endpointCount w := by
  classical
  have hex : ∃ j, (D.path j).start = a ∨ (D.path j).finish = a := by
    by_contra hn
    have hz : D.endpointCount a = 0 := by
      unfold Decomposition.endpointCount
      apply Finset.sum_eq_zero
      intro i _
      have hs : (D.path i).start ≠ a := fun h => hn ⟨i,Or.inl h⟩
      have he : (D.path i).finish ≠ a := fun h => hn ⟨i,Or.inr h⟩
      simp only [if_neg hs, if_neg he, Nat.add_zero]
    omega
  obtain ⟨j, hj⟩ := hex
  let D' := D.orientToward a
  have hj' : (D'.path j).finish.val = T.start :=
    (congrArg Subtype.val (D.orientToward_terminal a j hj)).trans ht.symm
  obtain ⟨F, hcount, hends⟩ := B.originalPairExtensionFamily p q hpq D' j T hj' hf
  refine ⟨F, ?_, ?_⟩
  · intro e he
    exact (hcount e).trans (congrArg (· + T.walk.edges.count e)
      (B.originalPair_edge_count p q hpq D' e he))
  · intro w hw
    have hw' : w.val ≠ T.start := fun h => hw (Subtype.ext (h.trans ht))
    exact (hends w hw').trans (D.orientToward_endpointCount a w)

end Gallai.WholeBowtie
