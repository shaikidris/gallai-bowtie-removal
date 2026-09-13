/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.PairRepairedCarrier
import Gallai.Foundations.Endpoints

/-! # Restore the complete old family after a synthetic pair repair

Exactly one carrier is modified; all others transfer to G unchanged. New local
paths are not yet appended here. The family has the original size and endpoint
vector, with one repair edge exchanged for the connector in its total counts.
-/

namespace Gallai.WholeBowtie

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

omit [DecidableEq V] in
/-- Mapping the actual carrier maps exactly its unordered edges. -/
theorem pairRepairedCarrier_edges (p q : {v : V // v ∉ B.vertices})
    (P : NonemptyPath (B.pairRepairedPuncture p q)) :
    (B.pairRepairedCarrier p q P).walk.edges = P.walk.edges.map (Sym2.map Subtype.val) := by
  exact SimpleGraph.Walk.edges_map (B.pairRepairedHom p q) P.walk

/-- An auxiliary carrier avoiding the repair edge uses only original edges. -/
theorem pairRepairedCarrier_original_edges (p q : {v : V // v ∉ B.vertices})
    (P : NonemptyPath (B.pairRepairedPuncture p q)) (hn : s(p, q) ∉ P.walk.edges) :
    ∀ e ∈ (B.pairRepairedCarrier p q P).walk.edges, e ∈ G.edgeSet := by
  intro e he
  have hs := (B.pairRepairedCarrier p q P).walk.edges_subset_edgeSet he
  rw [SimpleGraph.edgeSet_sup] at hs
  rcases hs with hg | hr
  · exact hg
  · have heq : e = s(p.val, q.val) := SimpleGraph.edgeSet_edge_subset hr
    rw [B.pairRepairedCarrier_edges] at he
    obtain ⟨f, hf, hfe⟩ := List.mem_map.mp he
    have hfq : f = s(p, q) := (Sym2.map.injective Subtype.val_injective)
      (hfe.trans heq)
    exact (hn (hfq ▸ hf)).elim

/-- Transfer every unselected carrier without changing its word or endpoints. -/
def unchangedPairCarrier (p q : {v : V // v ∉ B.vertices})
    (P : NonemptyPath (B.pairRepairedPuncture p q)) (hn : s(p, q) ∉ P.walk.edges) :
    NonemptyPath G :=
  (B.pairRepairedCarrier p q P).transfer G
    (B.pairRepairedCarrier_original_edges p q P hn)

/-- Restore all old carriers at zero path-count cost, with exact total edge balance. -/
theorem syntheticPairFamily (p q : {v : V // v ∉ B.vertices}) (hne : p ≠ q)
    (hmissing : ¬ G.Adj p.val q.val) (D : Decomposition (B.pairRepairedPuncture p q))
    (M : G.Walk p.val q.val) (hM : M.IsPath)
    (hcore : ∀ v ∈ M.support, v = p.val ∨ v = q.val ∨ v ∈ B.vertices) :
    ∃ F : Fin D.size → NonemptyPath G,
      (∀ i, (F i).start = (D.path i).start.val ∧
        (F i).finish = (D.path i).finish.val) ∧
      ∀ e, (∑ i, (F i).walk.edges.count e) +
        (if s(p.val, q.val) = e then 1 else 0) =
        (∑ i, (B.pairRepairedCarrier p q (D.path i)).walk.edges.count e) +
          M.edges.count e := by
  classical
  have ha : (B.pairRepairedPuncture p q).Adj p q := by
    change (toggleEdge B.puncture p q).Adj p q
    simp only [toggleEdge, show ¬ B.puncture.Adj p q from hmissing, if_false]
    exact Or.inr ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)
  obtain ⟨j, hj, huniq⟩ := D.covers s(p, q) ha
  obtain ⟨Q, hQs, hQt, hQc⟩ := B.restore_pairRepairedCarrier p q (D.path j) hj M hM hcore
  have hother (i : Fin D.size) (hij : i ≠ j) : s(p, q) ∉ (D.path i).walk.edges :=
    fun hi => hij (huniq i hi)
  let F : Fin D.size → NonemptyPath G := fun i =>
    if hij : i = j then Q else B.unchangedPairCarrier p q (D.path i) (hother i hij)
  have hFj : F j = Q := by simp only [F, dif_pos rfl]
  have hFi (i : Fin D.size) (hij : i ≠ j) :
      F i = B.unchangedPairCarrier p q (D.path i) (hother i hij) := by
    simp only [F, dif_neg hij]
  refine ⟨F, ?_, ?_⟩
  · intro i
    by_cases hij : i = j
    · subst i
      simpa only [F, dif_pos rfl] using And.intro hQs hQt
    · simp only [F, dif_neg hij, unchangedPairCarrier, NonemptyPath.transfer,
        pairRepairedCarrier, NonemptyPath.map]
      exact ⟨rfl, rfl⟩
  · intro e
    have hpoint (i : Fin D.size) :
        (F i).walk.edges.count e + (if i = j then (if s(p.val, q.val) = e then 1 else 0) else 0) =
        (B.pairRepairedCarrier p q (D.path i)).walk.edges.count e +
          (if i = j then M.edges.count e else 0) := by
      by_cases hij : i = j
      · subst i
        rw [hFj]
        simpa only [if_true] using hQc e
      · rw [hFi i hij]
        simp only [if_neg hij, unchangedPairCarrier,
          NonemptyPath.transfer_edges, Nat.add_zero]
    have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hpoint i)
    simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      using hsum

/-- Pointwise endpoint preservation gives the exact old endpoint vector. -/
theorem repairedFamily_endpoint_count (p q : {v : V // v ∉ B.vertices})
    (D : Decomposition (B.pairRepairedPuncture p q)) (F : Fin D.size → NonemptyPath G)
    (hends : ∀ i, (F i).start = (D.path i).start.val ∧
      (F i).finish = (D.path i).finish.val) (w : {v : V // v ∉ B.vertices}) :
    (∑ i, ((if (F i).start = w.val then 1 else 0) +
      (if (F i).finish = w.val then 1 else 0) : ℕ)) = D.endpointCount w := by
  unfold Decomposition.endpointCount
  apply Finset.sum_congr rfl
  intro i _
  rw [(hends i).1, (hends i).2]
  simp only [Subtype.ext_iff]

end Gallai.WholeBowtie
