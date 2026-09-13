/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedCheapPassingSelected
import Gallai.Transport.RetainedCheapTails

/-! # Exact local accounting for the cheap passing reconstruction -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true → (A j).val ∈ B.row i)

/-- Connector, remote tail and added paths partition the augmented local target. -/
theorem retainedCheapPassing_local_count (repair : Bool)
    (connector remote : List Vertex) (added : List (List Vertex))
    (h : Retained.CheapPassingAccepted s repair connector remote added) (e : Sym2 V) :
    ((wordEdges connector).map (Sym2.map (B.threeLabel A))).count e +
      ((wordEdges remote).map (Sym2.map (B.threeLabel A))).count e +
      (∑ i : Fin added.length, ((wordEdges added[i]).map (Sym2.map (B.threeLabel A))).count e) =
      ((targetEdges s ∪ retainedRepair repair).val.map (Sym2.map (B.threeLabel A))).count e := by
  obtain ⟨_,_,_,_,_,_,hacc,_⟩ := h
  have hc := congrArg (fun m : Multiset (Sym2 Vertex) =>
    (m.map (Sym2.map (B.threeLabel A))).count e) hacc.2
  simp only [Multiset.map_coe,Multiset.coe_count] at hc
  rw [familyEdges,List.map_flatMap,List.count_flatMap] at hc
  dsimp only [Function.comp_def] at hc
  change ((wordEdges connector).map (Sym2.map (B.threeLabel A))).count e +
    (((wordEdges remote).map (Sym2.map (B.threeLabel A))).count e +
      (added.map (fun w => ((wordEdges w).map (Sym2.map (B.threeLabel A))).count e)).sum) = _ at hc
  have hs : (added.map (fun w => ((wordEdges w).map (Sym2.map (B.threeLabel A))).count e)).sum =
      ∑ i : Fin added.length, ((wordEdges added[i]).map (Sym2.map (B.threeLabel A))).count e := by
    rw [← List.ofFn_getElem_eq_map,List.sum_ofFn]
    rfl
  rw [hs] at hc
  simpa only [Nat.add_assoc] using hc

include hrow in
/-- The full candidate family uses D.size plus the added-word count. All
actual choices, orientations and path-simplicity conditions are discharged. -/
theorem retainedCheapPassing_candidate
    (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj]
    (hOriginal : ∀ u v : B.StarSurvivor, H.Adj u v → G.Adj u.val v.val)
    (hpq : H.Adj B.completedHub (B.retainedSlot A 0) ∧
      H.Adj B.completedHub (B.retainedSlot A 1))
    (hneighbors : ∀ v, H.Adj B.completedHub v →
      v = B.retainedSlot A 0 ∨ v = B.retainedSlot A 1)
    (hr : ¬ H.Reachable B.completedHub (B.retainedSlot A 2))
    (D : Decomposition H) (hd : H.degree B.completedHub = 2)
    (hz : D.endpointCount B.completedHub = 0)
    (hpos : 0 < D.endpointCount (B.retainedSlot A 2))
    (repair : Bool) (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (connector remote : List Vertex) (added : List (List Vertex))
    (h : Retained.CheapPassingAccepted s repair connector remote added) :
    ∃ Q : Fin D.size ⊕ Fin added.length → NonemptyPath G,
      (∀ e, (∑ i, (Q i).walk.edges.count e) +
        ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e =
        (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) +
          ((targetEdges s ∪ retainedRepair repair).val.map (Sym2.map (B.threeLabel A))).count e) ∧
      ∀ w : B.StarSurvivor, w ≠ B.retainedSlot A 2 → D.endpointCount w ≤
        ∑ i, ((if (Q i).start = w.val then 1 else 0) +
          (if (Q i).finish = w.val then 1 else 0) : ℕ) := by
  classical
  obtain ⟨M,hM,hn,he,hm⟩ := B.retainedCheapPassingConnector A s hrow repair hp connector remote added h
  obtain ⟨T,hT,hTe,hTs⟩ := B.retainedCheapPassingRemote A s hrow repair hp connector remote added h
  have hf : ∀ v : B.StarSurvivor, v.val ∈ T.walk.support →
      v = B.retainedSlot A 2 ∨ H.Reachable B.completedHub v := by
    intro v hv
    rcases hTs v hv with hr | hx | hp | hq
    · exact Or.inl hr
    · exact Or.inr (hx ▸ SimpleGraph.Reachable.rfl)
    · exact Or.inr (hp.symm ▸ hpq.1.reachable)
    · exact Or.inr (hq.symm ▸ hpq.2.reachable)
  obtain ⟨F,hF,hEnd⟩ := B.retainedCheapPassingSelected H hOriginal
    (B.retainedSlot A 0) (B.retainedSlot A 1) (B.retainedSlot A 2) hr hneighbors
    D hd hz hpos M hM hn hm T hT hf
  have hacc := h.2.2.2.2.2.2.1
  let addedPath (i : Fin added.length) := B.realizeRetainedMember A s hrow repair hp
    (connector :: remote :: added) hacc added[i] (by simp)
  let Q : Fin D.size ⊕ Fin added.length → NonemptyPath G := Sum.elim F addedPath
  refine ⟨Q, ?_, ?_⟩
  · intro e
    have ha (i : Fin added.length) : (addedPath i).walk.edges =
        (wordEdges added[i]).map (Sym2.map (B.threeLabel A)) :=
      B.realizeRetainedMember_edges A s hrow repair hp _ hacc _ _
    have hc := hF e
    have hMe := congrArg (fun es : List (Sym2 V) => es.count e) he
    have hTc := congrArg (fun es : List (Sym2 V) => es.count e) hTe
    have hl := B.retainedCheapPassing_local_count A s repair connector remote added h e
    change (∑ i, (F i).walk.edges.count e) +
      ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e =
      (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) +
        M.edges.count e + T.walk.edges.count e at hc
    rw [Fintype.sum_sum_type]
    simp only [Q,Sum.elim_inl,Sum.elim_inr,ha]
    omega
  · intro w hw
    rw [Fintype.sum_sum_type]
    exact (hEnd w hw).trans (Nat.le_add_right _ _)

end Gallai.WholeBowtie
