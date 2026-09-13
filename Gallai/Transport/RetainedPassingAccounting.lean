/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedThroughFamily
import Gallai.Transport.ThreeAnchorRetainedWords

/-! # Adding the finite retained passing certificate to the old family -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true →
  (A j).val ∈ B.row i)

/-- The connector and added words account for the entire augmented local target. -/
theorem retainedPassing_local_count (repair : Bool) (connector : List Vertex)
    (added : List (List Vertex)) (h : RetainedPassingAccepted s repair connector added)
    (e : Sym2 V) :
    ((wordEdges connector).map (Sym2.map (B.threeLabel A))).count e +
      (∑ i : Fin added.length,
        ((wordEdges added[i]).map (Sym2.map (B.threeLabel A))).count e) =
    ((targetEdges s ∪ retainedRepair repair).val.map
      (Sym2.map (B.threeLabel A))).count e := by
  have hc := congrArg (fun m : Multiset (Sym2 Vertex) =>
    (m.map (Sym2.map (B.threeLabel A))).count e) h.2.2.2.2.2.1.2
  simp only [Multiset.map_coe, Multiset.coe_count] at hc
  rw [familyEdges, List.map_flatMap, List.count_flatMap] at hc
  dsimp only [Function.comp_def] at hc
  change ((wordEdges connector).map (Sym2.map (B.threeLabel A))).count e +
    (added.map (fun w => ((wordEdges w).map (Sym2.map (B.threeLabel A))).count e)).sum = _ at hc
  have hs : (added.map (fun w =>
      ((wordEdges w).map (Sym2.map (B.threeLabel A))).count e)).sum =
      ∑ i : Fin added.length,
        ((wordEdges added[i]).map (Sym2.map (B.threeLabel A))).count e := by
    rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
    rfl
  rw [hs] at hc
  exact hc

include hrow in
/-- Append actual simple added paths. This is a candidate family until the
ambient auxiliary/local edge partition is supplied by the graph construction. -/
theorem retainedPassing_append {n : ℕ} (F : Fin n → NonemptyPath G)
    (repair : Bool) (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (connector : List Vertex) (added : List (List Vertex))
    (h : RetainedPassingAccepted s repair connector added)
    (oldCount : Sym2 V → ℕ)
    (hF : ∀ e, (∑ i, (F i).walk.edges.count e) +
      ([s(B.label 0, (A 0).val), s(B.label 0, (A 1).val)] : List (Sym2 V)).count e =
      oldCount e + ((wordEdges connector).map (Sym2.map (B.threeLabel A))).count e) :
    ∃ Q : Fin n ⊕ Fin added.length → NonemptyPath G,
      (∀ e, (∑ i, (Q i).walk.edges.count e) +
        ([s(B.label 0, (A 0).val), s(B.label 0, (A 1).val)] : List (Sym2 V)).count e =
        oldCount e + ((targetEdges s ∪ retainedRepair repair).val.map
          (Sym2.map (B.threeLabel A))).count e) ∧
      ∀ v : V, (∑ i, ((if (F i).start = v then 1 else 0) +
        (if (F i).finish = v then 1 else 0) : ℕ)) ≤
        ∑ i, ((if (Q i).start = v then 1 else 0) +
          (if (Q i).finish = v then 1 else 0) : ℕ) := by
  classical
  let addedPath (i : Fin added.length) :=
    B.realizeRetainedMember A s hrow repair hp (connector :: added)
      h.2.2.2.2.2.1 added[i] (List.mem_cons_of_mem _ (List.getElem_mem _))
  let Q : Fin n ⊕ Fin added.length → NonemptyPath G := Sum.elim F addedPath
  refine ⟨Q, ?_, ?_⟩
  · intro e
    have ha (i : Fin added.length) : (addedPath i).walk.edges =
        (wordEdges added[i]).map (Sym2.map (B.threeLabel A)) :=
      B.realizeRetainedMember_edges A s hrow repair hp _ _ _ _
    have hf := hF e
    have hl := B.retainedPassing_local_count A s repair connector added h e
    rw [Fintype.sum_sum_type]
    simp only [Q, Sum.elim_inl, Sum.elim_inr, ha]
    omega
  · intro v
    rw [Fintype.sum_sum_type]
    exact Nat.le_add_right _ _

include hrow in
/-- A passing auxiliary decomposition and an accepted finite record produce
the entire candidate family, with exact local balance and all survivor reserves.
No carrier selection, connector realization or simplicity premise remains. -/
theorem retainedPassing_candidate
    (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj]
    (hle : H ≤ B.completedStar)
    (hOriginal : ∀ u v : B.StarSurvivor, H.Adj u v → G.Adj u.val v.val)
    (hneighbors : ∀ v, H.Adj B.completedHub v →
      v = B.retainedSlot A 0 ∨ v = B.retainedSlot A 1)
    (D : Decomposition H) (hd : H.degree B.completedHub = 2)
    (hzero : D.endpointCount B.completedHub = 0)
    (repair : Bool) (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (connector : List Vertex) (added : List (List Vertex))
    (h : RetainedPassingAccepted s repair connector added) :
    ∃ Q : Fin D.size ⊕ Fin added.length → NonemptyPath G,
      (∀ e, (∑ i, (Q i).walk.edges.count e) +
        ([s(B.label 0, (A 0).val), s(B.label 0, (A 1).val)] : List (Sym2 V)).count e =
        (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) +
          ((targetEdges s ∪ retainedRepair repair).val.map
            (Sym2.map (B.threeLabel A))).count e) ∧
      ∀ w : B.StarSurvivor, D.endpointCount w ≤
        ∑ i, ((if (Q i).start = w.val then 1 else 0) +
          (if (Q i).finish = w.val then 1 else 0) : ℕ) := by
  classical
  obtain ⟨M, hM, hn, he, hm⟩ :=
    B.retainedPassingConnector A s hrow repair hp connector added h
  obtain ⟨F, hF, hEnd⟩ := B.retainedThroughFamily H hle hOriginal
    (B.retainedSlot A 0) (B.retainedSlot A 1) hneighbors D hd hzero M hM hn hm
  have hF' : ∀ e, (∑ i, (F i).walk.edges.count e) +
      ([s(B.label 0, (A 0).val), s(B.label 0, (A 1).val)] : List (Sym2 V)).count e =
      (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) +
        ((wordEdges connector).map (Sym2.map (B.threeLabel A))).count e := by
    intro e
    exact (hF e).trans (congrArg (fun t : List (Sym2 V) =>
      (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) + t.count e) he)
  obtain ⟨Q, hQ, hReserve⟩ := B.retainedPassing_append A s hrow F repair hp
    connector added h _ hF'
  refine ⟨Q, hQ, ?_⟩
  intro w
  rw [← hEnd w]
  exact hReserve w.val

end Gallai.WholeBowtie
