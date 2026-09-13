/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedEndingAccounting
import Gallai.Transport.RetainedCheapTails
import Gallai.Transport.RetainedCheapEndingFamily

/-! # Three-tail kept-spoke accounting for cheap ending records -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)

/-- All three tails and the added words cover exactly the local target minus
the two spokes that remain in their old terminal carriers. -/
theorem retainedCheapEnding_local_count (repair : Bool)
    (u v remote : List Vertex) (added : List (List Vertex))
    (h : Retained.CheapEndingAccepted s repair [u,v] remote added) (e : Sym2 V) :
    ((wordEdges u).map (Sym2.map (B.threeLabel A))).count e +
      ((wordEdges v).map (Sym2.map (B.threeLabel A))).count e +
      ((wordEdges remote).map (Sym2.map (B.threeLabel A))).count e +
      (∑ i : Fin added.length, ((wordEdges added[i]).map (Sym2.map (B.threeLabel A))).count e) +
      ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e =
      ((targetEdges s ∪ retainedRepair repair).val.map (Sym2.map (B.threeLabel A))).count e := by
  obtain ⟨hs,_,_,_,_,_,hacc,_⟩ := h
  have hc := congrArg (fun m : Multiset (Sym2 Vertex) =>
    (m.map (Sym2.map (B.threeLabel A))).count e) hacc.2
  simp only [Multiset.map_coe,Multiset.coe_count] at hc
  rw [familyEdges,List.map_flatMap,List.count_flatMap] at hc
  change ((wordEdges u).map (Sym2.map (B.threeLabel A))).count e +
    (((wordEdges v).map (Sym2.map (B.threeLabel A))).count e +
      (((wordEdges remote).map (Sym2.map (B.threeLabel A))).count e +
        (added.map (fun w => ((wordEdges w).map (Sym2.map (B.threeLabel A))).count e)).sum)) = _ at hc
  have hsum : (added.map (fun w => ((wordEdges w).map (Sym2.map (B.threeLabel A))).count e)).sum =
      ∑ i : Fin added.length, ((wordEdges added[i]).map (Sym2.map (B.threeLabel A))).count e := by
    rw [← List.ofFn_getElem_eq_map,List.sum_ofFn]
    rfl
  rw [hsum] at hc
  have hp := congrArg (fun m : Multiset (Sym2 Vertex) =>
    (m.map (Sym2.map (B.threeLabel A))).count e) (retainedEnding_partition s repair hs)
  simp only [Multiset.map_add,Multiset.count_add,Multiset.map_coe,Multiset.coe_count,
    List.map_cons,List.map_nil,Sym2.map_mk,B.threeLabel_anchor] at hp
  have hzero : B.threeLabel A 0 = B.label 0 := B.threeLabel_core A 0
  rw [hzero] at hp
  omega

variable (hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true → (A j).val ∈ B.row i)
include hrow

/-- All cheap ending words are consumed by the actual three-carrier family.
Only the certificate's additional paths still need to be appended. -/
theorem retainedCheapEnding_word_family
    (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj]
    (hOriginal : ∀ u v : B.StarSurvivor, H.Adj u v → G.Adj u.val v.val)
    (hpq : H.Adj B.completedHub (B.retainedSlot A 0) ∧ H.Adj B.completedHub (B.retainedSlot A 1))
    (hr : ¬ H.Reachable B.completedHub (B.retainedSlot A 2))
    (D : Decomposition H) (hd : H.degree B.completedHub = 2)
    (hz : 0 < D.endpointCount B.completedHub) (hpos : 0 < D.endpointCount (B.retainedSlot A 2))
    (repair : Bool) (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (u v remote : List Vertex) (added : List (List Vertex))
    (h : Retained.CheapEndingAccepted s repair [u,v] remote added) :
    ∃ F : Fin D.size → NonemptyPath G,
      (∀ e, (∑ i, (F i).walk.edges.count e) =
        (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) +
          ((wordEdges u).map (Sym2.map (B.threeLabel A))).count e +
          ((wordEdges v).map (Sym2.map (B.threeLabel A))).count e +
          ((wordEdges remote).map (Sym2.map (B.threeLabel A))).count e) ∧
      ∀ w : B.StarSurvivor, w ≠ B.completedHub → w ≠ B.retainedSlot A 2 →
        D.endpointCount w ≤ ∑ i, ((if (F i).start = w.val then 1 else 0) +
          (if (F i).finish = w.val then 1 else 0) : ℕ) := by
  classical
  obtain ⟨U,hUs,hUe,hUf⟩ := B.retainedCheapEndingTail A s hrow repair hp [u,v] remote added h u (by simp)
  obtain ⟨W,hWs,hWe,hWf⟩ := B.retainedCheapEndingTail A s hrow repair hp [u,v] remote added h v (by simp)
  obtain ⟨R,hRs,hRe,hRf⟩ := B.retainedCheapEndingRemote A s hrow repair hp [u,v] remote added h
  let T : Fin 3 → NonemptyPath G := ![U,W,R]
  have ht (l) : (T l).start = (if l = 2 then B.retainedSlot A 2 else B.completedHub).val := by
    fin_cases l
    · exact hUs
    · exact hWs
    · exact hRs
  have hf (l) (w : B.StarSurvivor) (hw : w.val ∈ (T l).walk.support) :
      if l = 2 then w = B.retainedSlot A 2 ∨ H.Reachable B.completedHub w
        else w = B.completedHub ∨ w = B.retainedSlot A 2 := by
    fin_cases l
    · exact hUf w hw
    · exact hWf w hw
    · rcases hRf w hw with he | hx | hp | hq
      · exact Or.inl he
      · exact Or.inr (hx ▸ SimpleGraph.Reachable.rfl)
      · exact Or.inr (hp.symm ▸ hpq.1.reachable)
      · exact Or.inr (hq.symm ▸ hpq.2.reachable)
  obtain ⟨F,hF,hEnd⟩ := B.retainedCheapEndingFamily H hOriginal (B.retainedSlot A 2)
    hr D hd hz hpos T ht hf
  refine ⟨F,?_,hEnd⟩
  intro e
  have he : (∑ l, (T l).walk.edges.count e) =
      ((wordEdges u).map (Sym2.map (B.threeLabel A))).count e +
      ((wordEdges v).map (Sym2.map (B.threeLabel A))).count e +
      ((wordEdges remote).map (Sym2.map (B.threeLabel A))).count e := by
    simp [T,Fin.sum_univ_succ,hUe,hWe,hRe,Nat.add_assoc]
  have hc := hF e
  rw [he] at hc
  simpa only [Nat.add_assoc] using hc

end Gallai.WholeBowtie
