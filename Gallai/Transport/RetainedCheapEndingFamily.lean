/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedSeparatedFamily
import Gallai.Transport.RetainedCheapSelection

/-! # Automatic two-hub-tail and remote-tail family assembly -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- All three terminal extensions can be made simultaneously, without any
pairwise disjointness assumption on the two old hub carriers or their tails. -/
theorem retainedCheapEndingFamily (H : SimpleGraph B.StarSurvivor)
    [DecidableRel H.Adj]
    (hOriginal : ∀ u v : B.StarSurvivor, H.Adj u v → G.Adj u.val v.val)
    (r : B.StarSurvivor) (hr : ¬ H.Reachable B.completedHub r)
    (D : Decomposition H) (hd : H.degree B.completedHub = 2)
    (hz : 0 < D.endpointCount B.completedHub) (hpos : 0 < D.endpointCount r)
    (T : Fin 3 → NonemptyPath G)
    (ht : ∀ l, (T l).start = (if l = 2 then r else B.completedHub).val)
    (hf : ∀ l v, v.val ∈ (T l).walk.support →
      if l = 2 then v = r ∨ H.Reachable B.completedHub v else v = B.completedHub ∨ v = r) :
    ∃ F : Fin D.size → NonemptyPath G,
      (∀ e, (∑ i, (F i).walk.edges.count e) =
        (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) +
          ∑ l, (T l).walk.edges.count e) ∧
      ∀ w : B.StarSurvivor, w ≠ B.completedHub → w ≠ r → D.endpointCount w ≤
        ∑ i, ((if (F i).start = w.val then 1 else 0) +
          (if (F i).finish = w.val then 1 else 0) : ℕ) := by
  classical
  obtain ⟨i,j,k,hij,hik,hjk,hi,hj,hk⟩ := B.retainedCheap_ending_selection H r hr D hd hz hpos
  let idx : Fin 3 ↪ Fin D.size := ⟨![i,j,k], by
    intro a b he
    fin_cases a <;> fin_cases b <;> simp_all⟩
  let a (l : Fin 3) : B.StarSurvivor := if l = 2 then r else B.completedHub
  have ha (l) : (D.path (idx l)).start = a l ∨ (D.path (idx l)).finish = a l := by
    fin_cases l
    · exact hi
    · exact hj
    · exact hk
  have hsep (l) (v : B.StarSurvivor) (hv : v.val ∈ (T l).walk.support) :
      v = a l ∨ ¬ H.Reachable (a l) v := by
    have h := hf l v hv
    by_cases hl : l = 2
    · simp only [hl,ite_true] at h
      rcases h with he | hw
      · exact Or.inl (by simpa only [a,if_pos hl] using he)
      · refine Or.inr ?_
        intro hrv
        change H.Reachable (if l = 2 then r else B.completedHub) v at hrv
        rw [if_pos hl] at hrv
        exact hr (hw.trans hrv.symm)
    · simp only [if_neg hl] at h
      rcases h with hx | he
      · exact Or.inl (by simpa only [a,if_neg hl] using hx)
      · refine Or.inr ?_
        simpa only [a,if_neg hl,he] using hr
  obtain ⟨F,hcount,hEnd⟩ := B.retainedSeparatedFamily H hOriginal D idx a ha T ht hsep
  refine ⟨F,hcount,?_⟩
  intro w hwx hwr
  apply hEnd w
  intro l
  dsimp only [a]
  split_ifs <;> assumption

end Gallai.WholeBowtie
