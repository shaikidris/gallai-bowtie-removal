/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRichThroughMerge
import Gallai.Transport.SizeTwoAvoidingRecord
import Gallai.Operations.FamilyReplace

/-! # Actual rich through reconstruction on the old index set

Slot0 is the hub carrier and slots1/2/3 are distinct remote reserve carriers,
oriented towards the reserve. The two merged paths occupy slots0/2, slot1 is
absent, and slot3 receives its optional tail. All other carriers are unchanged.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Reconstruct all old slots from the actual through merge and reserve tail.
The new finite paths and global edge-coverage cancellation are added afterward. -/
theorem sizeTwo_rich_through_family (D : Decomposition B.syndromeStar)
    (j : Fin 4 ↪ Fin D.size) (w : B.StarSurvivor)
    (hsep : ¬ B.syndromeStar.Reachable B.completedHub w)
    (hx : B.completedHub ∈ (D.path (j 0)).walk.support)
    (hs : (D.path (j 0)).start ≠ B.completedHub)
    (ht : B.completedHub ≠ (D.path (j 0)).finish)
    (havoid : ∀ k, k ≠ j 0 → B.completedHub ∉ (D.path k).walk.support)
    (hw : ∀ l : Fin 3, (D.path (j l.succ)).finish = w)
    (M₀ : G.Walk ((D.path (j 0)).takeTo B.completedHub hx hs).walk.reverse.snd.val
      (D.path (j 1)).finish.val)
    (M₁ : G.Walk ((D.path (j 0)).dropFrom B.completedHub hx ht).walk.snd.val
      (D.path (j 2)).finish.val)
    (hM₀ : M₀.IsPath) (hn₀ : ¬ M₀.Nil) (hM₁ : M₁.IsPath) (hn₁ : ¬ M₁.Nil)
    (hm₀ : ∀ v : B.StarSurvivor, v.val ∈ M₀.support →
      v.val = ((D.path (j 0)).takeTo B.completedHub hx hs).walk.reverse.snd.val ∨
      v.val = (D.path (j 1)).finish.val ∨ v.val = B.label 0)
    (hm₁ : ∀ v : B.StarSurvivor, v.val ∈ M₁.support →
      v.val = ((D.path (j 0)).dropFrom B.completedHub hx ht).walk.snd.val ∨
      v.val = (D.path (j 2)).finish.val ∨ v.val = B.label 0)
    (T : Option (NonemptyPath G))
    (hT : ∀ Q ∈ T, Q.start = w.val ∧
      ∀ v ∈ Q.walk.support, v = Q.start ∨ v ∈ B.vertices) :
    ∃ N₀ N₁ N₂ : NonemptyPath G,
      N₀.start = (D.path (j 0)).start.val ∧ N₀.finish = (D.path (j 1)).start.val ∧
      N₁.start = (D.path (j 0)).finish.val ∧ N₁.finish = (D.path (j 2)).start.val ∧
      N₂.start = (D.path (j 3)).start.val ∧ N₂.finish = (T.map (·.finish)).getD w.val ∧
      (∀ e : Sym2 V, N₀.walk.edges.count e + N₁.walk.edges.count e + N₂.walk.edges.count e +
        ([s(B.label 0,((D.path (j 0)).takeTo B.completedHub hx hs).walk.reverse.snd.val),
          s(B.label 0,((D.path (j 0)).dropFrom B.completedHub hx ht).walk.snd.val)] :
          List (Sym2 V)).count e =
        (∑ l : Fin 4, ((D.path (j l)).walk.edges.map (Sym2.map Subtype.val)).count e) +
          M₀.edges.count e + M₁.edges.count e +
          ((T.map (fun Q => Q.walk.edges)).getD []).count e) ∧
      ∃ F : Fin D.size → Option (NonemptyPath G),
        (∀ l, F (j l) = ![some N₀,none,some N₁,some N₂] l) ∧
        ∀ k, (∀ l, j l ≠ k) → ∃ hk : k ≠ j 0,
          F k = some (B.syndromeAvoidingPath (D.path k) (havoid k hk)) := by
  classical
  obtain ⟨N₀,N₁,hs₀,ht₀,hs₁,ht₁,he⟩ := B.sizeTwo_rich_through_merge w hsep
    (D.path (j 0)) hx hs ht (D.path (j 1)) (D.path (j 2)) (hw 0) (hw 1)
    M₀ M₁ hM₀ hn₀ hM₁ hn₁ hm₀ hm₁
  have hk₃ : j 3 ≠ j 0 := fun h => (by decide : (3 : Fin 4) ≠ 0) (j.injective h)
  let C := B.syndromeAvoidingPath (D.path (j 3)) (havoid (j 3) hk₃)
  have hR : ∀ Q ∈ T, C.finish = Q.start ∧
      (∀ v ∈ Q.walk.support, v = Q.start ∨ v ∈ B.vertices) ∧
      Disjoint (C.freshSupport B.vertices) (Q.freshSupport B.vertices) := by
    intro Q hQ
    obtain ⟨hQs,hQv⟩ := hT Q hQ
    refine ⟨(congrArg Subtype.val (hw 2)).trans hQs.symm,hQv,?_⟩
    rw [show C.freshSupport B.vertices = ∅ from
      B.syndromeAvoidingPath_fresh_empty (D.path (j 3)) (havoid (j 3) hk₃)]
    exact Finset.disjoint_empty_left _
  obtain ⟨N₂,hs₂,ht₂,he₂⟩ := C.extend_optional_fresh none T B.vertices
    (by simp) hR (by simp)
  have hs₂' : N₂.start = (D.path (j 3)).start.val := hs₂
  have ht₂' : N₂.finish = (T.map (·.finish)).getD w.val := by
    simpa only [show C.finish = w.val from congrArg Subtype.val (hw 2)] using ht₂
  refine ⟨N₀,N₁,N₂,hs₀,ht₀,hs₁,ht₁,hs₂',ht₂',?_,?_⟩
  · intro e
    have hc := congrArg (List.count e) (B.syndromeAvoidingPath_edges
      (D.path (j 3)) (havoid (j 3) hk₃))
    have h₂ := congrArg (List.count e) he₂
    simp only [Option.map_none,Option.getD_none,List.nil_append,List.count_append] at h₂
    change C.walk.edges.count e = _ at hc
    have h₀ := he e
    have hsum (f : Fin 4 → ℕ) : (∑ l, f l) = f 0 + f 1 + f 2 + f 3 := by
      simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
      change f 0 + (f 1 + (f 2 + (f 3 + 0))) = _
      omega
    rw [hsum]
    omega
  · let base : Fin D.size → Option (NonemptyPath G) := fun k =>
      if hk : k = j 0 then none else some (B.syndromeAvoidingPath (D.path k) (havoid k hk))
    let R : Fin 4 → Option (NonemptyPath G) := ![some N₀,none,some N₁,some N₂]
    refine ⟨replaceFamily base j R,replaceFamily_selected base j R,?_⟩
    intro k hk
    have hk₀ : k ≠ j 0 := (hk 0).symm
    refine ⟨hk₀,?_⟩
    rw [replaceFamily_unselected base j R k (by rintro ⟨l,hl⟩; exact hk l hl)]
    exact dif_neg hk₀

end Gallai.WholeBowtie
