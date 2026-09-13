/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRichArmMerge
import Gallai.Transport.SizeTwoRichSeparatedAssembly
import Gallai.Transport.SizeTwoRichSeparatedMerge
import Gallai.Transport.SizeTwoRichSeparatedWords
import Gallai.Transport.SizeTwoRichSeparatedPair
import Gallai.Transport.SizeTwoRichWords
import Gallai.Transport.SizeTwoPassingDispatch
import Gallai.Operations.OptionalFamily
import Gallai.Operations.FamilyBalance

/-! # Complete reconstruction from two selected separated carriers

The actual pair construction supplies the balance. Replacing the selected old
slots and appending the checked local paths yields a decomposition of G.
Automatic selection of the two indices belongs in the sibling module.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

theorem sizeTwo_rich_separated_consumer (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (i : Fin 4) (connector tail : List Star.Vertex) (added : List (List Star.Vertex))
    (h : Rich.SeparatedAccepted (B.completedStarState A) i connector tail added)
    (D : Decomposition B.syndromeStar) (j : Fin 2 ↪ Fin D.size)
    (w : B.StarSurvivor) (hwlabel : w.val = B.completedLabel A (Rich.reserve i))
    (hsep : ¬ B.syndromeStar.Reachable B.completedHub w)
    (hx : B.completedHub ∈ (D.path (j 0)).walk.support)
    (hs : (D.path (j 0)).start ≠ B.completedHub)
    (ht : B.completedHub ≠ (D.path (j 0)).finish)
    (havoid : ∀ k, k ≠ j 0 → B.completedHub ∉ (D.path k).walk.support)
    (hw : (D.path (j 1)).finish = w) :
    ∃ P : Decomposition G, P.size ≤ D.size + 1 ∧
      ∀ v : B.StarSurvivor, (∀ t, B.completedLabel A t ≠ v.val) →
        D.endpointCount v ≤ P.endpointCount v.val := by
  classical
  obtain ⟨N₀,N₁,hePair,hendPair⟩ := B.sizeTwo_separated_pair A hSigma i connector tail
    added h w hwlabel hsep (D.path (j 0)) hx hs ht (D.path (j 1)) hw
  let base : Fin D.size → Option (NonemptyPath G) := fun k =>
    if hk : k = j 0 then none else some (B.syndromeAvoidingPath (D.path k) (havoid k hk))
  let outs : Fin 2 → Option (NonemptyPath G) := ![some N₀,some N₁]
  let F := replaceFamily base j outs
  have hselected (l : Fin 2) : F (j l) = outs l := replaceFamily_selected base j outs l
  have hother (k : Fin D.size) (hk : ∀ l, j l ≠ k) :
      ∃ hf : B.completedHub ∉ (D.path k).walk.support,
        F k = some (B.syndromeAvoidingPath (D.path k) hf) := by
    have hk₀ : k ≠ j 0 := (hk 0).symm
    refine ⟨havoid k hk₀,?_⟩
    change replaceFamily base j outs k = _
    rw [replaceFamily_unselected base j outs k (by rintro ⟨l,hl⟩; exact hk l hl)]
    exact dif_neg hk₀
  have two (f : Fin 2 → ℕ) : (∑ l, f l) = f 0 + f 1 := by
    simp [Fin.sum_univ_succ]
  have hmeasure (measure : NonemptyPath G → ℕ) :
      (∑ l : Fin 2, ((F (j l)).map measure).getD 0) = measure N₀ + measure N₁ := by
    simp_rw [hselected]
    simp [outs,Fin.sum_univ_succ]
  have hbalance (e : Sym2 V) :
      (∑ k, ((F k).map (fun Q => Q.walk.edges.count e)).getD 0) +
        ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e =
      (∑ k, ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e) +
        ((wordEdges connector).map (Sym2.map (B.completedLabel A))).count e +
        ((wordEdges tail).map (Sym2.map (B.completedLabel A))).count e := by
    rw [Nat.add_assoc]
    apply sum_grouped_balance _ _ j
    · rw [hmeasure,two]
      have hh := hePair e
      omega
    · intro k hk
      obtain ⟨hf,hF⟩ := hother k hk
      rw [hF]
      exact congrArg (List.count e) (B.syndromeAvoidingPath_edges (D.path k) hf)
  obtain ⟨P,hsize,hend⟩ := B.sizeTwo_separated_assemble A i connector tail added h
    hSigma D F hbalance
  refine ⟨P,hsize,?_⟩
  intro v hv
  let endpoint (Q : NonemptyPath G) : ℕ :=
    (if Q.start = v.val then 1 else 0) + (if Q.finish = v.val then 1 else 0)
  let old (k : Fin D.size) : ℕ :=
    (if (D.path k).start.val = v.val then 1 else 0) +
      (if (D.path k).finish.val = v.val then 1 else 0)
  have hends : (∑ k, ((F k).map endpoint).getD 0) = ∑ k, old k := by
    suffices hh : (∑ k, ((F k).map endpoint).getD 0) + 0 = (∑ k, old k) + 0 by
      simpa only [Nat.add_zero] using hh
    apply sum_grouped_balance old (fun k => ((F k).map endpoint).getD 0) j 0 0
    · rw [hmeasure,two]
      simpa only [endpoint,old,Nat.add_zero] using hendPair v.val hv
    · intro k hk
      obtain ⟨hf,hF⟩ := hother k hk
      rw [hF]
      rfl
  have hold : (∑ k, old k) = D.endpointCount v := by
    simp only [old,Decomposition.endpointCount,Subtype.val_inj]
  exact (hends.trans hold).symm.trans_le (hend v.val)

end Gallai.WholeBowtie
