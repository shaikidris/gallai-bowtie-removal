/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoForcedEndpoints
import Gallai.Transport.SizeTwoForcedSelection

/-! # A forced record reconstructs the entire old carrier family

Select the extra carrier from parity, reconstruct it and the central carrier,
and retain all other paths. This gives exact per-carrier balances and outside
endpoint preservation; adding the finite new paths is the next assembly step.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Actual carrier supply and the two splice constructions are consumed on
one family. The additional selected carrier is proved distinct, not assumed. -/
theorem sizeTwo_forced_family (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (D : Decomposition B.syndromeStar) (k₀ : Fin D.size)
    (hr : (D.path k₀).start = B.sizeTwoRemoteMarks A 0 ∨
      (D.path k₀).finish = B.sizeTwoRemoteMarks A 0)
    (hsRemote : (D.path k₀).start = B.sizeTwoRemoteMarks A 1 ∨
      (D.path k₀).finish = B.sizeTwoRemoteMarks A 1)
    (hx : B.completedHub ∈ (D.path k₀).walk.support)
    (hs : (D.path k₀).start ≠ B.completedHub)
    (ht : B.completedHub ≠ (D.path k₀).finish)
    (havoid : ∀ k, k ≠ k₀ → B.completedHub ∉ (D.path k).walk.support)
    (j : Fin 2) (connector extra tail : List Star.Vertex) (added : List (List Star.Vertex))
    (h : Forced.AcceptedRecord (B.completedStarState A) j connector extra tail added) :
    ∃ k₁ : Fin D.size, k₁ ≠ k₀ ∧ ∃ F : Fin D.size → NonemptyPath G,
      (∀ k e, (F k).walk.edges.count e +
        (if k = k₀ then
          ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e else 0) =
        ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e +
        (if k = k₀ then
          ((wordEdges connector).map (Sym2.map (B.completedLabel A))).count e +
          ((wordEdges tail).map (Sym2.map (B.completedLabel A))).count e else 0) +
        (if k = k₁ then ((wordEdges extra).map (Sym2.map (B.completedLabel A))).count e else 0)) ∧
      ∀ k v, (∀ t, B.completedLabel A t ≠ v) →
        ((F k).start = v ↔ (D.path k).start.val = v) ∧
        ((F k).finish = v ↔ (D.path k).finish.val = v) := by
  classical
  obtain ⟨f,hf⟩ := B.sizeTwo_forced_endpoint_carriers A D k₀ hr hsRemote
  let k₁ := f j
  have hk₁ : k₁ ≠ k₀ := (hf j).1
  have hextra : (D.path k₁).start.val = B.completedLabel A (Forced.extraAnchor j) ∨
      (D.path k₁).finish.val = B.completedLabel A (Forced.extraAnchor j) := by
    fin_cases j <;> exact (hf _).2
  obtain ⟨atStart,ha⟩ : ∃ atStart : Bool,
      (if atStart then (D.path k₀).start.val else (D.path k₀).finish.val) =
        B.completedLabel A .s := by
    rcases hsRemote with he | he
    · exact ⟨true,congrArg Subtype.val he⟩
    · exact ⟨false,congrArg Subtype.val he⟩
  have hpair := B.sizeTwo_passing_attachment_pair A hSigma (D.path k₀) hx hs ht
  obtain ⟨N₀,hN₀s,hN₀t,hN₀e⟩ := B.sizeTwo_forced_central_splice A j connector extra tail added h
    (D.path k₀) hx hs ht hpair atStart ha
  obtain ⟨N₁,hN₁ends,hN₁e⟩ := B.sizeTwo_forced_extra_splice A j connector extra tail added h
    (D.path k₁) (havoid k₁ hk₁) hextra
  have hcentral (e : Sym2 V) : N₀.walk.edges.count e +
      ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e =
      ((D.path k₀).walk.edges.map (Sym2.map Subtype.val)).count e +
      ((wordEdges connector).map (Sym2.map (B.completedLabel A))).count e +
      ((wordEdges tail).map (Sym2.map (B.completedLabel A))).count e := by
    have he := hN₀e e
    rcases hpair with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · simpa only [hu,hv,completedLabel] using he
    · simp only [hu,hv,completedLabel,List.count_cons,List.count_nil] at he ⊢
      omega
  let F : Fin D.size → NonemptyPath G := fun k =>
    if hk : k = k₀ then N₀ else
      if k = k₁ then N₁ else B.syndromeAvoidingPath (D.path k) (havoid k hk)
  have hF₀ : F k₀ = N₀ := by simp only [F,dif_pos rfl]
  have hF₁ : F k₁ = N₁ := by simp only [F,dif_neg hk₁,↓reduceIte]
  have hFother (k : Fin D.size) (hk : k ≠ k₀) (hl : k ≠ k₁) :
      F k = B.syndromeAvoidingPath (D.path k) (havoid k hk) := by
    simp only [F,dif_neg hk,if_neg hl]
  refine ⟨k₁,hk₁,F,?_,?_⟩
  · intro k e
    by_cases hk : k = k₀
    · subst k
      rw [hF₀]
      simpa only [hk₁.symm,↓reduceIte,Nat.add_zero,Nat.add_assoc] using hcentral e
    · by_cases hl : k = k₁
      · subst k
        rw [hF₁]
        simpa only [hk₁,↓reduceIte,Nat.add_zero] using hN₁e e
      · rw [hFother k hk hl]
        simp only [hk,hl,↓reduceIte,Nat.add_zero]
        exact congrArg (List.count e) (B.syndromeAvoidingPath_edges (D.path k) (havoid k hk))
  · intro k v hv
    by_cases hk : k = k₀
    · subst k
      simpa only [F,↓reduceDIte] using
        B.sizeTwo_forced_central_endpoints A j connector extra tail added h
          (D.path k₀) N₀ atStart ha hN₀s hN₀t v hv
    · by_cases hl : k = k₁
      · subst k
        simpa only [F,hk₁,↓reduceDIte,↓reduceIte] using
          B.sizeTwo_forced_extra_endpoints A j connector extra tail added h
            (D.path k₁) N₁ hN₁ends v hv
      · simp only [F,hk,hl,↓reduceDIte,↓reduceIte]
        exact ⟨Iff.rfl,Iff.rfl⟩

end Gallai.WholeBowtie
