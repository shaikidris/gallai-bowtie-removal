/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRichReconstruction
import Gallai.Transport.SizeTwoRichConnectors
import Gallai.Transport.SizeTwoRichOptionalTerminal
import Gallai.Transport.SizeTwoRichFamilyEndpoints
import Gallai.Transport.SizeTwoPassingDispatch

/-! # One-credit reconstruction from selected rich through carriers

The certificate supplies the connectors, the optional tail and the additional
paths. The actual carrier operations supply the balanced family; no edge-count
or favourable reconstruction premise is left to the caller.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- An accepted rich through record consumes four selected, oriented carriers
and preserves all endpoint reserves outside the local labels within one credit. -/
theorem sizeTwo_rich_through_consumer (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (i : Fin 4) (hi : Rich.isThrough i = true)
    (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
    (h : Rich.AcceptedRecord (B.completedStarState A) i words added)
    (D : Decomposition B.syndromeStar) (j : Fin 4 ↪ Fin D.size)
    (w : B.StarSurvivor) (hwlabel : w.val = B.completedLabel A (Rich.reserve i))
    (hsep : ¬ B.syndromeStar.Reachable B.completedHub w)
    (hx : B.completedHub ∈ (D.path (j 0)).walk.support)
    (hs : (D.path (j 0)).start ≠ B.completedHub)
    (ht : B.completedHub ≠ (D.path (j 0)).finish)
    (havoid : ∀ k, k ≠ j 0 → B.completedHub ∉ (D.path k).walk.support)
    (hw : ∀ l : Fin 3, (D.path (j l.succ)).finish = w) :
    ∃ P : Decomposition G, P.size ≤ D.size + 1 ∧
      ∀ v : B.StarSurvivor, (∀ t, B.completedLabel A t ≠ v.val) →
        D.endpointCount v ≤ P.endpointCount v.val := by
  classical
  let b := ((D.path (j 0)).takeTo B.completedHub hx hs).walk.reverse.snd
  let c := ((D.path (j 0)).dropFrom B.completedHub hx ht).walk.snd
  have hpair := B.sizeTwo_passing_attachment_pair A hSigma (D.path (j 0)) hx hs ht
  obtain ⟨M₀,M₁,hM₀,hn₀,hM₁,hn₁,hMe,hm₀,hm₁⟩ :=
    B.sizeTwo_rich_connectors A i hi words added h b c w hwlabel hpair
  let C₀ := M₀.copy rfl (congrArg Subtype.val (hw 0)).symm
  let C₁ := M₁.copy rfl (congrArg Subtype.val (hw 1)).symm
  let T := B.sizeTwoRichOptionalRole A i words added h 2
  have hb₂ : Rich.boundary i 2 = [Rich.reserve i] := by simp [Rich.boundary,hi]
  have hT : ∀ Q ∈ T, Q.start = w.val ∧
      ∀ v ∈ Q.walk.support, v = Q.start ∨ v ∈ B.vertices := by
    intro Q hQ
    obtain ⟨hj,rfl⟩ := B.sizeTwoRichOptionalRole_mem A i words added h 2 Q hQ
    obtain ⟨hQs,hQv⟩ := B.sizeTwoRichRole_single A i words added h 2 hj (Rich.reserve i) hb₂
    refine ⟨hQs.trans hwlabel.symm,?_⟩
    intro v hv
    simpa only [hQs] using hQv v hv
  have hC₀ : C₀.IsPath := (SimpleGraph.Walk.isPath_copy _ _ _).mpr hM₀
  have hC₁ : C₁.IsPath := (SimpleGraph.Walk.isPath_copy _ _ _).mpr hM₁
  have hnC₀ : ¬ C₀.Nil := by simpa only [C₀,SimpleGraph.Walk.nil_copy] using hn₀
  have hnC₁ : ¬ C₁.Nil := by simpa only [C₁,SimpleGraph.Walk.nil_copy] using hn₁
  have hw₁ : (D.path (j 1)).finish = w := hw 0
  have hw₂ : (D.path (j 2)).finish = w := hw 1
  have hmC₀ : ∀ v : B.StarSurvivor, v.val ∈ C₀.support →
      v.val = b.val ∨ v.val = (D.path (j 1)).finish.val ∨ v.val = B.label 0 := by
    intro v hv
    simp only [C₀,SimpleGraph.Walk.support_copy] at hv
    simpa only [hw₁] using hm₀ v hv
  have hmC₁ : ∀ v : B.StarSurvivor, v.val ∈ C₁.support →
      v.val = c.val ∨ v.val = (D.path (j 2)).finish.val ∨ v.val = B.label 0 := by
    intro v hv
    simp only [C₁,SimpleGraph.Walk.support_copy] at hv
    simpa only [hw₂] using hm₁ v hv
  obtain ⟨N₀,N₁,N₂,hs₀,ht₀,hs₁,ht₁,hs₂,ht₂,hgroup,F,hselected,hother⟩ :=
    B.sizeTwo_rich_through_family D j w hsep hx hs ht havoid hw
      C₀ C₁ hC₀ hnC₀ hC₁ hnC₁ hmC₀ hmC₁ T hT
  have ho : ∀ k, (∀ l, j l ≠ k) → ∃ hk : B.completedHub ∉ (D.path k).walk.support,
      F k = some (B.syndromeAvoidingPath (D.path k) hk) := by
    intro k hk
    obtain ⟨hk₀,hF⟩ := hother k hk
    exact ⟨havoid k hk₀,hF⟩
  let removed : List (Sym2 V) := [s(B.label 0,b.val),s(B.label 0,c.val)]
  let localEdges := C₀.edges ++ C₁.edges ++ (T.map (fun Q => Q.walk.edges)).getD []
  have hg : ∀ e, N₀.walk.edges.count e + N₁.walk.edges.count e + N₂.walk.edges.count e +
      removed.count e =
      (∑ l : Fin 4, ((D.path (j l)).walk.edges.map (Sym2.map Subtype.val)).count e) +
        localEdges.count e := by
    intro e
    simpa only [localEdges,List.count_append,Nat.add_assoc] using hgroup e
  have hf := B.sizeTwo_rich_through_family_counts D j N₀ N₁ N₂ F hselected ho
    removed localEdges hg
  have hw₃ : words 3 = [] := by
    have hh := h.1 3
    simpa [Rich.roleAccepted,Rich.boundary,hi] using hh
  have heLocal (e : Sym2 V) : localEdges.count e =
      ∑ l : Fin 4, ((wordEdges (words l)).map (Sym2.map (B.completedLabel A))).count e := by
    have hte := B.sizeTwoRichOptionalRole_edges A i words added h 2
    have hme := hMe e
    dsimp only [localEdges,C₀,C₁]
    rw [List.count_append,List.count_append,SimpleGraph.Walk.edges_copy,
      SimpleGraph.Walk.edges_copy,hte,hme]
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
    change _ = _ + (_ + (_ + (_ + 0)))
    simp [hw₃,wordEdges,Nat.add_assoc]
  have heRemoved (e : Sym2 V) : removed.count e =
      ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e := by
    change ([s(B.label 0,b.val),s(B.label 0,c.val)] : List (Sym2 V)).count e = _
    rcases hpair with ⟨hb,hc⟩ | ⟨hb,hc⟩
    · rw [hb,hc]; rfl
    · rw [hb,hc]
      change ([s(B.label 0,(A 1).val),s(B.label 0,(A 0).val)] : List (Sym2 V)).count e = _
      simp only [List.count_cons,List.count_nil,Nat.zero_add]
      exact Nat.add_comm _ _
  obtain ⟨P,hsize,hend⟩ := B.sizeTwo_rich_assemble A i words added h hSigma D F
    (j 1) (by simpa using hselected 1) (fun e => by
      simpa only [heRemoved,heLocal] using hf e)
  refine ⟨P,hsize,?_⟩
  intro v hv
  have hwv : w.val ≠ v.val := fun he => hv (Rich.reserve i) (hwlabel.symm.trans he)
  have hnv : N₂.finish ≠ v.val := by
    rw [ht₂]
    cases hTval : T with
    | none => simpa only [Option.map_none,Option.getD_none] using hwv
    | some Q =>
      have hQ : Q ∈ T := by rw [hTval]; simp
      obtain ⟨hj,rfl⟩ := B.sizeTwoRichOptionalRole_mem A i words added h 2 Q hQ
      simpa only [Option.map_some,Option.getD_some] using
        B.sizeTwoRichRole_finish_ne A i words added h 2 hj v.val hv
  have he := B.sizeTwo_rich_through_family_endpoints D j w hw N₀ N₁ N₂ F hselected ho
    hs₀ ht₀ hs₁ ht₁ hs₂ v.val hwv hnv
  have hev : (∑ k, ((if (D.path k).start.val = v.val then 1 else 0) +
      (if (D.path k).finish.val = v.val then 1 else 0 : ℕ))) = D.endpointCount v := by
    simp only [Decomposition.endpointCount,Subtype.val_inj]
  exact (he.trans hev).symm.trans_le (hend v.val)

end Gallai.WholeBowtie
