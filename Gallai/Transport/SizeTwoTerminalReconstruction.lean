/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoTerminalFamily
import Gallai.Transport.SizeTwoReconstruction
import Gallai.Transport.SizeTwoEndpointReserve

/-! # Accepted ordinary terminal records reconstruct the original graph -/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The two distinct terminal carriers release one spoke each. Their exact
total discharges global coverage without an original-spoke assumption. -/
theorem sizeTwo_terminal_reconstruction (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (i : Fin 13) (hi : through i = false)
    (D : Decomposition B.syndromeStar) (f : Fin 4 → Fin D.size)
    (hf : ∀ r : Fin 2,
      (D.path (f (remoteRole i r))).start = B.sizeTwoRemoteMarks A r ∨
      (D.path (f (remoteRole i r))).finish = B.sizeTwoRemoteMarks A r)
    (howner : ∀ j k, f j = f k ↔ owner i j = owner i k)
    (hx0 : (D.path (f 0)).finish = B.completedHub)
    (hu0 : (D.path (f 0)).walk.reverse.snd.val = B.completedLabel A Star.Vertex.p)
    (hx1 : (D.path (f 1)).finish = B.completedHub)
    (hu1 : (D.path (f 1)).walk.reverse.snd.val = B.completedLabel A Star.Vertex.q)
    (havoid : ∀ k, k ≠ f 0 → k ≠ f 1 → B.completedHub ∉ (D.path k).walk.support)
    (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
    (h : OrdinaryAccepted (B.completedStarState A) i words added) :
    ∃ P : Decomposition G, P.size = D.size + added.length ∧ P.size ≤ D.size + 2 ∧
      ∀ w : B.StarSurvivor, w.val ∉ B.vertices → Even (G.degree w.val) →
        D.endpointCount w ≤ P.endpointCount w.val := by
  classical
  obtain ⟨hne0,hne1,F,hF⟩ := B.sizeTwo_terminal_family A i hi D f hf howner hx0 hu0 hx1 hu1 havoid words added h
  have hneq : f 0 ≠ f 1 := fun he => terminal_owners_distinct i hi ((howner 0 1).mp he)
  let removed : Fin D.size → List (Sym2 V) := fun k =>
    if k = f 0 then [s(B.label 0,(A 0).val)]
    else if k = f 1 then [s(B.label 0,(A 1).val)] else []
  have hcarrier : ∀ k e, (F k).walk.edges.count e + (removed k).count e =
      ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e +
      ∑ j : Fin 4, if f j = k then
        ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e else 0 := by
    intro k e
    have he := (hF k).2.2 e
    rw [hu0,hu1] at he
    have hc : (removed k).count e =
        if k = f 0 then (if s(B.label 0,(A 0).val) = e then 1 else 0)
        else if k = f 1 then (if s(B.label 0,(A 1).val) = e then 1 else 0) else 0 := by
      by_cases hk0 : k = f 0 <;> by_cases hk1 : k = f 1 <;>
        by_cases he0 : s(B.label 0,(A 0).val) = e <;>
        by_cases he1 : s(B.label 0,(A 1).val) = e <;>
        simp [removed,hk0,hk1,Ne.symm hneq,he0,he1,List.count_cons]
    exact (congrArg (fun n => (F k).walk.edges.count e + n) hc).trans he
  have hremoved : ∀ e, (∑ k : Fin D.size, (removed k).count e) =
      ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e := by
    intro e
    have hsplit (k : Fin D.size) : (removed k).count e =
        (if k = f 0 then ([s(B.label 0,(A 0).val)] : List (Sym2 V)).count e else 0) +
        (if k = f 1 then ([s(B.label 0,(A 1).val)] : List (Sym2 V)).count e else 0) := by
      by_cases hk0 : k = f 0
      · subst k
        simp [removed,hneq]
      · by_cases hk1 : k = f 1 <;> simp [removed,hk0,hk1,hneq,Ne.symm hneq]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    simp [List.count_cons,Nat.add_comm]
  refine ⟨B.sizeTwoReconstruction A hSigma i words added h D f F removed hcarrier hremoved,
    B.sizeTwoReconstruction_size A hSigma i words added h D f F removed hcarrier hremoved,
    B.sizeTwoReconstruction_budget A hSigma i words added h D f F removed hcarrier hremoved,?_⟩
  intro w hout hw
  have hlabels := B.zero_even_outside_labels A ⟨w.val,hout⟩ hw
  have hxw : B.completedHub ≠ w := by
    intro he
    exact hlabels Star.Vertex.x (congrArg Subtype.val he)
  apply B.sizeTwoReconstruction_endpoint_reserve A i words added h hSigma D f F removed hcarrier hremoved w
  intro k
  have hstart : (F k).start = w.val ↔ (D.path k).start = w := by
    rw [(hF k).1]
    simpa only [Bool.false_eq_true,ite_false,Subtype.val_inj] using
      B.sizeTwo_optional_endpoint_iff A i words added h D f hf k false w.val hlabels
  have hfinish : (F k).finish = w.val ↔ (D.path k).finish = w := by
    rw [(hF k).2.1]
    by_cases hk0 : k = f 0
    · subst k
      simp [hx0,hxw,B.sizeTwoRole_finish_ne A i words added h 0 hne0 w.val hlabels]
    by_cases hk1 : k = f 1
    · subst k
      simp [Ne.symm hneq,hx1,hxw,B.sizeTwoRole_finish_ne A i words added h 1 hne1 w.val hlabels]
    · simp only [if_neg hk0,if_neg hk1]
      simpa only [ite_true,Subtype.val_inj] using
        B.sizeTwo_optional_endpoint_iff A i words added h D f hf k true w.val hlabels
  simp only [hstart,hfinish]

end Gallai.WholeBowtie
