/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoTerminalDispatch

/-! # Actual through-carrier dispatch without reorienting the decomposition -/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The two released attachments are precisely the normalized syndrome pair,
in one of its two orders. No choice of old carrier orientation is needed. -/
theorem sizeTwo_passing_attachment_pair (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (P : NonemptyPath B.syndromeStar)
    (hx : B.completedHub ∈ P.walk.support)
    (hs : P.start ≠ B.completedHub) (ht : B.completedHub ≠ P.finish) :
    ((P.takeTo B.completedHub hx hs).walk.reverse.snd.val = B.completedLabel A Star.Vertex.p ∧
     (P.dropFrom B.completedHub hx ht).walk.snd.val = B.completedLabel A Star.Vertex.q) ∨
    ((P.takeTo B.completedHub hx hs).walk.reverse.snd.val = B.completedLabel A Star.Vertex.q ∧
     (P.dropFrom B.completedHub hx ht).walk.snd.val = B.completedLabel A Star.Vertex.p) := by
  let b := (P.takeTo B.completedHub hx hs).walk.reverse.snd
  let c := (P.dropFrom B.completedHub hx ht).walk.snd
  have hadj := P.release_attachments_adj B.completedHub hx hs ht
  have hbc := P.release_attachments_ne B.completedHub hx hs ht
  have hb := (B.syndromeStar_hub_adj b).mp hadj.1
  have hc := (B.syndromeStar_hub_adj c).mp hadj.2
  rw [hSigma,Finset.mem_insert,Finset.mem_singleton] at hb hc
  change (b.val = _ ∧ c.val = _) ∨ (b.val = _ ∧ c.val = _)
  simp only [completedLabel]
  rcases hb with hb | hb <;> rcases hc with hc | hc
  · exact (hbc (Subtype.ext (hb.trans hc.symm))).elim
  · exact Or.inl ⟨hb,hc⟩
  · exact Or.inr ⟨hb,hc⟩
  · exact (hbc (Subtype.ext (hb.trans hc.symm))).elim

/-- Reconstruct the actual hub-through carrier with all its assigned remote
tails. Connector orientation is internal; old endpoint ownership is untouched. -/
theorem sizeTwo_dispatch_passing (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (i : Fin 13) (hi : through i = true)
    (D : Decomposition B.syndromeStar) (f : Fin 4 → Fin D.size)
    (hf : ∀ r : Fin 2,
      (D.path (f (remoteRole i r))).start = B.sizeTwoRemoteMarks A r ∨
      (D.path (f (remoteRole i r))).finish = B.sizeTwoRemoteMarks A r)
    (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
    (h : OrdinaryAccepted (B.completedStarState A) i words added)
    (hx : B.completedHub ∈ (D.path (f 0)).walk.support)
    (hs : (D.path (f 0)).start ≠ B.completedHub)
    (ht : B.completedHub ≠ (D.path (f 0)).finish)
    (howners : ∀ r : Fin 2, f (remoteRole i r) = f 0 →
      owner i (remoteRole i r) = owner i 0) :
    ∃ N : NonemptyPath G,
      N.start = ((B.sizeTwoAssignedRole A i words added h
        (B.sizeTwoEndpointRoles A i D f (f 0) false)).map (·.finish)).getD (D.path (f 0)).start.val ∧
      N.finish = ((B.sizeTwoAssignedRole A i words added h
        (B.sizeTwoEndpointRoles A i D f (f 0) true)).map (·.finish)).getD (D.path (f 0)).finish.val ∧
      ∀ e : Sym2 V, N.walk.edges.count e +
        ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e =
        ((D.path (f 0)).walk.edges.map (Sym2.map Subtype.val)).count e +
        ((wordEdges (words 0)).map (Sym2.map (B.completedLabel A))).count e +
        ∑ r : Fin 2, if f (remoteRole i r) = f 0 then
          ((wordEdges (words (remoteRole i r))).map (Sym2.map (B.completedLabel A))).count e else 0 := by
  have hne : words 0 ≠ [] := by
    intro he
    have hh := h.1 0
    rw [he] at hh
    exact required_connector_nonempty i hh
  have hpair := B.sizeTwo_passing_attachment_pair A hSigma (D.path (f 0)) hx hs ht
  have tails (side : Bool) : ∀ k ∈ B.sizeTwoEndpointRoles A i D f (f 0) side,
      ∃ symbol : Star.Vertex, boundary i k = [symbol] ∧
        (if side then (D.path (f 0)).finish.val else (D.path (f 0)).start.val) =
          B.completedLabel A symbol ∧ k ≠ 0 ∧ owner i k = owner i 0 := by
    intro k hk
    obtain ⟨r,hr,howner,hbk,hvk⟩ := B.sizeTwoEndpointRoles_spec A i D f hf (f 0) side k hk
    refine ⟨_,hbk,hvk,?_,?_⟩
    · intro he
      exact remoteRole_not_mandatory i r ((hr.trans he).symm ▸ (Or.inl rfl : mandatory i 0))
    · subst k
      exact howners r howner
  obtain ⟨N,hNs,hNt,hNe⟩ := B.sizeTwo_passing_record A i words added h 0 hne
    Star.Vertex.p Star.Vertex.q (by simp [boundary,hi]) (D.path (f 0)) hx hs ht hpair
    (B.sizeTwoEndpointRoles A i D f (f 0) false)
    (B.sizeTwoEndpointRoles A i D f (f 0) true)
    (tails false) (tails true)
    (fun k hk l hl => B.sizeTwoEndpointRoles_distinct A i D f hf (f 0) k l hk hl)
  refine ⟨N,hNs,hNt,?_⟩
  intro e
  have hsum := B.sizeTwoEndpointRoles_sum A i D f hf (f 0)
    (fun k => ((wordEdges (words k)).map (Sym2.map (B.completedLabel A))).count e)
  simp only [Fintype.sum_bool] at hsum
  have he := hNe e
  have hsp : ([s(B.label 0,((D.path (f 0)).takeTo B.completedHub hx hs).walk.reverse.snd.val),
      s(B.label 0,((D.path (f 0)).dropFrom B.completedHub hx ht).walk.snd.val)] : List (Sym2 V)).count e =
      ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e := by
    rcases hpair with ⟨hp,hq⟩ | ⟨hq,hp⟩
    · rw [hp,hq]
      rfl
    · rw [hq,hp]
      change ([s(B.label 0,(A 1).val),s(B.label 0,(A 0).val)] : List (Sym2 V)).count e = _
      simp only [List.count_cons,List.count_nil]
      omega
  rw [hsp] at he
  omega

end Gallai.WholeBowtie
