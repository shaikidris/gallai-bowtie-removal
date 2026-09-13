/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRemoteAssignment
import Gallai.Transport.SizeTwoTerminalRecord

/-! # Actual terminal-role dispatch with automatically selected remote tails -/
namespace Gallai.Certificate.SizeTwo

theorem mandatory_rejects_empty : ∀ i : Fin 13, ∀ j : Fin 4,
    mandatory i j → ¬ roleAccepted i j [] := by decide

theorem remoteRole_not_mandatory : ∀ i : Fin 13, ∀ r : Fin 2,
    ¬ mandatory i (remoteRole i r) := by decide

end Gallai.Certificate.SizeTwo

namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : B.AnchorNumbering) (i : Fin 13) (D : Decomposition B.syndromeStar)
variable (f : Fin 4 → Fin D.size)
variable (hf : ∀ r : Fin 2,
  (D.path (f (remoteRole i r))).start = B.sizeTwoRemoteMarks A r ∨
  (D.path (f (remoteRole i r))).finish = B.sizeTwoRemoteMarks A r)

include hf in
/-- A terminal hub endpoint cannot receive an external-anchor remote role. -/
theorem sizeTwoEndpointRoles_finish_hub (k : Fin D.size)
    (hx : (D.path k).finish = B.completedHub) :
    B.sizeTwoEndpointRoles A i D f k true = none := by
  cases ho : B.sizeTwoEndpointRoles A i D f k true with
  | none => rfl
  | some j =>
    have hj : j ∈ B.sizeTwoEndpointRoles A i D f k true := by rw [ho]; simp
    obtain ⟨r,_,_,_,hv⟩ := B.sizeTwoEndpointRoles_spec A i D f hf k true j hj
    have hxv : (D.path k).finish.val = B.label 0 := congrArg Subtype.val hx
    have hbad := hxv.symm.trans hv
    rw [B.completedLabel_anchor] at hbad
    exact (B.label_ne_numberedAnchor A 0 ⟨r.val + 2,by omega⟩ hbad).elim

include hf in
/-- The normalized terminal carrier now consumes its mandatory word and all
remote words assigned to it, without any supplied optional-role selector. -/
theorem sizeTwo_dispatch_terminal
    (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
    (h : OrdinaryAccepted (B.completedStarState A) i words added)
    (j : Fin 4) (hj : mandatory i j) (symbol : Star.Vertex)
    (hb : boundary i j = [symbol])
    (hx : (D.path (f j)).finish = B.completedHub)
    (hu : (D.path (f j)).walk.reverse.snd.val = B.completedLabel A symbol)
    (howners : ∀ r : Fin 2, f (remoteRole i r) = f j →
      owner i (remoteRole i r) = owner i j) :
    ∃ hne : words j ≠ [], ∃ N : NonemptyPath G,
      N.start = ((B.sizeTwoAssignedRole A i words added h
        (B.sizeTwoEndpointRoles A i D f (f j) false)).map (·.finish)).getD (D.path (f j)).start.val ∧
      N.finish = (B.sizeTwoRole A i words added h j hne).finish ∧
      ∀ e : Sym2 V, N.walk.edges.count e +
        (if s(B.label 0,(D.path (f j)).walk.reverse.snd.val) = e then 1 else 0) =
        ((D.path (f j)).walk.edges.map (Sym2.map Subtype.val)).count e +
        ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e +
        ∑ r : Fin 2, if f (remoteRole i r) = f j then
          ((wordEdges (words (remoteRole i r))).map (Sym2.map (B.completedLabel A))).count e else 0 := by
  have hne : words j ≠ [] := by
    intro he
    have hr := h.1 j
    rw [he] at hr
    exact mandatory_rejects_empty i j hj hr
  let left := B.sizeTwoEndpointRoles A i D f (f j) false
  obtain ⟨N,hNs,hNt,hNe⟩ := B.sizeTwo_terminal_assigned A i words added h j hne symbol hb
    (D.path (f j)) hx hu left (by
      intro k hk
      obtain ⟨r,hr,howner,hbk,hvk⟩ := B.sizeTwoEndpointRoles_spec A i D f hf (f j) false k hk
      refine ⟨_,hbk,hvk,?_,?_⟩
      · intro hkj
        exact remoteRole_not_mandatory i r ((hr.trans hkj).symm ▸ hj)
      · subst k
        exact howners r howner)
  refine ⟨hne,N,hNs,hNt,?_⟩
  intro e
  have hsum := B.sizeTwoEndpointRoles_sum A i D f hf (f j)
    (fun k => ((wordEdges (words k)).map (Sym2.map (B.completedLabel A))).count e)
  rw [Fintype.sum_bool,B.sizeTwoEndpointRoles_finish_hub A i D f hf (f j) hx] at hsum
  simp only [Option.map_none,Option.getD_none,Nat.zero_add,Nat.add_zero] at hsum
  have he := hNe e
  dsimp only [left] at he
  rw [hsum] at he
  exact he

end Gallai.WholeBowtie
