/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoPassingDispatch

/-! # Simultaneous ordinary passing reconstruction with exact endpoint formulas -/
namespace Gallai.Certificate.SizeTwo

/-- The fourth slot is inactive in passing mode, including its edge weight. -/
theorem passing_unused_empty (state : State) (i : Fin 13) (hi : through i = true)
    (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
    (h : OrdinaryAccepted state i words added) : words 3 = [] := by
  have hh := h.1 3
  simpa [roleAccepted,boundary,hi] using hh

/-- Passing hub and remote roles exhaust the nonzero word weights. -/
theorem passing_weight_sum {K : Type*} [DecidableEq K] (i : Fin 13)
    (hi : through i = true) (f : Fin 4 → K) (k : K) (w : Fin 4 → ℕ) (hw : w 3 = 0) :
    (∑ j : Fin 4, if f j = k then w j else 0) =
      (if f 0 = k then w 0 else 0) +
      ∑ r : Fin 2, if f (remoteRole i r) = k then w (remoteRole i r) else 0 := by
  simp [Fin.sum_univ_succ,remoteRole,hi,hw,Nat.add_assoc]

/-- Neither remote role is the deliberately unused fourth slot. -/
theorem passing_remote_ne_unused (i : Fin 13) (hi : through i = true) (r : Fin 2) :
    remoteRole i r ≠ 3 := by
  fin_cases r <;> simp [remoteRole,hi]

end Gallai.Certificate.SizeTwo

namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- All old carriers receive actual simple replacements in passing mode.
The unused slot may share an owner but has zero weight. Both endpoint formulas
are preserved for every replacement; global graph coverage remains separate. -/
theorem sizeTwo_passing_family (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (i : Fin 13) (hi : through i = true)
    (D : Decomposition B.syndromeStar) (f : Fin 4 → Fin D.size)
    (hf : ∀ r : Fin 2,
      (D.path (f (remoteRole i r))).start = B.sizeTwoRemoteMarks A r ∨
      (D.path (f (remoteRole i r))).finish = B.sizeTwoRemoteMarks A r)
    (howner : ∀ j k, j ≠ 3 → k ≠ 3 → (f j = f k ↔ owner i j = owner i k))
    (hx : B.completedHub ∈ (D.path (f 0)).walk.support)
    (hs : (D.path (f 0)).start ≠ B.completedHub)
    (ht : B.completedHub ≠ (D.path (f 0)).finish)
    (havoid : ∀ k, k ≠ f 0 → B.completedHub ∉ (D.path k).walk.support)
    (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
    (h : OrdinaryAccepted (B.completedStarState A) i words added) :
    ∃ F : Fin D.size → NonemptyPath G, ∀ k,
      (F k).start = ((B.sizeTwoAssignedRole A i words added h
        (B.sizeTwoEndpointRoles A i D f k false)).map (·.finish)).getD (D.path k).start.val ∧
      (F k).finish = ((B.sizeTwoAssignedRole A i words added h
        (B.sizeTwoEndpointRoles A i D f k true)).map (·.finish)).getD (D.path k).finish.val ∧
      ∀ e : Sym2 V, (F k).walk.edges.count e +
        (if k = f 0 then ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e else 0) =
        ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e +
        ∑ j : Fin 4, if f j = k then
          ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e else 0 := by
  classical
  have hweight (e : Sym2 V) :
      ((wordEdges (words 3)).map (Sym2.map (B.completedLabel A))).count e = 0 := by
    rw [passing_unused_empty _ i hi words added h]
    rfl
  obtain ⟨N0,hNs0,hNt0,hNe0⟩ := B.sizeTwo_dispatch_passing A hSigma i hi D f hf words added h hx hs ht
    (fun r he => (howner _ _ (passing_remote_ne_unused i hi r) (by decide)).mp he)
  have perCarrier : ∀ k : Fin D.size, ∃ N : NonemptyPath G,
      N.start = ((B.sizeTwoAssignedRole A i words added h
        (B.sizeTwoEndpointRoles A i D f k false)).map (·.finish)).getD (D.path k).start.val ∧
      N.finish = ((B.sizeTwoAssignedRole A i words added h
        (B.sizeTwoEndpointRoles A i D f k true)).map (·.finish)).getD (D.path k).finish.val ∧
      ∀ e : Sym2 V, N.walk.edges.count e +
        (if k = f 0 then ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e else 0) =
        ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e +
        ∑ j : Fin 4, if f j = k then
          ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e else 0 := by
    intro k
    by_cases hk : k = f 0
    · subst k
      refine ⟨N0,hNs0,hNt0,?_⟩
      intro e
      rw [passing_weight_sum i hi f (f 0) _ (hweight e)]
      simpa [Nat.add_assoc] using hNe0 e
    · obtain ⟨N,hNs,hNt,hNe⟩ := B.sizeTwo_dispatch_avoiding A i D f hf words added h
        (fun r s he => (howner _ _ (passing_remote_ne_unused i hi r)
          (passing_remote_ne_unused i hi s)).mp he) k (havoid k hk)
      refine ⟨N,hNs,hNt,?_⟩
      intro e
      rw [passing_weight_sum i hi f k _ (hweight e)]
      simpa [hk,Ne.symm hk] using hNe e
  exact ⟨fun k => Classical.choose (perCarrier k),fun k => Classical.choose_spec (perCarrier k)⟩

end Gallai.WholeBowtie
