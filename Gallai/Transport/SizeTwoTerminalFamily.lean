/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoTerminalDispatch

/-! # Simultaneous ordinary terminal reconstruction

Construct all old-carrier replacements from one normalized terminal profile.
The edge equation retains the released spokes explicitly; cancellation with
the auxiliary and addition of the extra certificate paths come afterwards.
-/
namespace Gallai.Certificate.SizeTwo

/-- In terminal mode the two hub slots and two remote slots exhaust the words. -/
theorem terminal_weight_sum {K : Type*} [DecidableEq K] (i : Fin 13)
    (hi : through i = false) (f : Fin 4 → K) (k : K) (w : Fin 4 → ℕ) :
    (∑ j : Fin 4, if f j = k then w j else 0) =
      (if f 0 = k then w 0 else 0) + (if f 1 = k then w 1 else 0) +
      ∑ r : Fin 2, if f (remoteRole i r) = k then w (remoteRole i r) else 0 := by
  simp [Fin.sum_univ_succ,remoteRole,hi,Nat.add_assoc]

end Gallai.Certificate.SizeTwo

namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- A normalized terminal profile supplies a replacement for EVERY old path,
with no global reconstruction premise. Optional remote tails are assigned by
actual endpoint ownership, even when they share a hub carrier. -/
theorem sizeTwo_terminal_family
    (A : B.AnchorNumbering) (i : Fin 13) (hi : through i = false)
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
    ∃ hne0 : words 0 ≠ [], ∃ hne1 : words 1 ≠ [],
    ∃ F : Fin D.size → NonemptyPath G, ∀ k,
      (F k).start = ((B.sizeTwoAssignedRole A i words added h
        (B.sizeTwoEndpointRoles A i D f k false)).map (·.finish)).getD (D.path k).start.val ∧
      (F k).finish = (if k = f 0 then (B.sizeTwoRole A i words added h 0 hne0).finish
        else if k = f 1 then (B.sizeTwoRole A i words added h 1 hne1).finish
        else ((B.sizeTwoAssignedRole A i words added h
          (B.sizeTwoEndpointRoles A i D f k true)).map (·.finish)).getD (D.path k).finish.val) ∧
      ∀ e : Sym2 V, (F k).walk.edges.count e +
        (if k = f 0 then (if s(B.label 0,(D.path (f 0)).walk.reverse.snd.val) = e then 1 else 0)
         else if k = f 1 then (if s(B.label 0,(D.path (f 1)).walk.reverse.snd.val) = e then 1 else 0)
         else 0) =
        ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e +
        ∑ j : Fin 4, if f j = k then
          ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e else 0 := by
  classical
  have hneq : f 0 ≠ f 1 := fun he => terminal_owners_distinct i hi ((howner 0 1).mp he)
  obtain ⟨hne0,N0,hNs0,hNt0,hNe0⟩ := B.sizeTwo_dispatch_terminal A i D f hf words added h
    0 (Or.inl rfl) Star.Vertex.p (by simp [boundary,hi]) hx0 hu0
    (fun r he => (howner _ _).mp he)
  obtain ⟨hne1,N1,hNs1,hNt1,hNe1⟩ := B.sizeTwo_dispatch_terminal A i D f hf words added h
    1 (Or.inr ⟨hi,rfl⟩) Star.Vertex.q (by simp [boundary,hi]) hx1 hu1
    (fun r he => (howner _ _).mp he)
  have perCarrier : ∀ k : Fin D.size, ∃ N : NonemptyPath G,
      N.start = ((B.sizeTwoAssignedRole A i words added h
        (B.sizeTwoEndpointRoles A i D f k false)).map (·.finish)).getD (D.path k).start.val ∧
      N.finish = (if k = f 0 then (B.sizeTwoRole A i words added h 0 hne0).finish
        else if k = f 1 then (B.sizeTwoRole A i words added h 1 hne1).finish
        else ((B.sizeTwoAssignedRole A i words added h
          (B.sizeTwoEndpointRoles A i D f k true)).map (·.finish)).getD (D.path k).finish.val) ∧
      ∀ e : Sym2 V, N.walk.edges.count e +
        (if k = f 0 then (if s(B.label 0,(D.path (f 0)).walk.reverse.snd.val) = e then 1 else 0)
         else if k = f 1 then (if s(B.label 0,(D.path (f 1)).walk.reverse.snd.val) = e then 1 else 0)
         else 0) =
        ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e +
        ∑ j : Fin 4, if f j = k then
          ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e else 0 := by
    intro k
    by_cases hk0 : k = f 0
    · subst k
      refine ⟨N0,hNs0,by simpa using hNt0,?_⟩
      intro e
      rw [terminal_weight_sum i hi]
      simpa [hneq,Ne.symm hneq,Nat.add_assoc] using hNe0 e
    by_cases hk1 : k = f 1
    · subst k
      refine ⟨N1,hNs1,by simpa [Ne.symm hneq] using hNt1,?_⟩
      intro e
      rw [terminal_weight_sum i hi]
      simpa [hneq,Ne.symm hneq,Nat.add_assoc] using hNe1 e
    · obtain ⟨N,hNs,hNt,hNe⟩ := B.sizeTwo_dispatch_avoiding A i D f hf words added h
        (fun r s he => (howner _ _).mp he) k (havoid k hk0 hk1)
      refine ⟨N,hNs,by simpa [hk0,hk1] using hNt,?_⟩
      intro e
      rw [terminal_weight_sum i hi]
      simpa [hk0,hk1,Ne.symm hk0,Ne.symm hk1] using hNe e
  exact ⟨hne0,hne1,fun k => Classical.choose (perCarrier k),fun k => Classical.choose_spec (perCarrier k)⟩

end Gallai.WholeBowtie
