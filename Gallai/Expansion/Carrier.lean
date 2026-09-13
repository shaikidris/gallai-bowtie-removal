/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Expansion.Words
import Gallai.Transport.CarrierSplice

/-!
# Reconstructing a released old carrier

The private vertices are disjoint from all old support. Once the hub is also
absent, a connector whose only old vertices are its attachments and the hub
has exactly the intersection properties required for simple splicing. Old
pieces may be nil; distinct carriers need not have disjoint supports.
-/

namespace Gallai.Star

universe u

variable {V : Type u} {H : SimpleGraph V} {a b c d x : V}

/-- Inclusion into the expanded graph preserves disjoint old supports. -/
theorem old_supports_disjoint (L : H.Walk a b) (R : H.Walk c d)
    (h : L.support.Disjoint R.support) :
    (L.map (oldHom H x)).support.Disjoint (R.map (oldHom H x)).support := by
  intro w hwL hwR
  rw [SimpleGraph.Walk.support_map] at hwL hwR
  rcases List.mem_map.mp hwL with ⟨v, hv, rfl⟩
  rcases List.mem_map.mp hwR with ⟨u, hu, he⟩
  have huv := oldHom_injective H x he
  subst u
  exact h hv hu

/-- A through connector meets the old left piece only at its left attachment. -/
theorem through_left_intersection (L : H.Walk a b) (R : H.Walk c d)
    (M : (expansion H x).Walk (.inl b) (.inl c))
    (hLR : L.support.Disjoint R.support) (hLhub : x ∉ L.support)
    (hMold : ∀ v, Sum.inl v ∈ M.support → v = b ∨ v = c ∨ v = x) :
    ∀ w, w ∈ (L.map (oldHom H x)).support → w ∈ M.support → w = .inl b := by
  intro w hwL hwM
  rw [SimpleGraph.Walk.support_map] at hwL
  rcases List.mem_map.mp hwL with ⟨v, hv, rfl⟩
  rcases hMold v hwM with rfl | rfl | rfl
  · rfl
  · exact False.elim (hLR hv R.start_mem_support)
  · exact False.elim (hLhub hv)

/-- A through connector meets the old right piece only at its right attachment. -/
theorem through_right_intersection (L : H.Walk a b) (R : H.Walk c d)
    (M : (expansion H x).Walk (.inl b) (.inl c))
    (hLR : L.support.Disjoint R.support) (hRhub : x ∉ R.support)
    (hMold : ∀ v, Sum.inl v ∈ M.support → v = b ∨ v = c ∨ v = x) :
    ∀ w, w ∈ M.support → w ∈ (R.map (oldHom H x)).support → w = .inl c := by
  intro w hwM hwR
  rw [SimpleGraph.Walk.support_map] at hwR
  rcases List.mem_map.mp hwR with ⟨v, hv, rfl⟩
  rcases hMold v hwM with rfl | rfl | rfl
  · exact False.elim (hLR L.end_mem_support hv)
  · rfl
  · exact False.elim (hRhub hv)

/-- Reconstruct a through carrier from its released pieces and a fresh connector. -/
def throughCarrier (L : H.Walk a b) (R : H.Walk c d)
    (M : (expansion H x).Walk (.inl b) (.inl c))
    (hL : L.IsPath) (hR : R.IsPath) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hLR : L.support.Disjoint R.support) (hLhub : x ∉ L.support) (hRhub : x ∉ R.support)
    (hMold : ∀ v, Sum.inl v ∈ M.support → v = b ∨ v = c ∨ v = x) :
    NonemptyPath (expansion H x) :=
  NonemptyPath.splice (L.map (oldHom H x)) M (R.map (oldHom H x))
    (hL.map (oldHom_injective H x)) hM (hR.map (oldHom_injective H x)) hne
    (old_supports_disjoint L R hLR) (through_left_intersection L R M hLR hLhub hMold)
    (through_right_intersection L R M hLR hRhub hMold)

/-- A reconstructed through carrier retains exactly its two old pieces and connector edges. -/
theorem throughCarrier_edges (L : H.Walk a b) (R : H.Walk c d)
    (M : (expansion H x).Walk (.inl b) (.inl c))
    (hL : L.IsPath) (hR : R.IsPath) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hLR : L.support.Disjoint R.support) (hLhub : x ∉ L.support) (hRhub : x ∉ R.support)
    (hMold : ∀ v, Sum.inl v ∈ M.support → v = b ∨ v = c ∨ v = x) :
    (throughCarrier L R M hL hR hM hne hLR hLhub hRhub hMold).walk.edges =
      (L.edges.map (Sym2.map (oldHom H x)) ++ M.edges) ++
        R.edges.map (Sym2.map (oldHom H x)) := by
  exact ((SimpleGraph.Walk.edges_append ((L.map (oldHom H x)).append M)
    (R.map (oldHom H x))).trans
      (congrArg (fun es => es ++ (R.map (oldHom H x)).edges)
        (SimpleGraph.Walk.edges_append (L.map (oldHom H x)) M))).trans
    (congrArg₂ (fun es fs => (es ++ M.edges) ++ fs)
      (L.edges_map (oldHom H x)) (R.edges_map (oldHom H x)))

/-- A terminal connector meets its old prefix only at the attachment. -/
theorem terminal_intersection {t : V ⊕ Fin 4} (L : H.Walk a b)
    (M : (expansion H x).Walk (.inl b) t) (hLhub : x ∉ L.support)
    (hMold : ∀ v, Sum.inl v ∈ M.support → v = b ∨ v = x) :
    ∀ w, w ∈ (L.map (oldHom H x)).support → w ∈ M.support → w = .inl b := by
  intro w hwL hwM
  rw [SimpleGraph.Walk.support_map] at hwL
  rcases List.mem_map.mp hwL with ⟨v, hv, rfl⟩
  rcases hMold v hwM with rfl | rfl
  · rfl
  · exact False.elim (hLhub hv)

/-- Reconstruct a terminal carrier, allowing a zero-edge old prefix. -/
def terminalCarrier {t : V ⊕ Fin 4} (L : H.Walk a b)
    (M : (expansion H x).Walk (.inl b) t)
    (hL : L.IsPath) (hM : M.IsPath) (hne : ¬ M.Nil) (hLhub : x ∉ L.support)
    (hMold : ∀ v, Sum.inl v ∈ M.support → v = b ∨ v = x) :
    NonemptyPath (expansion H x) where
  start := .inl a
  finish := t
  walk := (L.map (oldHom H x)).append M
  isPath := isPath_append_of_intersection _ _ (hL.map (oldHom_injective H x)) hM
    (terminal_intersection L M hLhub hMold)
  nonempty := fun hn => hne (SimpleGraph.Walk.nil_append_iff.mp hn).2

/-- A reconstructed terminal carrier retains exactly its prefix and connector edges. -/
theorem terminalCarrier_edges {t : V ⊕ Fin 4} (L : H.Walk a b)
    (M : (expansion H x).Walk (.inl b) t)
    (hL : L.IsPath) (hM : M.IsPath) (hne : ¬ M.Nil) (hLhub : x ∉ L.support)
    (hMold : ∀ v, Sum.inl v ∈ M.support → v = b ∨ v = x) :
    (terminalCarrier L M hL hM hne hLhub hMold).walk.edges =
      L.edges.map (Sym2.map (oldHom H x)) ++ M.edges := by
  exact (SimpleGraph.Walk.edges_append (L.map (oldHom H x)) M).trans
    (congrArg (fun es => es ++ M.edges) (L.edges_map (oldHom H x)))

end Gallai.Star
