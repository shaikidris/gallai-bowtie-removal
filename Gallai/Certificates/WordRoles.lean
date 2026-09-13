/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.WordFamily

/-! # Local terminal and connector roles

The permitted internal vertices are explicit per role. Their avoidance of
old carrier interiors is a separate ambient-transport obligation.
-/

namespace Gallai.Certificate

variable {V : Type*}

/-- A one-vertex boundary prescribes a terminal tail; a two-vertex boundary
prescribes a connector. Other boundary lengths are not part of this interface. -/
def Compatible (boundary : List V) (allowed : Finset V) (word : List V) : Prop :=
  match boundary with
  | [a] => word.head? = some a ∧ ∀ v ∈ word.tail, v ∈ allowed
  | [a, b] => word.head? = some a ∧ word.getLast? = some b ∧
      ∀ v ∈ word.tail.dropLast, v ∈ allowed
  | _ => False

instance [DecidableEq V] (boundary : List V) (allowed : Finset V) (word : List V) :
    Decidable (Compatible boundary allowed word) := by
  unfold Compatible
  split <;> infer_instance

/-- A terminal role introduces no vertex except its attachment and allowed vertices. -/
theorem compatible_single_support {a v : V} {allowed : Finset V} {word : List V}
    (h : Compatible [a] allowed word) (hv : v ∈ word) : v = a ∨ v ∈ allowed := by
  have hh : word.head? = some a := h.1
  cases word with
  | nil => simp at hv
  | cons u rest =>
    have hu : u = a := Option.some.inj hh
    subst u
    rcases List.mem_cons.mp hv with he | he
    · exact Or.inl he
    · exact Or.inr (h.2 v he)

/-- A connector role introduces no old vertex beyond its two attachments. -/
theorem compatible_pair_support {a b v : V} {allowed : Finset V} {word : List V}
    (h : Compatible [a, b] allowed word) (hv : v ∈ word) :
    v = a ∨ v = b ∨ v ∈ allowed := by
  have hh : word.head? = some a := h.1
  cases word with
  | nil => simp at hv
  | cons u rest =>
    have hu : u = a := Option.some.inj hh
    subst u
    rcases List.mem_cons.mp hv with he | he
    · exact Or.inl he
    · have hn : rest ≠ [] := List.ne_nil_of_mem he
      have hlast : rest.getLast hn = b := by
        have hl := h.2.1
        rw [List.getLast?_cons_of_ne_nil hn, List.getLast?_eq_some_getLast hn] at hl
        exact Option.some.inj hl
      rw [← List.dropLast_concat_getLast hn, List.mem_append, List.mem_singleton] at he
      rcases he with he | he
      · exact Or.inr (Or.inr (h.2.2 v he))
      · exact Or.inr (Or.inl (he.trans hlast))

/-- The permitted terminal support holds for the interpreted simple path itself. -/
theorem Accepted.realize_single_support {edges : Finset (Sym2 V)} {words : List (List V)}
    (h : Accepted edges words) (G : SimpleGraph V) (hG : ∀ e ∈ edges, e ∈ G.edgeSet)
    (i : Fin words.length) (a : V) (allowed : Finset V)
    (hr : Compatible [a] allowed words[i]) (v : V)
    (hv : v ∈ (h.realize G hG i).walk.support) : v = a ∨ v ∈ allowed := by
  rw [h.realize_support] at hv
  exact compatible_single_support hr hv

/-- The permitted connector support holds for the interpreted simple path itself. -/
theorem Accepted.realize_pair_support {edges : Finset (Sym2 V)} {words : List (List V)}
    (h : Accepted edges words) (G : SimpleGraph V) (hG : ∀ e ∈ edges, e ∈ G.edgeSet)
    (i : Fin words.length) (a b : V) (allowed : Finset V)
    (hr : Compatible [a, b] allowed words[i]) (v : V)
    (hv : v ∈ (h.realize G hG i).walk.support) : v = a ∨ v = b ∨ v ∈ allowed := by
  rw [h.realize_support] at hv
  exact compatible_pair_support hr hv

end Gallai.Certificate
