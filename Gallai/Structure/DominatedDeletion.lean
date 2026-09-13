/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Connected deletion dominated by a retained hub

Collapse every deleted vertex onto one retained hub. Edges either collapse
or remain adjacent when every surviving neighbour of a deleted vertex is
the hub or a neighbour of the hub. Mapping walks then proves connectivity
of the actual induced auxiliary, without a connected-deletion hypothesis.
-/

namespace Gallai

variable {V : Type*} (G : SimpleGraph V)

/-- Delete any hub-dominated set while preserving connectivity on survivors. -/
theorem connected_induce_of_deleted_dominated (S : Set V) (x : V) (hx : x ∈ S)
    (hc : G.Connected)
    (hd : ∀ u, u ∉ S → ∀ v, v ∈ S → G.Adj u v → v = x ∨ G.Adj x v) :
    (G.induce S).Connected := by
  classical
  let H := G.induce S
  let f : V → S := fun v => if h : v ∈ S then ⟨v, h⟩ else ⟨x, hx⟩
  have edge {u v : V} (h : G.Adj u v) : H.Reachable (f u) (f v) := by
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · simp only [f, dif_pos hu, dif_pos hv]
      exact (show H.Adj ⟨u, hu⟩ ⟨v, hv⟩ from h).reachable
    · simp only [f, dif_pos hu, dif_neg hv]
      rcases hd v hv u hu h.symm with hux | hxu
      · subst u
        exact SimpleGraph.Reachable.refl _
      · exact (show H.Adj ⟨u, hu⟩ ⟨x, hx⟩ from hxu.symm).reachable
    · simp only [f, dif_neg hu, dif_pos hv]
      rcases hd u hu v hv h with hvx | hxv
      · subst v
        exact SimpleGraph.Reachable.refl _
      · exact (show H.Adj ⟨x, hx⟩ ⟨v, hv⟩ from hxv).reachable
    · simp only [f, dif_neg hu, dif_neg hv]
      exact SimpleGraph.Reachable.refl _
  have mapped {u v : V} (p : G.Walk u v) : H.Reachable (f u) (f v) := by
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons h p ih => exact (edge h).trans ih
  have : Nonempty S := ⟨⟨x, hx⟩⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨p⟩ := hc.preconnected u.val v.val
  simpa only [f, dif_pos u.property, dif_pos v.property] using mapped p

end Gallai
