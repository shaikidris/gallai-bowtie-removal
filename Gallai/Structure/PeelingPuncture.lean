/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.EdgeDeletion
import Gallai.Structure.EvenSubgraph
import Lean.Elab.Tactic.Omega

/-! # Parity and even-neighbour bounds for odd-neighbour peeling

Only the deleted edge's ends change parity. Connectivity is not assumed:
the same local facts apply to both the connected and bridge branches.
-/

namespace Gallai

open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Removing an even--odd edge makes its first end odd and its second even.
Away from the second end, no newly even vertex is created. -/
theorem odd_neighbor_peeling_parity (x w : V) (hxw : G.Adj x w)
    (hx : Even (G.degree x)) (hw : Odd (G.degree w)) :
    let H := G.deleteEdges {s(x, w)}
    Odd (H.degree x) ∧ Even (H.degree w) ∧
      ∀ v, v ≠ w → Even (H.degree v) → Even (G.degree v) := by
  have hdx := degree_delete_edge_add_one G x w hxw
  have hdw := degree_delete_edge_add_one G w x hxw.symm
  rw [Sym2.eq_swap] at hdw
  have hx' : Odd ((G.deleteEdges {s(x, w)}).degree x) := by
    rw [Nat.even_iff] at hx
    rw [Nat.odd_iff]
    omega
  have hw' : Even ((G.deleteEdges {s(x, w)}).degree w) := by
    rw [Nat.odd_iff] at hw
    rw [Nat.even_iff]
    omega
  refine ⟨hx', hw', ?_⟩
  intro v hvw hv
  have hvx : v ≠ x := by
    intro h
    subst v
    exact Nat.not_even_iff_odd.mpr hx' hv
  rwa [degree_delete_edge_of_ne G x w v hvx hvw] at hv

/-- Every remaining neighbour of the peeled vertex, except the other named
exception, is still odd. This requires no degree or connectivity assumption. -/
theorem odd_neighbor_peeling_neighbors (x y w : V)
    (hcontact : ∀ v, G.Adj w v → Even (G.degree v) → v = x ∨ v = y) :
    ∀ v, (G.deleteEdges {s(x, w)}).Adj w v → v ≠ y →
      Odd ((G.deleteEdges {s(x, w)}).degree v) := by
  intro v ha hvy
  have hvw : v ≠ w := ha.ne.symm
  have hvx : v ≠ x := by
    rintro rfl
    exact (SimpleGraph.deleteEdges_adj.mp ha).2 (by simp [Sym2.eq_swap])
  rw [degree_delete_edge_of_ne G x w v hvx hvw]
  exact Nat.not_even_iff_odd.mp (fun he =>
    (hcontact v (SimpleGraph.deleteEdges_adj.mp ha).1 he).elim hvx hvy)

/-- Peeling creates at most one even neighbour at the peeled vertex and does
not increase any other relevant E-degree. Only y remains exceptional. -/
theorem odd_neighbor_peeling_cap (x y w : V) (hxw : G.Adj x w)
    (hx : Even (G.degree x)) (hw : Odd (G.degree w))
    (hcontact : ∀ v, G.Adj w v → Even (G.degree v) → v = x ∨ v = y)
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → v ≠ y → eDegree G v ≤ 3) :
    ∀ v, Even ((G.deleteEdges {s(x, w)}).degree v) → v ≠ y →
      eDegree (G.deleteEdges {s(x, w)}) v ≤ 3 := by
  classical
  let H := G.deleteEdges {s(x, w)}
  obtain ⟨hx', _, hold⟩ := odd_neighbor_peeling_parity x w hxw hx hw
  have hn := odd_neighbor_peeling_neighbors x y w hcontact
  intro v hv hvy
  by_cases hvw : v = w
  · subst v
    have hs : evenNeighbors H w ⊆ {y} := by
      intro t ht
      obtain ⟨ha, he⟩ := (mem_evenNeighbors w t).mp ht
      by_cases hty : t = y
      · simp [hty]
      · exact (Nat.not_even_iff_odd.mpr (hn t ha hty) he).elim
    exact (Finset.card_le_card hs).trans (by simp)
  · have hvg : Even (G.degree v) := hold v hvw hv
    have hvx : v ≠ x := by
      rintro rfl
      exact Nat.not_even_iff_odd.mpr hx' hv
    have hs : evenNeighbors H v ⊆ evenNeighbors G v := by
      intro t ht
      obtain ⟨ha, he⟩ := (mem_evenNeighbors v t).mp ht
      have htw : t ≠ w := by
        rintro rfl
        exact (hcontact v (SimpleGraph.deleteEdges_adj.mp ha).1.symm hvg).elim hvx hvy
      exact (mem_evenNeighbors v t).mpr
        ⟨(SimpleGraph.deleteEdges_adj.mp ha).1, hold t htw he⟩
    exact (Finset.card_le_card hs).trans (hcap v hvg hvx hvy)

end Gallai
