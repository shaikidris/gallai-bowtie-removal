/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.EvenSubgraph
import Gallai.Structure.OrderParity

/-! # Single even triangle graphs

The literal Botler--Sambinelli definition: the induced even graph is a triangle,
and every odd vertex has at least two even neighbours. No path budget is assumed.
-/

namespace Gallai

open scoped Finset

universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Single even triangle graph, expressed without choosing triangle labels. -/
structure IsSET : Prop where
  /-- The even vertex set has exactly three vertices. -/
  card_even : #{v : V | Even (G.degree v)} = 3
  /-- Every two distinct even vertices are adjacent. -/
  even_clique : ∀ a b, Even (G.degree a) → Even (G.degree b) → a ≠ b → G.Adj a b
  /-- Every odd vertex has at least two even neighbours. -/
  odd_neighbors : ∀ v, Odd (G.degree v) → 2 ≤ eDegree G v

variable {G}

/-- Every SET graph has odd order by the handshaking identity. -/
theorem IsSET.odd_order (h : IsSET G) : Odd (Fintype.card V) :=
  odd_order_of_three_even_vertices G h.card_even

variable [DecidableEq V]

/-- An even SET vertex is adjacent to exactly the other two even vertices. -/
theorem IsSET.evenNeighbors_eq_erase (h : IsSET G) (u : V) (hu : Even (G.degree u)) :
    evenNeighbors G u = (Finset.univ.filter fun v => Even (G.degree v)).erase u := by
  ext v
  simp only [mem_evenNeighbors, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨ha, he⟩
    exact ⟨ha.ne.symm, he⟩
  · rintro ⟨hne, he⟩
    exact ⟨h.even_clique u v hu he hne.symm, he⟩

/-- The E-degree of every even SET vertex is exactly two. -/
theorem IsSET.eDegree_even (h : IsSET G) (u : V) (hu : Even (G.degree u)) :
    eDegree G u = 2 := by
  unfold eDegree
  rw [h.evenNeighbors_eq_erase u hu, Finset.card_erase_of_mem (by simp [hu]), h.card_even]

omit [DecidableEq V] in
/-- Every vertex has at most three even neighbours. -/
theorem IsSET.eDegree_le_three (h : IsSET G) (u : V) : eDegree G u ≤ 3 := by
  have hs : evenNeighbors G u ⊆ Finset.univ.filter fun v => Even (G.degree v) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, ((mem_evenNeighbors u v).mp hv).2⟩
  exact (Finset.card_le_card hs).trans_eq h.card_even

/-- The designated even-neighbour star always has two or three spokes. -/
theorem IsSET.eDegree_two_or_three (h : IsSET G) (u : V) :
    eDegree G u = 2 ∨ eDegree G u = 3 := by
  have hupper := h.eDegree_le_three u
  by_cases he : Even (G.degree u)
  · exact Or.inl (h.eDegree_even u he)
  · have hlower := h.odd_neighbors u (Nat.not_even_iff_odd.mp he)
    omega

/-- No vertex of a SET graph is isolated or a leaf. -/
theorem IsSET.two_le_degree (h : IsSET G) (u : V) : 2 ≤ G.degree u := by
  have hl := eDegree_le_degree (G := G) u
  rcases h.eDegree_two_or_three u with he | he <;> omega

/-- A three-spoke even-neighbour star can only be centred at an odd vertex. -/
theorem IsSET.odd_of_eDegree_three (h : IsSET G) (u : V) (hu : eDegree G u = 3) :
    Odd (G.degree u) := by
  apply Nat.not_even_iff_odd.mp
  intro he
  have hd := h.eDegree_even u he
  omega

end Gallai
