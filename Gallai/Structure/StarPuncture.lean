/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.OddHubReserve

/-! # Exact degree changes after deleting a star -/

namespace Gallai

open scoped Finset

universe u
variable {V : Type u} [DecidableEq V]

/-- Away from the centre, a star edge joins a selected leaf to that centre. -/
theorem star_sup_adj_off_center (u : V) (B : Finset V) (v w : V) (hv : v ≠ u) :
    (B.sup (SimpleGraph.edge u)).Adj v w ↔ v ∈ B ∧ w = u := by
  induction B using Finset.induction with
  | empty => simp
  | @insert b B hb ih =>
    rw [Finset.sup_insert, SimpleGraph.sup_adj, ih]
    by_cases hw : w = u
    · subst w
      simp [SimpleGraph.edge_adj, hv]
    · simp [SimpleGraph.edge_adj, hv, hw]

/-- Delete exactly the selected hub spokes without deleting vertices. -/
abbrev starPuncture (G : SimpleGraph V) (u : V) (B : Finset V) : SimpleGraph V :=
  G \ B.sup (SimpleGraph.edge u)

/-- Every selected spoke is absent in the puncture. -/
theorem starPuncture_missing (G : SimpleGraph V) (u : V) (B : Finset V)
    (hu : u ∉ B) (v : V) (hv : v ∈ B) : ¬ (starPuncture G u B).Adj u v := by
  simp [starPuncture, SimpleGraph.sdiff_adj, star_sup_adj_center u B hu, hv]

omit [DecidableEq V] in
/-- Restoring a genuine deleted star recovers exactly the original graph. -/
theorem starPuncture_restore (G : SimpleGraph V) (u : V) (B : Finset V)
    (hb : ∀ v ∈ B, G.Adj u v) :
    starPuncture G u B ⊔ B.sup (SimpleGraph.edge u) = G := by
  have hs : B.sup (SimpleGraph.edge u) ≤ G := by
    apply Finset.sup_le
    intro v hv a b ha
    rw [SimpleGraph.edge_adj] at ha
    rcases ha.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hb _ hv
    · exact (hb _ hv).symm
  ext v w
  simp only [SimpleGraph.sup_adj, starPuncture, SimpleGraph.sdiff_adj]
  constructor
  · rintro (h | h)
    · exact h.1
    · exact hs h
  · intro h
    by_cases ha : (B.sup (SimpleGraph.edge u)).Adj v w
    · exact Or.inr ha
    · exact Or.inl ⟨h, ha⟩

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Local adjacency decision for finite puncture degree calculations. -/
noncomputable local instance starPunctureDecidableAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _

/-- At the hub, the selected neighbour set is removed exactly. -/
theorem starPuncture_neighbors_center (u : V) (B : Finset V) (hu : u ∉ B) :
    (starPuncture G u B).neighborFinset u = G.neighborFinset u \ B := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, starPuncture, SimpleGraph.sdiff_adj,
    star_sup_adj_center u B hu, Finset.mem_sdiff]

/-- At a selected leaf, the only lost neighbour is the hub. -/
theorem starPuncture_neighbors_leaf (u : V) (B : Finset V) (v : V)
    (hv : v ≠ u) (hb : v ∈ B) :
    (starPuncture G u B).neighborFinset v = (G.neighborFinset v).erase u := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, starPuncture, SimpleGraph.sdiff_adj,
    star_sup_adj_off_center u B v w hv, hb, true_and, Finset.mem_erase]
  tauto

/-- Every unselected nonhub keeps exactly its old neighbours. -/
theorem starPuncture_neighbors_other (u : V) (B : Finset V) (v : V)
    (hv : v ≠ u) (hb : v ∉ B) :
    (starPuncture G u B).neighborFinset v = G.neighborFinset v := by
  ext w
  simp [starPuncture, SimpleGraph.sdiff_adj, star_sup_adj_off_center u B v w hv, hb]

/-- Hub degree accounting for a genuine deleted star. -/
theorem starPuncture_degree_center (u : V) (B : Finset V) (hu : u ∉ B)
    (hb : B ⊆ G.neighborFinset u) :
    (starPuncture G u B).degree u + #B = G.degree u := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, starPuncture_neighbors_center G u B hu,
    Finset.card_sdiff_add_card_eq_card hb, SimpleGraph.card_neighborFinset_eq_degree]

/-- A selected genuine leaf loses exactly one incident edge. -/
theorem starPuncture_degree_leaf (u : V) (B : Finset V) (v : V)
    (hv : v ∈ B) (ha : G.Adj u v) :
    (starPuncture G u B).degree v + 1 = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    starPuncture_neighbors_leaf G u B v ha.ne.symm hv]
  simpa using Finset.card_erase_add_one ((G.mem_neighborFinset v u).mpr ha.symm)

/-- Every other nonhub keeps its degree. -/
theorem starPuncture_degree_other (u : V) (B : Finset V) (v : V)
    (hv : v ≠ u) (hb : v ∉ B) : (starPuncture G u B).degree v = G.degree v := by
  simpa using congrArg Finset.card (starPuncture_neighbors_other G u B v hv hb)

end Gallai
