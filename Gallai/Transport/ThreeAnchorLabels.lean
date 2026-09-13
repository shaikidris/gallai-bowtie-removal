/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorSynthetic
import Gallai.Structure.PunctureComponents
import Mathlib.Tactic.FinCases

/-! # Interpret three-anchor symbols without adding graph vertices

Three distinct retained vertices label the anchor slots. An unused slot is
permitted, but it must still be an existing retained vertex. Existence of the
slots and the actual row-state selection are separate producer obligations.
-/

namespace Gallai.WholeBowtie

open Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Interpret the five core and three retained symbols in the original graph. -/
def threeLabel (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) : Vertex → V :=
  ![B.label 0, B.label 1, B.label 2, B.label 3, B.label 4,
    (A 0).val, (A 1).val, (A 2).val]

theorem threeLabel_core (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 5) :
    B.threeLabel A (i.castAdd 3) = B.label i := by fin_cases i <;> rfl

theorem threeLabel_anchor (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (j : Fin 3) :
    B.threeLabel A (anchor j) = (A j).val := by fin_cases j <;> rfl

/-- Symbolic distinctness is preserved even when a slot is unused in the rows. -/
theorem threeLabel_injective (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) :
    Function.Injective (B.threeLabel A) := by
  have hc := B.label.injective
  have ha := Subtype.val_injective.comp A.injective
  have hs (i : Fin 5) (j : Fin 3) : B.label i ≠ (A j).val := by
    intro h
    apply (A j).property
    rw [← h]
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
  intro v w h
  fin_cases v <;> fin_cases w <;> simp only [threeLabel, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons] at h
  all_goals first
    | rfl
    | exact False.elim (hs _ _ h)
    | exact False.elim (hs _ _ h.symm)
    | exact False.elim (by have he := hc h; omega)
    | exact False.elim (by have he := ha h; omega)

/-- Every internal core symbol maps to a deleted vertex. -/
theorem threeLabel_fresh (A : Fin 3 ↪ {v : V // v ∉ B.vertices})
    (v : Vertex) (hv : v.val < 5) : B.threeLabel A v ∈ B.vertices := by
  have he : (⟨v.val, hv⟩ : Fin 5).castAdd 3 = v := rfl
  rw [← he, B.threeLabel_core]
  exact Finset.mem_map.mpr ⟨_, Finset.mem_univ _, rfl⟩

/-- Incidence-row interpretation supplies every original local edge of a record. -/
theorem threeLabel_target_edge (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
    (hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true →
      (A j).val ∈ B.row i) (e : Sym2 Vertex) (he : e ∈ targetEdges s) :
    Sym2.map (B.threeLabel A) e ∈ G.edgeSet := by
  rw [targetEdges, Finset.mem_union] at he
  rcases he with he | he
  · have hex : ∀ e : Sym2 Vertex,
        e ∈ ({s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(0, 4), s(3, 4)} : Finset _) →
        ∃ i j : Fin 5, bowtieGraph.Adj i j ∧ s(i.castAdd 3, j.castAdd 3) = e := by
      decide
    obtain ⟨i, j, hij, rfl⟩ := hex e he
    change G.Adj (B.threeLabel A (i.castAdd 3)) (B.threeLabel A (j.castAdd 3))
    rw [B.threeLabel_core, B.threeLabel_core]
    exact (B.adj_iff i j).mpr hij
  · obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp he
    have hbit := (Finset.mem_filter.mp hij).2
    change G.Adj (B.threeLabel A (i.castAdd 3)) (B.threeLabel A (anchor j))
    rw [B.threeLabel_core, B.threeLabel_anchor]
    exact ((B.mem_row i _).mp (hrow i j hbit)).1

end Gallai.WholeBowtie
