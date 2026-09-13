/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStar
import Gallai.Certificates.WordOrientation
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases

/-! # Canonical completed-star interfaces under anchor permutations

All 24 anchor permutations are covered, with a preimage for every target
interface. This is interface coverage, not incidence-state orbit coverage.
-/

namespace Gallai.Certificate.CompletedStar

open Star.Vertex

/-- Relabel anchors while fixing the released hub and private vertices. -/
def permuteAnchor (σ : Equiv.Perm (Fin 4)) : Star.Vertex → Star.Vertex
  | x => x
  | a => a
  | b => b
  | c => c
  | d => d
  | p => anchor (σ 0)
  | q => anchor (σ 1)
  | r => anchor (σ 2)
  | s => anchor (σ 3)

/-- The vertex action agrees with the literal bit-position action. -/
theorem permuteAnchor_anchor (σ : Equiv.Perm (Fin 4)) (j : Fin 4) :
    permuteAnchor σ (anchor j) = anchor (σ j) := by
  fin_cases j <;> rfl

private theorem permuteAnchor_left_inv (σ : Equiv.Perm (Fin 4)) (v : Star.Vertex) :
    permuteAnchor σ.symm (permuteAnchor σ v) = v := by
  cases v with
  | x => rfl
  | a => rfl
  | b => rfl
  | c => rfl
  | d => rfl
  | p =>
    exact (permuteAnchor_anchor σ.symm (σ 0)).trans
      (congrArg anchor (σ.symm_apply_apply 0))
  | q =>
    exact (permuteAnchor_anchor σ.symm (σ 1)).trans
      (congrArg anchor (σ.symm_apply_apply 1))
  | r =>
    exact (permuteAnchor_anchor σ.symm (σ 2)).trans
      (congrArg anchor (σ.symm_apply_apply 2))
  | s =>
    exact (permuteAnchor_anchor σ.symm (σ 3)).trans
      (congrArg anchor (σ.symm_apply_apply 3))

/-- The action is an equivalence, with the inverse anchor permutation. -/
def anchorEquiv (σ : Equiv.Perm (Fin 4)) : Equiv.Perm Star.Vertex where
  toFun := permuteAnchor σ
  invFun := permuteAnchor σ.symm
  left_inv := permuteAnchor_left_inv σ
  right_inv := permuteAnchor_left_inv σ.symm

/-- Expose the action's function without unfolding its inverse proofs. -/
theorem anchorEquiv_coe (σ : Equiv.Perm (Fin 4)) :
    (anchorEquiv σ : Star.Vertex → Star.Vertex) = permuteAnchor σ := rfl

/-- Orient pairs in catalogue order; singleton terminal boundaries are unchanged. -/
def orientBoundary (b : List Star.Vertex) : List Star.Vertex :=
  if b.length = 2 ∧ b ∉ [[p, q], [p, r], [p, s], [q, r], [q, s], [r, s]]
  then b.reverse else b

/-- The normalizer only reverses two-entry boundaries. -/
theorem orientBoundary_spec (b : List Star.Vertex) :
    orientBoundary b = b ∨ (b.length = 2 ∧ orientBoundary b = b.reverse) := by
  unfold orientBoundary
  split_ifs with h
  · exact Or.inr ⟨h.1, rfl⟩
  · exact Or.inl rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every requested canonical interface has a preimage under every anchor permutation. -/
theorem interface_preimage (σ : Equiv.Perm (Fin 4)) (j : Fin 10) :
    ∃ i : Fin 10,
      (((boundaries i).map (List.map (permuteAnchor σ))).map orientBoundary).Perm
        (boundaries j) := by
  revert σ j
  decide

/-- The anchor action preserves exactly the allowed released/private vertices. -/
theorem anchorEquiv_fresh (σ : Equiv.Perm (Fin 4)) :
    Star.fresh.toFinset.image (anchorEquiv σ) = Star.fresh.toFinset := by
  simp [Star.fresh, anchorEquiv, permuteAnchor]

/-- The protected anchor set is invariant under the action. -/
theorem anchorEquiv_anchors (σ : Equiv.Perm (Fin 4)) :
    Star.anchors.toFinset.image (anchorEquiv σ) = Star.anchors.toFinset := by
  revert σ
  decide

/-- The required endpoint vector is independent of interface and anchor names. -/
theorem boundary_count_pullback (σ : Equiv.Perm (Fin 4)) (i j : Fin 10) :
    (fun v => (boundaries i).flatten.count ((anchorEquiv σ).symm v)) =
      (fun v => (boundaries j).flatten.count v) := by
  funext v
  rw [boundary_count, boundary_count]
  have hm : (anchorEquiv σ).symm v ∈ Star.anchors ↔ v ∈ Star.anchors := by
    cases v <;> revert σ <;> decide
  simp only [hm]

/-- All canonical interfaces survive relabelling, with no new compatibility premise.
The edge target is still explicitly relabelled; incidence equivariance is separate. -/
theorem anchor_normalized_records (σ : Equiv.Perm (Fin 4)) (state : State)
    (h : ∀ i : Fin 10, ∃ repl added, AcceptedRecord state i repl added) (j : Fin 10) :
    ∃ repl added,
      RecordAccepted ((targetEdges state).map (anchorEquiv σ).toEmbedding.sym2Map)
        (roles j) repl added 2 Star.anchors.toFinset
        (fun v => (boundaries j).flatten.count v) := by
  obtain ⟨i, hi⟩ := interface_preimage σ j
  obtain ⟨repl, added, hr⟩ := h i
  have hm := hr.map (anchorEquiv σ)
  have hf : Star.fresh.toFinset.image (permuteAnchor σ) = Star.fresh.toFinset := by
    simpa only [anchorEquiv_coe] using anchorEquiv_fresh σ
  have ha : Star.anchors.toFinset.image (permuteAnchor σ) = Star.anchors.toFinset := by
    simpa only [anchorEquiv_coe] using anchorEquiv_anchors σ
  have hm' : RecordAccepted
      ((targetEdges state).map (anchorEquiv σ).toEmbedding.sym2Map)
      (((boundaries i).map (List.map (permuteAnchor σ))).map
        (fun b => (b, Star.fresh.toFinset)))
      (repl.map (List.map (anchorEquiv σ))) (added.map (List.map (anchorEquiv σ)))
      2 Star.anchors.toFinset (fun v => (boundaries j).flatten.count v) := by
    simpa only [roles, List.map_map, Function.comp_def,
      boundary_count_pullback σ i j, anchorEquiv_coe, hf, ha] using hm
  obtain ⟨new, hn⟩ := hm'.normalize_boundaries orientBoundary orientBoundary_spec hi
  exact ⟨new, added.map (List.map (anchorEquiv σ)), hn⟩

end Gallai.Certificate.CompletedStar
