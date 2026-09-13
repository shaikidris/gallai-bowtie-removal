/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarOrientation

/-! # Incidence-state symmetry of completed-star targets

Core rows use the verifier's new-to-old convention. The corresponding vertex
action is its inverse. Anchor permutations act old-to-new on bit positions.
-/

namespace Gallai.Certificate.CompletedStar

open Star.Vertex

/-- The eight new-row to old-row permutations, in verifier order. -/
def coreRowMap (k : Fin 8) : Fin 5 → Fin 5 :=
  ![![0, 1, 2, 3, 4], ![0, 1, 2, 4, 3], ![0, 2, 1, 3, 4], ![0, 2, 1, 4, 3],
    ![0, 3, 4, 1, 2], ![0, 4, 3, 1, 2], ![0, 3, 4, 2, 1], ![0, 4, 3, 2, 1]] k

/-- Actions five and six have order four and are mutual inverses. -/
def coreInverse (k : Fin 8) : Fin 8 := ![0, 1, 2, 3, 4, 6, 5, 7] k

private theorem coreRow_left (k : Fin 8) (i : Fin 5) :
    coreRowMap (coreInverse k) (coreRowMap k i) = i := by revert k i; decide

private theorem coreRow_right (k : Fin 8) (i : Fin 5) :
    coreRowMap k (coreRowMap (coreInverse k) i) = i := by revert k i; decide

/-- The row-index equivalence, whose inverse acts on vertices. -/
def coreRowEquiv (k : Fin 8) : Equiv.Perm (Fin 5) where
  toFun := coreRowMap k
  invFun := coreRowMap (coreInverse k)
  left_inv := coreRow_left k
  right_inv := coreRow_right k

/-- The core vertex action is inverse to the row lookup. -/
def permuteCore (k : Fin 8) : Star.Vertex → Star.Vertex
  | x => core (coreRowMap (coreInverse k) 0)
  | a => core (coreRowMap (coreInverse k) 1)
  | b => core (coreRowMap (coreInverse k) 2)
  | c => core (coreRowMap (coreInverse k) 3)
  | d => core (coreRowMap (coreInverse k) 4)
  | p => p
  | q => q
  | r => r
  | s => s

/-- Core action on all nine labels, fixing the four anchors. -/
def coreEquiv (k : Fin 8) : Equiv.Perm Star.Vertex where
  toFun := permuteCore k
  invFun := permuteCore (coreInverse k)
  left_inv v := by cases v <;> revert k <;> decide
  right_inv v := by cases v <;> revert k <;> decide

theorem coreEquiv_core (k : Fin 8) (i : Fin 5) :
    coreEquiv k (core i) = core ((coreRowEquiv k).symm i) := by
  fin_cases i <;> rfl

theorem coreEquiv_anchor (k : Fin 8) (j : Fin 4) :
    coreEquiv k (anchor j) = anchor j := by fin_cases j <;> rfl

theorem coreEquiv_edges (k : Fin 8) :
    coreEdges.map (coreEquiv k).toEmbedding.sym2Map = coreEdges := by revert k; decide

/-- Reindex the original incidence rows without changing anchor bits. -/
def coreState (k : Fin 8) (state : State) : State := fun i => state (coreRowMap k i)

/-- A computable bit permutation; its output bit at j is the old bit at the inverse image. -/
def permuteMask (σ : Equiv.Perm (Fin 4)) (m : Fin 16) : Fin 16 :=
  (if m.val.testBit (σ.symm 0).val then 1 else 0) +
  (if m.val.testBit (σ.symm 1).val then 2 else 0) +
  (if m.val.testBit (σ.symm 2).val then 4 else 0) +
  (if m.val.testBit (σ.symm 3).val then 8 else 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact bit semantics, for all 24 permutations and all 16 masks. -/
theorem permuteMask_bit (σ : Equiv.Perm (Fin 4)) (m : Fin 16) (j : Fin 4) :
    (permuteMask σ m).val.testBit j.val = m.val.testBit (σ.symm j).val := by
  revert σ m j
  decide

/-- Relabel anchor columns after any selected core row reindexing. -/
def anchorState (σ : Equiv.Perm (Fin 4)) (state : State) : State :=
  fun i => permuteMask σ (state i)

/-- Combined row action, matching the original finite verifier's convention. -/
def transformedState (k : Fin 8) (σ : Equiv.Perm (Fin 4)) (state : State) : State :=
  anchorState σ (coreState k state)

/-- Exact target-edge transport from the row and label actions. No state
parity or catalogue membership is needed for this structural identity. -/
theorem targetEdges_equivariant (state state' : State) (f : Equiv.Perm Star.Vertex)
    (ρ : Equiv.Perm (Fin 5)) (τ : Equiv.Perm (Fin 4))
    (hc : coreEdges.map f.toEmbedding.sym2Map = coreEdges)
    (hrow : ∀ i, f (core i) = core (ρ i))
    (ha : ∀ j, f (anchor j) = anchor (τ j))
    (hb : ∀ i j, (state' (ρ i)).val.testBit (τ j).val = (state i).val.testBit j.val) :
    (targetEdges state).map f.toEmbedding.sym2Map = targetEdges state' := by
  have he (i : Fin 5) (j : Fin 4) :
      f.toEmbedding.sym2Map s(core i, anchor j) = s(core (ρ i), anchor (τ j)) := by
    change s(f (core i), f (anchor j)) = _
    rw [hrow, ha]
  ext e
  constructor
  · intro h
    obtain ⟨old, ho, rfl⟩ := Finset.mem_map.mp h
    rcases (mem_targetEdges state old).mp ho with ho | ⟨i, j, hij, rfl⟩
    · apply (mem_targetEdges state' _).mpr
      left
      rw [← hc]
      exact Finset.mem_map.mpr ⟨old, ho, rfl⟩
    · exact (mem_targetEdges state' _).mpr
        (Or.inr ⟨ρ i, τ j, (hb i j).trans hij, (he i j).symm⟩)
  · intro h
    rcases (mem_targetEdges state' e).mp h with hc' | ⟨i, j, hij, rfl⟩
    · rw [← hc] at hc'
      obtain ⟨old, ho, heq⟩ := Finset.mem_map.mp hc'
      exact Finset.mem_map.mpr ⟨old, (mem_targetEdges state old).mpr (Or.inl ho), heq⟩
    · refine Finset.mem_map.mpr ⟨s(core (ρ.symm i), anchor (τ.symm j)), ?_, ?_⟩
      · apply (mem_targetEdges state _).mpr
        right
        refine ⟨ρ.symm i, τ.symm j, ?_, rfl⟩
        have ht := hb (ρ.symm i) (τ.symm j)
        simp only [Equiv.apply_symm_apply] at ht
        exact ht.symm.trans hij
      · simpa only [Equiv.apply_symm_apply] using he (ρ.symm i) (τ.symm j)

/-- Core row reindexing is exactly inverse core vertex relabelling. -/
theorem coreState_target (k : Fin 8) (state : State) :
    (targetEdges state).map (coreEquiv k).toEmbedding.sym2Map =
      targetEdges (coreState k state) := by
  apply targetEdges_equivariant state (coreState k state) (coreEquiv k)
    (coreRowEquiv k).symm (Equiv.refl _) (coreEquiv_edges k)
    (coreEquiv_core k) (coreEquiv_anchor k)
  intro i j
  change (state (coreRowMap k (coreRowMap (coreInverse k) i))).val.testBit j.val = _
  rw [coreRow_right]

/-- Anchor bit permutation and anchor vertex relabelling have the same target. -/
theorem anchorState_target (σ : Equiv.Perm (Fin 4)) (state : State) :
    (targetEdges state).map (anchorEquiv σ).toEmbedding.sym2Map =
      targetEdges (anchorState σ state) := by
  have hc : coreEdges.map (anchorEquiv σ).toEmbedding.sym2Map = coreEdges := by
    revert σ
    decide
  have hr (i : Fin 5) : anchorEquiv σ (core i) = core i := by fin_cases i <;> rfl
  apply targetEdges_equivariant state (anchorState σ state) (anchorEquiv σ)
    (Equiv.refl _) σ hc hr (permuteAnchor_anchor σ)
  intro i j
  change (permuteMask σ (state i)).val.testBit (σ j).val = _
  rw [permuteMask_bit, Equiv.symm_apply_apply]

private theorem coreEquiv_roles (k : Fin 8) (i : Fin 10) :
    (roles i).map (fun role => (role.1.map (coreEquiv k), role.2.image (coreEquiv k))) =
      roles i := by revert k i; decide

private theorem coreEquiv_anchors (k : Fin 8) :
    Star.anchors.toFinset.image (coreEquiv k) = Star.anchors.toFinset := by revert k; decide

private theorem core_count_pullback (k : Fin 8) (i : Fin 10) :
    (fun v => (boundaries i).flatten.count ((coreEquiv k).symm v)) =
      (fun v => (boundaries i).flatten.count v) := by
  funext v
  cases v <;> revert k i <;> decide

/-- Core symmetry preserves each canonical interface without normalization. -/
theorem AcceptedRecord.core_map {state : State} {i : Fin 10}
    {repl added : List (List Star.Vertex)} (h : AcceptedRecord state i repl added)
    (k : Fin 8) :
    AcceptedRecord (coreState k state) i
      (repl.map (List.map (coreEquiv k))) (added.map (List.map (coreEquiv k))) := by
  have hm := h.map (coreEquiv k)
  simpa only [AcceptedRecord, coreState_target, coreEquiv_roles,
    coreEquiv_anchors, core_count_pullback] using hm

/-- Every checked source interface gives every transformed-state interface,
with no target-edge correspondence or compatibility premise left to supply. -/
theorem transformed_records (k : Fin 8) (σ : Equiv.Perm (Fin 4)) (state : State)
    (h : ∀ i : Fin 10, ∃ repl added, AcceptedRecord state i repl added) (j : Fin 10) :
    ∃ repl added, AcceptedRecord (transformedState k σ state) j repl added := by
  have hc (i : Fin 10) : ∃ repl added, AcceptedRecord (coreState k state) i repl added := by
    obtain ⟨repl, added, hr⟩ := h i
    exact ⟨_, _, hr.core_map k⟩
  obtain ⟨repl, added, hr⟩ := anchor_normalized_records σ (coreState k state) hc j
  exact ⟨repl, added, by
    simpa only [AcceptedRecord, transformedState, anchorState_target] using hr⟩

end Gallai.Certificate.CompletedStar
