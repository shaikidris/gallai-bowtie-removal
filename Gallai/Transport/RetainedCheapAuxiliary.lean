/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedCheapReconstruction

/-! # Remote endpoint supply in the actual cheap retained auxiliaries -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The remote slot is used in every cheap representative, not merely padding. -/
theorem retainedCheap_remote_anchor
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 5)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (Retained.state (Retained.cheapIndex i) j)).val.testBit k.val = true ∧
        (A k).val = v) : (A 2).val ∈ B.anchors := by
  have hused : ∃ j : Fin 5,
      (rowMask (Retained.state (Retained.cheapIndex i) j)).val.testBit 2 = true := by
    fin_cases i <;> decide
  obtain ⟨j,hj⟩ := hused
  exact (B.mem_anchors _).mpr ⟨j,(hrows j _).mpr ⟨2,hj,rfl⟩⟩

/-- Private deletion with its indicated parity repair. Original repair edges
are deleted and synthetic ones inserted; this definition covers both. -/
def retainedCheapAuxiliary
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 5) :
    SimpleGraph B.StarSurvivor :=
  if Retained.repair (Retained.cheapIndex i) then
    B.retainedHubRepair (B.retainedSlot A 1) (B.retainedSlot A 2)
  else B.retainedHubGraph

instance retainedCheapAuxiliaryDecidableAdj
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 5) :
    DecidableRel (B.retainedCheapAuxiliary A i).Adj := by
  unfold retainedCheapAuxiliary
  split <;> infer_instance

/-- The finite syndrome certifies parity restoration at every retained vertex. -/
theorem retainedCheapAuxiliary_even_iff
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 5)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (Retained.state (Retained.cheapIndex i) j)).val.testBit k.val = true ∧
        (A k).val = v)
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (v : B.StarSurvivor) :
    Even ((B.retainedCheapAuxiliary A i).degree v) ↔ Even (G.degree v.val) := by
  classical
  have hs := (Retained.cheapPassing_checked i).2.1
  by_cases hr : Retained.repair (Retained.cheapIndex i) = true
  · simp only [hr, if_true] at hs
    have hne : B.retainedSlot A 1 ≠ B.retainedSlot A 2 := by
      intro he
      have hi : (1 : Fin 3) = 2 := A.injective
        (Subtype.ext (congrArg (fun w : B.StarSurvivor => w.val) he))
      exact (by decide : (1 : Fin 3) ≠ 2) hi
    have hd : (B.retainedCheapAuxiliary A i).degree v =
        (B.retainedHubRepair (B.retainedSlot A 1) (B.retainedSlot A 2)).degree v := by
      apply congrArg Finset.card
      ext w
      simp only [SimpleGraph.mem_neighborFinset]
      simp [retainedCheapAuxiliary, hr]
    rw [hd]
    exact B.retainedHubRepair_even_iff _ _ hne
        (B.threeAnchor_private_pair A _ hrows hA 1 2 hs) v
  · simp only [hr] at hs
    have hd : (B.retainedCheapAuxiliary A i).degree v = B.retainedHubGraph.degree v := by
      apply congrArg Finset.card
      ext w
      simp only [SimpleGraph.mem_neighborFinset]
      simp [retainedCheapAuxiliary, hr]
    rw [hd]
    exact B.retainedHub_even_iff (B.threeAnchor_private_empty A _ hrows hA hs) v

/-- No endpoint-selection premise is needed at the remote anchor: it is odd
in the actual auxiliary and hence exposed in every decomposition. -/
theorem retainedCheapAuxiliary_remote_positive
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 5)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (Retained.state (Retained.cheapIndex i) j)).val.testBit k.val = true ∧
        (A k).val = v)
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (D : Decomposition (B.retainedCheapAuxiliary A i)) :
    0 < D.endpointCount (B.retainedSlot A 2) := by
  classical
  apply D.endpointCount_pos_of_odd_degree
  apply Nat.not_even_iff_odd.mp
  intro he
  have ho := B.odd_degree_anchor (B.retainedCheap_remote_anchor A i hrows)
  exact (Nat.not_even_iff_odd.mpr ho)
    ((B.retainedCheapAuxiliary_even_iff A i hrows hA _).mp he)

end Gallai.WholeBowtie
