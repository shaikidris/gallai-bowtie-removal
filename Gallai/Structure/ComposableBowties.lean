/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.Syndrome
import Gallai.Structure.LowActivity
import Gallai.Foundations.Endpoints

/-! # The literal family interface for Theorem C

These predicates describe the input class, not a proof of composition.
Bowtie vertices are disjoint; their external odd anchors may overlap.
The optional designated vertex belongs to the residual even graph.
-/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Precisely the local classes supported by the manuscript composition proof. -/
def Supported (B : WholeBowtie G) : Prop :=
  B.activity ≤ 2 ∨ B.anchors.card ≤ 3 ∨
    (B.anchors.card = 4 ∧ (B.syndrome = ∅ ∨ B.syndrome = B.anchors))

/-- Complete family hypotheses; no disjointness of anchor sets is required. -/
def Admissible {t : ℕ} (Bs : Fin t → WholeBowtie G) (designated : Option V) : Prop :=
  (∀ i j, i ≠ j → Disjoint (Bs i).vertices (Bs j).vertices) ∧
  (∀ i, Supported (Bs i)) ∧
  (∀ y ∈ designated, Even (G.degree y) ∧ 0 < G.degree y ∧
    ∀ i, y ∉ (Bs i).vertices) ∧
  (∀ v, Even (G.degree v) → (∀ i, v ∉ (Bs i).vertices) →
    (∀ y ∈ designated, v ≠ y) → eDegree G v ≤ 3)

/-- The same decomposition carries the ceiling budget and optional exposure. -/
def Conclusion (G : SimpleGraph V) (designated : Option V) : Prop :=
  ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
    ∀ y ∈ designated, 2 ≤ D.endpointCount y

omit [DecidableRel G.Adj] in
/-- Without designation the conclusion is the bare ceiling budget. -/
theorem conclusion_none : Conclusion G none ↔
    ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 := by
  simp [Conclusion]

omit [DecidableRel G.Adj] in
/-- Designation requires exposure on the same budget witness. -/
theorem conclusion_some (y : V) : Conclusion G (some y) ↔
    ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount y := by
  simp [Conclusion]

/-- The empty undesignated family reduces exactly to the subcubic E-degree cap. -/
theorem admissible_empty_none (Bs : Fin 0 → WholeBowtie G) :
    Admissible Bs none ↔ ∀ v, Even (G.degree v) → eDegree G v ≤ 3 := by
  simp [Admissible]

/-- The designated base retains the positive-degree endpoint-theorem hypothesis. -/
theorem admissible_empty_some (Bs : Fin 0 → WholeBowtie G) (y : V) :
    Admissible Bs (some y) ↔
      (Even (G.degree y) ∧ 0 < G.degree y) ∧
      (∀ v, Even (G.degree v) → v ≠ y → eDegree G v ≤ 3) := by
  simp [Admissible]

/-- A high-activity four-anchor input is supported exactly for empty/full syndrome. -/
theorem supported_four (B : WholeBowtie G) (ha : 3 ≤ B.activity)
    (hA : B.anchors.card = 4) :
    Supported B ↔ B.syndrome = ∅ ∨ B.syndrome = B.anchors := by
  have hlow : ¬ B.activity ≤ 2 := by omega
  simp [Supported, hlow, hA]

end Gallai.Composition
