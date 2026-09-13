/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.CompositionInduction

/-! # Manuscript Theorem C: composition of arbitrarily many whole bowties -/
namespace Gallai
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Literal optional-designated form of Theorem C. Shared odd anchors are
allowed; no local induction premise or bound on the family size remains. -/
theorem theoremC (hc : G.Connected) (t : ℕ) (Bs : Fin t → WholeBowtie G)
    (designated : Option V)
    (hd : ∀ i j, i ≠ j → Disjoint (Bs i).vertices (Bs j).vertices)
    (hs : ∀ i, (Bs i).activity ≤ 2 ∨ (Bs i).anchors.card ≤ 3 ∨
      ((Bs i).anchors.card = 4 ∧
        ((Bs i).syndrome = ∅ ∨ (Bs i).syndrome = (Bs i).anchors)))
    (hy : ∀ y ∈ designated, Even (G.degree y) ∧ 0 < G.degree y ∧
      ∀ i, y ∉ (Bs i).vertices)
    (hcap : ∀ v, Even (G.degree v) → (∀ i, v ∉ (Bs i).vertices) →
      (∀ y ∈ designated, v ≠ y) → eDegree G v ≤ 3) :
    ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      ∀ y ∈ designated, 2 ≤ D.endpointCount y :=
  Composition.compose t G Bs designated hc ⟨hd, hs, hy, hcap⟩

end Gallai
