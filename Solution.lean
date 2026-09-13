/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.TheoremA
import Gallai.Expansion.Main
import Gallai.TheoremC
import Gallai.Corollaries
import Gallai.CounterexampleBoundary

/-! # Exact proved counterparts to the six Challenge statements -/
namespace Gallai.Palomar
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Theorem A. A whole bowtie with one other possible E-degree exception is
removable under any of the four displayed alternatives. The other exception
is exposed twice; at odd order the same witness exposes the centre twice. -/
theorem theoremA (B : WholeBowtie G) (hc : G.Connected) (y : V)
    (hyout : y ∉ B.vertices) (hy : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y → eDegree G v ≤ 3)
    (hcase : B.anchors.card ≤ 4 ∨ B.activity ≤ 2 ∨
      (∃ w ∈ B.row 0, ∀ v, G.Adj w v → Even (G.degree v) → v = B.label 0 ∨ v = y) ∨
      Odd (Fintype.card V)) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount y ∧
      (Odd (Fintype.card V) → 2 ≤ P.endpointCount (B.label 0)) := by
  exact B.theoremA hc y hyout hy hcap hcase

/-- Theorem B. Every decomposition lifts after expansion at a degree-four hub
with exactly two additional paths and the full displayed endpoint profile. -/
theorem expansion (D : Decomposition G) (x : V) (hd : G.degree x = 4) :
    ∃ E : Decomposition (Star.expansion G x), E.size = D.size + 2 ∧
      (∀ v, v ≠ x → E.endpointCount (Sum.inl v) = D.endpointCount v) ∧
      (D.endpointCount x = 0 → E.endpointCount (Sum.inl x) = 0) ∧
      (D.endpointCount x = 2 → E.endpointCount (Sum.inl x) = 2) ∧
      (D.endpointCount x = 4 → E.endpointCount (Sum.inl x) = 0) := by
  exact Star.fullIncidence_expansion D x hd

/-- Sharpness: the four-leaf star needs two paths, and its expansion needs four. -/
theorem expansionSharp :
    pathNumber (SimpleGraph.starGraph (0 : Fin 5)) = 2 ∧
      pathNumber (Star.expansion (SimpleGraph.starGraph (0 : Fin 5)) 0) = 4 := by
  exact Star.fullIncidence_expansion_sharp

/-- Theorem C. Any finite family of disjoint supported whole bowties can be
removed jointly. Shared anchors are allowed. One optional original even vertex
outside the family can be exposed twice on the resulting bounded witness. -/
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
      ∀ y ∈ designated, 2 ≤ D.endpointCount y := by
  exact Gallai.theoremC hc t Bs designated hd hs hy hcap

/-- Corollary A1. With at most four odd vertices in the two-bowtie kernel,
either prescribed centre can be exposed twice. Witnesses may differ. -/
theorem corollaryA1 {X Y : WholeBowtie G} (hc : G.Connected)
    (h : TwoBowtie.Kernel X Y) (ho : (TwoBowtie.oddVertices G).card ≤ 4) :
    ∀ z ∈ ({X.label 0, Y.label 0} : Finset V),
      ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
        2 ≤ D.endpointCount z := by
  exact TwoBowtie.corollaryA1 hc h ho

/-- Corollary A2. A counterexample within the two-bowtie kernel must have five
anchors at each bowtie, six odd vertices and order at least sixteen. At order
sixteen there are no other even vertices and at least four shared anchors. -/
theorem corollaryA2 {X Y : WholeBowtie G} (hc : G.Connected)
    (h : TwoBowtie.Kernel X Y)
    (hn : ¬ ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2) :
    5 ≤ X.anchors.card ∧ 5 ≤ Y.anchors.card ∧
    6 ≤ (TwoBowtie.oddVertices G).card ∧ 16 ≤ Fintype.card V ∧
    (Fintype.card V = 16 →
      (∀ v, Even (G.degree v) → v ∈ X.vertices ∪ Y.vertices) ∧
      4 ≤ (X.anchors ∩ Y.anchors).card) := by
  exact TwoBowtie.corollaryA2 hc h hn
end Gallai.Palomar
