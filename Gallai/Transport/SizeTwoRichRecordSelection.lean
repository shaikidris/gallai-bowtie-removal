/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoRichCoverage
import Gallai.Certificates.SizeTwoCatalogueStateAgreement
import Gallai.Structure.ZeroSyndromeRows

/-! # Actual normalized bowties select all one-credit interfaces

The graph's anchor numbering and activity prove the independent boundary
predicate. Representative coverage then selects records for the actual
original incidence rows. No rich-catalogue membership is assumed of the graph.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The high-activity normalized input supplies a checked record for every
through/terminal and r/s reserve interface. Reconstruction remains a consumer. -/
theorem sizeTwo_rich_records (A : B.AnchorNumbering) (ha : 3 ≤ B.activity)
    (o : Fin 234) (hstate : B.completedStarState A = Catalogue.state o) :
    ∃ b : Fin 12, ∃ k : Fin 15,
      Rich.Catalogue.state b k = B.completedStarState A ∧
      ∀ i : Fin 4, if Rich.Catalogue.special b k i then
        Rich.SeparatedAccepted (B.completedStarState A) i
          (Rich.Catalogue.words b k i 0) (Rich.Catalogue.words b k i 1)
          (Rich.Catalogue.added b k i)
      else Rich.AcceptedRecord (B.completedStarState A) i
        (Rich.Catalogue.words b k i) (Rich.Catalogue.added b k i) := by
  have he : B.completedStarState A = Catalogue.Rows.state o :=
    hstate.trans (Catalogue.state_eq_rows o)
  have hhigh : ZeroSyndrome.HighBoundary (Catalogue.Rows.state o) :=
    he ▸ B.completedStarState_high A ha
  obtain ⟨b,k,hbk⟩ := Rich.Catalogue.high_representative_covered o hhigh
  have hactual := hbk.trans he.symm
  refine ⟨b,k,hactual,?_⟩
  intro i
  rw [← hactual]
  exact Rich.Catalogue.accepted b k i

end Gallai.WholeBowtie
