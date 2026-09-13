/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarCatalogueSymmetry
import Gallai.Certificates.CompletedStarCoverage.Block00
import Gallai.Certificates.CompletedStarCoverage.Block01
import Gallai.Certificates.CompletedStarCoverage.Block02
import Gallai.Certificates.CompletedStarCoverage.Block03
import Gallai.Certificates.CompletedStarCoverage.Block04
import Gallai.Certificates.CompletedStarCoverage.Block05
import Gallai.Certificates.CompletedStarCoverage.Block06
import Gallai.Certificates.CompletedStarCoverage.Block07
import Gallai.Certificates.CompletedStarCoverage.Block08
import Gallai.Certificates.CompletedStarCoverage.Block09
import Gallai.Certificates.CompletedStarCoverage.Block10
import Gallai.Certificates.CompletedStarCoverage.Block11
import Gallai.Certificates.CompletedStarCoverage.Block12
import Gallai.Certificates.CompletedStarCoverage.Block13
import Gallai.Certificates.CompletedStarCoverage.Block14
import Gallai.Certificates.CompletedStarCoverage.Block15

/-! # Exhaustive full-syndrome representative coverage

All 4096 inputs are covered through the independently proved base-eight index.
The block equalities and catalogue acceptance are both consumed below.
-/

namespace Gallai.Certificate.CompletedStar.Coverage

/-- Every indexed state has a checked representative and symmetry action. -/
theorem indexed_covered (n : Fin 4096) :
    ∃ (o : Fin 67) (k : Fin 8) (σ : Equiv.Perm (Fin 4)),
      transformedState k σ (Catalogue.state o) = encodedAt n := by
  obtain ⟨b, i, rfl⟩ := blockIndex_surjective n
  fin_cases b
  · exact ⟨Block00.orbit i, Block00.action i,
      anchorPermutation (Block00.permutation i), Block00.witness i⟩
  · exact ⟨Block01.orbit i, Block01.action i,
      anchorPermutation (Block01.permutation i), Block01.witness i⟩
  · exact ⟨Block02.orbit i, Block02.action i,
      anchorPermutation (Block02.permutation i), Block02.witness i⟩
  · exact ⟨Block03.orbit i, Block03.action i,
      anchorPermutation (Block03.permutation i), Block03.witness i⟩
  · exact ⟨Block04.orbit i, Block04.action i,
      anchorPermutation (Block04.permutation i), Block04.witness i⟩
  · exact ⟨Block05.orbit i, Block05.action i,
      anchorPermutation (Block05.permutation i), Block05.witness i⟩
  · exact ⟨Block06.orbit i, Block06.action i,
      anchorPermutation (Block06.permutation i), Block06.witness i⟩
  · exact ⟨Block07.orbit i, Block07.action i,
      anchorPermutation (Block07.permutation i), Block07.witness i⟩
  · exact ⟨Block08.orbit i, Block08.action i,
      anchorPermutation (Block08.permutation i), Block08.witness i⟩
  · exact ⟨Block09.orbit i, Block09.action i,
      anchorPermutation (Block09.permutation i), Block09.witness i⟩
  · exact ⟨Block10.orbit i, Block10.action i,
      anchorPermutation (Block10.permutation i), Block10.witness i⟩
  · exact ⟨Block11.orbit i, Block11.action i,
      anchorPermutation (Block11.permutation i), Block11.witness i⟩
  · exact ⟨Block12.orbit i, Block12.action i,
      anchorPermutation (Block12.permutation i), Block12.witness i⟩
  · exact ⟨Block13.orbit i, Block13.action i,
      anchorPermutation (Block13.permutation i), Block13.witness i⟩
  · exact ⟨Block14.orbit i, Block14.action i,
      anchorPermutation (Block14.permutation i), Block14.witness i⟩
  · exact ⟨Block15.orbit i, Block15.action i,
      anchorPermutation (Block15.permutation i), Block15.witness i⟩

/-- All full-syndrome row states, not only enumerator outputs, are covered. -/
theorem fullState_covered (state : State) (h : FullState state) :
    ∃ (o : Fin 67) (k : Fin 8) (σ : Equiv.Perm (Fin 4)),
      transformedState k σ (Catalogue.state o) = state := by
  obtain ⟨n, rfl⟩ := fullState_indexed state h
  exact indexed_covered n

/-- The literal finite lemma needed by arbitrary ambient reconstruction. -/
theorem all_records (state : State) (h : FullState state) (j : Fin 10) :
    ∃ repl added, AcceptedRecord state j repl added := by
  obtain ⟨o, k, σ, rfl⟩ := fullState_covered state h
  exact Catalogue.transformed o k σ j

end Gallai.Certificate.CompletedStar.Coverage
