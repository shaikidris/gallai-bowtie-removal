/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeCoverage.Block00
import Gallai.Certificates.ZeroSyndromeCoverage.Block01
import Gallai.Certificates.ZeroSyndromeCoverage.Block02
import Gallai.Certificates.ZeroSyndromeCoverage.Block03
import Gallai.Certificates.ZeroSyndromeCoverage.Block04
import Gallai.Certificates.ZeroSyndromeCoverage.Block05
import Gallai.Certificates.ZeroSyndromeCoverage.Block06
import Gallai.Certificates.ZeroSyndromeCoverage.Block07
import Gallai.Certificates.ZeroSyndromeCoverage.Block08
import Gallai.Certificates.ZeroSyndromeCoverage.Block09
import Gallai.Certificates.ZeroSyndromeCoverage.Block10
import Gallai.Certificates.ZeroSyndromeCoverage.Block11
import Gallai.Certificates.ZeroSyndromeCoverage.Block12
import Gallai.Certificates.ZeroSyndromeCoverage.Block13
import Gallai.Certificates.ZeroSyndromeCoverage.Block14
import Gallai.Certificates.ZeroSyndromeCoverage.Block15

/-! # Exhaustive representative coverage of original high zero states -/
namespace Gallai.Certificate.ZeroSyndrome.Coverage
open CompletedStar
open CompletedStar.Coverage

/-- Every eligible original index is a symmetry image of a checked representative. -/
theorem indexed_covered (n : Fin 4096) (h : HighBoundary (zeroEncodedAt n)) :
    ∃ (o : Fin 44) (k : Fin 8) (σ : Equiv.Perm (Fin 4)),
      transformedState k σ (ZeroSyndrome.Catalogue.state o) = zeroEncodedAt n := by
  obtain ⟨b, i, rfl⟩ := blockIndex_surjective n
  fin_cases b
  · exact ⟨Block00.orbit i, Block00.action i,
      anchorPermutation (Block00.permutation i), Block00.witness i h⟩
  · exact ⟨Block01.orbit i, Block01.action i,
      anchorPermutation (Block01.permutation i), Block01.witness i h⟩
  · exact ⟨Block02.orbit i, Block02.action i,
      anchorPermutation (Block02.permutation i), Block02.witness i h⟩
  · exact ⟨Block03.orbit i, Block03.action i,
      anchorPermutation (Block03.permutation i), Block03.witness i h⟩
  · exact ⟨Block04.orbit i, Block04.action i,
      anchorPermutation (Block04.permutation i), Block04.witness i h⟩
  · exact ⟨Block05.orbit i, Block05.action i,
      anchorPermutation (Block05.permutation i), Block05.witness i h⟩
  · exact ⟨Block06.orbit i, Block06.action i,
      anchorPermutation (Block06.permutation i), Block06.witness i h⟩
  · exact ⟨Block07.orbit i, Block07.action i,
      anchorPermutation (Block07.permutation i), Block07.witness i h⟩
  · exact ⟨Block08.orbit i, Block08.action i,
      anchorPermutation (Block08.permutation i), Block08.witness i h⟩
  · exact ⟨Block09.orbit i, Block09.action i,
      anchorPermutation (Block09.permutation i), Block09.witness i h⟩
  · exact ⟨Block10.orbit i, Block10.action i,
      anchorPermutation (Block10.permutation i), Block10.witness i h⟩
  · exact ⟨Block11.orbit i, Block11.action i,
      anchorPermutation (Block11.permutation i), Block11.witness i h⟩
  · exact ⟨Block12.orbit i, Block12.action i,
      anchorPermutation (Block12.permutation i), Block12.witness i h⟩
  · exact ⟨Block13.orbit i, Block13.action i,
      anchorPermutation (Block13.permutation i), Block13.witness i h⟩
  · exact ⟨Block14.orbit i, Block14.action i,
      anchorPermutation (Block14.permutation i), Block14.witness i h⟩
  · exact ⟨Block15.orbit i, Block15.action i,
      anchorPermutation (Block15.permutation i), Block15.witness i h⟩

/-- Coverage is over the independently defined domain, not a supplied row list. -/
theorem highZeroState_covered (s : State) (h : HighZeroState s) :
    ∃ (o : Fin 44) (k : Fin 8) (σ : Equiv.Perm (Fin 4)),
      transformedState k σ (ZeroSyndrome.Catalogue.state o) = s := by
  obtain ⟨n, hn, rfl⟩ := highZeroState_indexed s h
  exact indexed_covered n hn

end Gallai.Certificate.ZeroSyndrome.Coverage
