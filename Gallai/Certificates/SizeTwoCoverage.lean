/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCoverage.Block00
import Gallai.Certificates.SizeTwoCoverage.Block01
import Gallai.Certificates.SizeTwoCoverage.Block02
import Gallai.Certificates.SizeTwoCoverage.Block03
import Gallai.Certificates.SizeTwoCoverage.Block04
import Gallai.Certificates.SizeTwoCoverage.Block05
import Gallai.Certificates.SizeTwoCoverage.Block06
import Gallai.Certificates.SizeTwoCoverage.Block07
import Gallai.Certificates.SizeTwoCoverage.Block08
import Gallai.Certificates.SizeTwoCoverage.Block09
import Gallai.Certificates.SizeTwoCoverage.Block10
import Gallai.Certificates.SizeTwoCoverage.Block11
import Gallai.Certificates.SizeTwoCoverage.Block12
import Gallai.Certificates.SizeTwoCoverage.Block13
import Gallai.Certificates.SizeTwoCoverage.Block14
import Gallai.Certificates.SizeTwoCoverage.Block15

/-! # Complete normalized size-two representative coverage

This establishes row coverage, not transport of accepted words or exceptions.
-/
namespace Gallai.Certificate.SizeTwo.Coverage
open CompletedStar CompletedStar.Coverage

/-- All4096 indexed states have pair-preserving representative witnesses. -/
theorem indexed_covered (n : Fin 4096) :
    ∃ (o : Fin 234) (k : Fin 8) (σ : Equiv.Perm (Fin 4)),
      (∀ j : Fin 4, (σ j).val < 2 ↔ j.val < 2) ∧
      transformedState k σ (SizeTwo.Catalogue.Rows.state o) = pairEncodedAt n := by
  obtain ⟨b,i,rfl⟩ := blockIndex_surjective n
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

/-- Coverage is over the independently defined parity domain, not a supplied list. -/
theorem pairState_covered (s : State) (h : PairState s) :
    ∃ (o : Fin 234) (k : Fin 8) (σ : Equiv.Perm (Fin 4)),
      (∀ j : Fin 4, (σ j).val < 2 ↔ j.val < 2) ∧
      transformedState k σ (SizeTwo.Catalogue.Rows.state o) = s := by
  obtain ⟨n,rfl⟩ := pairState_indexed s h
  exact indexed_covered n

end Gallai.Certificate.SizeTwo.Coverage
