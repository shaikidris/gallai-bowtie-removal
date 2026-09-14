/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCoverage.Block03.Core
import Gallai.Certificates.SizeTwoCoverage.Block03.Sub0
import Gallai.Certificates.SizeTwoCoverage.Block03.Sub1
import Gallai.Certificates.SizeTwoCoverage.Block03.Sub2
import Gallai.Certificates.SizeTwoCoverage.Block03.Sub3
import Mathlib.Tactic.FinCases

namespace Gallai.Certificate.SizeTwo.Coverage.Block03
open CompletedStar CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem witness_chunked (q : Fin 4) (r : Fin 64) :
    (∀ j : Fin 4, (anchorPermutation (permutation ⟨q.val * 64 + r.val, by omega⟩) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action ⟨q.val * 64 + r.val, by omega⟩)
      (anchorPermutation (permutation ⟨q.val * 64 + r.val, by omega⟩))
      (SizeTwo.Catalogue.Rows.state (orbit ⟨q.val * 64 + r.val, by omega⟩)) =
        pairEncodedAt (blockIndex 3 ⟨q.val * 64 + r.val, by omega⟩) := by
  fin_cases q
  · exact witness_chunk_0 r
  · exact witness_chunk_1 r
  · exact witness_chunk_2 r
  · exact witness_chunk_3 r
/-- Every original indexed state is the displayed pair-preserving symmetry image. -/
theorem witness (i : Fin 256) :
    (∀ j : Fin 4, (anchorPermutation (permutation i) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action i) (anchorPermutation (permutation i))
      (SizeTwo.Catalogue.Rows.state (orbit i)) = pairEncodedAt (blockIndex 3 i) := by
  let q : Fin 4 := ⟨i.val / 64, by omega⟩
  let r : Fin 64 := ⟨i.val % 64, by omega⟩
  have h := witness_chunked q r
  have heq : (⟨q.val * 64 + r.val, by omega⟩ : Fin 256) = i := by
    apply Fin.ext
    dsimp [q, r]
    omega
  simpa only [heq] using h

end Gallai.Certificate.SizeTwo.Coverage.Block03
