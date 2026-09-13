/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarUniverse
import Gallai.Certificates.CompletedStarSymmetry

/-! # Exhaustive base-eight input indexing

The finite coverage table is indexed by all four free even rows, not by
states discovered by the external generator. Surjectivity is proved here.
-/

namespace Gallai.Certificate.CompletedStar

/-- Four base-eight digits, least significant row first. -/
def inputDigits (n : Fin 4096) : Fin 4 → Fin 8 :=
  ![⟨n.val % 8, Nat.mod_lt _ (by decide)⟩,
    ⟨n.val / 8 % 8, Nat.mod_lt _ (by decide)⟩,
    ⟨n.val / 64 % 8, Nat.mod_lt _ (by decide)⟩,
    ⟨n.val / 512 % 8, Nat.mod_lt _ (by decide)⟩]

/-- Every four-free-row input occurs in the index domain. -/
theorem inputDigits_surjective : Function.Surjective inputDigits := by
  intro q
  have h0 := (q 0).isLt
  have h1 := (q 1).isLt
  have h2 := (q 2).isLt
  have h3 := (q 3).isLt
  let n : Fin 4096 := ⟨(q 0).val + 8 * (q 1).val + 64 * (q 2).val +
    512 * (q 3).val, by omega⟩
  refine ⟨n, ?_⟩
  funext j
  fin_cases j <;> apply Fin.ext
  all_goals dsimp [inputDigits, n]; omega

/-- The full-syndrome row state at an exhaustive finite input index. -/
def encodedAt (n : Fin 4096) : State := encodedState (inputDigits n)

/-- Every actual full-syndrome state is represented by an input index. -/
theorem fullState_indexed (state : State) (h : FullState state) :
    ∃ n : Fin 4096, encodedAt n = state := by
  obtain ⟨q, hq⟩ := fullState_encoded state h
  obtain ⟨n, hn⟩ := inputDigits_surjective q
  exact ⟨n, by simpa only [encodedAt, hn] using hq⟩

/-- Sixteen independently checked blocks of 256 consecutive indices. -/
def blockIndex (b : Fin 16) (i : Fin 256) : Fin 4096 :=
  ⟨256 * b.val + i.val, by have := b.isLt; have := i.isLt; omega⟩

/-- The proof blocks exhaust the input domain, including both endpoints. -/
theorem blockIndex_surjective (n : Fin 4096) :
    ∃ b i, blockIndex b i = n := by
  refine ⟨⟨n.val / 256, by have := n.isLt; omega⟩,
    ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩, ?_⟩
  apply Fin.ext
  dsimp [blockIndex]
  omega

end Gallai.Certificate.CompletedStar
