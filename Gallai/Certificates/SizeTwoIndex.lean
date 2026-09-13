/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoUniverse
import Gallai.Certificates.CompletedStarIndex

/-! # Exhaustive size-two table indexing

Reuse the proved base-eight index. No list of catalogue representatives is
used to establish that every normalized actual state has a table index.
-/
namespace Gallai.Certificate.SizeTwo
open CompletedStar

/-- Normalized syndrome-pq state at the four-row base-eight index. -/
def pairEncodedAt (n : Fin 4096) : State := pairEncodedState (inputDigits n)

/-- Every independently admissible state has an exhaustive table index. -/
theorem pairState_indexed (s : State) (h : PairState s) :
    ∃ n : Fin 4096, pairEncodedAt n = s := by
  obtain ⟨q,hq⟩ := pairState_encoded s h
  obtain ⟨n,hn⟩ := inputDigits_surjective q
  exact ⟨n, (congrArg pairEncodedState hn).trans hq⟩

end Gallai.Certificate.SizeTwo

namespace Gallai.WholeBowtie
open Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The actual normalized graph state enters the same4096-entry lookup domain. -/
theorem completedStarState_pair_indexed (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val}) :
    ∃ n : Fin 4096, pairEncodedAt n = B.completedStarState A :=
  pairState_indexed _ (B.completedStarState_pair A hSigma)

end Gallai.WholeBowtie
