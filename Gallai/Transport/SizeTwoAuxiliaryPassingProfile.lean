/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoPassingSelection
import Gallai.Transport.SizeTwoPassingFamily

/-! # Passing profiles of the unchanged actual syndrome decomposition -/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The zero-endpoint hub case supplies every profile premise of passing
reconstruction on the ORIGINAL decomposition. Connector reversal is handled
locally, so neither orientation normalization nor reselection is needed. -/
theorem sizeTwo_auxiliary_passing_profile (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (D : Decomposition B.syndromeStar) (he : D.endpointCount B.completedHub = 0)
    (hr : 0 < D.endpointCount (B.sizeTwoRemoteMarks A 0))
    (hs : 0 < D.endpointCount (B.sizeTwoRemoteMarks A 1)) :
    ∃ f : Fin 4 → Fin D.size, ∃ i : Fin 13,
      through i = true ∧
      (∀ r : Fin 2,
        (D.path (f (remoteRole i r))).start = B.sizeTwoRemoteMarks A r ∨
        (D.path (f (remoteRole i r))).finish = B.sizeTwoRemoteMarks A r) ∧
      (∀ j k, j ≠ 3 → k ≠ 3 → (f j = f k ↔ owner i j = owner i k)) ∧
      B.completedHub ∈ (D.path (f 0)).walk.support ∧
      (D.path (f 0)).start ≠ B.completedHub ∧
      B.completedHub ≠ (D.path (f 0)).finish ∧
      ∀ k, k ≠ f 0 → B.completedHub ∉ (D.path k).walk.support := by
  have hne : (A 0).val ≠ (A 1).val := by
    intro hh
    have hi := A.injective (Subtype.ext hh)
    exact (by decide : (0 : Fin 4) ≠ 1) hi
  have hcard : B.syndrome.card = 2 := by simp [hSigma,hne]
  obtain ⟨f,i,hi,hx,hstart,hfinish,hr',hs',howner,hunique⟩ :=
    D.sizeTwo_passing_selection B.completedHub (B.sizeTwoRemoteMarks A 0)
      (B.sizeTwoRemoteMarks A 1) (B.syndromeStar_hub_degree_two hcard) he hr hs
  refine ⟨f,i,hi,?_,howner,hx,hstart,hfinish.symm,?_⟩
  · intro r
    fin_cases r
    · simpa [remoteRole,hi] using hr'
    · simpa [remoteRole,hi] using hs'
  · intro k hk hmem
    exact hk (hunique k hmem)

end Gallai.WholeBowtie
