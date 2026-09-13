/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoAuxiliaryPassingProfile
import Gallai.Transport.SizeTwoAuxiliaryTerminalProfile
import Gallai.Transport.SizeTwoPassingReconstruction
import Gallai.Transport.SizeTwoTerminalReconstruction
import Gallai.Structure.SyndromeStarParity
import Gallai.Foundations.EndpointBounds

/-! # Actual-decomposition consumer for ordinary size-two certificates

The profile is chosen from the given auxiliary decomposition before any
certificate words are supplied. No favourable carrier arrangement, endpoint
assignment, orientation, or reconstruction hypothesis is an input.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Every actual auxiliary decomposition supplies a legal ordinary profile.
Any accepted record for THAT profile reconstructs G with its exact record cost
and preserves all even outside endpoint reserves on a single witness. -/
theorem sizeTwo_ordinary_consumer (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (D : Decomposition B.syndromeStar) :
    ∃ i : Fin 13, ∀ words : Fin 4 → List Star.Vertex, ∀ added : List (List Star.Vertex),
      OrdinaryAccepted (B.completedStarState A) i words added →
      ∃ P : Decomposition G, P.size = D.size + added.length ∧ P.size ≤ D.size + 2 ∧
        ∀ w : B.StarSurvivor, w.val ∉ B.vertices → Even (G.degree w.val) →
          D.endpointCount w ≤ P.endpointCount w.val := by
  have hne : (A 0).val ≠ (A 1).val := by
    intro hh
    exact (by decide : (0 : Fin 4) ≠ 1) (A.injective (Subtype.ext hh))
  have hcard : B.syndrome.card = 2 := by simp [hSigma,hne]
  have hremote (r : Fin 2) : 0 < D.endpointCount (B.sizeTwoRemoteMarks A r) := by
    apply D.endpointCount_pos_of_odd_degree
    apply Nat.not_even_iff_odd.mp
    intro he
    have ho : Odd (G.degree (B.sizeTwoRemoteMarks A r).val) :=
      B.odd_degree_anchor (A ⟨r.val + 2,by omega⟩).property
    exact Nat.not_even_iff_odd.mpr ho ((B.syndromeStar_even_iff _).mp he)
  rcases D.degree_two_carrier_profiles B.completedHub (B.syndromeStar_hub_degree_two hcard) with
    ⟨he,_⟩ | ⟨he,_⟩
  · obtain ⟨f,i,hi,hf,howner,hx,hs,ht,havoid⟩ :=
      B.sizeTwo_auxiliary_passing_profile A hSigma D he (hremote 0) (hremote 1)
    refine ⟨i,?_⟩
    intro words added h
    exact B.sizeTwo_passing_reconstruction A hSigma i hi D f hf howner hx hs ht havoid words added h
  · obtain ⟨E,hsize,hcounts,f,i,hi,hf,howner,hx0,hu0,hx1,hu1,havoid⟩ :=
      B.sizeTwo_auxiliary_terminal_profile A hSigma D he (hremote 0) (hremote 1)
    refine ⟨i,?_⟩
    intro words added h
    obtain ⟨P,hPsize,hPbound,hPreserve⟩ :=
      B.sizeTwo_terminal_reconstruction A hSigma i hi E f hf howner hx0 hu0 hx1 hu1 havoid words added h
    refine ⟨P,?_,?_,?_⟩
    · exact hPsize.trans (congrArg (fun n => n + added.length) hsize)
    · simpa only [hsize] using hPbound
    · intro w hout hw
      rw [← hcounts w]
      exact hPreserve w hout hw

/-- Two actual reconstruction credits and the designated reserve consume an
ordinary record without any further graph or carrier hypotheses. -/
theorem sizeTwo_two_credit_consumer (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (D : Decomposition B.syndromeStar) (budget : ℕ) (hbudget : D.size + 2 ≤ budget)
    (y : B.StarSurvivor) (hyout : y.val ∉ B.vertices) (hy : Even (G.degree y.val))
    (hyD : 2 ≤ D.endpointCount y) :
    ∃ i : Fin 13, ∀ words : Fin 4 → List Star.Vertex, ∀ added : List (List Star.Vertex),
      OrdinaryAccepted (B.completedStarState A) i words added →
      ∃ P : Decomposition G, P.size ≤ budget ∧ 2 ≤ P.endpointCount y.val := by
  obtain ⟨i,hi⟩ := B.sizeTwo_ordinary_consumer A hSigma D
  refine ⟨i,?_⟩
  intro words added h
  obtain ⟨P,_,hP,hend⟩ := hi words added h
  exact ⟨P,hP.trans hbudget,hyD.trans (hend y hyout hy)⟩

end Gallai.WholeBowtie
