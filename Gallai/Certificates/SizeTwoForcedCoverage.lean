/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoExceptionClassification
import Gallai.Certificates.SizeTwoForcedCatalogue
import Gallai.Certificates.SizeTwoCatalogueStateAgreement

/-! # Every forced-endpoint tag has a checked one-extra-endpoint record -/
namespace Gallai.Certificate.SizeTwo.Catalogue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem forced_covered (o : Fin 234) (i : Fin 13) (h : kind o i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = o := by
  have hi := nonbasic_profile o i (fun hb => by rw [hb] at h; cases h)
  subst i
  fin_cases o
  all_goals first
    | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩
    | exact ⟨4,rfl⟩ | exact ⟨5,rfl⟩ | exact ⟨6,rfl⟩ | exact ⟨7,rfl⟩
    | exact ⟨8,rfl⟩ | exact ⟨9,rfl⟩ | exact ⟨10,rfl⟩ | exact ⟨11,rfl⟩
    | exact ⟨12,rfl⟩ | exact ⟨13,rfl⟩ | exact ⟨14,rfl⟩ | exact ⟨15,rfl⟩
    | exact ⟨16,rfl⟩ | exact ⟨17,rfl⟩ | exact ⟨18,rfl⟩ | exact ⟨19,rfl⟩
    | exact ⟨20,rfl⟩ | exact ⟨21,rfl⟩ | exact ⟨22,rfl⟩ | exact ⟨23,rfl⟩
    | exact ⟨24,rfl⟩ | exact ⟨25,rfl⟩ | exact ⟨26,rfl⟩ | exact ⟨27,rfl⟩
    | exact ⟨28,rfl⟩ | exact ⟨29,rfl⟩ | exact ⟨30,rfl⟩ | exact ⟨31,rfl⟩
    | exact ⟨32,rfl⟩ | exact ⟨33,rfl⟩ | cases h

/-- Acceptance is stated at the actual ordinary catalogue state, not merely
at an unrelated copied row table. -/
theorem forced_record (o : Fin 234) (i : Fin 13) (h : kind o i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.AcceptedRecord (state o) (Forced.Catalogue.extraIndex j)
      (Forced.Catalogue.connector j) (Forced.Catalogue.extra j)
      (Forced.Catalogue.tail j) (Forced.Catalogue.added j) := by
  obtain ⟨j,hj⟩ := forced_covered o i h
  have hs : Forced.Catalogue.state j = state o := by
    rw [state_eq_rows,← hj]
    exact Forced.Catalogue.state_eq_rows j
  refine ⟨j,?_⟩
  rw [← hs]
  exact Forced.Catalogue.accepted j

end Gallai.Certificate.SizeTwo.Catalogue
