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

private theorem forced_covered_row_000 (i : Fin 13) (h : kind (0 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (0 : Fin 234) := by
  have hi := nonbasic_profile (0 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_001 (i : Fin 13) (h : kind (1 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (1 : Fin 234) := by
  have hi := nonbasic_profile (1 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_002 (i : Fin 13) (h : kind (2 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (2 : Fin 234) := by
  have hi := nonbasic_profile (2 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_003 (i : Fin 13) (h : kind (3 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (3 : Fin 234) := by
  have hi := nonbasic_profile (3 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_004 (i : Fin 13) (h : kind (4 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (4 : Fin 234) := by
  have hi := nonbasic_profile (4 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_005 (i : Fin 13) (h : kind (5 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (5 : Fin 234) := by
  have hi := nonbasic_profile (5 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_006 (i : Fin 13) (h : kind (6 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (6 : Fin 234) := by
  have hi := nonbasic_profile (6 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_007 (i : Fin 13) (h : kind (7 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (7 : Fin 234) := by
  have hi := nonbasic_profile (7 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_008 (i : Fin 13) (h : kind (8 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (8 : Fin 234) := by
  have hi := nonbasic_profile (8 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_009 (i : Fin 13) (h : kind (9 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (9 : Fin 234) := by
  have hi := nonbasic_profile (9 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_010 (i : Fin 13) (h : kind (10 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (10 : Fin 234) := by
  have hi := nonbasic_profile (10 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_011 (i : Fin 13) (h : kind (11 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (11 : Fin 234) := by
  have hi := nonbasic_profile (11 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_012 (i : Fin 13) (h : kind (12 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (12 : Fin 234) := by
  have hi := nonbasic_profile (12 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_013 (i : Fin 13) (h : kind (13 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (13 : Fin 234) := by
  have hi := nonbasic_profile (13 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_014 (i : Fin 13) (h : kind (14 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (14 : Fin 234) := by
  have hi := nonbasic_profile (14 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_015 (i : Fin 13) (h : kind (15 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (15 : Fin 234) := by
  have hi := nonbasic_profile (15 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_016 (i : Fin 13) (h : kind (16 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (16 : Fin 234) := by
  have hi := nonbasic_profile (16 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_017 (i : Fin 13) (h : kind (17 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (17 : Fin 234) := by
  have hi := nonbasic_profile (17 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_018 (i : Fin 13) (h : kind (18 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (18 : Fin 234) := by
  have hi := nonbasic_profile (18 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_019 (i : Fin 13) (h : kind (19 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (19 : Fin 234) := by
  have hi := nonbasic_profile (19 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_020 (i : Fin 13) (h : kind (20 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (20 : Fin 234) := by
  have hi := nonbasic_profile (20 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_021 (i : Fin 13) (h : kind (21 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (21 : Fin 234) := by
  have hi := nonbasic_profile (21 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_022 (i : Fin 13) (h : kind (22 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (22 : Fin 234) := by
  have hi := nonbasic_profile (22 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_023 (i : Fin 13) (h : kind (23 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (23 : Fin 234) := by
  have hi := nonbasic_profile (23 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_024 (i : Fin 13) (h : kind (24 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (24 : Fin 234) := by
  have hi := nonbasic_profile (24 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_025 (i : Fin 13) (h : kind (25 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (25 : Fin 234) := by
  have hi := nonbasic_profile (25 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_026 (i : Fin 13) (h : kind (26 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (26 : Fin 234) := by
  have hi := nonbasic_profile (26 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_027 (i : Fin 13) (h : kind (27 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (27 : Fin 234) := by
  have hi := nonbasic_profile (27 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_028 (i : Fin 13) (h : kind (28 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (28 : Fin 234) := by
  have hi := nonbasic_profile (28 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_029 (i : Fin 13) (h : kind (29 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (29 : Fin 234) := by
  have hi := nonbasic_profile (29 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_030 (i : Fin 13) (h : kind (30 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (30 : Fin 234) := by
  have hi := nonbasic_profile (30 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_031 (i : Fin 13) (h : kind (31 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (31 : Fin 234) := by
  have hi := nonbasic_profile (31 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_032 (i : Fin 13) (h : kind (32 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (32 : Fin 234) := by
  have hi := nonbasic_profile (32 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_033 (i : Fin 13) (h : kind (33 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (33 : Fin 234) := by
  have hi := nonbasic_profile (33 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_034 (i : Fin 13) (h : kind (34 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (34 : Fin 234) := by
  have hi := nonbasic_profile (34 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_035 (i : Fin 13) (h : kind (35 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (35 : Fin 234) := by
  have hi := nonbasic_profile (35 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_036 (i : Fin 13) (h : kind (36 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (36 : Fin 234) := by
  have hi := nonbasic_profile (36 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_037 (i : Fin 13) (h : kind (37 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (37 : Fin 234) := by
  have hi := nonbasic_profile (37 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_038 (i : Fin 13) (h : kind (38 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (38 : Fin 234) := by
  have hi := nonbasic_profile (38 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_039 (i : Fin 13) (h : kind (39 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (39 : Fin 234) := by
  have hi := nonbasic_profile (39 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_040 (i : Fin 13) (h : kind (40 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (40 : Fin 234) := by
  have hi := nonbasic_profile (40 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_041 (i : Fin 13) (h : kind (41 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (41 : Fin 234) := by
  have hi := nonbasic_profile (41 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_042 (i : Fin 13) (h : kind (42 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (42 : Fin 234) := by
  have hi := nonbasic_profile (42 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_043 (i : Fin 13) (h : kind (43 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (43 : Fin 234) := by
  have hi := nonbasic_profile (43 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_044 (i : Fin 13) (h : kind (44 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (44 : Fin 234) := by
  have hi := nonbasic_profile (44 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_045 (i : Fin 13) (h : kind (45 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (45 : Fin 234) := by
  have hi := nonbasic_profile (45 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_046 (i : Fin 13) (h : kind (46 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (46 : Fin 234) := by
  have hi := nonbasic_profile (46 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_047 (i : Fin 13) (h : kind (47 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (47 : Fin 234) := by
  have hi := nonbasic_profile (47 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_048 (i : Fin 13) (h : kind (48 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (48 : Fin 234) := by
  have hi := nonbasic_profile (48 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_049 (i : Fin 13) (h : kind (49 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (49 : Fin 234) := by
  have hi := nonbasic_profile (49 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_050 (i : Fin 13) (h : kind (50 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (50 : Fin 234) := by
  have hi := nonbasic_profile (50 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_051 (i : Fin 13) (h : kind (51 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (51 : Fin 234) := by
  have hi := nonbasic_profile (51 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_052 (i : Fin 13) (h : kind (52 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (52 : Fin 234) := by
  have hi := nonbasic_profile (52 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_053 (i : Fin 13) (h : kind (53 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (53 : Fin 234) := by
  have hi := nonbasic_profile (53 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_054 (i : Fin 13) (h : kind (54 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (54 : Fin 234) := by
  have hi := nonbasic_profile (54 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_055 (i : Fin 13) (h : kind (55 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (55 : Fin 234) := by
  have hi := nonbasic_profile (55 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_056 (i : Fin 13) (h : kind (56 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (56 : Fin 234) := by
  have hi := nonbasic_profile (56 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_057 (i : Fin 13) (h : kind (57 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (57 : Fin 234) := by
  have hi := nonbasic_profile (57 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_058 (i : Fin 13) (h : kind (58 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (58 : Fin 234) := by
  have hi := nonbasic_profile (58 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_059 (i : Fin 13) (h : kind (59 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (59 : Fin 234) := by
  have hi := nonbasic_profile (59 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_060 (i : Fin 13) (h : kind (60 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (60 : Fin 234) := by
  have hi := nonbasic_profile (60 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_061 (i : Fin 13) (h : kind (61 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (61 : Fin 234) := by
  have hi := nonbasic_profile (61 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_062 (i : Fin 13) (h : kind (62 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (62 : Fin 234) := by
  have hi := nonbasic_profile (62 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_063 (i : Fin 13) (h : kind (63 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (63 : Fin 234) := by
  have hi := nonbasic_profile (63 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_064 (i : Fin 13) (h : kind (64 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (64 : Fin 234) := by
  have hi := nonbasic_profile (64 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_065 (i : Fin 13) (h : kind (65 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (65 : Fin 234) := by
  have hi := nonbasic_profile (65 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_066 (i : Fin 13) (h : kind (66 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (66 : Fin 234) := by
  have hi := nonbasic_profile (66 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_067 (i : Fin 13) (h : kind (67 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (67 : Fin 234) := by
  have hi := nonbasic_profile (67 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_068 (i : Fin 13) (h : kind (68 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (68 : Fin 234) := by
  have hi := nonbasic_profile (68 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_069 (i : Fin 13) (h : kind (69 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (69 : Fin 234) := by
  have hi := nonbasic_profile (69 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_070 (i : Fin 13) (h : kind (70 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (70 : Fin 234) := by
  have hi := nonbasic_profile (70 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_071 (i : Fin 13) (h : kind (71 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (71 : Fin 234) := by
  have hi := nonbasic_profile (71 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_072 (i : Fin 13) (h : kind (72 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (72 : Fin 234) := by
  have hi := nonbasic_profile (72 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_073 (i : Fin 13) (h : kind (73 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (73 : Fin 234) := by
  have hi := nonbasic_profile (73 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_074 (i : Fin 13) (h : kind (74 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (74 : Fin 234) := by
  have hi := nonbasic_profile (74 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_075 (i : Fin 13) (h : kind (75 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (75 : Fin 234) := by
  have hi := nonbasic_profile (75 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_076 (i : Fin 13) (h : kind (76 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (76 : Fin 234) := by
  have hi := nonbasic_profile (76 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_077 (i : Fin 13) (h : kind (77 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (77 : Fin 234) := by
  have hi := nonbasic_profile (77 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_078 (i : Fin 13) (h : kind (78 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (78 : Fin 234) := by
  have hi := nonbasic_profile (78 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_079 (i : Fin 13) (h : kind (79 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (79 : Fin 234) := by
  have hi := nonbasic_profile (79 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_080 (i : Fin 13) (h : kind (80 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (80 : Fin 234) := by
  have hi := nonbasic_profile (80 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_081 (i : Fin 13) (h : kind (81 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (81 : Fin 234) := by
  have hi := nonbasic_profile (81 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_082 (i : Fin 13) (h : kind (82 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (82 : Fin 234) := by
  have hi := nonbasic_profile (82 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_083 (i : Fin 13) (h : kind (83 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (83 : Fin 234) := by
  have hi := nonbasic_profile (83 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_084 (i : Fin 13) (h : kind (84 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (84 : Fin 234) := by
  have hi := nonbasic_profile (84 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_085 (i : Fin 13) (h : kind (85 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (85 : Fin 234) := by
  have hi := nonbasic_profile (85 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_086 (i : Fin 13) (h : kind (86 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (86 : Fin 234) := by
  have hi := nonbasic_profile (86 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_087 (i : Fin 13) (h : kind (87 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (87 : Fin 234) := by
  have hi := nonbasic_profile (87 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_088 (i : Fin 13) (h : kind (88 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (88 : Fin 234) := by
  have hi := nonbasic_profile (88 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_089 (i : Fin 13) (h : kind (89 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (89 : Fin 234) := by
  have hi := nonbasic_profile (89 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_090 (i : Fin 13) (h : kind (90 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (90 : Fin 234) := by
  have hi := nonbasic_profile (90 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_091 (i : Fin 13) (h : kind (91 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (91 : Fin 234) := by
  have hi := nonbasic_profile (91 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_092 (i : Fin 13) (h : kind (92 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (92 : Fin 234) := by
  have hi := nonbasic_profile (92 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_093 (i : Fin 13) (h : kind (93 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (93 : Fin 234) := by
  have hi := nonbasic_profile (93 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_094 (i : Fin 13) (h : kind (94 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (94 : Fin 234) := by
  have hi := nonbasic_profile (94 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_095 (i : Fin 13) (h : kind (95 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (95 : Fin 234) := by
  have hi := nonbasic_profile (95 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_096 (i : Fin 13) (h : kind (96 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (96 : Fin 234) := by
  have hi := nonbasic_profile (96 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_097 (i : Fin 13) (h : kind (97 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (97 : Fin 234) := by
  have hi := nonbasic_profile (97 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_098 (i : Fin 13) (h : kind (98 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (98 : Fin 234) := by
  have hi := nonbasic_profile (98 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_099 (i : Fin 13) (h : kind (99 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (99 : Fin 234) := by
  have hi := nonbasic_profile (99 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_100 (i : Fin 13) (h : kind (100 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (100 : Fin 234) := by
  have hi := nonbasic_profile (100 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_101 (i : Fin 13) (h : kind (101 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (101 : Fin 234) := by
  have hi := nonbasic_profile (101 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_102 (i : Fin 13) (h : kind (102 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (102 : Fin 234) := by
  have hi := nonbasic_profile (102 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_103 (i : Fin 13) (h : kind (103 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (103 : Fin 234) := by
  have hi := nonbasic_profile (103 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_104 (i : Fin 13) (h : kind (104 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (104 : Fin 234) := by
  have hi := nonbasic_profile (104 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_105 (i : Fin 13) (h : kind (105 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (105 : Fin 234) := by
  have hi := nonbasic_profile (105 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_106 (i : Fin 13) (h : kind (106 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (106 : Fin 234) := by
  have hi := nonbasic_profile (106 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_107 (i : Fin 13) (h : kind (107 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (107 : Fin 234) := by
  have hi := nonbasic_profile (107 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_108 (i : Fin 13) (h : kind (108 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (108 : Fin 234) := by
  have hi := nonbasic_profile (108 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_109 (i : Fin 13) (h : kind (109 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (109 : Fin 234) := by
  have hi := nonbasic_profile (109 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_110 (i : Fin 13) (h : kind (110 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (110 : Fin 234) := by
  have hi := nonbasic_profile (110 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_111 (i : Fin 13) (h : kind (111 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (111 : Fin 234) := by
  have hi := nonbasic_profile (111 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_112 (i : Fin 13) (h : kind (112 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (112 : Fin 234) := by
  have hi := nonbasic_profile (112 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_113 (i : Fin 13) (h : kind (113 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (113 : Fin 234) := by
  have hi := nonbasic_profile (113 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_114 (i : Fin 13) (h : kind (114 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (114 : Fin 234) := by
  have hi := nonbasic_profile (114 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_115 (i : Fin 13) (h : kind (115 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (115 : Fin 234) := by
  have hi := nonbasic_profile (115 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_116 (i : Fin 13) (h : kind (116 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (116 : Fin 234) := by
  have hi := nonbasic_profile (116 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_117 (i : Fin 13) (h : kind (117 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (117 : Fin 234) := by
  have hi := nonbasic_profile (117 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_118 (i : Fin 13) (h : kind (118 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (118 : Fin 234) := by
  have hi := nonbasic_profile (118 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_119 (i : Fin 13) (h : kind (119 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (119 : Fin 234) := by
  have hi := nonbasic_profile (119 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_120 (i : Fin 13) (h : kind (120 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (120 : Fin 234) := by
  have hi := nonbasic_profile (120 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_121 (i : Fin 13) (h : kind (121 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (121 : Fin 234) := by
  have hi := nonbasic_profile (121 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_122 (i : Fin 13) (h : kind (122 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (122 : Fin 234) := by
  have hi := nonbasic_profile (122 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_123 (i : Fin 13) (h : kind (123 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (123 : Fin 234) := by
  have hi := nonbasic_profile (123 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_124 (i : Fin 13) (h : kind (124 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (124 : Fin 234) := by
  have hi := nonbasic_profile (124 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_125 (i : Fin 13) (h : kind (125 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (125 : Fin 234) := by
  have hi := nonbasic_profile (125 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_126 (i : Fin 13) (h : kind (126 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (126 : Fin 234) := by
  have hi := nonbasic_profile (126 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_127 (i : Fin 13) (h : kind (127 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (127 : Fin 234) := by
  have hi := nonbasic_profile (127 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_128 (i : Fin 13) (h : kind (128 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (128 : Fin 234) := by
  have hi := nonbasic_profile (128 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_129 (i : Fin 13) (h : kind (129 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (129 : Fin 234) := by
  have hi := nonbasic_profile (129 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_130 (i : Fin 13) (h : kind (130 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (130 : Fin 234) := by
  have hi := nonbasic_profile (130 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_131 (i : Fin 13) (h : kind (131 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (131 : Fin 234) := by
  have hi := nonbasic_profile (131 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_132 (i : Fin 13) (h : kind (132 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (132 : Fin 234) := by
  have hi := nonbasic_profile (132 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_133 (i : Fin 13) (h : kind (133 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (133 : Fin 234) := by
  have hi := nonbasic_profile (133 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_134 (i : Fin 13) (h : kind (134 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (134 : Fin 234) := by
  have hi := nonbasic_profile (134 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_135 (i : Fin 13) (h : kind (135 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (135 : Fin 234) := by
  have hi := nonbasic_profile (135 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_136 (i : Fin 13) (h : kind (136 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (136 : Fin 234) := by
  have hi := nonbasic_profile (136 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_137 (i : Fin 13) (h : kind (137 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (137 : Fin 234) := by
  have hi := nonbasic_profile (137 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_138 (i : Fin 13) (h : kind (138 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (138 : Fin 234) := by
  have hi := nonbasic_profile (138 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_139 (i : Fin 13) (h : kind (139 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (139 : Fin 234) := by
  have hi := nonbasic_profile (139 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_140 (i : Fin 13) (h : kind (140 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (140 : Fin 234) := by
  have hi := nonbasic_profile (140 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_141 (i : Fin 13) (h : kind (141 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (141 : Fin 234) := by
  have hi := nonbasic_profile (141 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_142 (i : Fin 13) (h : kind (142 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (142 : Fin 234) := by
  have hi := nonbasic_profile (142 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_143 (i : Fin 13) (h : kind (143 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (143 : Fin 234) := by
  have hi := nonbasic_profile (143 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_144 (i : Fin 13) (h : kind (144 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (144 : Fin 234) := by
  have hi := nonbasic_profile (144 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_145 (i : Fin 13) (h : kind (145 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (145 : Fin 234) := by
  have hi := nonbasic_profile (145 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_146 (i : Fin 13) (h : kind (146 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (146 : Fin 234) := by
  have hi := nonbasic_profile (146 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_147 (i : Fin 13) (h : kind (147 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (147 : Fin 234) := by
  have hi := nonbasic_profile (147 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_148 (i : Fin 13) (h : kind (148 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (148 : Fin 234) := by
  have hi := nonbasic_profile (148 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_149 (i : Fin 13) (h : kind (149 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (149 : Fin 234) := by
  have hi := nonbasic_profile (149 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_150 (i : Fin 13) (h : kind (150 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (150 : Fin 234) := by
  have hi := nonbasic_profile (150 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_151 (i : Fin 13) (h : kind (151 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (151 : Fin 234) := by
  have hi := nonbasic_profile (151 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_152 (i : Fin 13) (h : kind (152 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (152 : Fin 234) := by
  have hi := nonbasic_profile (152 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_153 (i : Fin 13) (h : kind (153 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (153 : Fin 234) := by
  have hi := nonbasic_profile (153 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_154 (i : Fin 13) (h : kind (154 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (154 : Fin 234) := by
  have hi := nonbasic_profile (154 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_155 (i : Fin 13) (h : kind (155 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (155 : Fin 234) := by
  have hi := nonbasic_profile (155 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_156 (i : Fin 13) (h : kind (156 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (156 : Fin 234) := by
  have hi := nonbasic_profile (156 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_157 (i : Fin 13) (h : kind (157 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (157 : Fin 234) := by
  have hi := nonbasic_profile (157 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_158 (i : Fin 13) (h : kind (158 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (158 : Fin 234) := by
  have hi := nonbasic_profile (158 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_159 (i : Fin 13) (h : kind (159 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (159 : Fin 234) := by
  have hi := nonbasic_profile (159 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_160 (i : Fin 13) (h : kind (160 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (160 : Fin 234) := by
  have hi := nonbasic_profile (160 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_161 (i : Fin 13) (h : kind (161 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (161 : Fin 234) := by
  have hi := nonbasic_profile (161 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_162 (i : Fin 13) (h : kind (162 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (162 : Fin 234) := by
  have hi := nonbasic_profile (162 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_163 (i : Fin 13) (h : kind (163 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (163 : Fin 234) := by
  have hi := nonbasic_profile (163 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_164 (i : Fin 13) (h : kind (164 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (164 : Fin 234) := by
  have hi := nonbasic_profile (164 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_165 (i : Fin 13) (h : kind (165 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (165 : Fin 234) := by
  have hi := nonbasic_profile (165 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_166 (i : Fin 13) (h : kind (166 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (166 : Fin 234) := by
  have hi := nonbasic_profile (166 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_167 (i : Fin 13) (h : kind (167 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (167 : Fin 234) := by
  have hi := nonbasic_profile (167 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_168 (i : Fin 13) (h : kind (168 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (168 : Fin 234) := by
  have hi := nonbasic_profile (168 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_169 (i : Fin 13) (h : kind (169 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (169 : Fin 234) := by
  have hi := nonbasic_profile (169 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_170 (i : Fin 13) (h : kind (170 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (170 : Fin 234) := by
  have hi := nonbasic_profile (170 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_171 (i : Fin 13) (h : kind (171 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (171 : Fin 234) := by
  have hi := nonbasic_profile (171 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_172 (i : Fin 13) (h : kind (172 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (172 : Fin 234) := by
  have hi := nonbasic_profile (172 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_173 (i : Fin 13) (h : kind (173 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (173 : Fin 234) := by
  have hi := nonbasic_profile (173 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_174 (i : Fin 13) (h : kind (174 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (174 : Fin 234) := by
  have hi := nonbasic_profile (174 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_175 (i : Fin 13) (h : kind (175 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (175 : Fin 234) := by
  have hi := nonbasic_profile (175 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_176 (i : Fin 13) (h : kind (176 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (176 : Fin 234) := by
  have hi := nonbasic_profile (176 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_177 (i : Fin 13) (h : kind (177 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (177 : Fin 234) := by
  have hi := nonbasic_profile (177 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_178 (i : Fin 13) (h : kind (178 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (178 : Fin 234) := by
  have hi := nonbasic_profile (178 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_179 (i : Fin 13) (h : kind (179 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (179 : Fin 234) := by
  have hi := nonbasic_profile (179 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_180 (i : Fin 13) (h : kind (180 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (180 : Fin 234) := by
  have hi := nonbasic_profile (180 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_181 (i : Fin 13) (h : kind (181 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (181 : Fin 234) := by
  have hi := nonbasic_profile (181 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_182 (i : Fin 13) (h : kind (182 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (182 : Fin 234) := by
  have hi := nonbasic_profile (182 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_183 (i : Fin 13) (h : kind (183 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (183 : Fin 234) := by
  have hi := nonbasic_profile (183 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_184 (i : Fin 13) (h : kind (184 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (184 : Fin 234) := by
  have hi := nonbasic_profile (184 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_185 (i : Fin 13) (h : kind (185 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (185 : Fin 234) := by
  have hi := nonbasic_profile (185 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_186 (i : Fin 13) (h : kind (186 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (186 : Fin 234) := by
  have hi := nonbasic_profile (186 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_187 (i : Fin 13) (h : kind (187 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (187 : Fin 234) := by
  have hi := nonbasic_profile (187 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_188 (i : Fin 13) (h : kind (188 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (188 : Fin 234) := by
  have hi := nonbasic_profile (188 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_189 (i : Fin 13) (h : kind (189 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (189 : Fin 234) := by
  have hi := nonbasic_profile (189 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_190 (i : Fin 13) (h : kind (190 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (190 : Fin 234) := by
  have hi := nonbasic_profile (190 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_191 (i : Fin 13) (h : kind (191 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (191 : Fin 234) := by
  have hi := nonbasic_profile (191 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_192 (i : Fin 13) (h : kind (192 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (192 : Fin 234) := by
  have hi := nonbasic_profile (192 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_193 (i : Fin 13) (h : kind (193 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (193 : Fin 234) := by
  have hi := nonbasic_profile (193 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_194 (i : Fin 13) (h : kind (194 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (194 : Fin 234) := by
  have hi := nonbasic_profile (194 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_195 (i : Fin 13) (h : kind (195 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (195 : Fin 234) := by
  have hi := nonbasic_profile (195 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_196 (i : Fin 13) (h : kind (196 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (196 : Fin 234) := by
  have hi := nonbasic_profile (196 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_197 (i : Fin 13) (h : kind (197 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (197 : Fin 234) := by
  have hi := nonbasic_profile (197 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_198 (i : Fin 13) (h : kind (198 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (198 : Fin 234) := by
  have hi := nonbasic_profile (198 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_199 (i : Fin 13) (h : kind (199 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (199 : Fin 234) := by
  have hi := nonbasic_profile (199 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_200 (i : Fin 13) (h : kind (200 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (200 : Fin 234) := by
  have hi := nonbasic_profile (200 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_201 (i : Fin 13) (h : kind (201 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (201 : Fin 234) := by
  have hi := nonbasic_profile (201 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_202 (i : Fin 13) (h : kind (202 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (202 : Fin 234) := by
  have hi := nonbasic_profile (202 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_203 (i : Fin 13) (h : kind (203 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (203 : Fin 234) := by
  have hi := nonbasic_profile (203 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_204 (i : Fin 13) (h : kind (204 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (204 : Fin 234) := by
  have hi := nonbasic_profile (204 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_205 (i : Fin 13) (h : kind (205 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (205 : Fin 234) := by
  have hi := nonbasic_profile (205 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_206 (i : Fin 13) (h : kind (206 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (206 : Fin 234) := by
  have hi := nonbasic_profile (206 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_207 (i : Fin 13) (h : kind (207 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (207 : Fin 234) := by
  have hi := nonbasic_profile (207 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_208 (i : Fin 13) (h : kind (208 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (208 : Fin 234) := by
  have hi := nonbasic_profile (208 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_209 (i : Fin 13) (h : kind (209 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (209 : Fin 234) := by
  have hi := nonbasic_profile (209 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_210 (i : Fin 13) (h : kind (210 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (210 : Fin 234) := by
  have hi := nonbasic_profile (210 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_211 (i : Fin 13) (h : kind (211 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (211 : Fin 234) := by
  have hi := nonbasic_profile (211 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_212 (i : Fin 13) (h : kind (212 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (212 : Fin 234) := by
  have hi := nonbasic_profile (212 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_213 (i : Fin 13) (h : kind (213 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (213 : Fin 234) := by
  have hi := nonbasic_profile (213 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_214 (i : Fin 13) (h : kind (214 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (214 : Fin 234) := by
  have hi := nonbasic_profile (214 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_215 (i : Fin 13) (h : kind (215 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (215 : Fin 234) := by
  have hi := nonbasic_profile (215 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_216 (i : Fin 13) (h : kind (216 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (216 : Fin 234) := by
  have hi := nonbasic_profile (216 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_217 (i : Fin 13) (h : kind (217 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (217 : Fin 234) := by
  have hi := nonbasic_profile (217 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_218 (i : Fin 13) (h : kind (218 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (218 : Fin 234) := by
  have hi := nonbasic_profile (218 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_219 (i : Fin 13) (h : kind (219 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (219 : Fin 234) := by
  have hi := nonbasic_profile (219 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_220 (i : Fin 13) (h : kind (220 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (220 : Fin 234) := by
  have hi := nonbasic_profile (220 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_221 (i : Fin 13) (h : kind (221 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (221 : Fin 234) := by
  have hi := nonbasic_profile (221 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_222 (i : Fin 13) (h : kind (222 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (222 : Fin 234) := by
  have hi := nonbasic_profile (222 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_223 (i : Fin 13) (h : kind (223 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (223 : Fin 234) := by
  have hi := nonbasic_profile (223 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_224 (i : Fin 13) (h : kind (224 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (224 : Fin 234) := by
  have hi := nonbasic_profile (224 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_225 (i : Fin 13) (h : kind (225 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (225 : Fin 234) := by
  have hi := nonbasic_profile (225 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_226 (i : Fin 13) (h : kind (226 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (226 : Fin 234) := by
  have hi := nonbasic_profile (226 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_227 (i : Fin 13) (h : kind (227 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (227 : Fin 234) := by
  have hi := nonbasic_profile (227 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_228 (i : Fin 13) (h : kind (228 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (228 : Fin 234) := by
  have hi := nonbasic_profile (228 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_229 (i : Fin 13) (h : kind (229 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (229 : Fin 234) := by
  have hi := nonbasic_profile (229 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_230 (i : Fin 13) (h : kind (230 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (230 : Fin 234) := by
  have hi := nonbasic_profile (230 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_231 (i : Fin 13) (h : kind (231 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (231 : Fin 234) := by
  have hi := nonbasic_profile (231 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_232 (i : Fin 13) (h : kind (232 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (232 : Fin 234) := by
  have hi := nonbasic_profile (232 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

private theorem forced_covered_row_233 (i : Fin 13) (h : kind (233 : Fin 234) i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = (233 : Fin 234) := by
  have hi := nonbasic_profile (233 : Fin 234) i (fun hb => by rw [hb] at h; cases h)
  subst i
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

theorem forced_covered (o : Fin 234) (i : Fin 13) (h : kind o i = .forcedEndpoints) :
    ∃ j : Fin 34, Forced.Catalogue.orbit j = o := by
  fin_cases o
  · exact forced_covered_row_000 i h
  · exact forced_covered_row_001 i h
  · exact forced_covered_row_002 i h
  · exact forced_covered_row_003 i h
  · exact forced_covered_row_004 i h
  · exact forced_covered_row_005 i h
  · exact forced_covered_row_006 i h
  · exact forced_covered_row_007 i h
  · exact forced_covered_row_008 i h
  · exact forced_covered_row_009 i h
  · exact forced_covered_row_010 i h
  · exact forced_covered_row_011 i h
  · exact forced_covered_row_012 i h
  · exact forced_covered_row_013 i h
  · exact forced_covered_row_014 i h
  · exact forced_covered_row_015 i h
  · exact forced_covered_row_016 i h
  · exact forced_covered_row_017 i h
  · exact forced_covered_row_018 i h
  · exact forced_covered_row_019 i h
  · exact forced_covered_row_020 i h
  · exact forced_covered_row_021 i h
  · exact forced_covered_row_022 i h
  · exact forced_covered_row_023 i h
  · exact forced_covered_row_024 i h
  · exact forced_covered_row_025 i h
  · exact forced_covered_row_026 i h
  · exact forced_covered_row_027 i h
  · exact forced_covered_row_028 i h
  · exact forced_covered_row_029 i h
  · exact forced_covered_row_030 i h
  · exact forced_covered_row_031 i h
  · exact forced_covered_row_032 i h
  · exact forced_covered_row_033 i h
  · exact forced_covered_row_034 i h
  · exact forced_covered_row_035 i h
  · exact forced_covered_row_036 i h
  · exact forced_covered_row_037 i h
  · exact forced_covered_row_038 i h
  · exact forced_covered_row_039 i h
  · exact forced_covered_row_040 i h
  · exact forced_covered_row_041 i h
  · exact forced_covered_row_042 i h
  · exact forced_covered_row_043 i h
  · exact forced_covered_row_044 i h
  · exact forced_covered_row_045 i h
  · exact forced_covered_row_046 i h
  · exact forced_covered_row_047 i h
  · exact forced_covered_row_048 i h
  · exact forced_covered_row_049 i h
  · exact forced_covered_row_050 i h
  · exact forced_covered_row_051 i h
  · exact forced_covered_row_052 i h
  · exact forced_covered_row_053 i h
  · exact forced_covered_row_054 i h
  · exact forced_covered_row_055 i h
  · exact forced_covered_row_056 i h
  · exact forced_covered_row_057 i h
  · exact forced_covered_row_058 i h
  · exact forced_covered_row_059 i h
  · exact forced_covered_row_060 i h
  · exact forced_covered_row_061 i h
  · exact forced_covered_row_062 i h
  · exact forced_covered_row_063 i h
  · exact forced_covered_row_064 i h
  · exact forced_covered_row_065 i h
  · exact forced_covered_row_066 i h
  · exact forced_covered_row_067 i h
  · exact forced_covered_row_068 i h
  · exact forced_covered_row_069 i h
  · exact forced_covered_row_070 i h
  · exact forced_covered_row_071 i h
  · exact forced_covered_row_072 i h
  · exact forced_covered_row_073 i h
  · exact forced_covered_row_074 i h
  · exact forced_covered_row_075 i h
  · exact forced_covered_row_076 i h
  · exact forced_covered_row_077 i h
  · exact forced_covered_row_078 i h
  · exact forced_covered_row_079 i h
  · exact forced_covered_row_080 i h
  · exact forced_covered_row_081 i h
  · exact forced_covered_row_082 i h
  · exact forced_covered_row_083 i h
  · exact forced_covered_row_084 i h
  · exact forced_covered_row_085 i h
  · exact forced_covered_row_086 i h
  · exact forced_covered_row_087 i h
  · exact forced_covered_row_088 i h
  · exact forced_covered_row_089 i h
  · exact forced_covered_row_090 i h
  · exact forced_covered_row_091 i h
  · exact forced_covered_row_092 i h
  · exact forced_covered_row_093 i h
  · exact forced_covered_row_094 i h
  · exact forced_covered_row_095 i h
  · exact forced_covered_row_096 i h
  · exact forced_covered_row_097 i h
  · exact forced_covered_row_098 i h
  · exact forced_covered_row_099 i h
  · exact forced_covered_row_100 i h
  · exact forced_covered_row_101 i h
  · exact forced_covered_row_102 i h
  · exact forced_covered_row_103 i h
  · exact forced_covered_row_104 i h
  · exact forced_covered_row_105 i h
  · exact forced_covered_row_106 i h
  · exact forced_covered_row_107 i h
  · exact forced_covered_row_108 i h
  · exact forced_covered_row_109 i h
  · exact forced_covered_row_110 i h
  · exact forced_covered_row_111 i h
  · exact forced_covered_row_112 i h
  · exact forced_covered_row_113 i h
  · exact forced_covered_row_114 i h
  · exact forced_covered_row_115 i h
  · exact forced_covered_row_116 i h
  · exact forced_covered_row_117 i h
  · exact forced_covered_row_118 i h
  · exact forced_covered_row_119 i h
  · exact forced_covered_row_120 i h
  · exact forced_covered_row_121 i h
  · exact forced_covered_row_122 i h
  · exact forced_covered_row_123 i h
  · exact forced_covered_row_124 i h
  · exact forced_covered_row_125 i h
  · exact forced_covered_row_126 i h
  · exact forced_covered_row_127 i h
  · exact forced_covered_row_128 i h
  · exact forced_covered_row_129 i h
  · exact forced_covered_row_130 i h
  · exact forced_covered_row_131 i h
  · exact forced_covered_row_132 i h
  · exact forced_covered_row_133 i h
  · exact forced_covered_row_134 i h
  · exact forced_covered_row_135 i h
  · exact forced_covered_row_136 i h
  · exact forced_covered_row_137 i h
  · exact forced_covered_row_138 i h
  · exact forced_covered_row_139 i h
  · exact forced_covered_row_140 i h
  · exact forced_covered_row_141 i h
  · exact forced_covered_row_142 i h
  · exact forced_covered_row_143 i h
  · exact forced_covered_row_144 i h
  · exact forced_covered_row_145 i h
  · exact forced_covered_row_146 i h
  · exact forced_covered_row_147 i h
  · exact forced_covered_row_148 i h
  · exact forced_covered_row_149 i h
  · exact forced_covered_row_150 i h
  · exact forced_covered_row_151 i h
  · exact forced_covered_row_152 i h
  · exact forced_covered_row_153 i h
  · exact forced_covered_row_154 i h
  · exact forced_covered_row_155 i h
  · exact forced_covered_row_156 i h
  · exact forced_covered_row_157 i h
  · exact forced_covered_row_158 i h
  · exact forced_covered_row_159 i h
  · exact forced_covered_row_160 i h
  · exact forced_covered_row_161 i h
  · exact forced_covered_row_162 i h
  · exact forced_covered_row_163 i h
  · exact forced_covered_row_164 i h
  · exact forced_covered_row_165 i h
  · exact forced_covered_row_166 i h
  · exact forced_covered_row_167 i h
  · exact forced_covered_row_168 i h
  · exact forced_covered_row_169 i h
  · exact forced_covered_row_170 i h
  · exact forced_covered_row_171 i h
  · exact forced_covered_row_172 i h
  · exact forced_covered_row_173 i h
  · exact forced_covered_row_174 i h
  · exact forced_covered_row_175 i h
  · exact forced_covered_row_176 i h
  · exact forced_covered_row_177 i h
  · exact forced_covered_row_178 i h
  · exact forced_covered_row_179 i h
  · exact forced_covered_row_180 i h
  · exact forced_covered_row_181 i h
  · exact forced_covered_row_182 i h
  · exact forced_covered_row_183 i h
  · exact forced_covered_row_184 i h
  · exact forced_covered_row_185 i h
  · exact forced_covered_row_186 i h
  · exact forced_covered_row_187 i h
  · exact forced_covered_row_188 i h
  · exact forced_covered_row_189 i h
  · exact forced_covered_row_190 i h
  · exact forced_covered_row_191 i h
  · exact forced_covered_row_192 i h
  · exact forced_covered_row_193 i h
  · exact forced_covered_row_194 i h
  · exact forced_covered_row_195 i h
  · exact forced_covered_row_196 i h
  · exact forced_covered_row_197 i h
  · exact forced_covered_row_198 i h
  · exact forced_covered_row_199 i h
  · exact forced_covered_row_200 i h
  · exact forced_covered_row_201 i h
  · exact forced_covered_row_202 i h
  · exact forced_covered_row_203 i h
  · exact forced_covered_row_204 i h
  · exact forced_covered_row_205 i h
  · exact forced_covered_row_206 i h
  · exact forced_covered_row_207 i h
  · exact forced_covered_row_208 i h
  · exact forced_covered_row_209 i h
  · exact forced_covered_row_210 i h
  · exact forced_covered_row_211 i h
  · exact forced_covered_row_212 i h
  · exact forced_covered_row_213 i h
  · exact forced_covered_row_214 i h
  · exact forced_covered_row_215 i h
  · exact forced_covered_row_216 i h
  · exact forced_covered_row_217 i h
  · exact forced_covered_row_218 i h
  · exact forced_covered_row_219 i h
  · exact forced_covered_row_220 i h
  · exact forced_covered_row_221 i h
  · exact forced_covered_row_222 i h
  · exact forced_covered_row_223 i h
  · exact forced_covered_row_224 i h
  · exact forced_covered_row_225 i h
  · exact forced_covered_row_226 i h
  · exact forced_covered_row_227 i h
  · exact forced_covered_row_228 i h
  · exact forced_covered_row_229 i h
  · exact forced_covered_row_230 i h
  · exact forced_covered_row_231 i h
  · exact forced_covered_row_232 i h
  · exact forced_covered_row_233 i h


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
