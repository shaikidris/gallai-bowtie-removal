/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCatalogue

/-! # Exact exceptional profile and state classification

These facts inspect the literal checked registry. They do not assert that
forced-endpoint or Fan transports have been constructed.
-/
namespace Gallai.Certificate.SizeTwo.Catalogue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every non-basic record uses the single shared through-carrier profile. -/
theorem nonbasic_profile (o : Fin 234) (i : Fin 13) (h : kind o i ≠ .basic) : i = 0 := by
  fin_cases o <;> fin_cases i
  all_goals first | rfl | exact (h rfl).elim

/-- The symbolic two-ear tag is attached only to the proved low-activity state. -/
theorem twoEar_state (o : Fin 234) (i : Fin 13) (h : kind o i = .twoEar) :
    state o = ![15,0,0,0,12] := by
  have hi := nonbasic_profile o i (fun hb => by rw [hb] at h; cases h)
  subst i
  fin_cases o
  all_goals first | rfl | cases h

/-- The symbolic Fan tag has the exact row pattern required by restoration. -/
theorem fan_state (o : Fin 234) (i : Fin 13) (h : kind o i = .fan) :
    state o = ![15,0,12,12,12] := by
  have hi := nonbasic_profile o i (fun hb => by rw [hb] at h; cases h)
  subst i
  fin_cases o
  all_goals first | rfl | cases h

end Gallai.Certificate.SizeTwo.Catalogue
