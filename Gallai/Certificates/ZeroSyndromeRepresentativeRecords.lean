/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeCatalogue
import Gallai.Certificates.ZeroSyndromeCatalogueInterfaceCoverage

/-! # Records for every actual interface at each stored representative

This closes record and interface coverage. Relabeling and exhaustive original
row-state coverage are separate obligations; no graph-order bound is used.
-/

namespace Gallai.Certificate.ZeroSyndrome.Catalogue

/-- Every legal requested component/carrier pair has a checked two-credit record. -/
theorem two_records (o : Fin 44) (c k : Labels) (h : (c, k) ∈ interfaces) :
    ∃ tails added, TwoCreditAccepted (state o) c k tails added := by
  obtain ⟨i, rfl, rfl⟩ := two_surjective c k h
  exact ⟨twoTails o i, twoAdded o i, two_accepted o i⟩

/-- Every separated requested component partition has a checked one-credit record. -/
theorem one_records (o : Fin 44) (c : Labels) (h : c ∈ separatedPartitions) :
    ∃ tails added, OneCreditAccepted (state o) c tails added := by
  obtain ⟨i, rfl⟩ := one_surjective c h
  exact ⟨oneTails o i, oneAdded o i, one_accepted o i⟩

end Gallai.Certificate.ZeroSyndrome.Catalogue
