/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarCatalogue
import Gallai.Certificates.CompletedStarSymmetry

/-! # All symmetry images of the stored catalogue

The result uses the literal transformed incidence state. It does not yet
assert that the symmetry images exhaust the full labelled-state domain.
-/

namespace Gallai.Certificate.CompletedStar.Catalogue

/-- All eight core actions and all anchor permutations preserve record existence
at every requested canonical interface of each stored representative. -/
theorem transformed (o : Fin 67) (k : Fin 8) (σ : Equiv.Perm (Fin 4)) (j : Fin 10) :
    ∃ repl added, AcceptedRecord (transformedState k σ (state o)) j repl added := by
  apply transformed_records k σ (state o) _ j
  intro i
  exact ⟨replacements o i, added o i, accepted o i⟩

end Gallai.Certificate.CompletedStar.Catalogue
