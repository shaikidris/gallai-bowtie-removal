/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoOrdinary

/-! # Explicit ordinary catalogue branch tags

A tag is data, not an exceptional transport theorem. Only basic records are
consumed by the existing ordinary reconstruction contract.
-/
namespace Gallai.Certificate.SizeTwo.Catalogue

/-- Distinct proof obligations in the two-credit certificate catalogue. -/
inductive RecordKind where
  | basic
  | forcedEndpoints
  | fan
  | twoEar
  deriving DecidableEq, Repr

end Gallai.Certificate.SizeTwo.Catalogue
