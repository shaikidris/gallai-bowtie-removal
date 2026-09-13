/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCatalogue
import Gallai.Certificates.SizeTwoCatalogueRows

/-! # Agreement of lightweight coverage rows and checked certificate rows

The expensive finite coverage reductions need only literal rows. This exact
bridge connects that lightweight table back to the accepted-record registry.
-/
namespace Gallai.Certificate.SizeTwo.Catalogue

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Lightweight coverage and the checked record registry refer to identical rows. -/
theorem state_eq_rows (o : Fin 234) : state o = Rows.state o := by
  fin_cases o <;> rfl

end Gallai.Certificate.SizeTwo.Catalogue
