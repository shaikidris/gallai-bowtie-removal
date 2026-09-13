/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.Profiles

/-!
# Endpoint locations in the fixed star certificates

All terminal replacements finish at a private vertex. The two added words
have explicit endpoint pairs, supplying the entire new endpoint count at the
released hub. These statements concern the same words as the edge certificates.
-/

namespace Gallai.Star

/-- Every terminal replacement ends at a private vertex, never at an old anchor or hub. -/
theorem Profile.terminalWord_last_private (p : Profile) (i : Fin p.terminals) :
    ∃ v ∈ [Vertex.a, .b, .c, .d], (p.terminalWord i).getLast? = some v := by
  cases p <;> dsimp [Profile.terminals] at i
  · exact Fin.elim0 i
  · fin_cases i <;> decide
  · fin_cases i <;> decide

/-- Explicit endpoint symbols of either additional word. -/
def Profile.addedEnds (p : Profile) (i : Fin 2) : Vertex × Vertex :=
  match p with
  | .zero => (.a, .d)
  | .two => (.x, .a)
  | .four => if i.val = 0 then (.d, .a) else (.c, .b)

/-- The explicit endpoint pair belongs to the actual indexed added word. -/
theorem Profile.addedEnds_correct (p : Profile) (i : Fin 2) :
    (p.added[i.val]'(by rw [p.valid.2.1]; exact i.isLt)).head? =
        some (p.addedEnds i).1 ∧
      (p.added[i.val]'(by rw [p.valid.2.1]; exact i.isLt)).getLast? =
        some (p.addedEnds i).2 := by
  cases p <;> fin_cases i <;> decide

end Gallai.Star
