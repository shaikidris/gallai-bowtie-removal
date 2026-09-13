/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ComposableBowties
import Gallai.Inputs.OneException
import Gallai.Inputs.FloorOrSET
import Gallai.Inputs.SETReserve

/-! # The zero-bowtie base of the simultaneous composition induction -/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A subcubic even graph gives the undesignated ceiling conclusion. -/
theorem base_none (hc : G.Connected)
    (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3) :
    Conclusion G none := by
  apply conclusion_none.mpr
  rcases floor_or_set G hc hcap with ⟨D, hD⟩ | hs
  · exact ⟨D, hD.trans (Nat.div_le_div_right (Nat.le_succ _))⟩
  · obtain ⟨u⟩ := hc.nonempty
    obtain ⟨D, hD, _⟩ := hs.endpoint_reserve u
    exact ⟨D, hD⟩

/-- The designated base uses the proved endpoint theorem, retaining positivity. -/
theorem base_some (hc : G.Connected) (y : V) (hy : Even (G.degree y))
    (hp : 0 < G.degree y)
    (hcap : ∀ v, Even (G.degree v) → v ≠ y → eDegree G v ≤ 3) :
    Conclusion G (some y) :=
  (conclusion_some y).mpr (one_exception_endpoint G y hc hp hy hcap)

/-- Both zero-family cases are discharged on one optional-designation interface. -/
theorem empty_family (hc : G.Connected) (Bs : Fin 0 → WholeBowtie G)
    (designated : Option V) (h : Admissible Bs designated) :
    Conclusion G designated := by
  cases designated with
  | none => exact base_none hc ((admissible_empty_none Bs).mp h)
  | some y =>
    obtain ⟨⟨hy, hp⟩, hcap⟩ := (admissible_empty_some Bs y).mp h
    exact base_some hc y hy hp hcap

end Gallai.Composition
