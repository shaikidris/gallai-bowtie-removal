/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorStateCode
import Gallai.Certificates.ThreeAnchorRetained

namespace Gallai.Certificate.ThreeAnchor.RetainedOrbits
open Orbits

/-- All eight permutations of the two bowtie pairs fixing the hub. -/
def coreOrder (c : Fin 8) : Fin 5 → Fin 5 :=
  (![![0,1,2,3,4], ![0,2,1,3,4], ![0,1,2,4,3], ![0,2,1,4,3],
     ![0,3,4,1,2], ![0,4,3,1,2], ![0,3,4,2,1], ![0,4,3,2,1]] :
     Fin 8 → Fin 5 → Fin 5) c

/-- All permutations of the three anchor slots, including unused slots. -/
def anchorOrder (a : Fin 6) : Fin 3 → Fin 3 :=
  (![![0,1,2], ![0,2,1], ![1,0,2], ![1,2,0], ![2,0,1], ![2,1,0]] :
    Fin 6 → Fin 3 → Fin 3) a

theorem coreOrder_bijective : ∀ c, Function.Bijective (coreOrder c) := by decide
theorem anchorOrder_bijective : ∀ a, Function.Bijective (anchorOrder a) := by decide
theorem coreOrder_zero : ∀ c, coreOrder c 0 = 0 := by decide

/-- Equality of every incidence bit after a hub-fixing core permutation and
an anchor permutation. This is stronger than equality of aggregate syndromes. -/
def Normalizes (s : State) (r : Fin 6) (c : Fin 8) (a : Fin 6) : Prop :=
  ∀ j : Fin 5, ∀ k : Fin 3,
    (rowMask (s (coreOrder c j))).val.testBit (anchorOrder a k).val =
      (rowMask (Retained.state r j)).val.testBit k.val

instance (s : State) (r : Fin 6) (c : Fin 8) (a : Fin 6) :
    Decidable (Normalizes s r c a) := by unfold Normalizes; infer_instance
end Gallai.Certificate.ThreeAnchor.RetainedOrbits
