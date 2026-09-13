/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoOrdinary

/-! # Exhaustive finite carrier partitions for the ordinary size-two interface

Actual carrier selection must still establish the terminal restrictions:
two distinct x-terminal paths, neither having both r and s as other endpoints.
This module proves the finite partition classification once those hold.
-/
namespace Gallai.Certificate.SizeTwo

def ValidOwners (passing : Bool) (f : Fin 4 → Fin 4) : Prop :=
  passing = true ∨ (f 0 ≠ f 1 ∧
    ¬ (f 2 = f 0 ∧ f 3 = f 0) ∧ ¬ (f 2 = f 1 ∧ f 3 = f 1))

def SamePartition (passing : Bool) (f g : Fin 4 → Fin 4) : Prop :=
  ∀ j k, (passing = true → j ≠ 3 ∧ k ≠ 3) → (f j = f k ↔ g j = g k)

instance (b : Bool) (f : Fin 4 → Fin 4) : Decidable (ValidOwners b f) := by
  unfold ValidOwners; infer_instance
instance (b : Bool) (f g : Fin 4 → Fin 4) : Decidable (SamePartition b f g) := by
  unfold SamePartition; infer_instance

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-- Every abstract owner assignment satisfying the literal terminal endpoint
restrictions is represented among the five through/eight terminal profiles. -/
theorem owner_partition_complete : ∀ b : Bool, ∀ f : Fin 4 → Fin 4,
    ValidOwners b f → ∃ i : Fin 13, through i = b ∧ SamePartition b f (owner i) := by
  decide

/-- Every listed terminal profile satisfies the endpoint restrictions. -/
theorem owner_partition_valid : ∀ i : Fin 13, ValidOwners (through i) (owner i) := by
  decide

end Gallai.Certificate.SizeTwo
