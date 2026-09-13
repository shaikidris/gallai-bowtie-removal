/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.WordRoles

/-! # Soundness of normalized local reconstruction records

This joins exact edge coverage, ordered attachment roles, the number of added
paths and protected endpoint demands. It proves a local decomposition, not
the ambient substitution or coverage of every required input interface.
-/

namespace Gallai.Certificate

variable {V : Type*} [DecidableEq V]

/-- A normalized record keeps every role's allowed vertices explicit and
preserves role occurrences even when their boundary data coincide. -/
def RecordAccepted (edges : Finset (Sym2 V)) (roles : List (List V × Finset V))
    (replacements added : List (List V)) (budget : ℕ)
    (marked : Finset V) (required : V → ℕ) : Prop :=
  Accepted edges (replacements ++ added) ∧
    List.Forall₂ (fun role word => Compatible role.1 role.2 word) roles replacements ∧
    added.length ≤ budget ∧
    ∀ v ∈ marked, required v ≤ endpoints (replacements ++ added) v

instance (edges : Finset (Sym2 V)) (roles : List (List V × Finset V))
    (replacements added : List (List V)) (budget : ℕ)
    (marked : Finset V) (required : V → ℕ) :
    Decidable (RecordAccepted edges roles replacements added budget marked required) := by
  unfold RecordAccepted
  infer_instance

/-- Record acceptance supplies a single local graph decomposition with its
local role-plus-addition budget and all protected endpoint demands together.
The role count is not asserted to equal the number of old ambient carriers. -/
theorem record_sound (edges : Finset (Sym2 V)) (roles : List (List V × Finset V))
    (replacements added : List (List V)) (budget : ℕ)
    (marked : Finset V) (required : V → ℕ)
    (h : RecordAccepted edges roles replacements added budget marked required)
    (G : SimpleGraph V) (hG : ∀ e, e ∈ edges ↔ e ∈ G.edgeSet) :
    ∃ D : Decomposition G, D.size = replacements.length + added.length ∧
      D.size ≤ roles.length + budget ∧
      ∀ v ∈ marked, required v ≤ D.endpointCount v := by
  refine ⟨h.1.toDecomposition G hG, ?_, ?_, ?_⟩
  · simp only [Accepted.toDecomposition_size, List.length_append]
  · have hlen := h.2.1.length_eq
    simp only [Accepted.toDecomposition_size, List.length_append]
    exact Nat.add_le_add (Nat.le_of_eq hlen.symm) h.2.2.1
  · intro v hv
    rw [h.1.toDecomposition_endpointCount]
    exact h.2.2.2 v hv

end Gallai.Certificate
