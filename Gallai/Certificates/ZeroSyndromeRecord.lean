/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStar
import Gallai.Certificates.ZeroSyndromePartitions

/-! # Zero-syndrome record acceptance

Original target edges are the six bowtie edges and the five original incidence
rows. Empty tails leave their old endpoint unchanged. Local edge acceptance
is separate from the two-credit coincident-carrier and one-credit separation
conditions. No graph edges between anchors are changed or checked here.
-/

namespace Gallai.Certificate.ZeroSyndrome

open CompletedStar

/-- One possibly empty outward path word for each of the four anchors. -/
abbrev Tails := Fin 4 → List Star.Vertex

/-- The exact local words consuming edges: omit empty tails, retain every
added path occurrence. Empty added paths are rejected by ordinary acceptance. -/
def localWords (tails : Tails) (added : List (List Star.Vertex)) : List (List Star.Vertex) :=
  (List.ofFn tails).filter (fun w => !w.isEmpty) ++ added

/-- An outward tail may leave its attachment only for deleted vertices or
anchors in another original component. -/
def TailAllowed (components : Labels) (i : Fin 4) (word : List Star.Vertex) : Prop :=
  word = [] ∨ (word.head? = some (anchor i) ∧
    ∀ v ∈ word.tail, v ∈ Star.fresh ∨
      ∃ j : Fin 4, components j ≠ components i ∧ v = anchor j)

instance (c : Labels) (i : Fin 4) (word : List Star.Vertex) :
    Decidable (TailAllowed c i word) := by
  unfold TailAllowed
  infer_instance

/-- Shared edge/simplicity/freshness contract of both zero-syndrome branches. -/
def RecordCore (state : State) (components : Labels) (tails : Tails)
    (added : List (List Star.Vertex)) : Prop :=
  Accepted (targetEdges state) (localWords tails added) ∧
    ∀ i, TailAllowed components i (tails i)

instance (state : State) (c : Labels) (tails : Tails) (added : List (List Star.Vertex)) :
    Decidable (RecordCore state c tails added) := by
  unfold RecordCore
  infer_instance

/-- Two-credit records permit two tails on one old carrier only when their
post-attachment vertex sets are disjoint. -/
def TwoCreditAccepted (state : State) (components carriers : Labels) (tails : Tails)
    (added : List (List Star.Vertex)) : Prop :=
  (components, carriers) ∈ interfaces ∧ RecordCore state components tails added ∧
    added.length ≤ 2 ∧ ∀ i j, i ≠ j → carriers i = carriers j →
      (tails i).tail.Disjoint (tails j).tail

/-- One-credit records extend at most one anchor in each original component. -/
def OneCreditAccepted (state : State) (components : Labels) (tails : Tails)
    (added : List (List Star.Vertex)) : Prop :=
  components ∈ separatedPartitions ∧ RecordCore state components tails added ∧
    added.length ≤ 1 ∧ ∀ i j, i ≠ j → tails i ≠ [] → tails j ≠ [] →
      components i ≠ components j

instance (state : State) (c k : Labels) (tails : Tails) (added : List (List Star.Vertex)) :
    Decidable (TwoCreditAccepted state c k tails added) := by
  unfold TwoCreditAccepted List.Disjoint
  infer_instance

instance (state : State) (c : Labels) (tails : Tails) (added : List (List Star.Vertex)) :
    Decidable (OneCreditAccepted state c tails added) := by
  unfold OneCreditAccepted
  infer_instance

/-- A nonempty accepted tail is a genuine simple path word, not a trail. -/
theorem RecordCore.tail_simple {state : State} {c : Labels} {tails : Tails}
    {added : List (List Star.Vertex)} (h : RecordCore state c tails added)
    (i : Fin 4) (hi : tails i ≠ []) : 2 ≤ (tails i).length ∧ (tails i).Nodup := by
  apply h.1.1
  apply List.mem_append_left
  apply List.mem_filter.mpr
  exact ⟨List.mem_ofFn.mpr ⟨i, rfl⟩, by simpa using hi⟩

end Gallai.Certificate.ZeroSyndrome
