/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ZeroSyndromeTailCompatibility

/-! # Assigning accepted tails to actual endpoint slots

An active tail belongs to its chosen old carrier and its original anchor.
Distinct anchors cannot occupy the same endpoint slot. A slot without an
active tail receives a nil walk, not an extra decomposition path.
-/

namespace Gallai.WholeBowtie

open Certificate Certificate.CompletedStar Certificate.ZeroSyndrome
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The literal ownership and attachment condition for an active tail. -/
def ZeroTailAt (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size) (tails : Tails) (k : Fin D.size) (u : V) (j : Fin 4) : Prop :=
  f (A j) = k ∧ (A j).val = u ∧ tails j ≠ []

/-- A single old endpoint slot cannot receive two different anchor tails. -/
theorem zeroTailAt_unique (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size) (tails : Tails) (k : Fin D.size) (u : V)
    (i j : Fin 4) (hi : B.ZeroTailAt A D f tails k u i)
    (hj : B.ZeroTailAt A D f tails k u j) : i = j :=
  A.injective (Subtype.ext (hi.2.1.trans hj.2.1.symm))

/-- The unique active word at a slot, or the empty word for an unchanged slot. -/
noncomputable def zeroAssignedWord (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size) (tails : Tails) (k : Fin D.size) (u : V) : List Star.Vertex := by
  classical
  exact if h : ∃ j, B.ZeroTailAt A D f tails k u j then tails (Classical.choose h) else []

/-- Every active tail is recovered at its own slot; choice loses no occurrence. -/
theorem zeroAssignedWord_at (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size) (tails : Tails) (k : Fin D.size) (u : V)
    (j : Fin 4) (hj : B.ZeroTailAt A D f tails k u j) :
    B.zeroAssignedWord A D f tails k u = tails j := by
  classical
  have he : ∃ i, B.ZeroTailAt A D f tails k u i := ⟨j, hj⟩
  rw [zeroAssignedWord, dif_pos he]
  rw [B.zeroTailAt_unique A D f tails k u _ j (Classical.choose_spec he) hj]

/-- Retype a selected active tail at its actual endpoint slot. -/
noncomputable def zeroActiveTail (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size) (tails : Tails) (added : List (List Star.Vertex))
    (h : RecordCore (B.completedStarState A) (B.zeroComponentLabels A) tails added)
    (k : Fin D.size) (u : V) (j : Fin 4) (hj : B.ZeroTailAt A D f tails k u j) :
    Σ v : V, G.Walk u v :=
    let P := B.realizeZeroTail A (B.zeroComponentLabels A) tails added h j hj.2.2
    ⟨P.finish, P.walk.copy ((B.realizeZeroTail_start A (B.zeroComponentLabels A)
      tails added h j hj.2.2).trans hj.2.1) rfl⟩

/-- An outward walk with its possibly new end; a missing tail is a nil walk. -/
noncomputable def zeroAssignedTail (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size) (tails : Tails) (added : List (List Star.Vertex))
    (h : RecordCore (B.completedStarState A) (B.zeroComponentLabels A) tails added)
    (k : Fin D.size) (u : V) : Σ v : V, G.Walk u v := by
  classical
  exact if he : ∃ j, B.ZeroTailAt A D f tails k u j then
    B.zeroActiveTail A D f tails added h k u (Classical.choose he) (Classical.choose_spec he)
  else ⟨u, .nil⟩

theorem zeroAssignedTail_pos (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size) (tails : Tails) (added : List (List Star.Vertex))
    (h : RecordCore (B.completedStarState A) (B.zeroComponentLabels A) tails added)
    (k : Fin D.size) (u : V) (he : ∃ j, B.ZeroTailAt A D f tails k u j) :
    B.zeroAssignedTail A D f tails added h k u =
      B.zeroActiveTail A D f tails added h k u (Classical.choose he) (Classical.choose_spec he) :=
  dif_pos he

theorem zeroAssignedTail_neg (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size) (tails : Tails) (added : List (List Star.Vertex))
    (h : RecordCore (B.completedStarState A) (B.zeroComponentLabels A) tails added)
    (k : Fin D.size) (u : V) (he : ¬∃ j, B.ZeroTailAt A D f tails k u j) :
    B.zeroAssignedTail A D f tails added h k u = ⟨u, .nil⟩ := dif_neg he

/-- Every assigned outward walk is simple, including untouched slots. -/
theorem zeroAssignedTail_isPath (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size) (tails : Tails) (added : List (List Star.Vertex))
    (h : RecordCore (B.completedStarState A) (B.zeroComponentLabels A) tails added)
    (k : Fin D.size) (u : V) :
    (B.zeroAssignedTail A D f tails added h k u).2.IsPath := by
  classical
  by_cases he : ∃ j, B.ZeroTailAt A D f tails k u j
  · rw [B.zeroAssignedTail_pos A D f tails added h k u he]
    simp only [zeroActiveTail, SimpleGraph.Walk.isPath_copy]
    exact (B.realizeZeroTail A (B.zeroComponentLabels A) tails added h _ _).isPath
  · rw [B.zeroAssignedTail_neg A D f tails added h k u he]
    simp

/-- The assigned walk contributes exactly its assigned local-word edges. -/
theorem zeroAssignedTail_edges (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size) (tails : Tails) (added : List (List Star.Vertex))
    (h : RecordCore (B.completedStarState A) (B.zeroComponentLabels A) tails added)
    (k : Fin D.size) (u : V) :
    (B.zeroAssignedTail A D f tails added h k u).2.edges =
      (Certificate.wordEdges (B.zeroAssignedWord A D f tails k u)).map
        (Sym2.map (B.completedLabel A)) := by
  classical
  by_cases he : ∃ j, B.ZeroTailAt A D f tails k u j
  · rw [B.zeroAssignedTail_pos A D f tails added h k u he]
    simp only [zeroAssignedWord, dif_pos he, zeroActiveTail,
      SimpleGraph.Walk.edges_copy]
    exact B.realizeOriginalMember_edges A _ h.1 _ _
  · rw [B.zeroAssignedTail_neg A D f tails added h k u he]
    simp [zeroAssignedWord, he, Certificate.wordEdges]

/-- Post-attachment support is exactly the mapped assigned word tail, also
for an unchanged slot where both sides are empty. -/
theorem zeroAssignedTail_support_tail (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size) (tails : Tails) (added : List (List Star.Vertex))
    (h : RecordCore (B.completedStarState A) (B.zeroComponentLabels A) tails added)
    (k : Fin D.size) (u : V) :
    (B.zeroAssignedTail A D f tails added h k u).2.support.tail =
      (B.zeroAssignedWord A D f tails k u).tail.map (B.completedLabel A) := by
  classical
  by_cases he : ∃ j, B.ZeroTailAt A D f tails k u j
  · rw [B.zeroAssignedTail_pos A D f tails added h k u he]
    simp only [zeroAssignedWord, dif_pos he, List.map_tail]
    exact congrArg List.tail ((SimpleGraph.Walk.support_copy
      (B.realizeZeroTail A (B.zeroComponentLabels A) tails added h
        (Classical.choose he) (Classical.choose_spec he).2.2).walk _ rfl).trans
      (B.realizeOriginalMember_support A _ h.1 _ _))
  · rw [B.zeroAssignedTail_neg A D f tails added h k u he]
    simp [zeroAssignedWord, he]

end Gallai.WholeBowtie
