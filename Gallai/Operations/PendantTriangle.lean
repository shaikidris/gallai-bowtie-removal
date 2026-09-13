/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.AttachedMerge
import Gallai.Operations.DecompositionMap
import Mathlib.Tactic.FinCases

/-! # Restore a pendant triangle at cost one

The two private vertices are isolated in the old graph. The hub only needs
an incident old edge, not a terminal old carrier. Exposed-vertex gluing
handles the through-carrier case and preserves every old endpoint count.
-/

namespace Gallai

private def triangleLong : NonemptyPath (⊤ : SimpleGraph (Fin 3)) where
  start := 0
  finish := 2
  walk := .cons (show (⊤ : SimpleGraph (Fin 3)).Adj 0 1 by decide)
    (.cons (show (⊤ : SimpleGraph (Fin 3)).Adj 1 2 by decide) .nil)
  isPath := by simp [SimpleGraph.Walk.cons_isPath_iff]
  nonempty := SimpleGraph.Walk.not_nil_cons

private def triangleShort : NonemptyPath (⊤ : SimpleGraph (Fin 3)) where
  start := 2
  finish := 0
  walk := .cons (by decide) .nil
  isPath := by simp [SimpleGraph.Walk.cons_isPath_iff]
  nonempty := SimpleGraph.Walk.not_nil_cons

/-- Two simple paths partition a triangle and expose its zero-labelled vertex twice. -/
def triangleDecomposition : Decomposition (⊤ : SimpleGraph (Fin 3)) where
  size := 2
  path i := if i = 0 then triangleLong else triangleShort
  covers := by
    intro e
    induction e using Sym2.inductionOn with
    | _ a b =>
      change a ≠ b → ∃! i : Fin 2,
        s(a, b) ∈ (if i = 0 then triangleLong else triangleShort).walk.edges
      intro hab
      fin_cases a <;> fin_cases b
      all_goals first
        | exact (hab rfl).elim
        | (refine ⟨0, by decide, ?_⟩
           intro i hi
           fin_cases i
           · rfl
           · simp [triangleShort] at hi)
        | (refine ⟨1, by decide, ?_⟩
           intro i hi
           fin_cases i
           · simp [triangleLong] at hi
           · rfl)

/-- The chosen triangle interface has two paths and two exposed hub endpoints. -/
theorem triangleDecomposition_profile : triangleDecomposition.size = 2 ∧
    triangleDecomposition.endpointCount 0 = 2 := by decide

namespace Decomposition

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Restore a fresh pendant triangle at exactly one additional path, preserving
all endpoint multiplicities away from its two private vertices, including the hub. -/
theorem attach_pendant_triangle (D : Decomposition G) (f : Fin 3 ↪ V)
    (h1 : ∀ v, ¬ G.Adj (f 1) v) (h2 : ∀ v, ¬ G.Adj (f 2) v)
    (hx : ∃ v, G.Adj (f 0) v) :
    ∃ E : Decomposition ((⊤ : SimpleGraph (Fin 3)).map f ⊔ G),
      E.size = D.size + 1 ∧
      ∀ v, v ≠ f 1 → v ≠ f 2 → E.endpointCount v = D.endpointCount v := by
  classical
  let T := triangleDecomposition.map f
  have ht : T.endpointCount (f 0) = 2 := by
    rw [map_endpointCount]
    exact triangleDecomposition_profile.2
  have meet (w : V) (ha : ∃ a, ((⊤ : SimpleGraph (Fin 3)).map f).Adj w a)
      (hb : ∃ b, G.Adj w b) : w = f 0 := by
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    obtain ⟨i, j, _, hi, _⟩ := (SimpleGraph.map_adj f ⊤ w a).mp ha
    subst w
    fin_cases i
    · rfl
    · exact (h1 b hb).elim
    · exact (h2 b hb).elim
  obtain ⟨E, hs, he⟩ := T.glue_at_exposed_vertex D (f 0) (by omega) hx meet
  have hsize : T.size = 2 := rfl
  refine ⟨E, by omega, ?_⟩
  intro v hv1 hv2
  have h := he v
  by_cases hv0 : v = f 0
  · subst v
    simp only [ht, ite_true] at h
    omega
  · have hnot : v ∉ Set.range f := by
      rintro ⟨i, rfl⟩
      fin_cases i
      · exact hv0 rfl
      · exact hv1 rfl
      · exact hv2 rfl
    have hz : T.endpointCount v = 0 := map_endpointCount_of_notMem_range _ f v hnot
    simp only [hz, if_neg (Ne.symm hv0)] at h
    omega

end Decomposition
end Gallai
