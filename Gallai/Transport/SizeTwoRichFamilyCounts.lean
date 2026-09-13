/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRichThroughFamily
import Gallai.Operations.FamilyBalance

/-! # Lift the actual rich through group to whole-family edge counts

The group consists of four old carriers and three new carriers. The fourth
output slot is absent. All unselected carriers are mapped unchanged; their
counts cancel through the grouped conservation theorem.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Exact whole-family conservation after the actual three-for-four carrier
replacement. Removed spokes and local words remain explicit until the
original-graph boundary balance cancels them. -/
theorem sizeTwo_rich_through_family_counts (D : Decomposition B.syndromeStar)
    (j : Fin 4 ↪ Fin D.size) (N₀ N₁ N₂ : NonemptyPath G)
    (F : Fin D.size → Option (NonemptyPath G))
    (hselected : ∀ l, F (j l) = ![some N₀,none,some N₁,some N₂] l)
    (hother : ∀ k, (∀ l, j l ≠ k) →
      ∃ hk : B.completedHub ∉ (D.path k).walk.support,
        F k = some (B.syndromeAvoidingPath (D.path k) hk))
    (removed localEdges : List (Sym2 V))
    (hgroup : ∀ e : Sym2 V,
      N₀.walk.edges.count e + N₁.walk.edges.count e + N₂.walk.edges.count e + removed.count e =
        (∑ l : Fin 4, ((D.path (j l)).walk.edges.map (Sym2.map Subtype.val)).count e) +
        localEdges.count e) :
    ∀ e : Sym2 V,
      (∑ k, ((F k).map (fun P => P.walk.edges.count e)).getD 0) + removed.count e =
        (∑ k, ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e) +
        localEdges.count e := by
  intro e
  apply sum_grouped_balance
    (fun k => ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e)
    (fun k => ((F k).map (fun P => P.walk.edges.count e)).getD 0) j
  · have hsum : (∑ l : Fin 4, ((F (j l)).map (fun P => P.walk.edges.count e)).getD 0) =
        N₀.walk.edges.count e + N₁.walk.edges.count e + N₂.walk.edges.count e := by
      simp_rw [hselected]
      simp [Fin.sum_univ_succ,Nat.add_assoc]
    rw [hsum]
    exact hgroup e
  · intro k hk
    obtain ⟨hfree,hF⟩ := hother k hk
    rw [hF]
    exact congrArg (List.count e) (B.syndromeAvoidingPath_edges (D.path k) hfree)

end Gallai.WholeBowtie
