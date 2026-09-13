/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoFamilyAccounting
import Gallai.Transport.SizeTwoBoundaryCounts

/-! # Global reconstruction from actual size-two carrier equations

No global coverage hypothesis is supplied. Per-carrier equations and the
explicit total of released spokes imply unique coverage of the original G.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : B.AnchorNumbering)
variable (hSigma : B.syndrome = {(A 0).val,(A 1).val})
variable (i : Fin 13) (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
variable (h : OrdinaryAccepted (B.completedStarState A) i words added)
variable (D : Decomposition B.syndromeStar) (f : Fin 4 → Fin D.size)
variable (F : Fin D.size → NonemptyPath G) (removed : Fin D.size → List (Sym2 V))
variable (hcarrier : ∀ k e, (F k).walk.edges.count e + (removed k).count e =
  ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e +
  ∑ j : Fin 4, if f j = k then
    ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e else 0)
variable (hremoved : ∀ e, (∑ k : Fin D.size, (removed k).count e) =
  ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e)

include hSigma hcarrier hremoved in
/-- Spoke cancellation converts the supplied LOCAL equations into exact
GLOBAL edge multiplicity one on every original graph edge. -/
theorem sizeTwo_reconstructed_edge_count (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (∑ k : Fin D.size, (F k).walk.edges.count e) +
      (∑ k : Fin added.length, (B.sizeTwoAddedPath A i words added h k).walk.edges.count e) = 1 := by
  have hb := B.sizeTwo_family_balance A i words added h D f F removed hcarrier e
  have hg := B.sizeTwo_original_edge_balance A hSigma D e he
  have hr := hremoved e
  omega

/-- The actual decomposition of G obtained by concatenating the replacement
family and the added certificate paths. Its coverage is derived, not assumed. -/
noncomputable def sizeTwoReconstruction : Decomposition G :=
  Decomposition.ofEdgeCounts
    (fun k : Fin (D.size + added.length) =>
      Sum.elim F (B.sizeTwoAddedPath A i words added h) (finSumFinEquiv.symm k))
    (by
      intro e he
      rw [(finSumFinEquiv : Fin D.size ⊕ Fin added.length ≃ Fin (D.size + added.length)).symm.sum_comp
        (fun k => (Sum.elim F (B.sizeTwoAddedPath A i words added h) k).walk.edges.count e)]
      rw [Fintype.sum_sum_type]
      exact B.sizeTwo_reconstructed_edge_count A hSigma i words added h D f F removed hcarrier hremoved e he)

/-- The exact path count is inherited from the selected record, including
records using fewer than the ordinary two-credit allowance. -/
theorem sizeTwoReconstruction_size :
    (B.sizeTwoReconstruction A hSigma i words added h D f F removed hcarrier hremoved).size =
      D.size + added.length := rfl

/-- Ordinary acceptance gives the two-credit bound for the actual decomposition. -/
theorem sizeTwoReconstruction_budget :
    (B.sizeTwoReconstruction A hSigma i words added h D f F removed hcarrier hremoved).size ≤
      D.size + 2 := Nat.add_le_add_left h.2.2.2 _

end Gallai.WholeBowtie
