/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoFan
import Gallai.Transport.SizeTwoBoundaryCounts
import Gallai.Operations.DecompositionMap
import Gallai.Operations.Union

/-! # The actual initial decomposition for the Fan exception

The two literal paths are mapped to original vertices and combined with the
syndrome auxiliary. Disjointness is derived from the actual local state and
syndrome, not supplied as a carrier-compatibility hypothesis.
-/
namespace Gallai.WholeBowtie

open Certificate
open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

def sizeTwoFanLabel (A : B.AnchorNumbering) : Star.Vertex ↪ V :=
  ⟨B.completedLabel A, B.completedLabel_injective A⟩

def sizeTwoFanAdded (A : B.AnchorNumbering) : SimpleGraph V :=
  SizeTwo.Fan.initialGraph.map (B.sizeTwoFanLabel A)

def sizeTwoFanAux : SimpleGraph V :=
  B.syndromeStar.map (Function.Embedding.subtype _)

def sizeTwoFanAddedDecomposition (A : B.AnchorNumbering) :
    Decomposition (B.sizeTwoFanAdded A) :=
  SizeTwo.Fan.initialDecomposition.map (B.sizeTwoFanLabel A)

theorem sizeTwoFanAdded_size (A : B.AnchorNumbering) :
    (B.sizeTwoFanAddedDecomposition A).size = 2 := rfl

theorem sizeTwoFanAdded_endpoints (A : B.AnchorNumbering) (v : Star.Vertex) :
    (B.sizeTwoFanAddedDecomposition A).endpointCount (B.completedLabel A v) =
      (if v = .a then 2 else 0) + (if v = .s then 2 else 0) := by
  exact (SizeTwo.Fan.initialDecomposition.map_endpointCount
    (B.sizeTwoFanLabel A) v).trans (SizeTwo.Fan.initialDecomposition_endpoints v)

/-- Only the retained pq spokes can be both local and auxiliary; neither is
used by an initial added path. -/
theorem sizeTwoFan_initial_disjoint (A : B.AnchorNumbering)
    (hstate : B.completedStarState A = SizeTwo.Fan.state)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val}) :
    Disjoint B.sizeTwoFanAux.edgeSet (B.sizeTwoFanAdded A).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e heAux heAdded
  rw [sizeTwoFanAdded, SimpleGraph.edgeSet_map] at heAdded
  obtain ⟨q,hq,rfl⟩ := heAdded
  have hqi := (SizeTwo.Fan.initialGraph_edges q).mpr hq
  have hqt : q ∈ CompletedStar.targetEdges (B.completedStarState A) := by
    rw [hstate, SizeTwo.Fan.target_partition]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hqi)
  have hpre : ∃ f ∈ B.syndromeStar.edgeSet,
      Sym2.map Subtype.val f = Sym2.map (B.completedLabel A) q := by
    rw [sizeTwoFanAux, SimpleGraph.edgeSet_map] at heAux
    obtain ⟨f,hf,he⟩ := heAux
    exact ⟨f,hf,he⟩
  have hspoke := (B.sizeTwo_local_auxiliary_iff A hSigma q hqt).mp hpre
  have hret : q ∈ SizeTwo.Fan.retainedEdges := by
    rcases hspoke with hp | hp
    · have he : q = s(Star.Vertex.x, Star.Vertex.p) :=
        Sym2.map.injective (B.completedLabel_injective A) hp
      simp [he, SizeTwo.Fan.retainedEdges]
    · have he : q = s(Star.Vertex.x, Star.Vertex.q) :=
        Sym2.map.injective (B.completedLabel_injective A) hp
      simp [he, SizeTwo.Fan.retainedEdges]
  exact Finset.disjoint_left.mp SizeTwo.Fan.initial_disjoint_retained hqi hret

/-- The Fan auxiliary receives exactly two new paths. The endpoint vector
is retained on the same witness used by the subsequent restoration. -/
theorem sizeTwoFan_initial_decomposition (A : B.AnchorNumbering)
    (hstate : B.completedStarState A = SizeTwo.Fan.state)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (D : Decomposition B.syndromeStar) :
    ∃ E : Decomposition (B.sizeTwoFanAux ⊔ B.sizeTwoFanAdded A),
      E.size = D.size + 2 ∧ ∀ v,
        E.endpointCount v =
          (D.map (Function.Embedding.subtype _)).endpointCount v +
          (B.sizeTwoFanAddedDecomposition A).endpointCount v := by
  obtain ⟨E,hs,he⟩ := (D.map (Function.Embedding.subtype _)).union_disjoint_endpoints
    (B.sizeTwoFanAddedDecomposition A) (B.sizeTwoFan_initial_disjoint A hstate hSigma)
  exact ⟨E,hs,he⟩

end Gallai.WholeBowtie
