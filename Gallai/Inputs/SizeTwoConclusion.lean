/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.SizeTwoRichFrontier
import Gallai.Transport.SizeTwoRichDispatch

/-! # Original-graph endpoint theorem for four-anchor size-two syndrome -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Close both credit regimes of the actual graph. No connected-puncture,
chosen auxiliary decomposition or favourable carrier premise is required. -/
theorem sizeTwo_endpoint (hA : B.anchors.card = 4) (hs : B.syndrome.card = 2)
    (hc : G.Connected) (y : V) (hyout : y ∉ B.vertices) (hy : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y → eDegree G v ≤ 3) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ P.endpointCount y := by
  rcases B.sizeTwo_endpoint_or_rich_representative hA hs hc y hyout hy hcap with
    solved | ⟨R,A,o,_,hRv,ha,hSigma,hstate,z,hzy,D,hyD,hbudget,w,hwA,hwS,hsep,hwD⟩
  · exact solved
  · obtain ⟨P,hsize,hend⟩ := R.sizeTwo_rich_dispatch A hSigma ha o hstate D w hwA hwS hsep hwD
    have hyR : y ∉ R.vertices := by rwa [hRv]
    have hlabels : ∀ t, R.completedLabel A t ≠ z.val := by
      simpa only [hzy] using R.zero_even_outside_labels A ⟨y,hyR⟩ hy
    refine ⟨P,hsize.trans hbudget,?_⟩
    have hh := hyD.trans (hend z hlabels)
    simpa only [hzy] using hh

end Gallai.WholeBowtie
