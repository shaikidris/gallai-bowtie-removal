/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.SizeTwoNormalization
import Gallai.Transport.SizeTwoCatalogueTwoCredit
import Gallai.Inputs.SyndromeStarMixedCredit

/-! # The remaining size-two obligation is a normalized one-credit reserve

Normalize the actual bowtie before choosing an auxiliary decomposition.
Low activity and the entire two-credit branch are discharged. What remains
is an explicit high-activity representative with a disconnected rich anchor.
This reduction does not claim to have proved the one-credit reconstruction.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- For every actual four-anchor size-two graph, either the required endpoint
conclusion holds or the precise one-credit reserve instance exists. -/
theorem sizeTwo_endpoint_or_rich_representative (hA : B.anchors.card = 4)
    (hs : B.syndrome.card = 2) (hc : G.Connected) (y : V) (hyout : y ∉ B.vertices)
    (hy : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y → eDegree G v ≤ 3) :
    (∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ P.endpointCount y) ∨
    ∃ R : WholeBowtie G, ∃ A : R.AnchorNumbering, ∃ o : Fin 234,
      R.label 0 = B.label 0 ∧ R.vertices = B.vertices ∧ 3 ≤ R.activity ∧
      R.syndrome = {(A 0).val,(A 1).val} ∧ R.completedStarState A = Catalogue.state o ∧
      ∃ z : R.StarSurvivor, z.val = y ∧ ∃ D : Decomposition R.syndromeStar,
        2 ≤ D.endpointCount z ∧ D.size + 1 ≤ (Fintype.card V + 1) / 2 ∧
        ∃ w : R.StarSurvivor, w.val ∈ R.anchors ∧ w.val ∉ R.syndrome ∧
          ¬ R.syndromeStar.Reachable R.completedHub w ∧ 3 ≤ D.endpointCount w := by
  classical
  obtain ⟨R,hRh,hRv,A,o,hSigma,hstate⟩ := B.sizeTwo_normalized_representative hA hs
  have hyR : y ∉ R.vertices := by rwa [hRv]
  have hcapR : ∀ v, Even (G.degree v) → v ≠ R.label 0 → v ≠ y → eDegree G v ≤ 3 := by
    intro v hev hvx hvy
    exact hcap v hev (by simpa only [hRh] using hvx) hvy
  by_cases hlow : R.activity ≤ 2
  · exact Or.inl (R.low_activity_endpoint hlow hc y hyR hy hcapR)
  have hhigh : 3 ≤ R.activity := by omega
  let z : R.StarSurvivor := R.completedOutside y hyR
  have hx : z.val ≠ R.label 0 := by
    intro he
    apply hyR
    change y = R.label 0 at he
    rw [he]
    exact Finset.mem_map.mpr ⟨0,Finset.mem_univ _,rfl⟩
  have hAR : R.anchors.card = 4 := by
    simpa only [Fintype.card_coe,Fintype.card_fin] using (Fintype.card_congr A).symm
  have hne : (A 0).val ≠ (A 1).val := by
    intro he
    exact (by decide : (0 : Fin 4) ≠ 1) (A.injective (Subtype.ext he))
  have hSR : R.syndrome.card = 2 := by simp [hSigma,hne]
  obtain ⟨D,hyD,hcredits⟩ := R.syndromeStar_mixed_credit hc (Nat.le_of_eq hAR) hSR
    z hx hy hcapR
  rcases hcredits with htwo | ⟨hone,w,hwA,hwS,hwC,hwD⟩
  · exact Or.inl (R.sizeTwo_catalogue_two_credit A hSigma o hstate hc z hyR hy hcapR D htwo hyD)
  · exact Or.inr ⟨R,A,o,hRh,hRv,hhigh,hSigma,hstate,z,rfl,D,hyD,hone,w,hwA,hwS,hwC,hwD⟩

end Gallai.WholeBowtie
