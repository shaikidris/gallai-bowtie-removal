/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoForcedCatalogueConsumer
import Gallai.Transport.SizeTwoFanConsumer
import Gallai.Transport.SizeTwoLowActivityException
import Gallai.Transport.SizeTwoOrdinaryConsumer

/-! # Every representative catalogue state consumes two actual credits

Choose the interface from the actual auxiliary decomposition, then dispatch
its literal record kind. This includes all exceptional cases and does not
assume a favourable profile or an accepted basic record.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The complete representative catalogue gives the Gallai endpoint bound
whenever the actual syndrome decomposition has two reconstruction credits. -/
theorem sizeTwo_catalogue_two_credit (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (o : Fin 234) (hstate : B.completedStarState A = Catalogue.state o)
    (hc : G.Connected) (y : B.StarSurvivor) (hyout : y.val ∉ B.vertices)
    (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3)
    (D : Decomposition B.syndromeStar)
    (hbudget : D.size + 2 ≤ (Fintype.card V + 1) / 2)
    (hyD : 2 ≤ D.endpointCount y) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ P.endpointCount y.val := by
  have hne : (A 0).val ≠ (A 1).val := by
    intro hh
    exact (by decide : (0 : Fin 4) ≠ 1) (A.injective (Subtype.ext hh))
  have hcard : B.syndrome.card = 2 := by simp [hSigma,hne]
  have hremote (r : Fin 2) : 0 < D.endpointCount (B.sizeTwoRemoteMarks A r) := by
    apply D.endpointCount_pos_of_odd_degree
    apply Nat.not_even_iff_odd.mp
    intro he
    have ho : Odd (G.degree (B.sizeTwoRemoteMarks A r).val) :=
      B.odd_degree_anchor (A ⟨r.val + 2,by omega⟩).property
    exact Nat.not_even_iff_odd.mpr ho ((B.syndromeStar_even_iff _).mp he)
  rcases D.degree_two_carrier_profiles B.completedHub (B.syndromeStar_hub_degree_two hcard) with
    ⟨he,_⟩ | ⟨he,_⟩
  · obtain ⟨f,i,hi,hf,howner,hx,hs,ht,havoid⟩ :=
      B.sizeTwo_auxiliary_passing_profile A hSigma D he (hremote 0) (hremote 1)
    cases hk : Catalogue.kind o i with
    | basic =>
      have hrec := Catalogue.basic_accepted o i hk
      rw [← hstate] at hrec
      obtain ⟨P,_,hP,hend⟩ := B.sizeTwo_passing_reconstruction A hSigma i hi D f hf howner hx hs ht havoid
        (Catalogue.words o i) (Catalogue.added o i) hrec
      exact ⟨P,hP.trans hbudget,hyD.trans (hend y hyout hy)⟩
    | forcedEndpoints =>
      exact B.sizeTwo_catalogue_forced_endpoint A hSigma o i hstate hk D f hf howner hx hs ht havoid
        _ hbudget y hyout hy hyD
    | fan =>
      exact B.sizeTwo_catalogue_fan_endpoint A o i hstate hk hSigma D _ hbudget y hyout hy hyD
    | twoEar =>
      exact B.sizeTwo_twoEar_endpoint A (hstate.trans (Catalogue.twoEar_state o i hk))
        hc y.val hyout hy hcap
  · obtain ⟨E,hsize,hcounts,f,i,hi,hf,howner,hx0,hu0,hx1,hu1,havoid⟩ :=
      B.sizeTwo_auxiliary_terminal_profile A hSigma D he (hremote 0) (hremote 1)
    have hk : Catalogue.kind o i = .basic := by
      by_contra hn
      have hz := Catalogue.nonbasic_profile o i hn
      subst i
      cases hi
    have hrec := Catalogue.basic_accepted o i hk
    rw [← hstate] at hrec
    obtain ⟨P,_,hP,hend⟩ := B.sizeTwo_terminal_reconstruction A hSigma i hi E f hf howner
      hx0 hu0 hx1 hu1 havoid (Catalogue.words o i) (Catalogue.added o i) hrec
    have hbudgetE : E.size + 2 ≤ (Fintype.card V + 1) / 2 := hsize.symm ▸ hbudget
    have hyE : 2 ≤ E.endpointCount y := (hcounts y).symm ▸ hyD
    exact ⟨P,hP.trans hbudgetE,hyE.trans (hend y hyout hy)⟩

end Gallai.WholeBowtie
