/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoForcedConsumer
import Gallai.Certificates.SizeTwoForcedCoverage

/-! # Every forced catalogue tag is consumed on its actual passing profile

The stored state and profile select a checked forced word record. Its transport
returns an original-graph decomposition and designated endpoint reserve.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- All 34 forced records have actual graph consumers, rather than merely
finite edge-partition proofs. The profile is the one obtained from D. -/
theorem sizeTwo_catalogue_forced_endpoint (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (o : Fin 234) (i : Fin 13) (hstate : B.completedStarState A = Catalogue.state o)
    (hkind : Catalogue.kind o i = .forcedEndpoints)
    (D : Decomposition B.syndromeStar) (f : Fin 4 → Fin D.size)
    (hf : ∀ r : Fin 2,
      (D.path (f (remoteRole i r))).start = B.sizeTwoRemoteMarks A r ∨
      (D.path (f (remoteRole i r))).finish = B.sizeTwoRemoteMarks A r)
    (howner : ∀ j k, j ≠ 3 → k ≠ 3 → (f j = f k ↔ owner i j = owner i k))
    (hx : B.completedHub ∈ (D.path (f 0)).walk.support)
    (hs : (D.path (f 0)).start ≠ B.completedHub)
    (ht : B.completedHub ≠ (D.path (f 0)).finish)
    (havoid : ∀ k, k ≠ f 0 → B.completedHub ∉ (D.path k).walk.support)
    (budget : ℕ) (hbudget : D.size + 2 ≤ budget)
    (y : B.StarSurvivor) (hyout : y.val ∉ B.vertices) (hy : Even (G.degree y.val))
    (hyD : 2 ≤ D.endpointCount y) :
    ∃ P : Decomposition G, P.size ≤ budget ∧ 2 ≤ P.endpointCount y.val := by
  have hi := Catalogue.nonbasic_profile o i (fun hb => by rw [hb] at hkind; cases hkind)
  subst i
  obtain ⟨j,hrecord⟩ := Catalogue.forced_record o 0 hkind
  rw [← hstate] at hrecord
  obtain ⟨P,_,hP,hend⟩ := B.sizeTwo_forced_profile_zero A hSigma D f hf howner hx hs ht havoid
    (Forced.Catalogue.extraIndex j) (Forced.Catalogue.connector j) (Forced.Catalogue.extra j)
    (Forced.Catalogue.tail j) (Forced.Catalogue.added j) hrecord
  exact ⟨P,hP.trans hbudget,hyD.trans (hend y hyout hy)⟩

end Gallai.WholeBowtie
