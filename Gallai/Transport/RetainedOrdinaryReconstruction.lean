/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedPassingReconstruction
import Gallai.Transport.RetainedEndingReconstruction

/-! # Ordinary retained reconstruction without an endpoint-profile assumption -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The passing and one-tail terminal records together consume every
decomposition of the ordinary retained auxiliary, not a favourable choice. -/
theorem retainedOrdinary_reconstruction
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
    (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)
    (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj] (repair : Bool)
    (hAdj : ∀ u v, H.Adj u v ↔ G.Adj u.val v.val ∧
      ¬ (repair = true ∧ s(u.val,v.val) = s((A 1).val,(A 2).val)))
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (D : Decomposition H)
    (connector tail : List Vertex) (passingAdded endingAdded : List (List Vertex))
    (hpassing : RetainedPassingAccepted s repair connector passingAdded)
    (hending : RetainedEndingAccepted s repair [tail] endingAdded) :
    ∃ E : Decomposition G, E.size ≤ D.size + 2 ∧
      ∀ w : B.StarSurvivor, w ≠ B.completedHub → D.endpointCount w ≤ E.endpointCount w.val := by
  by_cases hz : D.endpointCount B.completedHub = 0
  · obtain ⟨E, _, hb, he⟩ := B.retainedPassing_reconstruction A s hrows H repair
      hAdj hp D hz connector passingAdded hpassing
    exact ⟨E, hb, fun w _ => he w⟩
  · obtain ⟨E, _, hb, he⟩ := B.retainedEnding_reconstruction A s hrows H repair
      hAdj hp D (Nat.pos_of_ne_zero hz) tail endingAdded hending
    exact ⟨E, hb, he⟩

/-- All six normalized ordinary catalogue rows now have profile-independent
ambient reconstruction. Orbit coverage remains a separate obligation. -/
theorem retainedOrdinary_representative
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 6)
    (hrows : ∀ j v, v ∈ B.row j ↔
      ∃ k, (rowMask (Retained.state i j)).val.testBit k.val = true ∧ (A k).val = v)
    (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj]
    (hAdj : ∀ u v, H.Adj u v ↔ G.Adj u.val v.val ∧
      ¬ (Retained.repair i = true ∧ s(u.val,v.val) = s((A 1).val,(A 2).val)))
    (hp : Retained.repair i = true → G.Adj (A 1).val (A 2).val)
    (D : Decomposition H) :
    ∃ E : Decomposition G, E.size ≤ D.size + 2 ∧
      ∀ w : B.StarSurvivor, w ≠ B.completedHub → D.endpointCount w ≤ E.endpointCount w.val :=
  B.retainedOrdinary_reconstruction A (Retained.state i) hrows H (Retained.repair i)
    hAdj hp D (Retained.passing i) [0,2,1] (Retained.passingAdded i) (Retained.endingAdded i)
    (Retained.passing_checked i) (Retained.ending_checked i)

end Gallai.WholeBowtie
