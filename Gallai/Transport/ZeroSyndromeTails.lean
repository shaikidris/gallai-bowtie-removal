/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ZeroSyndromeInterface
import Gallai.Transport.EndpointTails

/-! # Certificate freshness in the actual ambient graph

The verifier permits post-attachment tail vertices in the deleted bowtie or
among anchors outside the old carrier's component. The latter restriction
concerns the entire old path, not only its chosen endpoint.
-/

namespace Gallai.WholeBowtie

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- View a whole-deletion carrier as a path in the original graph. -/
def punctureCarrier (P : NonemptyPath B.puncture) : NonemptyPath G :=
  P.map ⟨Subtype.val, fun h => h⟩ Subtype.val_injective

omit [DecidableEq V] in
/-- The original vertex list is exactly the subtype projection. -/
theorem punctureCarrier_support (P : NonemptyPath B.puncture) :
    (B.punctureCarrier P).walk.support = P.walk.support.map Subtype.val := by
  exact P.map_support _ _

/-- The certificate's allowed tail vertices avoid every vertex of the actual
chosen carrier. No restriction on original edges between anchors is used. -/
theorem allowed_tail_avoids_puncture_carrier (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (a : B.anchors) (tail : List V)
    (ht : ∀ v ∈ tail, v ∈ B.vertices ∨
      ∃ b : B.anchors, B.anchorComponent a ≠ B.anchorComponent b ∧ v = b.val) :
    tail.Disjoint (B.punctureCarrier (D.path (f a))).walk.support := by
  intro v hvt hvc
  rw [B.punctureCarrier_support] at hvc
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hvc
  rcases ht w.val hvt with hB | ⟨b, hab, he⟩
  · exact w.property hB
  · have hwB : w = B.anchorPunctureVertex b := Subtype.ext he
    exact B.other_component_anchor_avoids_carrier D f hf a b hab (hwB ▸ hw)

end Gallai.WholeBowtie
