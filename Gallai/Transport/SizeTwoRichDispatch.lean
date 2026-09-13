/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRichThroughSelected
import Gallai.Transport.SizeTwoRichTerminalSelected
import Gallai.Transport.SizeTwoRichSeparatedSelected
import Gallai.Transport.SizeTwoRichRecordSelection

/-! # Exhaustive actual-graph rich profile and record dispatch -/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The graph itself determines the reserve symbol, hub profile and accepted
record. Every resulting ordinary or special record has a compiled consumer. -/
theorem sizeTwo_rich_dispatch (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val}) (ha : 3 ≤ B.activity)
    (o : Fin 234) (hstate : B.completedStarState A = Catalogue.state o)
    (D : Decomposition B.syndromeStar) (w : B.StarSurvivor)
    (hwa : w.val ∈ B.anchors) (hwn : w.val ∉ B.syndrome)
    (hsep : ¬ B.syndromeStar.Reachable B.completedHub w)
    (hw : 3 ≤ D.endpointCount w) :
    ∃ P : Decomposition G, P.size ≤ D.size + 1 ∧
      ∀ v : B.StarSurvivor, (∀ t, B.completedLabel A t ≠ v.val) →
        D.endpointCount v ≤ P.endpointCount v.val := by
  classical
  obtain ⟨b,k,_,records⟩ := B.sizeTwo_rich_records A ha o hstate
  have consume (i : Fin 4) (hl : w.val = B.completedLabel A (Rich.reserve i))
      (hp : (Rich.isThrough i = true ∧ D.endpointCount B.completedHub = 0) ∨
        (Rich.isThrough i = false ∧ D.endpointCount B.completedHub = 2)) :
      ∃ P : Decomposition G, P.size ≤ D.size + 1 ∧
        ∀ v : B.StarSurvivor, (∀ t, B.completedLabel A t ≠ v.val) →
          D.endpointCount v ≤ P.endpointCount v.val := by
    have hr := records i
    split at hr
    · rcases hp with ⟨hi,he⟩ | ⟨hi,he⟩
      · exact B.sizeTwo_rich_separated_selected A hSigma i _ _ _ hr D he w hl hsep hw
      · exact (Bool.false_ne_true (hi.symm.trans hr.1)).elim
    · rcases hp with ⟨hi,he⟩ | ⟨hi,he⟩
      · exact B.sizeTwo_rich_through_selected A hSigma i hi _ _ hr D he w hl hsep hw
      · exact B.sizeTwo_rich_terminal_selected A hSigma i hi _ _ hr D he w hl hsep hw
  have hn : (A 0).val ≠ (A 1).val := by
    intro he
    exact (by decide : (0 : Fin 4) ≠ 1) (A.injective (Subtype.ext he))
  have hd := B.syndromeStar_hub_degree_two (by simp [hSigma,hn])
  have hcount := D.degree_eq_endpoint_add_twice_through B.completedHub
  have he : D.endpointCount B.completedHub = 0 ∨ D.endpointCount B.completedHub = 2 := by
    rw [hd] at hcount
    omega
  have hl : w.val = B.completedLabel A .r ∨ w.val = B.completedLabel A .s := by
    obtain ⟨j,hj⟩ := A.surjective ⟨w.val,hwa⟩
    have hv : (A j).val = w.val := congrArg Subtype.val hj
    fin_cases j
    · exact (hwn (by rw [hSigma]; simp [← hv])).elim
    · exact (hwn (by rw [hSigma]; simp [← hv])).elim
    · exact Or.inl hv.symm
    · exact Or.inr hv.symm
  rcases he with he | he <;> rcases hl with hl | hl
  · exact consume 0 hl (Or.inl ⟨by decide,he⟩)
  · exact consume 1 hl (Or.inl ⟨by decide,he⟩)
  · exact consume 2 hl (Or.inr ⟨by decide,he⟩)
  · exact consume 3 hl (Or.inr ⟨by decide,he⟩)

end Gallai.WholeBowtie
