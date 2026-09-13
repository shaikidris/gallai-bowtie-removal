/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRichSeparatedConsumer
import Gallai.Transport.SizeTwoRichSelection
import Gallai.Foundations.DegreeTwoCarriers
import Gallai.Operations.Orient
import Mathlib.Data.Fin.Tuple.Embedding

/-! # Automatic selection for the special separated rich interfaces -/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Select and orient actual carriers, then consume either separated record.
No balanced-family, attachment-order or carrier-index premise remains. -/
theorem sizeTwo_rich_separated_selected (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (i : Fin 4) (connector tail : List Star.Vertex) (added : List (List Star.Vertex))
    (h : Rich.SeparatedAccepted (B.completedStarState A) i connector tail added)
    (D : Decomposition B.syndromeStar) (he : D.endpointCount B.completedHub = 0)
    (w : B.StarSurvivor) (hwlabel : w.val = B.completedLabel A (Rich.reserve i))
    (hsep : ¬ B.syndromeStar.Reachable B.completedHub w)
    (hw : 3 ≤ D.endpointCount w) :
    ∃ P : Decomposition G, P.size ≤ D.size + 1 ∧
      ∀ v : B.StarSurvivor, (∀ t, B.completedLabel A t ≠ v.val) →
        D.endpointCount v ≤ P.endpointCount v.val := by
  classical
  let E := D.orientToward w
  have hn : (A 0).val ≠ (A 1).val := by
    intro ha
    exact (by decide : (0 : Fin 4) ≠ 1) (A.injective (Subtype.ext ha))
  have hd : B.syndromeStar.degree B.completedHub = 2 :=
    B.syndromeStar_hub_degree_two (by simp [hSigma,hn])
  have heE : E.endpointCount B.completedHub = 0 :=
    (D.orientToward_endpointCount w B.completedHub).trans he
  obtain ⟨k,hx,hs,ht,havoid⟩ := E.degree_two_through_carrier B.completedHub hd heE
  obtain ⟨f,hf⟩ := B.sizeTwo_rich_carrier_selection D w hsep hw
  have hxD : B.completedHub ∈ (D.path k).walk.support :=
    ((D.path k).mem_toward_support w B.completedHub).mp hx
  have hk : k ≠ f 0 := (hf 0).2 k hxD |>.1
  let j : Fin 2 ↪ Fin E.size := Function.Embedding.embFinTwo hk
  have hfinish : (E.path (j 1)).finish = w :=
    D.orientToward_terminal w (f 0) (hf 0).1
  obtain ⟨P,hsize,hend⟩ := B.sizeTwo_rich_separated_consumer A hSigma i connector tail added h
    E j w hwlabel hsep hx hs ht havoid hfinish
  refine ⟨P,hsize,?_⟩
  intro v hv
  exact (D.orientToward_endpointCount w v).symm.trans_le (hend v hv)

end Gallai.WholeBowtie
