/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRichThroughConsumer
import Gallai.Transport.SizeTwoRichSelection
import Gallai.Foundations.DegreeTwoCarriers
import Gallai.Operations.Orient
import Mathlib.Data.Fin.Tuple.Embedding

/-! # Automatic selection for the rich through reconstruction

Three endpoint occurrences in the remote component select distinct carriers.
Uniform orientation preserves every endpoint count. The degree-two passing
hub then supplies the unique fourth carrier, so no selection premise remains.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The complete ordinary rich-through interface, from endpoint supply rather
than caller-selected carriers, with one extra path and outside endpoint reserves. -/
theorem sizeTwo_rich_through_selected (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (i : Fin 4) (hi : Rich.isThrough i = true)
    (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
    (h : Rich.AcceptedRecord (B.completedStarState A) i words added)
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
  have hk : k ∉ Set.range f := by
    rintro ⟨l,hl⟩
    exact (hf l).2 k hxD |>.1 <| hl.symm
  let j : Fin 4 ↪ Fin E.size := Fin.Embedding.cons f hk
  have hfinish : ∀ l : Fin 3, (E.path (j l.succ)).finish = w := by
    intro l
    exact D.orientToward_terminal w (f l) (hf l).1
  obtain ⟨P,hsize,hend⟩ := B.sizeTwo_rich_through_consumer A hSigma i hi words added h
    E j w hwlabel hsep hx hs ht havoid hfinish
  refine ⟨P,hsize,?_⟩
  intro v hv
  have hEv := D.orientToward_endpointCount w v
  exact hEv.symm.trans_le (hend v hv)

end Gallai.WholeBowtie
