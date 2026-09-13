import Gallai.Transport.SizeTwoRichTerminalConsumer
import Gallai.Transport.SizeTwoRichSelection
import Gallai.Foundations.DegreeTwoCarriers
import Gallai.Operations.Orient
import Gallai.Transport.SizeTwoHubSelection
import Mathlib.Data.Fin.Tuple.Embedding

/-! # Automatic carrier selection for the ordinary rich terminal interface -/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Two actual spoke owners and three remote endpoint owners give the terminal
reconstruction without any caller-selected carrier or orientation premise. -/
theorem sizeTwo_rich_terminal_selected (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (i : Fin 4) (hi : Rich.isThrough i = false)
    (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
    (h : Rich.AcceptedRecord (B.completedStarState A) i words added)
    (D : Decomposition B.syndromeStar) (he : D.endpointCount B.completedHub = 2)
    (w : B.StarSurvivor) (hwlabel : w.val = B.completedLabel A (Rich.reserve i))
    (hsep : ¬ B.syndromeStar.Reachable B.completedHub w)
    (hw : 3 ≤ D.endpointCount w) :
    ∃ P : Decomposition G, P.size ≤ D.size + 1 ∧
      ∀ v : B.StarSurvivor, (∀ t, B.completedLabel A t ≠ v.val) →
        D.endpointCount v ≤ P.endpointCount v.val := by
  classical
  let E := D.orientToward w
  let H := E.orientToward B.completedHub
  let p := B.completedOutside (A 0).val (B.numberedAnchor_not_mem A 0)
  let q := B.completedOutside (A 1).val (B.numberedAnchor_not_mem A 1)
  have hn : (A 0).val ≠ (A 1).val := by
    intro ha
    exact (by decide : (0 : Fin 4) ≠ 1) (A.injective (Subtype.ext ha))
  have hd := B.syndromeStar_hub_degree_two (by simp [hSigma,hn])
  have hp : B.syndromeStar.Adj B.completedHub p :=
    (B.syndromeStar_hub_adj p).mpr (by simp [hSigma,p,completedOutside])
  have hq : B.syndromeStar.Adj B.completedHub q :=
    (B.syndromeStar_hub_adj q).mpr (by simp [hSigma,q,completedOutside])
  have hpq : p ≠ q := fun he => hn (congrArg (fun v : B.StarSurvivor => v.val) he)
  have heE : E.endpointCount B.completedHub = 2 :=
    (D.orientToward_endpointCount w B.completedHub).trans he
  obtain ⟨ip,iq,hpqI,hxp,hpmark,hxq,hqmark,havoid⟩ :=
    E.degree_two_terminal_spoke_selection B.completedHub p q hd heE hp hq hpq
  obtain ⟨f,hf⟩ := B.sizeTwo_rich_carrier_selection D w hsep hw
  have hwE (l : Fin 3) : (E.path (f l)).finish = w :=
    D.orientToward_terminal w (f l) (hf l).1
  have hfree (l : Fin 3) : B.completedHub ∉ (E.path (f l)).walk.support := by
    intro hx
    exact hsep (hwE l ▸ ((E.path (f l)).walk.dropUntil B.completedHub hx).reachable)
  have hwH (l : Fin 3) : (H.path (f l)).finish = w := by
    have hs : (E.path (f l)).start ≠ B.completedHub := by
      intro he
      exact hfree l (he ▸ (E.path (f l)).walk.start_mem_support)
    change ((E.path (f l)).toward B.completedHub).finish = w
    rw [(E.path (f l)).toward_of_start_ne B.completedHub hs]
    exact hwE l
  have hxpE : B.completedHub ∈ (E.path ip).walk.support :=
    ((E.path ip).mem_toward_support B.completedHub B.completedHub).mp
      (by
        have hfinish : (H.path ip).finish = B.completedHub := hxp
        exact (congrArg (fun v => v ∈ (H.path ip).walk.support) hfinish).mp
          (H.path ip).walk.end_mem_support)
  have hxqE : B.completedHub ∈ (E.path iq).walk.support :=
    ((E.path iq).mem_toward_support B.completedHub B.completedHub).mp
      (by
        have hfinish : (H.path iq).finish = B.completedHub := hxq
        exact (congrArg (fun v => v ∈ (H.path iq).walk.support) hfinish).mp
          (H.path iq).walk.end_mem_support)
  have hip : ip ∉ Set.range f := by
    rintro ⟨l,hl⟩
    exact hfree l (hl ▸ hxpE)
  have hiq : iq ∉ Set.range f := by
    rintro ⟨l,hl⟩
    exact hfree l (hl ▸ hxqE)
  let jq : Fin 4 ↪ Fin H.size := Fin.Embedding.cons f hiq
  have hipq : ip ∉ Set.range jq := by
    rintro ⟨l,hl⟩
    rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨r,rfl⟩
    · change iq = ip at hl
      exact hpqI hl.symm
    · change f r = ip at hl
      exact hip ⟨r,hl⟩
  let j : Fin 5 ↪ Fin H.size := Fin.Embedding.cons jq hipq
  have havoidH : ∀ k, k ≠ j 0 → k ≠ j 1 → B.completedHub ∉ (H.path k).walk.support := by
    intro k hkp hkq hk
    exact havoid k hkp hkq (((E.path k).mem_toward_support B.completedHub B.completedHub).mp hk)
  have hpm : (H.path (j 0)).walk.reverse.snd.val = B.completedLabel A .p :=
    congrArg Subtype.val hpmark
  have hqm : (H.path (j 1)).walk.reverse.snd.val = B.completedLabel A .q :=
    congrArg Subtype.val hqmark
  obtain ⟨P,hsize,hend⟩ := B.sizeTwo_rich_terminal_consumer A hSigma i hi words added h
    H j w hwlabel hsep hxp hxq hpm hqm havoidH hwH
  refine ⟨P,hsize,?_⟩
  intro v hv
  have hcounts : H.endpointCount v = D.endpointCount v :=
    (E.orientToward_endpointCount B.completedHub v).trans (D.orientToward_endpointCount w v)
  exact hcounts.symm.trans_le (hend v hv)

end Gallai.WholeBowtie
