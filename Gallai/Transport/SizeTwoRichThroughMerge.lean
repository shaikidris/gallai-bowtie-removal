/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRichArmMerge

/-! # The two joined carriers in the one-credit through reconstruction

Two remote endpoint carriers receive the two released arms of the hub carrier.
The three old carriers become two, before adding the remaining local paths.
The statement tracks both endpoint pairs and every original edge multiplicity.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The through scheme saves one carrier, without imposing mutual support
disjointness on the two reserve paths. Distinctness of their decomposition
indices is supplied separately when assembling the complete family. -/
theorem sizeTwo_rich_through_merge (w : B.StarSurvivor)
    (hsep : ¬ B.syndromeStar.Reachable B.completedHub w)
    (P : NonemptyPath B.syndromeStar) (hx : B.completedHub ∈ P.walk.support)
    (hs : P.start ≠ B.completedHub) (ht : B.completedHub ≠ P.finish)
    (Q₀ Q₁ : NonemptyPath B.syndromeStar) (hQ₀ : Q₀.finish = w) (hQ₁ : Q₁.finish = w)
    (M₀ : G.Walk (P.takeTo B.completedHub hx hs).walk.reverse.snd.val Q₀.finish.val)
    (M₁ : G.Walk (P.dropFrom B.completedHub hx ht).walk.snd.val Q₁.finish.val)
    (hM₀ : M₀.IsPath) (hn₀ : ¬ M₀.Nil) (hM₁ : M₁.IsPath) (hn₁ : ¬ M₁.Nil)
    (hm₀ : ∀ v : B.StarSurvivor, v.val ∈ M₀.support →
      v.val = (P.takeTo B.completedHub hx hs).walk.reverse.snd.val ∨
      v.val = Q₀.finish.val ∨ v.val = B.label 0)
    (hm₁ : ∀ v : B.StarSurvivor, v.val ∈ M₁.support →
      v.val = (P.dropFrom B.completedHub hx ht).walk.snd.val ∨
      v.val = Q₁.finish.val ∨ v.val = B.label 0) :
    ∃ N₀ N₁ : NonemptyPath G,
      N₀.start = P.start.val ∧ N₀.finish = Q₀.start.val ∧
      N₁.start = P.finish.val ∧ N₁.finish = Q₁.start.val ∧
      ∀ e : Sym2 V, N₀.walk.edges.count e + N₁.walk.edges.count e +
        ([s(B.label 0, (P.takeTo B.completedHub hx hs).walk.reverse.snd.val),
          s(B.label 0, (P.dropFrom B.completedHub hx ht).walk.snd.val)] :
            List (Sym2 V)).count e =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e +
        (Q₀.walk.edges.map (Sym2.map Subtype.val)).count e +
        (Q₁.walk.edges.map (Sym2.map Subtype.val)).count e +
        M₀.edges.count e + M₁.edges.count e := by
  obtain ⟨N₀, hs₀, ht₀, he₀⟩ := B.sizeTwo_rich_arm_merge w hsep
    (P.releaseLeft B.completedHub hx hs)
    (P.releaseLeft_isPath B.completedHub hx hs)
    (P.hub_notMem_releaseLeft B.completedHub hx hs)
    (P.takeTo B.completedHub hx hs).walk.reachable.symm Q₀ hQ₀ M₀ hM₀ hn₀ hm₀
  have hxR : B.completedHub ∉ (P.releaseRight B.completedHub hx ht).reverse.support := by
    simpa using P.hub_notMem_releaseRight B.completedHub hx ht
  obtain ⟨N₁, hs₁, ht₁, he₁⟩ := B.sizeTwo_rich_arm_merge w hsep
    (P.releaseRight B.completedHub hx ht).reverse
    (P.releaseRight_isPath B.completedHub hx ht).reverse hxR
    (P.dropFrom B.completedHub hx ht).walk.reachable Q₁ hQ₁ M₁ hM₁ hn₁ hm₁
  refine ⟨N₀, N₁, hs₀, ht₀, hs₁, ht₁, ?_⟩
  intro e
  have h₀ := congrArg (fun es : List (Sym2 V) => es.count e) he₀
  have h₁ := congrArg (fun es : List (Sym2 V) => es.count e) he₁
  have hold := congrArg (fun es : List (Sym2 B.StarSurvivor) =>
    (es.map (Sym2.map Subtype.val)).count e) (P.release_edges B.completedHub hx hs ht)
  simp only [SimpleGraph.Walk.edges_reverse, List.map_reverse, List.count_reverse,
    List.count_append] at h₀ h₁
  simp only [List.map_append, List.map_cons, List.map_nil, Sym2.map_mk,
    List.count_append] at hold
  change (List.map (Sym2.map Subtype.val) (P.releaseLeft B.completedHub hx hs).edges).count e +
    ([s(B.label 0, (P.takeTo B.completedHub hx hs).walk.reverse.snd.val),
      s(B.label 0, (P.dropFrom B.completedHub hx ht).walk.snd.val)] : List (Sym2 V)).count e +
    (List.map (Sym2.map Subtype.val) (P.releaseRight B.completedHub hx ht).edges).count e =
    (P.walk.edges.map (Sym2.map Subtype.val)).count e at hold
  omega

end Gallai.WholeBowtie
