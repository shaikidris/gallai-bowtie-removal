/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRichWords

/-! # Match the rich connector words to either actual through orientation

Both connectors end at the same remote reserve. Swapping which connector is
assigned to which released arm preserves their total edge contribution and
does not reverse either old reserve carrier.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Every accepted rich through record supplies actual connectors for either
order of its two released attachments. The edge sum and support restrictions
are those required by sizeTwo_rich_through_family. -/
theorem sizeTwo_rich_connectors (A : B.AnchorNumbering) (i : Fin 4)
    (hi : Rich.isThrough i = true) (words : Fin 4 → List Star.Vertex)
    (added : List (List Star.Vertex))
    (h : Rich.AcceptedRecord (B.completedStarState A) i words added)
    (b c w : B.StarSurvivor) (hw : w.val = B.completedLabel A (Rich.reserve i))
    (hpair : (b.val = B.completedLabel A .p ∧ c.val = B.completedLabel A .q) ∨
      (b.val = B.completedLabel A .q ∧ c.val = B.completedLabel A .p)) :
    ∃ M₀ : G.Walk b.val w.val, ∃ M₁ : G.Walk c.val w.val,
      M₀.IsPath ∧ ¬ M₀.Nil ∧ M₁.IsPath ∧ ¬ M₁.Nil ∧
      (∀ e : Sym2 V, M₀.edges.count e + M₁.edges.count e =
        ((wordEdges (words 0)).map (Sym2.map (B.completedLabel A))).count e +
        ((wordEdges (words 1)).map (Sym2.map (B.completedLabel A))).count e) ∧
      (∀ v : B.StarSurvivor, v.val ∈ M₀.support →
        v.val = b.val ∨ v.val = w.val ∨ v.val = B.label 0) ∧
      (∀ v : B.StarSurvivor, v.val ∈ M₁.support →
        v.val = c.val ∨ v.val = w.val ∨ v.val = B.label 0) := by
  have hn₀ : words 0 ≠ [] := by
    intro he
    exact Rich.mandatory_nonempty i 0 (Or.inl rfl) (he ▸ h.1 0)
  have hn₁ : words 1 ≠ [] := by
    intro he
    exact Rich.mandatory_nonempty i 1 (Or.inr ⟨hi,rfl⟩) (he ▸ h.1 1)
  have hb₀ : Rich.boundary i 0 = [.p,Rich.reserve i] := by simp [Rich.boundary,hi]
  have hb₁ : Rich.boundary i 1 = [.q,Rich.reserve i] := by simp [Rich.boundary,hi]
  have role (j : Fin 4) (hj : words j ≠ []) (u : Star.Vertex)
      (hb : Rich.boundary i j = [u,Rich.reserve i])
      (a : B.StarSurvivor) (ha : a.val = B.completedLabel A u) :
      ∃ M : G.Walk a.val w.val, M.IsPath ∧ ¬ M.Nil ∧
        M.edges = (wordEdges (words j)).map (Sym2.map (B.completedLabel A)) ∧
        ∀ v : B.StarSurvivor, v.val ∈ M.support →
          v.val = a.val ∨ v.val = w.val ∨ v.val = B.label 0 := by
    let Q := B.sizeTwoRichRole A i words added h j hj
    obtain ⟨hQs,hQt,hQv⟩ := B.sizeTwoRichRole_pair A i words added h j hj u (Rich.reserve i) hb
    have hs : Q.start = a.val := hQs.trans ha.symm
    have ht : Q.finish = w.val := hQt.trans hw.symm
    refine ⟨Q.walk.copy hs ht,(SimpleGraph.Walk.isPath_copy _ _ _).mpr Q.isPath,?_,?_,?_⟩
    · simpa only [SimpleGraph.Walk.nil_copy] using Q.nonempty
    · exact (SimpleGraph.Walk.edges_copy Q.walk hs ht).trans
        (B.sizeTwoRichRole_edges A i words added h j hj)
    · intro v hv
      rw [SimpleGraph.Walk.support_copy] at hv
      simpa only [← ha,← hw] using hQv v hv
  rcases hpair with ⟨hb,hc⟩ | ⟨hb,hc⟩
  · obtain ⟨M₀,hM₀,hm₀,he₀,hv₀⟩ := role 0 hn₀ .p hb₀ b hb
    obtain ⟨M₁,hM₁,hm₁,he₁,hv₁⟩ := role 1 hn₁ .q hb₁ c hc
    exact ⟨M₀,M₁,hM₀,hm₀,hM₁,hm₁,fun e => by rw [he₀,he₁],hv₀,hv₁⟩
  · obtain ⟨M₀,hM₀,hm₀,he₀,hv₀⟩ := role 1 hn₁ .q hb₁ b hb
    obtain ⟨M₁,hM₁,hm₁,he₁,hv₁⟩ := role 0 hn₀ .p hb₀ c hc
    refine ⟨M₀,M₁,hM₀,hm₀,hM₁,hm₁,?_,hv₀,hv₁⟩
    intro e
    rw [he₀,he₁,Nat.add_comm]

end Gallai.WholeBowtie
