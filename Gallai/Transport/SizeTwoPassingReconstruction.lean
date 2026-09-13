/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoPassingFamily
import Gallai.Transport.SizeTwoReconstruction
import Gallai.Transport.SizeTwoEndpointReserve

/-! # Accepted ordinary passing records reconstruct the original graph -/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Actual passing-family construction supplies global coverage and preserves
every even outside endpoint reserve on the SAME reconstructed decomposition.
Catalogue coverage remains a separate obligation. -/
theorem sizeTwo_passing_reconstruction (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (i : Fin 13) (hi : through i = true)
    (D : Decomposition B.syndromeStar) (f : Fin 4 → Fin D.size)
    (hf : ∀ r : Fin 2,
      (D.path (f (remoteRole i r))).start = B.sizeTwoRemoteMarks A r ∨
      (D.path (f (remoteRole i r))).finish = B.sizeTwoRemoteMarks A r)
    (howner : ∀ j k, j ≠ 3 → k ≠ 3 → (f j = f k ↔ owner i j = owner i k))
    (hx : B.completedHub ∈ (D.path (f 0)).walk.support)
    (hs : (D.path (f 0)).start ≠ B.completedHub)
    (ht : B.completedHub ≠ (D.path (f 0)).finish)
    (havoid : ∀ k, k ≠ f 0 → B.completedHub ∉ (D.path k).walk.support)
    (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
    (h : OrdinaryAccepted (B.completedStarState A) i words added) :
    ∃ P : Decomposition G, P.size = D.size + added.length ∧ P.size ≤ D.size + 2 ∧
      ∀ w : B.StarSurvivor, w.val ∉ B.vertices → Even (G.degree w.val) →
        D.endpointCount w ≤ P.endpointCount w.val := by
  classical
  obtain ⟨F,hF⟩ := B.sizeTwo_passing_family A hSigma i hi D f hf howner hx hs ht havoid words added h
  let removed : Fin D.size → List (Sym2 V) := fun k =>
    if k = f 0 then [s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] else []
  have hcarrier : ∀ k e, (F k).walk.edges.count e + (removed k).count e =
      ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e +
      ∑ j : Fin 4, if f j = k then
        ((wordEdges (words j)).map (Sym2.map (B.completedLabel A))).count e else 0 := by
    intro k e
    by_cases hk : k = f 0 <;> simpa [removed,hk] using (hF k).2.2 e
  have hremoved : ∀ e, (∑ k : Fin D.size, (removed k).count e) =
      ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e := by
    intro e
    rw [Finset.sum_eq_single (f 0)]
    · simp [removed]
    · intro k _ hk
      simp [removed,hk]
    · simp
  refine ⟨B.sizeTwoReconstruction A hSigma i words added h D f F removed hcarrier hremoved,
    B.sizeTwoReconstruction_size A hSigma i words added h D f F removed hcarrier hremoved,
    B.sizeTwoReconstruction_budget A hSigma i words added h D f F removed hcarrier hremoved,?_⟩
  intro w hout hw
  apply B.sizeTwoReconstruction_endpoint_reserve A i words added h hSigma D f F removed hcarrier hremoved w
  intro k
  exact B.sizeTwo_optional_endpoint_contribution A i words added h D f hf k (F k)
    (hF k).1 (hF k).2.1 w (B.zero_even_outside_labels A ⟨w.val,hout⟩ hw)

end Gallai.WholeBowtie
