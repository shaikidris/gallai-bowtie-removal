import Gallai.Transport.SizeTwoRichReconstruction

/-! # One-added-path assembly for the separated rich interface

This consumes an explicitly balanced reconstructed family. Constructing that
family from the two actual old carriers remains the consumer's obligation.
Unlike ordinary rich assembly, no absent old slot is assumed or credited.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : B.AnchorNumbering) (i : Fin 4)
variable (connector tail : List Star.Vertex) (added : List (List Star.Vertex))
variable (h : Rich.SeparatedAccepted (B.completedStarState A) i connector tail added)

include h in
/-- The separated record partitions the original local edges, including both
mandatory replacements and all at-most-one additional paths. -/
theorem sizeTwo_separated_local_edge_sum (e : Sym2 V) :
    ((wordEdges connector).map (Sym2.map (B.completedLabel A))).count e +
    ((wordEdges tail).map (Sym2.map (B.completedLabel A))).count e +
    (∑ k : Fin added.length,
      ((wordEdges added[k]).map (Sym2.map (B.completedLabel A))).count e) =
    ((CompletedStar.targetEdges (B.completedStarState A)).val.map
      (Sym2.map (B.completedLabel A))).count e := by
  have hc := congrArg (fun m : Multiset (Sym2 Star.Vertex) =>
    (m.map (Sym2.map (B.completedLabel A))).count e) h.2.2.2.1.2
  simp only [Multiset.map_coe,Multiset.coe_count] at hc
  rw [familyEdges,List.map_flatMap,List.count_flatMap] at hc
  dsimp only [Function.comp_def] at hc
  simp only [List.cons_append,List.nil_append,List.map_cons,List.sum_cons] at hc
  rw [← List.ofFn_getElem_eq_map added
    (fun w => ((wordEdges w).map (Sym2.map (B.completedLabel A))).count e),
    List.sum_ofFn] at hc
  rw [Nat.add_assoc]
  convert hc using 1
  congr 2

/-- Each added word in the separated certificate is an actual original path. -/
noncomputable def sizeTwoSeparatedAddedPath (k : Fin added.length) : NonemptyPath G :=
  B.realizeOriginalMember A ([connector,tail] ++ added) h.2.2.2.1 added[k]
    (List.mem_append_right _ (List.getElem_mem _))

include h in
/-- Transport an accounted two-for-two family without a fictitious saved slot.
Exact graph coverage follows from the finite record and auxiliary edge balance. -/
theorem sizeTwo_separated_assemble
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (D : Decomposition B.syndromeStar) (F : Fin D.size → Option (NonemptyPath G))
    (hbalance : ∀ e : Sym2 V,
      (∑ l, ((F l).map (fun P => P.walk.edges.count e)).getD 0) +
        ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e =
      (∑ l, ((D.path l).walk.edges.map (Sym2.map Subtype.val)).count e) +
        ((wordEdges connector).map (Sym2.map (B.completedLabel A))).count e +
        ((wordEdges tail).map (Sym2.map (B.completedLabel A))).count e) :
    ∃ P : Decomposition G, P.size ≤ D.size + 1 ∧
      ∀ v : V, (∑ l, ((F l).map (fun Q => (if Q.start = v then 1 else 0) +
        (if Q.finish = v then 1 else 0 : ℕ))).getD 0) ≤ P.endpointCount v := by
  have hc : ∀ e ∈ G.edgeSet,
      (∑ l, ((F l).map (fun P => P.walk.edges.count e)).getD 0) +
      (∑ l : Fin added.length,
        (B.sizeTwoSeparatedAddedPath A i connector tail added h l).walk.edges.count e) = 1 := by
    intro e he
    have ha : (∑ l : Fin added.length,
        (B.sizeTwoSeparatedAddedPath A i connector tail added h l).walk.edges.count e) =
        ∑ l : Fin added.length,
          ((wordEdges added[l]).map (Sym2.map (B.completedLabel A))).count e := by
      apply Finset.sum_congr rfl
      intro l _
      exact congrArg (List.count e)
        (B.realizeOriginalMember_edges A _ h.2.2.2.1 added[l] _)
    have hf := hbalance e
    have hl := B.sizeTwo_separated_local_edge_sum A i connector tail added h e
    have hg := B.sizeTwo_original_edge_balance A hSigma D e he
    omega
  obtain ⟨P,hsize,hend⟩ := Decomposition.optional_append F
    (B.sizeTwoSeparatedAddedPath A i connector tail added h) hc
  refine ⟨P,by have := h.2.2.2.2; omega,?_⟩
  intro v
  rw [hend]
  exact Nat.le_add_right _ _

end Gallai.WholeBowtie
