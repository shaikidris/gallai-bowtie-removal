import Gallai.Transport.SizeTwoRichSeparatedAssembly

/-! # Actual connector and tail from a separated certificate -/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The two mandatory words supply nonempty original paths, their attachment
endpoints, permitted old support, and exact edges. The tail cannot end at an
outside-label vertex whose endpoint reserve must be preserved. -/
theorem sizeTwo_separated_words (A : B.AnchorNumbering) (i : Fin 4)
    (connector tail : List Star.Vertex) (added : List (List Star.Vertex))
    (h : Rich.SeparatedAccepted (B.completedStarState A) i connector tail added) :
    ∃ C T : NonemptyPath G,
      C.start = B.completedLabel A .p ∧
      C.finish = B.completedLabel A (Rich.reserve i) ∧
      T.start = B.completedLabel A .q ∧
      (∀ v : B.StarSurvivor, v.val ∈ C.walk.support →
        v.val = B.completedLabel A .p ∨
        v.val = B.completedLabel A (Rich.reserve i) ∨ v.val = B.label 0) ∧
      (∀ v : B.StarSurvivor, v.val ∈ T.walk.support →
        v.val = B.completedLabel A .q ∨ v.val = B.label 0) ∧
      C.walk.edges = (wordEdges connector).map (Sym2.map (B.completedLabel A)) ∧
      T.walk.edges = (wordEdges tail).map (Sym2.map (B.completedLabel A)) ∧
      ∀ v : V, (∀ t, B.completedLabel A t ≠ v) → T.finish ≠ v := by
  have hcMem : connector ∈ [connector,tail] ++ added := by simp
  have htMem : tail ∈ [connector,tail] ++ added := by simp
  let C := B.realizeOriginalMember A ([connector,tail] ++ added) h.2.2.2.1 connector hcMem
  let T := B.realizeOriginalMember A ([connector,tail] ++ added) h.2.2.2.1 tail htMem
  have hcSupport : C.walk.support = connector.map (B.completedLabel A) :=
    B.realizeOriginalMember_support A _ h.2.2.2.1 _ _
  have htSupport : T.walk.support = tail.map (B.completedLabel A) :=
    B.realizeOriginalMember_support A _ h.2.2.2.1 _ _
  have hcs : C.start = B.completedLabel A .p := by
    have he := congrArg List.head? hcSupport
    rw [List.head?_map,h.2.1.1] at he
    rw [List.head?_eq_some_head (by simp),SimpleGraph.Walk.head_support] at he
    exact Option.some.inj he
  have hct : C.finish = B.completedLabel A (Rich.reserve i) := by
    have he := congrArg List.getLast? hcSupport
    rw [List.getLast?_map,h.2.1.2.1] at he
    rw [List.getLast?_eq_some_getLast (by simp),SimpleGraph.Walk.getLast_support] at he
    exact Option.some.inj he
  have hts : T.start = B.completedLabel A .q := by
    have he := congrArg List.head? htSupport
    rw [List.head?_map,h.2.2.1.1] at he
    rw [List.head?_eq_some_head (by simp),SimpleGraph.Walk.head_support] at he
    exact Option.some.inj he
  refine ⟨C,T,hcs,hct,hts,?_,?_,?_,?_,?_⟩
  · intro v hv
    rw [hcSupport] at hv
    obtain ⟨t,ht,htv⟩ := List.mem_map.mp hv
    rcases compatible_pair_support h.2.1 ht with he | he | hf
    · exact Or.inl (htv.symm.trans (congrArg (B.completedLabel A) he))
    · exact Or.inr (Or.inl (htv.symm.trans (congrArg (B.completedLabel A) he)))
    · exact Or.inr (Or.inr (B.survivor_mem_vertices v
        (htv ▸ B.completedLabel_fresh A t hf)))
  · intro v hv
    rw [htSupport] at hv
    obtain ⟨t,ht,htv⟩ := List.mem_map.mp hv
    rcases compatible_single_support h.2.2.1 ht with he | hf
    · exact Or.inl (htv.symm.trans (congrArg (B.completedLabel A) he))
    · exact Or.inr (B.survivor_mem_vertices v
        (htv ▸ B.completedLabel_fresh A t hf))
  · exact B.realizeOriginalMember_edges A _ h.2.2.2.1 _ _
  · exact B.realizeOriginalMember_edges A _ h.2.2.2.1 _ _
  · intro v hv he
    have hm := T.walk.end_mem_support
    rw [htSupport,he] at hm
    obtain ⟨t,_,ht⟩ := List.mem_map.mp hm
    exact hv t ht

end Gallai.WholeBowtie
