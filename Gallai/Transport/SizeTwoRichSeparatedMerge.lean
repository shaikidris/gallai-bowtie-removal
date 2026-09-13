import Gallai.Transport.SizeTwoRichArmMerge

/-! # Two-for-two separated carrier reconstruction

One released arm joins a remote endpoint carrier. The other arm receives a
mandatory nonempty tail. Neither released arm is assumed nonempty.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Split the hub carrier and merge only its first arm with a remote path.
The two output paths may meet each other; each is individually simple. -/
theorem sizeTwo_separated_merge (w : B.StarSurvivor)
    (hsep : ¬ B.syndromeStar.Reachable B.completedHub w)
    (P : NonemptyPath B.syndromeStar) (hx : B.completedHub ∈ P.walk.support)
    (hs : P.start ≠ B.completedHub) (ht : B.completedHub ≠ P.finish)
    (Q : NonemptyPath B.syndromeStar) (hQ : Q.finish = w)
    (M : G.Walk (P.takeTo B.completedHub hx hs).walk.reverse.snd.val Q.finish.val)
    {c : V} (T : G.Walk (P.dropFrom B.completedHub hx ht).walk.snd.val c)
    (hM : M.IsPath) (hnM : ¬ M.Nil) (hT : T.IsPath) (hnT : ¬ T.Nil)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = (P.takeTo B.completedHub hx hs).walk.reverse.snd.val ∨
      v.val = Q.finish.val ∨ v.val = B.label 0)
    (htail : ∀ v : B.StarSurvivor, v.val ∈ T.support →
      v.val = (P.dropFrom B.completedHub hx ht).walk.snd.val ∨ v.val = B.label 0) :
    ∃ N₀ N₁ : NonemptyPath G,
      N₀.start = P.start.val ∧ N₀.finish = Q.start.val ∧
      N₁.start = P.finish.val ∧ N₁.finish = c ∧
      ∀ e : Sym2 V, N₀.walk.edges.count e + N₁.walk.edges.count e +
        ([s(B.label 0,(P.takeTo B.completedHub hx hs).walk.reverse.snd.val),
          s(B.label 0,(P.dropFrom B.completedHub hx ht).walk.snd.val)] :
            List (Sym2 V)).count e =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e +
        (Q.walk.edges.map (Sym2.map Subtype.val)).count e +
        M.edges.count e + T.edges.count e := by
  obtain ⟨N₀,hs₀,ht₀,he₀⟩ := B.sizeTwo_rich_arm_merge w hsep
    (P.releaseLeft B.completedHub hx hs)
    (P.releaseLeft_isPath B.completedHub hx hs)
    (P.hub_notMem_releaseLeft B.completedHub hx hs)
    (P.takeTo B.completedHub hx hs).walk.reachable.symm Q hQ M hM hnM hm
  let R := (P.releaseRight B.completedHub hx ht).reverse
  have hxR : B.completedHub ∉ R.support := by
    simpa only [R,SimpleGraph.Walk.support_reverse,List.mem_reverse] using
      P.hub_notMem_releaseRight B.completedHub hx ht
  let N₁ := B.retainedTerminalCarrier B.syndromeStar B.syndromeStar_le_completedStar
    R T (P.releaseRight_isPath B.completedHub hx ht).reverse hT hnT hxR htail
  refine ⟨N₀,N₁,hs₀,ht₀,rfl,rfl,?_⟩
  intro e
  have h₀ := congrArg (List.count e) he₀
  have h₁ := congrArg (List.count e)
    (B.retainedTerminalCarrier_edges B.syndromeStar B.syndromeStar_le_completedStar
      R T (P.releaseRight_isPath B.completedHub hx ht).reverse hT hnT hxR htail)
  have hold := congrArg (fun es : List (Sym2 B.StarSurvivor) =>
    (es.map (Sym2.map Subtype.val)).count e) (P.release_edges B.completedHub hx hs ht)
  change N₁.walk.edges.count e = _ at h₁
  simp only [SimpleGraph.Walk.edges_reverse,List.map_reverse,List.count_reverse,
    List.count_append] at h₀
  simp only [R,SimpleGraph.Walk.edges_reverse,List.map_reverse,List.count_reverse,
    List.count_append] at h₁
  simp only [List.map_append,List.map_cons,List.map_nil,Sym2.map_mk,
    List.count_append] at hold
  change (List.map (Sym2.map Subtype.val) (P.releaseLeft B.completedHub hx hs).edges).count e +
    ([s(B.label 0,(P.takeTo B.completedHub hx hs).walk.reverse.snd.val),
      s(B.label 0,(P.dropFrom B.completedHub hx ht).walk.snd.val)] : List (Sym2 V)).count e +
    (List.map (Sym2.map Subtype.val) (P.releaseRight B.completedHub hx ht).edges).count e =
    (P.walk.edges.map (Sym2.map Subtype.val)).count e at hold
  omega

/-- Mirrored attachment order: join the right released arm to the remote
carrier and put the nonempty tail on the left arm. No reorientation premise
or identity between reverse take/drop operations is needed. -/
theorem sizeTwo_separated_merge_right (w : B.StarSurvivor)
    (hsep : ¬ B.syndromeStar.Reachable B.completedHub w)
    (P : NonemptyPath B.syndromeStar) (hx : B.completedHub ∈ P.walk.support)
    (hs : P.start ≠ B.completedHub) (ht : B.completedHub ≠ P.finish)
    (Q : NonemptyPath B.syndromeStar) (hQ : Q.finish = w)
    (M : G.Walk (P.dropFrom B.completedHub hx ht).walk.snd.val Q.finish.val)
    {c : V} (T : G.Walk (P.takeTo B.completedHub hx hs).walk.reverse.snd.val c)
    (hM : M.IsPath) (hnM : ¬ M.Nil) (hT : T.IsPath) (hnT : ¬ T.Nil)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = (P.dropFrom B.completedHub hx ht).walk.snd.val ∨
      v.val = Q.finish.val ∨ v.val = B.label 0)
    (htail : ∀ v : B.StarSurvivor, v.val ∈ T.support →
      v.val = (P.takeTo B.completedHub hx hs).walk.reverse.snd.val ∨ v.val = B.label 0) :
    ∃ N₀ N₁ : NonemptyPath G,
      N₀.start = P.finish.val ∧ N₀.finish = Q.start.val ∧
      N₁.start = P.start.val ∧ N₁.finish = c ∧
      ∀ e : Sym2 V, N₀.walk.edges.count e + N₁.walk.edges.count e +
        ([s(B.label 0,(P.takeTo B.completedHub hx hs).walk.reverse.snd.val),
          s(B.label 0,(P.dropFrom B.completedHub hx ht).walk.snd.val)] :
            List (Sym2 V)).count e =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e +
        (Q.walk.edges.map (Sym2.map Subtype.val)).count e +
        M.edges.count e + T.edges.count e := by
  let R := (P.releaseRight B.completedHub hx ht).reverse
  have hxR : B.completedHub ∉ R.support := by
    simpa only [R,SimpleGraph.Walk.support_reverse,List.mem_reverse] using
      P.hub_notMem_releaseRight B.completedHub hx ht
  obtain ⟨N₀,hs₀,ht₀,he₀⟩ := B.sizeTwo_rich_arm_merge w hsep R
    (P.releaseRight_isPath B.completedHub hx ht).reverse hxR
    (P.dropFrom B.completedHub hx ht).walk.reachable Q hQ M hM hnM hm
  let L := P.releaseLeft B.completedHub hx hs
  let N₁ := B.retainedTerminalCarrier B.syndromeStar B.syndromeStar_le_completedStar
    L T (P.releaseLeft_isPath B.completedHub hx hs) hT hnT
    (P.hub_notMem_releaseLeft B.completedHub hx hs) htail
  refine ⟨N₀,N₁,hs₀,ht₀,rfl,rfl,?_⟩
  intro e
  have h₀ := congrArg (List.count e) he₀
  have h₁ := congrArg (List.count e)
    (B.retainedTerminalCarrier_edges B.syndromeStar B.syndromeStar_le_completedStar
      L T (P.releaseLeft_isPath B.completedHub hx hs) hT hnT
      (P.hub_notMem_releaseLeft B.completedHub hx hs) htail)
  have hold := congrArg (fun es : List (Sym2 B.StarSurvivor) =>
    (es.map (Sym2.map Subtype.val)).count e) (P.release_edges B.completedHub hx hs ht)
  change N₁.walk.edges.count e = _ at h₁
  simp only [R,SimpleGraph.Walk.edges_reverse,List.map_reverse,List.count_reverse,
    List.count_append] at h₀
  simp only [L,List.count_append] at h₁
  simp only [List.map_append,List.map_cons,List.map_nil,Sym2.map_mk,
    List.count_append] at hold
  change (List.map (Sym2.map Subtype.val) (P.releaseLeft B.completedHub hx hs).edges).count e +
    ([s(B.label 0,(P.takeTo B.completedHub hx hs).walk.reverse.snd.val),
      s(B.label 0,(P.dropFrom B.completedHub hx ht).walk.snd.val)] : List (Sym2 V)).count e +
    (List.map (Sym2.map Subtype.val) (P.releaseRight B.completedHub hx ht).edges).count e =
    (P.walk.edges.map (Sym2.map Subtype.val)).count e at hold
  omega

end Gallai.WholeBowtie
