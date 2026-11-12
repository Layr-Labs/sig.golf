import SigGolfCandidate.OuterResidualValues
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OuterResidualDisclosure
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open OuterCanonBase
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual
attribute [local instance] Classical.propDecidable
set_option allowUnsafeReducibility true in
attribute [local reducible] OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Coord

def wGroundDisclosed : List Coord :=
  ((Finset.univ : Finset WctNodePos).filter fun n=>
    Paired.wTrialCap n.1.coord.val n.1.level.val≠1 ∧ n.1.nonce.val=0).toList.flatMap
    fun n=>wTrialDeps n++(childSlots (.wctNode n)).map Prod.fst

theorem wGroundDisclosed_shape {c : Coord} (hc : c∈wGroundDisclosed) : ∃n,c=.inl (.wctNode n) := by
  unfold wGroundDisclosed at hc
  obtain ⟨n,hn,hc⟩:=List.mem_flatMap.mp hc
  have h23 : 2≤n.1.level.val ∧ n.1.level.val≤5 := by
    simp only [Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and] at hn
    by_contra h
    exact hn.1 (Paired.wTrialCap_off (fun hl=>h (OuterExtractBounds.level _ _ hl)))
  rcases List.mem_append.mp hc with hc|hc
  · unfold wTrialDeps at hc
    split_ifs at hc
    · cases hc
    · obtain ⟨j,_,rfl⟩:=List.mem_map.mp hc
      exact ⟨_,rfl⟩
  · obtain ⟨⟨c',b⟩,hcs,rfl⟩:=List.mem_map.mp hc
    simp only [childSlots,childSlots.match_1] at hcs
    have hf : ∀k x,ftsChild n.1.index n.1.coord n.1.level.val k=some x → ∃m,x=.inl (.wctNode m) := by
      intro k x hx
      unfold ftsChild at hx
      rw [if_neg (by omega)] at hx
      obtain ⟨m,_,rfl⟩:=Option.map_eq_some_iff.mp hx
      exact ⟨m,rfl⟩
    simp only [List.mem_append,Option.mem_toList,Option.map_eq_some_iff,Prod.mk.injEq] at hcs
    rcases hcs with (⟨x,hx,hxe,_⟩|⟨x,hx,hxe,_⟩)|hcs
    · subst hxe;exact hf _ _ hx
    · subst hxe;exact hf _ _ hx
    · split_ifs at hcs with h5
      · simp only [Option.mem_toList,Option.map_eq_some_iff,Prod.mk.injEq] at hcs
        obtain ⟨x,hx,hxe,_⟩:=hcs
        subst hxe
        unfold prevTop at hx
        split_ifs at hx <;> cases hx
        exact ⟨_,rfl⟩
      · simp at hcs
#print axioms wGroundDisclosed_shape
end OuterResidualDisclosure
