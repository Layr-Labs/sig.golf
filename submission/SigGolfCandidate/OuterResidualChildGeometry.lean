import SigGolfCandidate.OuterResidualSlotReadout
import SigGolfCandidate.OuterResidualCellCongruence
import SigGolfCandidate.OuterResidualLeafMessage
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OuterResidualChildGeometry
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open OuterCanonBase OuterResidualValues
open OuterResidualGroundChildren (childSlots)
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual (chainChild wctItem endPoint treeChild)
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (padCoord ftsChild)
open OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (wct_childSlots_used ftsChild_used UsedCoord)
open ClaudeWCT.W9.T3.Security.LargeResidual (leafBlock)
attribute [local instance] Classical.propDecidable

theorem padCoord_used (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) (side : Fin 2) {c : Coord}
    (hc : padCoord index coord branch side=some c) : UsedCoord c := by
  unfold padCoord at hc
  split_ifs at hc with h0 hodd
  · exact ftsChild_used _ _ _ _ (by split_ifs <;> omega) _ hc
  · refine ftsChild_used _ _ _ _ ?_ _ hc
    have hf : SigGolfCandidate.Research.SharedForest.firstCoord (coord.val-1)=false := by
      simp [SigGolfCandidate.Research.SharedForest.firstCoord];omega
    simp [hf]

theorem childSlots_used (N : Node) (hu : Paired.Filtered.Used N)
    (cs : Coord×Nat) (hc : cs∈childSlots N) : UsedCoord cs.1 := by
  cases N with
  | wctNode n=>exact wct_childSlots_used hu hc
  | forest index=>exact False.elim hu
  | chain p=>
    change cs∈[(chainChild p,if WCT9.isG p.1.layer p.1.chain.val then 0 else 3)] at hc
    simp only [List.mem_singleton] at hc
    subst cs
    unfold chainChild
    split_ifs <;> trivial
  | leaf L=>
    change cs∈(List.range (chainCount L.1.lay)).map (fun i=>(.inl (.chain (endPoint L.1 i)),leafBlock L.1.lay i)) at hc
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hc
    trivial
  | wctChain p=>
    change cs∈[(wctItem p.1 p.2.val,if WCT9.ftsIsG p.1.2.2.2.val then 0 else 3)] at hc
    simp only [List.mem_singleton] at hc
    subst cs
    unfold wctItem
    split_ifs <;> trivial
  | wctLeaf L=>
    simp only [childSlots,List.mem_append] at hc
    rcases hc with hc|hc
    · obtain ⟨t,rfl⟩:=List.mem_ofFn.mp hc
      unfold wctItem
      rw [if_neg (by decide)]
      trivial
    · obtain ⟨c,hpc,he⟩:=Option.map_eq_some_iff.mp (Option.mem_toList.mp hc)
      cases he
      exact padCoord_used _ _ _ _ hpc
  | node n=>
    obtain ⟨c,b⟩:=cs
    change (c,b)∈(if trialCap n.1.lay n.1.level.val≤n.1.nonce.val then [] else
      ((treeChild n.1.lay n.1.tree n.1.level.val (2*n.1.idx.val)).map (·,0)).toList++
      ((treeChild n.1.lay n.1.tree n.1.level.val (2*n.1.idx.val+1)).map (·,3)).toList) at hc
    split_ifs at hc
    · cases hc
    simp only [List.mem_append,Option.mem_toList,Option.map_eq_some_iff,Prod.mk.injEq] at hc
    rcases hc with ⟨x,hx,rfl,-⟩|⟨x,hx,rfl,-⟩ <;>
    · unfold treeChild at hx
      split_ifs at hx
      · obtain ⟨L,_,rfl⟩:=Option.map_eq_some_iff.mp hx;trivial
      · obtain ⟨m,_,rfl⟩:=Option.map_eq_some_iff.mp hx;trivial
theorem childSlots_ne (N : Node) (hu : Paired.Filtered.Used N)
    (cs : Coord×Nat) (hc : cs∈childSlots N) : cs.1≠.inl N := by
  cases N with
  | wctNode n=>exact OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.wct_childSlots_ne hc
  | forest index=>exact False.elim hu
  | chain p=>
    change cs∈[(chainChild p,if WCT9.isG p.1.layer p.1.chain.val then 0 else 3)] at hc
    simp only [List.mem_singleton] at hc
    subst cs
    intro he
    change chainChild p=.inl (.chain p) at he
    unfold chainChild at he
    split_ifs at he with hz
    · have he' := Node.chain.inj (Sum.inl.inj he)
      have hs:=congrArg (fun q=>q.2.val) he'
      simp only [SigGolfCandidate.T3.Security.ChainGraph.predecessor] at hs
      have hp:=p.2.isLt
      omega
  | wctChain p=>
    change cs∈[(wctItem p.1 p.2.val,if WCT9.ftsIsG p.1.2.2.2.val then 0 else 3)] at hc
    simp only [List.mem_singleton] at hc
    subst cs
    intro he
    change wctItem p.1 p.2.val=.inl (.wctChain p) at he
    unfold wctItem at he
    split_ifs at he with hz
    · have he' := Node.wctChain.inj (Sum.inl.inj he)
      have hs:=congrArg (fun q : WctPoint=>q.2.val) he'
      simp only at hs
      have hp:=p.2.isLt
      omega
  | leaf L=>
    change cs∈(List.range (chainCount L.1.lay)).map (fun i=>(.inl (.chain (endPoint L.1 i)),leafBlock L.1.lay i)) at hc
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hc
    intro he;cases he
  | wctLeaf L=>
    simp only [childSlots,List.mem_append] at hc
    rcases hc with hc|hc
    · obtain ⟨t,rfl⟩:=List.mem_ofFn.mp hc
      intro he
      change wctItem (L.index,L.coord,L.child,t) 4=.inl (.wctLeaf L) at he
      unfold wctItem at he
      rw [if_neg (by decide)] at he
      cases he
    · obtain ⟨c,hpc,he⟩:=Option.map_eq_some_iff.mp (Option.mem_toList.mp hc)
      cases he
      obtain ⟨n,hn,_⟩:=OuterResidualPadCongruence.padCoord_nonce hpc
      change c≠.inl (.wctLeaf L)
      rw [hn]
      intro he;cases he
  | node n=>
    obtain ⟨c,b⟩:=cs
    change (c,b)∈(if trialCap n.1.lay n.1.level.val≤n.1.nonce.val then [] else
      ((treeChild n.1.lay n.1.tree n.1.level.val (2*n.1.idx.val)).map (·,0)).toList++
      ((treeChild n.1.lay n.1.tree n.1.level.val (2*n.1.idx.val+1)).map (·,3)).toList) at hc
    split_ifs at hc
    · cases hc
    simp only [List.mem_append,Option.mem_toList,Option.map_eq_some_iff,Prod.mk.injEq] at hc
    rcases hc with ⟨x,hx,rfl,-⟩|⟨x,hx,rfl,-⟩ <;>
    · intro he
      change x=.inl (.node n) at he
      rw [he] at hx
      exact OuterLifted2.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.treeChild_ne_self n _ hx
#print axioms childSlots_ne
#print axioms childSlots_used
end OuterResidualChildGeometry
