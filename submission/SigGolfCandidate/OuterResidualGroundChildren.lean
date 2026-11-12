import SigGolfCandidate.OuterResidualRouter
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OuterResidualGroundChildren
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open OuterCanonBase OuterResidualValues
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual (wTrialDeps wctItem keygenCacheDisclosed encodingDisclosed trialsDisclosed groundChildren)
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (ftsChild padCoord)
attribute [local instance] Classical.propDecidable
set_option allowUnsafeReducibility true in
attribute [local reducible] OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Coord

def topTrialsDisclosed : List Coord := trialsDisclosed++(groundChildren++OuterResidualDisclosure.wGroundDisclosed)
def keygenDisclosed : List Coord := keygenCacheDisclosed++encodingDisclosed++topTrialsDisclosed

def childSlots : Node → List (Coord×Nat)
  | .wctLeaf L=>(List.ofFn fun t : Fin 6=>(wctItem (L.index,L.coord,L.child,t) 4,ClaudeWCT.W9.T3.Security.LargeResidual.ftsLeafSlot t.val))++
    ((padCoord L.index L.coord (L.child.val%2) 0).map (·,2)).toList
  | .wctNode n=>if Paired.wTrialCap n.1.coord.val n.1.level.val≤n.1.nonce.val then [] else
    ((ftsChild n.1.index n.1.coord n.1.level.val (2*n.1.idx.val)).map (·,0)).toList++
    ((ftsChild n.1.index n.1.coord n.1.level.val (2*n.1.idx.val+1)).map (·,3)).toList++
    (if n.1.level.val=4 then ((padCoord n.1.index n.1.coord (n.1.idx.val/2) 1).map (·,2)).toList else [])
  | n=>OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.childSlots n

theorem wGround_mem_keygen {n : WctNodePos} (h1 : Paired.wTrialCap n.1.coord.val n.1.level.val≠1) {c : Coord}
    (hc : c∈wTrialDeps n++(OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.childSlots (.wctNode n)).map Prod.fst) :
    c∈keygenDisclosed := by
  apply List.mem_append_right
  apply List.mem_append_right
  apply List.mem_append_right
  unfold OuterResidualDisclosure.wGroundDisclosed
  refine List.mem_flatMap.mpr ⟨Paired.wWithNonce n 0,?_,hc⟩
  simp only [Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨h1,Paired.wWithNonce_nonce n (by norm_num)⟩

theorem wGround_childSlots_keygen {n : WctNodePos} (h1 : Paired.wTrialCap n.1.coord.val n.1.level.val≠1)
    {cs : Coord×Nat} (hc : cs∈childSlots (.wctNode n)) : cs.1∈keygenDisclosed := by
  have hp : OuterExtractGround.ftsNonceLevel n.1.coord.val n.1.level.val := by
    by_contra h
    exact h1 (Paired.wTrialCap_off h)
  have h23:=OuterExtractBounds.level _ _ hp
  have h0 : n.1.level.val≠0 := by omega
  have h4 : n.1.level.val≠4 := by
    rcases hp with hi|ho
    · unfold ClaudeWCT.W9.T3M.Extract.Paired.ftsNonceLevel at hi;omega
    · omega
  by_cases hov : Paired.wTrialCap n.1.coord.val n.1.level.val≤n.1.nonce.val
  · simp only [childSlots,if_pos hov] at hc;cases hc
  have he (k : Nat) : ftsChild n.1.index n.1.coord n.1.level.val k=
      OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.ftsChild n.1.index n.1.coord n.1.level.val k := by
    unfold ftsChild OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.ftsChild
    rw [if_neg h0,if_neg h0]
  simp only [childSlots,if_neg hov,if_neg h4,List.append_nil,he] at hc
  have hg : cs∈OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.childSlots (.wctNode n) := by
    simp only [OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.childSlots,
      OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.childSlots.match_1]
    exact List.mem_append_left _ hc
  exact wGround_mem_keygen h1 (List.mem_append_right _ (List.mem_map.mpr ⟨cs,hg,rfl⟩))
#print axioms wGround_childSlots_keygen
end OuterResidualGroundChildren
