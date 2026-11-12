import SigGolfCandidate.OuterNodeValue
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterNodeReference
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3M.Extract.Paired
open SigGolfCandidate.Research.SharedForest

theorem hash_response (answers : Answers) (coord index heap n : Nat) (left right : Digest) :
    evalWithAnswerFn answers (OuterGroundCore.hashN coord index heap n left right)=
      OuterGroundCore.value coord heap (answers (.inl (.inr (pad64
        (ClaudeWCT.WCT9.wctTopInput coord index heap left (BitVec.ofNat 128 (n%2^64)) right))))) := rfl

theorem outer (answers : Answers) (index coord nd : Nat) (hc : coord<9)
    (hf : OuterExtractModel.first coord=false) (hn : nd<2) :
    proj (.wctNode index coord 5 nd)
      (answers (.inl (.inr (OuterExtractModel.honestInput answers (.wctNode index coord 5 nd)))))=
      (OuterExtractModel.nodes answers index coord).getD (2+nd) 0 := by
  let ns:=OuterExtractModel.nodes answers index coord
  let left:=ns.getD (2*(2+nd)) 0
  let right:=ns.getD (2*(2+nd)+1) 0
  have hg:=OuterExtractModel.nodes_graph answers index coord hc
  have href:=hg.2.2 (2+nd) (by simpa [heapCut,hf]) (by omega) (by simp [heapCut,hf])
  simp only [OuterCanonicalNode.node,hf,true_and,if_pos (show 2+nd<4 by omega),evalWithAnswerFn_map] at href
  have hv:=OuterNodeValue.value answers coord index (2+nd) left right
  rw [hash_response,OuterNodeValue.projection coord index nd hc hf hn] at hv
  have hi : OuterExtractModel.honestInput answers (.wctNode index coord 5 nd)=
      pad64 (ClaudeWCT.WCT9.wctTopInput coord index (2+nd) left
        (BitVec.ofNat 128 ((evalWithAnswerFn answers (OuterGroundCore.nodeAt coord index (2+nd) left right)).1%2^64)) right) := by
    simp only [OuterExtractModel.honestInput,show (6:Nat)-5=1 by decide,show (2:Nat)^1=2 by decide,
      if_neg (by decide : ¬(5:Nat)=4),if_pos (show OuterExtractGround.ftsNonceLevel coord 5 from Or.inr ⟨rfl,hf⟩)]
    unfold OuterExtractModel.honestFtsNonce OuterExtractGround.nodeAt
    rw [if_pos (show 2+nd<4 by omega)]
  rw [hi]
  exact hv.symm.trans href.symm
#print axioms hash_response
#print axioms outer
end OuterNodeReference
