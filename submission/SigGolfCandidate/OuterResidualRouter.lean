import SigGolfCandidate.OuterResidualValueLaws
import SigGolfCandidate.OuterResidualDisclosure
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OuterResidualRouter
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open OuterCanonBase OuterResidualValues
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual (trialCoord wTrialCoord)
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (coordVal routerLabels AuxData)
open OuterLifted.ClaudeWCT.W9.T3.Security.CanonEncoding (childIndex childIndex_treeBits)
attribute [local instance] Classical.propDecidable

theorem selCoordV_coordVal_sel (s : Secrets) (labels : Labels) (N : Node) :
    selCoordV (coordVal s labels) (.inl N)=.inl (N.sel labels) := by
  cases N with
  | node n=>
    change Sum.inl (Node.node (withNonce n (OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.selNonceV (coordVal s labels) n)))=_
    rw [OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired.selNonceV_coordVal]
    rfl
  | wctNode n=>
    change Sum.inl (Node.wctNode (Paired.wWithNonce n (wSelNonceV (coordVal s labels) n)))=_
    rw [OuterResidualProjection.wSelNonceV_coordVal]
    rfl
  | _=>rfl

theorem selCoordV_router (vals : Coord → Digest) (a : AuxData) (N : Node) :
    selCoordV vals (.inl N)=.inl (N.sel (routerLabels vals a)) := by
  have h2 : selCoordV vals (.inl N)=selCoordV (coordVal (fun _=>0) (routerLabels vals a)) (.inl N) :=
    OuterResidualValueLaws.selCoordV_congr (.inl N) (fun n _ _ j _=>by
      unfold trialCoord
      simp only [coordVal,coordVal.match_1,routerLabels]
      exact (OuterLifted.ClaudeWCT.W9.T3.Security.CanonGraph.Paired.joinLabels_val
        (fun M=>vals (.inl M)) a.high (.node (withNonce n j))).symm)
      (fun n _ _ j _=>by
      unfold wTrialCoord
      simp only [coordVal,coordVal.match_1,routerLabels]
      exact (OuterLifted.ClaudeWCT.W9.T3.Security.CanonGraph.Paired.joinLabels_val
        (fun M=>vals (.inl M)) a.high (.wctNode (Paired.wWithNonce n j))).symm)
  rw [h2]
  exact selCoordV_coordVal_sel _ _ N

theorem proj_sel_router (vals : Coord → Digest) (a : AuxData) (n : TreeNode) :
    (Node.node n).toPos.proj (routerLabels vals a (.node (selNode (routerLabels vals a) n)))=
      vals (selCoordV vals (.inl (.node n))) := by
  rw [selCoordV_router vals a]
  exact OuterLifted.ClaudeWCT.W9.T3.Security.CanonGraph.Paired.joinLabels_node
    (fun M=>vals (.inl M)) a.high (selNode (routerLabels vals a) n)
theorem proj_sel_router_wct (vals : Coord → Digest) (a : AuxData) (n : WctNodePos) :
    ClaudeWCT.W9.T3M.Extract.Paired.proj (Node.wctNode n).toPos
      (routerLabels vals a (.wctNode (Paired.wSelNode (routerLabels vals a) n)))=
      vals (selCoordV vals (.inl (.wctNode n))) := by
  rw [selCoordV_router vals a]
  exact OuterLifted.ClaudeWCT.W9.T3.Security.CanonGraph.Paired.joinLabels_val
    (fun M=>vals (.inl M)) a.high (.wctNode (Paired.wSelNode (routerLabels vals a) n))

theorem msgLabel_router (vals : Coord → Digest) (a : AuxData) (L : EncLeaf) :
    OuterLifted.ClaudeWCT.W9.T3.Security.CanonEncoding.Paired.msgLabel (routerLabels vals a) L=msgVals vals L := by
  unfold OuterLifted.ClaudeWCT.W9.T3.Security.CanonEncoding.Paired.msgLabel msgVals
  by_cases hl : L.1.lay.val<3
  · rw [dif_pos hl,dif_pos hl]
    congr 1
    · exact (treeLabel_top _ _ _ (childIndex_treeBits L hl) 0).trans (proj_sel_router vals a _)
    · exact (treeLabel_top _ _ _ (childIndex_treeBits L hl) 1).trans (proj_sel_router vals a _)
  · rw [dif_neg hl,dif_neg hl]
    congr 1
    · exact (OuterResidualProjection.paired_ftsLabel_top _ _ _ 0).trans (proj_sel_router_wct vals a _)
    · exact (OuterResidualProjection.paired_ftsLabel_top _ _ _ 1).trans (proj_sel_router_wct vals a _)
#print axioms selCoordV_router
#print axioms msgLabel_router
end OuterResidualRouter
