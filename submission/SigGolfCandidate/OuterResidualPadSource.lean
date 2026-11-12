import SigGolfCandidate.OuterResidualPadModel
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OuterResidualPadSource
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open OuterCanonBase OuterResidualValues
open OuterLifted.ClaudeWCT.W9.T3.Security.LargeResidual.Paired (coordVal ftsChild padCoord)

theorem coordVal_selCoordV_wct (s : Secrets) (labels : Labels) (n : WctNodePos) :
    coordVal s labels (selCoordV (coordVal s labels) (.inl (.wctNode n)))=
      ClaudeWCT.W9.T3M.Extract.Paired.proj (Node.wctNode n).toPos
        (labels (.wctNode (Paired.wSelNode labels n))) := by
  rw [OuterResidualRouter.selCoordV_coordVal_sel]
  rfl

theorem ftsLabel_eq (s : Secrets) (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) :
    Paired.ftsLabel labels index coord level c=OuterResidualPadModel.ftsChildVal (coordVal s labels) index coord level c := by
  unfold Paired.ftsLabel OuterResidualPadModel.ftsChildVal ftsChild selVals
  by_cases h0 : level=0
  · rw [if_pos h0,if_pos h0]
    split_ifs <;> rfl
  · rw [if_neg h0,if_neg h0]
    cases hn : ftsNodeAt index coord (level-1) c with
    | none=>rfl
    | some n=>
      simp only [Option.map_some,Option.getD_some]
      rw [coordVal_selCoordV_wct]
      simp only [Node.toPos,ftsNodeAt_coord hn,ftsNodeAt_level hn]
      have hi : n.1.index=index := by
        unfold ftsNodeAt at hn
        split_ifs at hn
        cases hn
        rfl
      have hc : n.1.idx.val=c := by
        unfold ftsNodeAt at hn
        split_ifs at hn
        cases hn
        rfl
      rw [hi,hc]

theorem pads_eq (s : Secrets) (labels : Labels) (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) :
    Paired.pads labels index coord branch=OuterResidualPadModel.padVals (coordVal s labels) index coord branch := by
  unfold Paired.pads OuterResidualPadModel.padVals padCoord
  split_ifs with hz ho
  · rfl
  all_goals
    dsimp only
    rw [ftsLabel_eq s,ftsLabel_eq s]
    rfl
#print axioms ftsLabel_eq
#print axioms pads_eq
end OuterResidualPadSource
