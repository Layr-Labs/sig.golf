import SigGolfCandidate.OuterCanonHonestInput
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option maxErrors 30
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonBase.Paired
open ClaudeWCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
attribute [local instance low] Classical.propDecidable
def CapFailT (labels : Labels) : Prop :=
  ∃ n : TreeNode, ((n.1.lay = 0 ∧ n.1.level.val < 11) ∨
      (n.1.lay ≠ 0 ∧ WCT9.lowerZeroBits n.1.lay.val (2 ^ (height n.1.lay - n.1.level.val - 1)) ≠ 0)) ∧
    n.1.nonce.val = 0 ∧ ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j
/-- E8: some FTS ground position (node level 3, Y7: or level 2 of coordinates `0..3`; nonce-0 representative)
exhausts its cap. -/
def CapFailW (labels : Labels) : Prop :=
  ∃ m : WctNodePos, OuterExtractGround.ftsNonceLevel m.1.coord.val m.1.level.val ∧ m.1.nonce.val = 0 ∧
    ∀ j < wTrialCap m.1.coord.val m.1.level.val, wTrialFails labels m j
/-- Some multi-trial position (tree or, E8, FTS ground) exhausts its nonce cap. -/
def CapFail (labels : Labels) : Prop := CapFailT labels ∨ CapFailW labels

noncomputable local instance instSampleableTypeLabels_capFail : SampleableType Labels :=
  SampleableType.ofFintype _

end OuterCanonBase.Paired
