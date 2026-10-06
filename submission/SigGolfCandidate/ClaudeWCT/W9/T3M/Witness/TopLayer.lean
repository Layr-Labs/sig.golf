import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (wvalue wpath wchainPads wmerklePad wchainHeaderPad chainP layerP nodeHashP recoverLayerP)
theorem topLayerP_of_decode (w : WBytes) (index : Nat) {answer : Digest} {digits : List Nat}
    (h : decode 0 answer = some digits) : topLayerP w index answer = some <$> layerP w index 0 digits := by
  unfold topLayerP
  rw [WCT9.topDecodeRun_of_decode h]
  unfold layerP topChainP topFinishP
  generalize route index 0 = p
  obtain ⟨leaf, tree⟩ := p
  rfl
theorem topLayerP_of_decode_none (w : WBytes) (index : Nat) {answer : Digest} (h : decode 0 answer = none) :
    topLayerP w index answer =
      (fun _ => none) <$> WCT9.topRejectChains (topChainP w (route index 0).2 (route index 0).1) answer := by
  unfold topLayerP
  exact WCT9.topDecodeRun_of_decode_none h
theorem eval_topLayerP_none (answers : QueryImpl Spec Id) (w : WBytes) (index : Nat) {answer : Digest}
    (h : decode 0 answer = none) : evalWithAnswerFn answers (topLayerP w index answer) = none :=
  WCT9.eval_topDecodeRun_none answers h
theorem decode_of_eval_topLayerP (answers : QueryImpl Spec Id) (w : WBytes) (index : Nat) {answer out : Digest}
    (h : evalWithAnswerFn answers (topLayerP w index answer) = some out) :
    ∃ digits, decode 0 answer = some digits :=
  WCT9.decode_of_eval_topDecodeRun answers h
theorem verifyTopP_of_decode (sig : WCT9.Signature) (pads : Pads) (index : Nat) {answer : Digest}
    {digits : List Nat} (h : decode 0 answer = some digits) :
    verifyTopP sig pads index answer = some <$> recoverLayerP (WCT9.toT3Signature sig) pads.toT3 index 0 digits := by
  unfold verifyTopP
  rw [WCT9.topDecodeRun_of_decode h]
  unfold recoverLayerP
  generalize route index 0 = p
  obtain ⟨leaf, tree⟩ := p
  rfl
theorem eval_verifyTopP_none (answers : QueryImpl Spec Id) (sig : WCT9.Signature) (pads : Pads) (index : Nat)
    {answer : Digest} (h : decode 0 answer = none) :
    evalWithAnswerFn answers (verifyTopP sig pads index answer) = none :=
  WCT9.eval_topDecodeRun_none answers h
end ClaudeWCT.W9.T3M
