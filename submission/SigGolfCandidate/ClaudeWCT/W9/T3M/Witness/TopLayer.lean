import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (chainP nodeHashP recoverLayerP)
theorem topLayerP_of_decode (w : WBytes) (index : Nat) {answer : Digest} {digits : List Nat}
    (h : decode 0 answer = some digits) : topLayerP w index answer = some <$> layerP w index 0 digits := by
  unfold topLayerP
  rw [WCT9.topDecodeRun_of_decode h]
  have hd := (WCT9.decode_top_some h).2.2.2
  rw [← hd]
  unfold layerP topChainP topFinishP
  generalize route index 0 = p
  obtain ⟨leaf, tree⟩ := p
  rfl
theorem topLayerP_of_decode_none (w : WBytes) (index : Nat) {answer : Digest} (h : decode 0 answer = none) :
    topLayerP w index answer =
      (fun _ => none) <$> WCT9.topRejectChains (topChainP w (route index 0).2 (route index 0).1 (dataDigits 0 answer)) answer := by
  unfold topLayerP
  exact WCT9.topDecodeRun_of_decode_none h
theorem eval_topLayerP_none (answers : QueryImpl Spec Id) (w : WBytes) (index : Nat) {answer : Digest}
    (h : decode 0 answer = none) : evalWithAnswerFn answers (topLayerP w index answer) = none :=
  WCT9.eval_topDecodeRun_none answers h
theorem decode_of_eval_topLayerP (answers : QueryImpl Spec Id) (w : WBytes) (index : Nat) {answer out : Digest}
    (h : evalWithAnswerFn answers (topLayerP w index answer) = some out) :
    ∃ digits, decode 0 answer = some digits :=
  WCT9.decode_of_eval_topDecodeRun answers h
/-- Padded top layer after decoding (campaign S1: one-word fold labels with witness high words `pads.merkleHigh`). -/
def recoverTopP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (digits : List Nat) : M Digest := do
  let (leaf, tree) := route index 0
  let ends ← (List.finRange (chainCount 0)).mapM fun i =>
    chainP 0 tree leaf i.val (digits.getD i.val 0) (maxDigit 0 i.val - digits.getD i.val 0)
      (pads.chain 0 i).1 (pads.chain 0 i).2 (pads.chainHeader 0 i) ((sig.layers 0).values i)
  let value ← leafHash 0 tree leaf ends
  (List.finRange (height 0)).foldlM (fun value j => do
    let other := (sig.layers 0).path j
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashPH (0 : Layer).val tree (2 ^ (height 0 - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (pads.merkleHigh 0 j) (pads.merkle 0 j) pair.2) value
theorem verifyTopP_of_decode (sig : WCT9.Signature) (pads : Pads) (index : Nat) {answer : Digest}
    {digits : List Nat} (h : decode 0 answer = some digits) :
    verifyTopP sig pads index answer = some <$> recoverTopP (effectiveSignature sig pads digits) pads index digits := by
  unfold verifyTopP
  rw [WCT9.topDecodeRun_of_decode h]
  have hd := (WCT9.decode_top_some h).2.2.2
  rw [← hd]
  unfold recoverTopP
  generalize route index 0 = p
  obtain ⟨leaf, tree⟩ := p
  rfl
theorem eval_verifyTopP_none (answers : QueryImpl Spec Id) (sig : WCT9.Signature) (pads : Pads) (index : Nat)
    {answer : Digest} (h : decode 0 answer = none) :
    evalWithAnswerFn answers (verifyTopP sig pads index answer) = none :=
  WCT9.eval_topDecodeRun_none answers h
end ClaudeWCT.W9.T3M
