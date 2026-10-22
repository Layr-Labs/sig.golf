import SigGolfCandidate.ClaudeWCT_W9_T3M_Witness_VerifyP

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (chainP nodeHashP recoverLayerP)
/-- Campaign T51: on the top layer the skipped-copy reads see the same digits with or without the checksum digit
(the checksum chain 50 is never a safe zero copy). -/
theorem safeZeroCopy_top_append (answer : Digest) (c i : Nat) (hi : i < 51) :
    WCT9.safeZeroCopy 0 (dataDigits 0 answer ++ [c]) i ↔ WCT9.safeZeroCopy 0 (dataDigits 0 answer) i := by
  have hl := WCT9.dataDigits_top_length answer
  unfold WCT9.safeZeroCopy
  by_cases h50 : i < 50
  · rw [List.getD_append _ _ _ i (by omega), List.getD_append _ _ _ (i - 1) (by omega)]
  · have : i = 50 := by omega
    subst this
    simp
theorem wvalueFor_top_append (w : WBytes) (answer : Digest) (c i : Nat) (hi : i < 51) :
    wvalueFor w 0 (dataDigits 0 answer ++ [c]) i = wvalueFor w 0 (dataDigits 0 answer) i := by
  unfold wvalueFor
  rw [if_congr (safeZeroCopy_top_append answer c i hi) rfl rfl]
theorem topLayerP_of_decode (w : WBytes) (index : Nat) {answer : Digest} {digits : List Nat}
    (h : decode 0 answer = some digits) : topLayerP w index answer = some <$> layerP w index 0 digits := by
  unfold topLayerP
  rw [WCT9.topDecodeRun_of_decode h]
  have hd := (WCT9.decode_top_some h).2.2.2
  unfold layerP topChainP topFinishP
  generalize route index 0 = p
  obtain ⟨leaf, tree⟩ := p
  have hv : ∀ i : Fin (chainCount 0), wvalueFor w 0 (dataDigits 0 answer) i.val = wvalueFor w 0 digits i.val := by
    intro i
    rw [hd, wvalueFor_top_append w answer _ i.val i.isLt]
  simp only [hv]

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
theorem eval_verifyTopP_none (answers : QueryImpl Spec Id) (sig : WCT9.Signature) (pads : Pads) (index : Nat)
    {answer : Digest} (h : decode 0 answer = none) :
    evalWithAnswerFn answers (verifyTopP sig pads index answer) = none :=
  WCT9.eval_topDecodeRun_none answers h
end ClaudeWCT.W9.T3M
