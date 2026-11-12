import SigGolfCandidate.OuterRawExpandFacts
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterGoodOverlay
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots (LeafAddr)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Paired
open ClaudeWCT.W9.T3.Security.CanonicalExtract

theorem shaped (answers : Answers) (out : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (ns : List Nat) (index : Nat) (lay : Layer) (ds : List Nat) :
    Extract.LayerShaped answers (OuterExpand.witEncOuter out w ns) index lay ds ↔
      Extract.LayerShaped answers (witEncF16 out w) index lay ds := by
  have hb : 7664≤layerBase lay := by fin_cases lay <;> decide +kernel
  have hl := (leafBufferBase_bounds lay).1
  have ht (off : Nat) (ho : 7664≤off) := OuterVerifierLayers.dig out w ns off (Or.inr ho)
  simp (disch := omega) only [Extract.LayerShaped,wpath,wmerklePad,wmerkleHigh,wvalueFor,wvalue,
    wchainPads,wchainHeaderPad,wleafHigh,chainBlock,merkleBlock,leafBufferSlot,ht]

theorem bcCtr (out : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat)
    (index : Nat) (lay : Layer) :
    wbcCtr (OuterExpand.witEncOuter out w ns) index lay=wbcCtr (witEncF16 out w) index lay := by
  have hrow := ClaudeWCT.W9.T3M.PairedNonce.rowBlock_out index lay
  unfold wbcCtr wle32 bcCounterOff
  exact OuterVerifierLayers.extract out w ns _ 4 (by rcases hrow with h|h <;>omega)
theorem bcPad (out : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat)
    (index : Nat) (lay : Layer) :
    wbcPad (OuterExpand.witEncOuter out w ns) index lay=wbcPad (witEncF16 out w) index lay := by
  have hrow := ClaudeWCT.W9.T3M.PairedNonce.rowBlock_out index lay
  unfold wbcPad bcCounterOff
  exact OuterVerifierLayers.extract out w ns _ 12 (by rcases hrow with h|h <;>omega)
theorem bcHigh (out : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat)
    (index : Nat) (lay : Layer) :
    wbcHigh (OuterExpand.witEncOuter out w ns) index lay=wbcHigh (witEncF16 out w) index lay := by
  have hrow := ClaudeWCT.W9.T3M.PairedNonce.rowBlock_out index lay
  unfold wbcHigh
  rw [OuterVerifierLayers.dig out w ns _ (by rcases hrow with h|h <;>omega)]
theorem bcRight (out : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat) :
    wbcRight (OuterExpand.witEncOuter out w ns)=wbcRight (witEncF16 out w) := by
  exact OuterVerifierLayers.dig out w ns 48 (Or.inl (by decide))
theorem honestHint (answers : Answers) (messages : LeafAddr→WCT9.LayerMsg)
    (out : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat) (index : Nat) (lay : Layer) :
    HonestHint answers messages (OuterExpand.witEncOuter out w ns) index lay ↔
      HonestHint answers messages (witEncF16 out w) index lay := by
  have hi : layerEncodingInputP lay (route index lay).2 (route index lay).1
      (messages (SigGolfCandidate.T3.Security.WotsExtract.routeLeaf index lay))
      (wbcCtr (OuterExpand.witEncOuter out w ns) index lay)
      (wbcPad (OuterExpand.witEncOuter out w ns) index lay)
      (wbcRight (OuterExpand.witEncOuter out w ns)) (wbcHigh (OuterExpand.witEncOuter out w ns) index lay)=
    layerEncodingInputP lay (route index lay).2 (route index lay).1
      (messages (SigGolfCandidate.T3.Security.WotsExtract.routeLeaf index lay))
      (wbcCtr (witEncF16 out w) index lay) (wbcPad (witEncF16 out w) index lay)
      (wbcRight (witEncF16 out w)) (wbcHigh (witEncF16 out w) index lay) := by
    rw [bcCtr,bcPad,bcRight,bcHigh]
  have ha:=congrArg (fun q : HashInput=>answers (.inl (.inr q))) (congrArg pad64 hi)
  unfold HonestHint
  rw [ha,OuterVerifierLayers.topHigh,wtopHigh_witEncF16]
theorem good (answers : Answers) (messages : LeafAddr→WCT9.LayerMsg)
    (out : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat) (index : Nat) (lay : Layer) :
    Good answers messages (OuterExpand.witEncOuter out w ns) index lay ↔
      Good answers messages (witEncF16 out w) index lay := by
  simp only [ClaudeWCT.W9.T3.Security.CanonicalExtract.Good,honestHint,Extract.CanonicalFrame,
    bcCtr,bcPad,bcHigh,bcRight,OuterVerifierLayers.topHigh,wtopHigh_witEncF16,shaped]

#print axioms shaped
#print axioms good
end OuterGoodOverlay
