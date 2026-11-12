import SigGolfCandidate.OuterForestSuffix
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterExpandSource
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M Message)
open SigGolfCandidate.Research ClaudeWCT ClaudeWCT.W9.T3M
open ClaudeWCT.W9.Machine.Expand.SharedCompactMain
theorem expandN_source (message : SigGolfCandidate.T3.Message) (pk : Digest) (b : SharedCodec.CBytes)
    (hfill : SharedForest.fillTopSignature (SharedCodec.sigDecC b) 0=SharedCodec.sigDecC b) :
    OuterExpand.expandN message pk (SharedCodec.sigDecC b)=
      if (SharedCodec.sigDecC b).policyHints.toNat ≥ 12288 then pure none else
        SharedForest.sharedDigestSearch (SharedCodec.sigDecC b).rho message 0 ((11*2^17)) >>= fun result=>
          match result with
          | none => pure none
          | some (counter,output)=>OuterForestSuffix.forestProgram output b counter pk := by
  unfold OuterExpand.expandN
  rw [hfill]
  by_cases bad:(SharedCodec.sigDecC b).policyHints.toNat ≥ 12288
  · simp only [bad,ite_true]
  rw [if_neg bad,if_neg bad]
  apply congrArg (fun k=>SharedForest.sharedDigestSearch (SharedCodec.sigDecC b).rho message 0 ((11*2^17)) >>= k)
  funext result
  cases result with
  | none => rfl
  | some pair =>
    rcases pair with ⟨counter,output⟩
    unfold OuterForestSuffix.forestProgram OuterLayersRecovery.recoverProgram
    apply congrArg (fun k=>OuterForestCorrectness.recoverForest (WCT9.digestIndex output)
      (SharedForest.forestSelectionFromOutput output) (SharedForest.forestWordsFromOutput output)
      (SharedCodec.sigDecC b).forest >>= k)
    funext forest
    simp only [bind_assoc]
    apply congrArg (fun k=>SharedForest.recoverHintedLayers (SharedCodec.sigDecC b) (WCT9.digestIndex output)
      (WCT9.topSib (SharedForest.mainSignature (SharedCodec.sigDecC b))) 4 (.pair forest.1.1 forest.1.2) >>= k)
    funext layers
    cases layers with
    | none => rfl
    | some layers =>
      dsimp only
      by_cases valid:OuterSigning.policyHintsValid (WCT9.digestIndex output) (SharedCodec.sigDecC b).policyHints layers.digits layers.lows=true
      · simp only [valid,Bool.not_true,Bool.false_eq_true,ite_false,ite_true,pure_bind]
        unfold topProgram
        by_cases root:layers.root=pk
        · simp only [root,ite_true,pure_bind,Option.map_some,hfill,OuterForestSuffix.appendNonces]
        · simp only [root,ite_false,bind_assoc]
          apply congrArg (fun k=>WCT9.searchTop (WCT9.digestIndex output) layers.foldedTop
            (WCT9.topSib (SharedForest.mainSignature (SharedCodec.sigDecC b))) pk WCT9.searchFuel 1 >>= k)
          funext c
          cases c <;> rfl
      · have vf : OuterSigning.policyHintsValid (WCT9.digestIndex output) (SharedCodec.sigDecC b).policyHints layers.digits layers.lows=false :=
          Bool.eq_false_iff.mpr valid
        simp only [vf,Bool.not_false,Bool.false_eq_true,ite_true,ite_false,pure_bind,OuterForestSuffix.appendNonces]

#print axioms expandN_source
end OuterExpandSource
