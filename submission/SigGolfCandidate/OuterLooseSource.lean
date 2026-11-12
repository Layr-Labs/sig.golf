import SigGolfCandidate.OuterLooseCodec
import SigGolfCandidate.OuterCompactCorrectness
import SigGolfCandidate.OuterCompactBudget
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterLooseSource
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec

def signCompact (cache : SigGolfCandidate.T3.Cache) (message : Message) : M (Option OuterSignatureCodec.NewSig) :=
  (Option.map (fun s=>OuterLooseCodec.compress (sigBC s))) <$> OuterSigning.sign cache message

theorem signFromOutput_eq (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hall : OuterHybridGlobalCorrectness.ForestsOK answers)
    (he : evalWithAnswerFn answers (OuterSigning.signFromOutput cache rho counter output)=some w) :
    OuterLooseCodec.compress (sigBC w.signature)=OuterSignatureCodec.compress (sigBC w.signature) := by
  have hf:=OuterHonestCarriers.signFromOutput_forest answers cache rho counter output w he
  have h:=hall (digestIndex output) (digestIndex_lt output)
  apply OuterLooseCodec.compress_eq
  rw [OuterCarrierSerialization.read_carriers]
  apply OuterCarrierBits.five_clear
  all_goals rw [hf]
  · exact OuterHonestCarriers.forest_pair_zero answers _ _ _ h 0
  · exact OuterHonestCarriers.forest_pair_zero answers _ _ _ h 1
  · exact OuterHonestCarriers.forest_pair_zero answers _ _ _ h 2
  · exact OuterHonestCarriers.forest_pair_zero answers _ _ _ h 3
  · exact OuterHonestCarriers.forest_singleton_zero answers _ _ _ h

theorem sign_eq (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (hall : OuterHybridGlobalCorrectness.ForestsOK answers) :
    evalWithAnswerFn answers (signCompact cache message)=evalWithAnswerFn answers (OuterExpand.signCompact cache message) := by
  unfold signCompact OuterExpand.signCompact
  simp only [evalWithAnswerFn_map]
  cases hs : evalWithAnswerFn answers (OuterSigning.sign cache message) with
  | none=>simp only [Option.map_none]
  | some sig=>
    simp only [Option.map_some]
    have hp : evalWithAnswerFn answers (OuterSigning.signPayload cache message)=some sig := by
      unfold OuterSigning.sign at hs
      simp only [evalWithAnswerFn_bind] at hs
      split_ifs at hs
      · simp only [evalWithAnswerFn_pure,reduceCtorEq] at hs
      · exact hs
    obtain ⟨counter,output,w,hd,hw,rfl⟩:=OuterSignatureComponents.signPayload_components answers cache message sig hp
    exact congrArg some (signFromOutput_eq answers cache _ counter output w hall hw)
#print axioms signFromOutput_eq
#print axioms sign_eq
end OuterLooseSource
