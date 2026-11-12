import SigGolfCandidate.OuterHonestComplete
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterAllMessagesComplete
open OracleComp OracleSpec OracleComp.EvalDist
open SigGolfCandidate.T3 SigGolfCandidate.T3.SourceReplay
open SigGolfCandidate.T3M.Final ClaudeWCT.W9.T3M.Final

noncomputable def program : M Bool:=foldAll msgs OuterHonestComplete.program true

theorem hashOnly : HashOnly program:=allQ_foldAll' msgs OuterHonestComplete.program OuterHonestComplete.hashOnly true

theorem good (answers : Correctness.Answers)
    (hsign : OuterSourceCompleteness.SigningComplete answers (evalWithAnswerFn answers keygen).2)
    (htree : SigGolfCandidate.Research.SharedForest.TopTreeOK answers)
    (hlower : SigGolfCandidate.Research.SharedForest.LowerTreesOK answers)
    (hforest : OuterHybridGlobalCorrectness.ForestsOK answers) : evalWithAnswerFn answers program=true := by
  rw [program,evalWithAnswerFn_foldAll]
  simp only [Bool.true_and,List.all_eq_true]
  intro message hm
  exact OuterHonestComplete.good message answers hsign htree hlower hforest

theorem failure_small (secret : BitVec 256) :
    Pr[fun value=>value=false | (simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅]≤1/(2:ENNReal)^128 :=
  OuterCompletenessProbability.failure_small program hashOnly good secret

theorem complete (secret : BitVec 256) :
    1-1/(2:ENNReal)^128≤Pr[=true | (simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] := by
  have hf:=failure_small secret
  rw [probEvent_eq_eq_probOutput] at hf
  rw [probOutput_true_eq_sub]
  simp only [probFailure_eq_zero,tsub_zero]
  exact tsub_le_tsub_left hf 1
#print axioms complete
end OuterAllMessagesComplete
