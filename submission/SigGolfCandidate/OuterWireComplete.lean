import SigGolfCandidate.OuterWireEval
import SigGolfCandidate.OuterExpandVerified
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterWireComplete
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness

theorem complete (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (ns5 : List Nat)
    (he : evalWithAnswerFn answers (OuterExpand.expandN message pk sig)=some (output,w,ns5)) :
    evalWithAnswerFn answers (ClaudeWCT.W9.T3M.Paired.verifyP message pk
      (OuterExpand.witEncOuter output w ns5))=true := by
  rw [OuterWireEval.eval_eq answers message pk sig output w ns5 he]
  exact OuterExpandVerified.verified answers message pk sig output w ns5 he
#print axioms complete
end OuterWireComplete
