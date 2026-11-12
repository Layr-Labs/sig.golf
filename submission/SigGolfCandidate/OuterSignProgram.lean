import SigGolfCandidate.OuterSignOutput
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignProgram
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.Machine.Sign
theorem sign_program (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) :
    OuterSigning.sign (cacheDec cache) msg=(do
      let tag ← SigGolfCandidate.T3.privateMac (cacheDec cache).region
      if tag ≠ (cacheDec cache).tag then pure none else do
        let rho ← SigGolfCandidate.T3.privateNonce msg
        let r ← sharedDigestSearch rho msg 0 ((11*2^17))
        match r with
        | none => pure none
        | some (_,a) => OuterSignOutput.outputProgram cache rho a) := by
  simp only [OuterSigning.sign,OuterSigning.signPayload,ClaudeWCT.WCT9.digestAttemptLimit]
  congr 1
  funext tag
  split <;>rename_i ht
  · rfl
  · congr 1
    funext rho
    congr 1
    funext r
    cases r with
    | none => rfl
    | some r =>
      rcases r with ⟨c,a⟩
      dsimp only
      refine Eq.trans ?_ (OuterSignOutput.outputProgram_source cache rho c a)
      congr 1
      funext w
      cases w <;>rfl


#print axioms sign_program
end OuterSignProgram
