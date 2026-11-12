import SigGolfCandidate.OuterConditionalCertificate
import SigGolfCandidate.OuterRawExpand
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterSecurityGame
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 (M Spec Message Digest Cache keygen privateInput)
open SigGolfCandidate.T3.Security (Request forwardWorld)
open SigGolfCandidate.Research.SharedForest (Signature)
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)
abbrev Requests:=Request →ₒ Option Signature
abbrev Forgery:=ClaudeWCT.W9.T3M.Final.Paired.ForgeryP
abbrev Adversary:=ClaudeWCT.W9.T3M.Final.Paired.AdversaryP

def wire (sig : Signature) : OuterSignatureCodec.NewSig:=
  OuterSignatureCodec.compress (ClaudeWCT.W9.T3M.SharedCodec.sigBC sig)
def signedWire (sig : Signature) : OuterSignatureCodec.NewSig:=
  OuterLooseCodec.compress (ClaudeWCT.W9.T3M.SharedCodec.sigBC sig)

def signingOracle : QueryImpl Requests (WriterT (QueryLog Requests) M):=
  QueryImpl.withLogging fun request=>liftM (OuterSigning.sign request.cache request.message)

noncomputable def checkForgery (pk : Digest) (log : QueryLog Requests) : Forgery→M Bool := by
  classical
  exact fun forgery=>do
    match forgery with
    | .witness message wb=>
      let verified←ClaudeWCT.W9.T3M.Paired.verifyP message pk wb
      pure (decide (¬∃entry∈log,entry.1.message=message ∧ entry.2.isSome=true) && verified)
    | .signature message sig=>
      let wb←OuterRawExpand.expandB message pk sig
      let some wb:=wb | return false
      let verified←ClaudeWCT.W9.T3M.Paired.verifyP message pk wb
      pure (decide (¬∃entry∈log,entry.1.message=message ∧ entry.2.map ClaudeWCT.W9.T3M.SharedCodec.sigBC=some (ClaudeWCT.W9.T3M.SharedCodec.sigBC sig)) && verified)

noncomputable def game (adversary : Adversary) : M Bool := do
  let (pk,cache)←keygen
  let (forgery,log)←(simulateQ
    ((fun input=>liftM (forwardWorld input) : QueryImpl OracleWorld (WriterT (QueryLog Requests) M))+
      signingOracle) (adversary pk cache)).run
  let some forgery:=forgery | return false
  let verified←checkForgery pk log forgery
  pure (decide (log.length≤2^32) && verified)

noncomputable def experiment (adversary : Adversary) : ProbComp (Bool×Nat):=
  sampleMasterSeed >>=fun secret=>
    (simulateQ romImpl (SphincsSecurity.countHashQueries
      (SigGolfCandidate.T3.Derivation.realize (privateInput secret) (game adversary)))).run' ∅

def Secure : Prop:=∀(adversary : Adversary)(q : Nat),1≤q→
  Pr[fun r=>r.1=true ∧ r.2≤q | experiment adversary]≤(q:ENNReal)/2^127

/-- Purely identifies the OR-packing source oracle's wire response. -/
theorem signing_wire (answers : SigGolfCandidate.T3.Correctness.Answers) (cache : Cache) (message : Message) :
    evalWithAnswerFn answers (OuterLooseSource.signCompact cache message)=
      (evalWithAnswerFn answers (OuterSigning.sign cache message)).map signedWire := by
  rw [OuterLooseSource.signCompact,evalWithAnswerFn_map]
  rfl
#print axioms signing_wire
end OuterSecurityGame
