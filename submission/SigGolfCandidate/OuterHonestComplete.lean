import SigGolfCandidate.OuterWireComplete
import SigGolfCandidate.OuterLooseHashOnly
import SigGolfCandidate.OuterCompletenessProbability
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterHonestComplete
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.SourceReplay SigGolfCandidate.T3.Correctness
open SigGolfCandidate.Research.SharedForest

def program (message : Message) : M Bool := do
  let keys←keygen
  let sig←OuterLooseSource.signCompact keys.2 message
  let some sig:=sig | pure false
  let wit←OuterExpand.expandCompact message keys.1 sig
  let some wit:=wit | pure false
  ClaudeWCT.W9.T3M.Paired.verifyP message keys.1 wit

theorem hashOnly (message : Message) : HashOnly (program message) := by
  unfold program
  refine hashOnly_bind hashOnly_keygen fun keys=>hashOnly_bind (OuterLooseHashOnly.signCompact ..) fun sig=>?_
  cases sig with
  | none=>exact hashOnly_pure _
  | some sig=>
    refine hashOnly_bind (OuterHashOnly.expandCompact ..) fun wit=>?_
    cases wit with
    | none=>exact hashOnly_pure _
    | some wit=>
      exact SigGolfCandidate.T3M.allQ_mono (ClaudeWCT.W9.T3M.Paired.publicOnly_verifyP ..)
        (by rintro ((tag|input)|coord) h <;> first | exact h.elim | trivial)

theorem expand_accepts (answers : Answers) (message : Message) (pk : Digest)
    (sig : OuterSignatureCodec.NewSig) (wit : ClaudeWCT.W9.T3M.WBytes)
    (he : evalWithAnswerFn answers (OuterExpand.expandCompact message pk sig)=some wit) :
    evalWithAnswerFn answers (ClaudeWCT.W9.T3M.Paired.verifyP message pk wit)=true := by
  unfold OuterExpand.expandCompact at he
  rw [evalWithAnswerFn_map] at he
  cases hx : evalWithAnswerFn answers (OuterExpand.expandN message pk
    (ClaudeWCT.W9.T3M.SharedCodec.sigDecC (OuterSignatureCodec.expand sig))) with
  | none=>simp only [hx,Option.map_none,reduceCtorEq] at he
  | some packet=>
    simp only [hx,Option.map_some,Option.some.injEq] at he
    subst wit
    exact OuterWireComplete.complete answers message pk _ packet.1 packet.2.1 packet.2.2 hx

theorem good (message : Message) (answers : Answers)
    (hsign : OuterSourceCompleteness.SigningComplete answers (evalWithAnswerFn answers keygen).2)
    (htree : TopTreeOK answers) (hlower : LowerTreesOK answers)
    (hforest : OuterHybridGlobalCorrectness.ForestsOK answers) :
    evalWithAnswerFn answers (program message)=true := by
  obtain ⟨raw,hr⟩:=hsign message
  have hs : evalWithAnswerFn answers (OuterExpand.signCompact (evalWithAnswerFn answers keygen).2 message)=
      some (OuterSignatureCodec.compress (ClaudeWCT.W9.T3M.SharedCodec.sigBC raw)) := by
    rw [OuterExpand.signCompact,evalWithAnswerFn_map,hr]
    rfl
  have hk:=keygen_correct answers
  obtain ⟨wit,hw⟩:=OuterCompactCorrectness.sign_expands answers _ hk.2.1 htree hlower hforest message _ hk.1 _ hs
  have ha:=expand_accepts answers message _ _ wit hw
  simp only [program,evalWithAnswerFn_bind,OuterLooseSource.sign_eq answers _ message hforest,hs,hw,ha]

theorem failure_small (message : Message) (secret : BitVec 256) :
    Pr[fun value=>value=false | (simulateQ SphincsSecurity.romImpl
      (realize secret (program message))).run' ∅]≤1/(2:ENNReal)^128 :=
  OuterCompletenessProbability.failure_small (program message) (hashOnly message) (good message) secret
#print axioms good
#print axioms failure_small
end OuterHonestComplete
