import SigGolfCandidate.OuterSignRun
import SigGolfCandidate.OuterExpandRun
import SigGolfCandidate.OuterVerifyRun
import SigGolfCandidate.OuterLooseSource
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterRunValues
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3M
open OuterImageValidity
set_option allowUnsafeReducibility true in
attribute [local reducible] OuterRuntime.runtimeSub SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input

theorem verify (m : Message) (pk : PublicKey) (w : Bytes 21756) :
    (fun r=>r.value.isSome) <$> sub.run .verify (m,pk,w)=
      mrealize 0 (ClaudeWCT.W9.T3M.Paired.verifyP m pk w) := by
  have h:=congrArg (fun x=>(fun p : Option Unit×Nat=>p.1.isSome) <$> x) (OuterVerifyRun.refines m pk w)
  simp only [Functor.map_map] at h
  refine h.trans ?_
  have e : (fun p : Bool×Nat=>((if p.1 then some () else none : Option Unit)).isSome)=Prod.fst := by
    funext p;rcases p with ⟨_|_,n⟩ <;> rfl
  rw [e,fst_countCalls]

theorem sign (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    (fun r=>r.value) <$> sub.run .sign (sk,cache,m)=
      mrealize sk (OuterLooseSource.signCompact (SigGolfCandidate.T3M.cacheDec cache) m) := by
  have h:=congrArg (fun x=>Prod.fst <$> x) (OuterSignRun.refines sk cache m)
  simp only [Functor.map_map] at h
  conv_rhs => rw [OuterLooseSource.signCompact,mrealize_map]
  change _ = (fun o=>o.map (fun sig=>OuterLooseCodec.compress (ClaudeWCT.W9.T3M.SharedCodec.sigBC sig))) <$>
    mrealize sk (OuterSigning.sign (cacheDec cache) m)
  refine h.trans ?_
  simpa only [Functor.map_map] using congrArg
    (fun x=>(fun o=>o.map (fun sig=>OuterLooseCodec.compress (ClaudeWCT.W9.T3M.SharedCodec.sigBC sig))) <$> x)
    (fst_countBoth (mrealize sk (OuterSigning.sign (cacheDec cache) m)))

theorem expand (m : Message) (pk : PublicKey) (sig : OuterSignatureCodec.NewSig) :
    (fun r=>r.value) <$> sub.run .expand (m,pk,sig)=mrealize 0 (OuterExpand.expandCompact m pk sig) := by
  have h:=congrArg (fun x=>Prod.fst <$> x) (OuterExpandRun.refines m pk sig)
  simp only [Functor.map_map] at h
  conv_rhs => rw [OuterExpand.expandCompact,mrealize_map]
  change _ = (Option.map OuterExpandRun.encode) <$> mrealize 0 (OuterExpand.expandN m pk
    (ClaudeWCT.W9.T3M.SharedCodec.sigDecC (OuterSignatureCodec.expand sig)))
  refine h.trans ?_
  simpa only [Functor.map_map] using congrArg (fun x=>(Option.map OuterExpandRun.encode) <$> x)
    (fst_countBoth (mrealize 0 (OuterExpand.expandN m pk
      (ClaudeWCT.W9.T3M.SharedCodec.sigDecC (OuterSignatureCodec.expand sig)))))

#print axioms verify
#print axioms sign
#print axioms expand
end OuterRunValues
