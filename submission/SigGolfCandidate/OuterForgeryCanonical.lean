import SigGolfCandidate.OuterFreshSignature
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterExpansionSecurity
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots (entriesOf)
open SigGolfCandidate.T3.Security.WotsExtract (entriesOf_mono)
open SigGolfCandidate.Research.SharedForest W9Machine
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open ClaudeWCT.W9.T3.Security.CanonicalExtract
theorem checkForgery_canonical_or_collision (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (hcache : published.region = cacheRegion (maskedTop answers)) (pk : Digest)
    (hpk : pk = Extract.honestRoot answers 0 0) (log : QueryLog Final.Paired.Requests)
    (hlog : ∀ entry ∈ log, entry.2 = evalWithAnswerFn answers (OuterLifted.ClaudeWCT.W9.T3.Security.WPair.Paired.authenticatedSign published entry.1))
    (forgery : Final.Paired.ForgeryP)
    (haccept : evalWithAnswerFn answers (OuterSecurityGame.checkForgery pk log forgery) = true) :
    OuterLifted.ClaudeWCT.W9.T3.Security.CanonicalExtract.WotsPrimitiveSrc answers (OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers)
        (entriesOf answers (queried answers (OuterSecurityGame.checkForgery pk log forgery))) ∨
      OuterLifted.ClaudeWCT.W9.T3M.Extract.Paired.FtsHitIn answers (queried answers (OuterSecurityGame.checkForgery pk log forgery)) ∨
      ∃ (message : Message) (wb : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput),
        OuterLifted.ClaudeWCT.W9.T3M.Final.Paired.WitnessOf answers pk forgery message wb ∧
        (wdc wb).toNat < WCT9.digestVerifyWindow ∧
        evalWithAnswerFn answers (digest (wrho wb) message (wdc wb)) = output ∧
        (.inl (.inr (pad64 (digestInput (wrho wb) message (wdc wb)))) : Spec.Domain) ∈
          queried answers (OuterSecurityGame.checkForgery pk log forgery) ∧
        output.toNat / 2^242 % 16384 < 929 ∧
        (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
        (∀ lay : Layer, Good answers (OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers) wb (WCT9.digestIndex output) lay) ∧
        OuterLifted.ClaudeWCT.W9.T3M.Extract.Paired.ForestOpenings answers wb (WCT9.digestIndex output)
          (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)) ∧
        ¬ ClaudeWCT.W9.T3.Security.WPair.Paired.SignedDigest log message (wrho wb) := by
  obtain ⟨hfresh,message,wb,hw,hv,hsub⟩ := OuterLifted.ClaudeWCT.W9.T3M.Final.Paired.check_accepting answers pk log forgery haccept
  obtain ⟨output,hc,hd,hq,hgate,hrank,hcases⟩ :=
    OuterLifted.ClaudeWCT.W9.T3.Security.CanonicalExtract.verifyP_canonical_or_collision answers message pk wb hpk hv
  rcases hcases with hp | hh | ⟨hg,ho⟩
  · exact Or.inl (hp.mono (entriesOf_mono hsub))
  · exact Or.inr (Or.inl (hh.mono hsub))
  · refine Or.inr (Or.inr ⟨message,wb,output,hw,hc,hd,hsub _ hq,hgate,hrank,hg,ho,?_⟩)
    cases forgery with
    | witness sourceMessage sourceWitness =>
        obtain ⟨hm,hb⟩ := hw
        subst sourceMessage sourceWitness
        exact ClaudeWCT.W9.T3.Security.WPair.Paired.fresh_witness_not_signed_digest log message wb (wrho wb) hfresh
    | signature sourceMessage sig =>
        obtain ⟨hm,he⟩ := hw
        subst sourceMessage
        obtain ⟨N,w,ns,hn,rfl⟩:=OuterRawExpandFacts.expandB_some answers message pk sig wb he
        have hout : N=output := (OuterRawExpandFacts.digest answers message pk sig N w ns hn).symm.trans hd
        subst N
        rw [OuterRawExpandFacts.nonce answers message pk sig output w ns hn]
        exact OuterExpansionSecurity.fresh_signature_not_signed_digest answers published hcache log hlog
          message pk sig output w ns hfresh hn hg ho

#print axioms OuterExpansionSecurity.checkForgery_canonical_or_collision
end OuterExpansionSecurity
