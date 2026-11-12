import SigGolfCandidate.OuterExpandedEq
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
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open ClaudeWCT.W9.T3.Security.WPair.Paired
open SigGolfCandidate.T3.Security
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
theorem fresh_signature_not_signed_digest (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (hcache : published.region=cacheRegion (maskedTop answers)) (log : QueryLog ClaudeWCT.W9.T3.Security.WPair.Paired.Requests)
    (hlog : ∀entry∈log,entry.2=evalWithAnswerFn answers
      (OuterLifted.ClaudeWCT.W9.T3.Security.WPair.Paired.authenticatedSign published entry.1))
    (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat)
    (hfresh : Final.Paired.Fresh log (.signature message sig))
    (he : evalWithAnswerFn answers (OuterExpand.expandN message pk sig)=some (output,w,ns))
    (hg : ∀lay,ClaudeWCT.W9.T3.Security.CanonicalExtract.Good answers
      (OuterLifted.ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.sourceMessages answers)
      (OuterExpand.witEncOuter output w ns) (WCT9.digestIndex output) lay)
    (ho : OuterLifted.ClaudeWCT.W9.T3M.Extract.Paired.ForestOpenings answers (OuterExpand.witEncOuter output w ns)
      (WCT9.digestIndex output) (rawChildFromOutput output) (fun coord=>WCT9.embed (forestRank output coord.val))) :
    ¬SignedDigest log message sig.rho := by
  classical
  rintro ⟨entry,hin,hm,signed,hsigned,hrho⟩
  have hreply:=hlog entry hin
  rw [hsigned,OuterLifted.ClaudeWCT.W9.T3.Security.WPair.Paired.eval_authenticatedSign] at hreply
  have hsource : evalWithAnswerFn answers (OuterSigning.signPayload published message)=some signed := by
    by_cases hc : entry.1.cache=published
    · rw [if_pos hc,hc,hm] at hreply
      exact hreply.symm
    · rw [if_neg hc] at hreply
      cases hreply
  have hwire:=same_nonce_signed_wire answers published hcache message pk sig signed output w ns he hg ho hsource hrho.symm
  apply hfresh
  refine ⟨entry,hin,hm,?_⟩
  rw [hsigned,Option.map_some,hwire]
#print axioms fresh_signature_not_signed_digest
end OuterExpansionSecurity
