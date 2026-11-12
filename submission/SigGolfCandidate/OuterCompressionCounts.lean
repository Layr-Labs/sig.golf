import SigGolfCandidate.OuterCompactCounts
import SigGolfCandidate.OuterPublicQueries
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCompressionCounts
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M.Final
open OuterImageValidity
set_option allowUnsafeReducibility true in
attribute [local reducible] OuterRuntime.runtimeSub SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input

theorem sign (sk : SecretKey) (cache : Bytes 131072) (m : Message) (hash : Hash) :
    (evalWithAnswerFn hash (sub.run .sign (sk,cache,m))).hashCompressions=
      (evalWithAnswerFn hash (mrealize sk (SigGolfCandidate.T3.Cost.countBlocks
        (OuterLooseSource.signCompact (cacheDec cache) m)))).2 :=
  abstract_count_refinement sk hash (OuterLooseSource.signCompact (cacheDec cache) m)
    (sub.run .sign (sk,cache,m)) id (OuterCompactCounts.sign sk cache m) (OuterGoodQueries.compactSign ..)

theorem expand (m : Message) (pk : PublicKey) (sig : OuterSignatureCodec.NewSig) (hash : Hash) :
    (evalWithAnswerFn hash (sub.run .expand (m,pk,sig))).hashCompressions=
      (evalWithAnswerFn hash (mrealize 0 (SigGolfCandidate.T3.Cost.countBlocks
        (OuterExpand.expandCompact m pk sig)))).2 :=
  abstract_count_refinement 0 hash (OuterExpand.expandCompact m pk sig)
    (sub.run .expand (m,pk,sig)) id (OuterCompactCounts.expand m pk sig) (OuterGoodQueries.compactExpand ..)
#print axioms sign
#print axioms expand
end OuterCompressionCounts
