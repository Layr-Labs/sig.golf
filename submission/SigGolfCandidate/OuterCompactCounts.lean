import SigGolfCandidate.OuterRunValues
import SigGolfCandidate.OuterGoodQueries
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCompactCounts
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3M
open OuterImageValidity
set_option allowUnsafeReducibility true in
attribute [local reducible] OuterRuntime.runtimeSub SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input

theorem countBoth_map {α β : Type} (f : α→β) (p : OracleComp HashSpec α) :
    countBoth (f <$> p)=(fun q=>(f q.1,q.2)) <$> countBoth p := by
  simp only [countBoth,simulateQ_map,StateT.run_map]

theorem sign (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    (fun r=>(r.value,r.hashCalls,r.hashCompressions)) <$> sub.run .sign (sk,cache,m)=
      (fun p=>(p.1,p.2.1,p.2.2)) <$>
        countBoth (mrealize sk (OuterLooseSource.signCompact (cacheDec cache) m)) := by
  conv_rhs => rw [OuterLooseSource.signCompact,mrealize_map,countBoth_map,Functor.map_map]
  exact OuterSignRun.refines sk cache m

theorem expand (m : Message) (pk : PublicKey) (sig : OuterSignatureCodec.NewSig) :
    (fun r=>(r.value,r.hashCalls,r.hashCompressions)) <$> sub.run .expand (m,pk,sig)=
      (fun p=>(p.1,p.2.1,p.2.2)) <$>
        countBoth (mrealize 0 (OuterExpand.expandCompact m pk sig)) := by
  conv_rhs => rw [OuterExpand.expandCompact,mrealize_map,countBoth_map,Functor.map_map]
  exact OuterExpandRun.refines m pk sig
#print axioms sign
#print axioms expand
end OuterCompactCounts
