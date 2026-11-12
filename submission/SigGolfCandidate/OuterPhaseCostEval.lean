import SigGolfCandidate.OuterCompressionCounts
import SigGolfCandidate.OuterKeygenValue
import SigGolfCandidate.OuterLooseExpansionBudget
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterPhaseCostEval
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3 (keygen)
open OuterImageValidity
set_option allowUnsafeReducibility true in
attribute [local reducible] OuterRuntime.runtimeSub SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
attribute [local irreducible] SigGolfCandidate.Legacy.Submission.run

theorem key_value (sk : SecretKey) (hash : Hash) :
    (sub.runWith hash .keygen sk).value=some
      ((evalWithAnswerFn hash (mrealize sk keygen)).1,cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2) := by
  have h:=congrArg (evalWithAnswerFn hash) (OuterKeygenValue.value sk)
  simpa only [evalWithAnswerFn_map,Submission.runWith] using h

theorem sign (sk : SecretKey) (m : Message) (hash : Hash) :
    evalWithAnswerFn hash ((fun r=>r.costs .sign) <$> sub.honest sk m)=
      evalWithAnswerFn hash ((fun r=>r.2) <$> mrealize sk (OuterLooseBudget.honestSignCount m)) := by
  have h:=generic_outer_sign_cost sub hash sk m (mrealize sk keygen)
    (fun key=>(key.1,cacheB key.2))
    (fun key=>Prod.snd <$> mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (OuterLooseSource.signCompact key.2 m)))
    (key_value sk hash) (fun key=>by
      rw [evalWithAnswerFn_map]
      simpa only [cacheDec_cacheB,Submission.runWith] using OuterCompressionCounts.sign sk (cacheB key.2) m hash)
  exact h.trans (congrArg (evalWithAnswerFn hash)
    (generic_count_pipeline sk keygen (fun key=>SigGolfCandidate.T3.Cost.countBlocks (OuterLooseSource.signCompact key.2 m)) Prod.snd))

theorem sign_value (sk : SecretKey) (cache : SigGolfCandidate.T3.Cache) (m : Message) (hash : Hash) :
    (sub.runWith hash .sign (sk,cacheB cache,m)).value=
      (evalWithAnswerFn hash (mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (OuterLooseSource.signCompact cache m)))).1 := by
  have h:=congrArg (evalWithAnswerFn hash) (OuterRunValues.sign sk (cacheB cache) m)
  simp only [evalWithAnswerFn_map,cacheDec_cacheB] at h
  rw [eval_mrealize] at h ⊢
  rw [SigGolfCandidate.T3.Cost.countBlocks,eval_cost_fst]
  simpa only [Submission.runWith] using h

theorem expand_cost (sk : SecretKey) (m : Message) (pk : PublicKey) (sig : OuterSignatureCodec.NewSig) (hash : Hash) :
    (sub.runWith hash .expand (m,pk,sig)).hashCompressions=
      evalWithAnswerFn hash (Prod.snd <$> mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (OuterExpand.expandCompact m pk sig))) := by
  have h:=OuterCompressionCounts.expand m pk sig hash
  have hp : AllQueriesSatisfy (SigGolfCandidate.T3.Cost.countBlocks (OuterExpand.expandCompact m pk sig)) isPublic :=
    allQ_countWith SigGolfCandidate.T3.Cost.weight (OuterPublicQueries.expandCompact m pk sig)
  rw [mrealize_public 0 sk hp] at h
  rw [evalWithAnswerFn_map]
  simpa only [Submission.runWith] using h

theorem expand (sk : SecretKey) (m : Message) (hash : Hash) :
    evalWithAnswerFn hash ((fun r=>r.costs .expand) <$> sub.honest sk m)=
      evalWithAnswerFn hash ((fun r=>r.2) <$> mrealize sk (OuterLooseMoment.joint m)) := by
  have h:=generic_outer_expand_cost sub hash sk m (mrealize sk keygen)
    (fun key=>(key.1,cacheB key.2))
    (fun key=>mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (OuterLooseSource.signCompact key.2 m))) Prod.fst id
    (fun key sig=>Prod.snd <$> mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (OuterExpand.expandCompact m key.1 sig)))
    (key_value sk hash) (fun key=>by simpa only [Option.map_id,id_eq] using sign_value sk key.2 m hash)
    (fun key sig=>expand_cost sk m key.1 sig hash)
  exact h.trans (congrArg (evalWithAnswerFn hash)
    (generic_joint_count_pipeline sk keygen (fun key=>OuterLooseSource.signCompact key.2 m)
      (fun key sig=>OuterExpand.expandCompact m key.1 sig)))
#print axioms sign
#print axioms expand
end OuterPhaseCostEval
