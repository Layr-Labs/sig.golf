import SigGolfCandidate.OuterRunValues
import SigGolfCandidate.OuterKeygenValue
import SigGolfCandidate.OuterPublicQueries
import SigGolfCandidate.OuterAllMessagesComplete
import SigGolfCandidate.OuterGoodQueries
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterRuntimeComplete
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.Legacy SigGolfCandidate.Bridge
open SigGolfCandidate.T3 (M Spec keygen realize)
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open ClaudeWCT.W9.T3M.Final
open OuterImageValidity
set_option allowUnsafeReducibility true in
attribute [local reducible] OuterRuntime.runtimeSub SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input

theorem successPipe_eq (sk : SecretKey) (m : Message) :
    successPipe sub sk m=mrealize sk (OuterHonestComplete.program m) := by
  unfold successPipe OuterHonestComplete.program
  rw [OuterKeygenValue.value,bind_map_left,mrealize_bind]
  refine bind_congr fun kp=>?_
  simp only
  rw [OuterRunValues.sign,cacheDec_cacheB,mrealize_bind]
  refine bind_congr fun s=>?_
  cases s with
  | none=>rfl
  | some sig=>
    simp only
    rw [OuterRunValues.expand,mrealize_bind,
      mrealize_public 0 sk (OuterPublicQueries.expandCompact m kp.1 sig)]
    refine bind_congr fun e=>?_
    cases e with
    | none=>rfl
    | some w=>exact (OuterRunValues.verify m kp.1 w).trans (mrealize_public 0 sk (ClaudeWCT.W9.T3M.Paired.publicOnly_verifyP m kp.1 w))

theorem allSucceed_eq (sk : SecretKey) :
    HonestSummary.allSucceed <$> sub.allMessages sk=mrealize sk OuterAllMessagesComplete.program := by
  rw [allSucceed_allMessages,OuterAllMessagesComplete.program,mrealize_foldAll]
  exact congrArg (fun F=>foldAll msgs F true) (funext fun m=>by rw [success_honest_eq,successPipe_eq])

theorem good_program (message : Message) :
    AllQueriesSatisfy (OuterHonestComplete.program message) SigGolfCandidate.T3.Cost.GoodQuery := by
  unfold OuterHonestComplete.program
  refine allQ_bind goodQ_keygen fun keys=>allQ_bind (OuterGoodQueries.compactSign ..) fun sig=>?_
  cases sig with
  | none=>exact allQ_pure _
  | some sig=>
    refine allQ_bind (OuterGoodQueries.compactExpand ..) fun wit=>?_
    cases wit with
    | none=>exact allQ_pure _
    | some w=>exact ClaudeWCT.W9.T3M.Paired.goodQ_verifyP ..

theorem randomOracle_core (sk : SecretKey) :
    withRandomOracle (mrealize sk OuterAllMessagesComplete.program)=
      (simulateQ SphincsSecurity.romImpl (realize sk OuterAllMessagesComplete.program)).run' ∅ := by
  have hgood : AllQueriesSatisfy OuterAllMessagesComplete.program SigGolfCandidate.T3.Cost.GoodQuery:=
    allQ_foldAll' msgs OuterHonestComplete.program good_program true
  have hhash:=OuterAllMessagesComplete.hashOnly
  unfold withRandomOracle
  rw [mrealize_eq_relabel,←run'_relabel_on toQ {l|Aligned l} toQ_injOn _ (allQ_hrealize sk hgood) ∅ ∅
    (fun _ _=>rfl),realize_eq_liftM sk hhash,SphincsSecurity.romImpl,
    QueryImpl.simulateQ_add_liftM_right]

theorem complete : sub.Complete := by
  intro sk
  have hP : Pr[fun summary=>summary.allSucceed=true | withRandomOracle (sub.allMessages sk)]=
      Pr[=true | withRandomOracle (mrealize sk OuterAllMessagesComplete.program)] := by
    rw [←allSucceed_eq sk,withRandomOracle_map',←probEvent_eq_eq_probOutput,probEvent_map]
    rfl
  rw [hP,randomOracle_core sk]
  exact OuterAllMessagesComplete.complete sk
#print axioms complete
end OuterRuntimeComplete
