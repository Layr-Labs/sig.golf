import SigGolfCandidate.OuterHashOnly
import SigGolfCandidate.OuterHybridGlobalCorrectness
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterCodecChecks
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SigGolfCandidate.T3.SourceReplay
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.TopMoment
open ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh
open OuterForestBudget OuterHybridForestComplete

theorem build_hashOnly (first : Bool) (index coord : Nat) (selected : Child) (word : Rank)
    (pads : Nat→PairRoot) (hc : coord<9) : HashOnly (buildCoord first index coord selected word pads) :=
  ClaudeWCT.WCT9.Wots.allQueriesSatisfy_mono (OuterForestDomains.build_queries first index coord selected word pads hc)
    (fun q hq=>OuterHashOnly.fts_isHash index q hq)

theorem pair_hashOnly (index pair : Nat) (hp : pair<4) (st : Bool × PairRoot) : HashOnly (pairCheck index pair st) := by
  unfold pairCheck
  exact hashOnly_bind (build_hashOnly true index (2*pair) _ _ _ (by omega)) fun a=>
    hashOnly_bind (build_hashOnly false index (2*pair+1) _ _ _ (by omega)) (fun _=>hashOnly_pure _)

theorem forest_hashOnly (index : Nat) : HashOnly (forestCheck index) := by
  unfold forestCheck
  exact hashOnly_bind (pair_hashOnly index 0 (by decide) _) fun a=>
    hashOnly_bind (pair_hashOnly index 1 (by decide) _) fun b=>
      hashOnly_bind (pair_hashOnly index 2 (by decide) _) fun c=>
        hashOnly_bind (pair_hashOnly index 3 (by decide) _) fun d=>
          hashOnly_bind (build_hashOnly false index 8 _ _ _ (by decide)) (fun _=>hashOnly_pure _)

theorem check_hashOnly : HashOnly OuterHybridGlobalComplete.check := by
  unfold OuterHybridGlobalComplete.check
  refine hashOnly_foldlM _ _ (fun acc index=>?_) _
  unfold OuterHybridGlobalComplete.checkStep
  exact hashOnly_bind (forest_hashOnly index) (fun _=>hashOnly_pure _)

noncomputable def checks : M (Bool × Bool) := lowerCheck >>= fun low=>(fun fts=>(fts,low)) <$> OuterHybridGlobalComplete.check

theorem checks_hashOnly : HashOnly checks := by
  unfold checks
  exact hashOnly_bind hashOnly_lowerCheck (fun _=>hashOnly_map _ check_hashOnly)

theorem buildTopTree_fresh (secret : BitVec 256) (r : List (List Digest) × RCache)
    (hr : r∈support (roRun secret buildTopTree ∅)) : OuterGlobalFresh.AllFFresh r.2 :=
  OuterGlobalFresh.preserves_allF secret buildTopTree
    (fun target coord index heap ht hp=>OuterGlobalFresh.fav_buildTopTree secret target coord index heap ht hp)
    ∅ OuterGlobalFresh.allFFresh_empty r hr

theorem checks_eval (answers : SigGolfCandidate.T3.Correctness.Answers) :
    evalWithAnswerFn answers checks=
      (evalWithAnswerFn answers OuterHybridGlobalComplete.check,
       evalWithAnswerFn answers lowerCheck) := by
  simp only [checks,evalWithAnswerFn_bind,evalWithAnswerFn_map]

theorem fts_marginal (secret : BitVec 256) (cache : RCache) :
    Ev secret checks cache (fun r=>if r.1.1 then 0 else 1)=
      Ev secret OuterHybridGlobalComplete.check cache (fun r=>if r.1 then 0 else 1) := by
  symm
  exact SigGolfCandidate.Research.SharedExpansionV6.Ev_presample_fst secret OuterHybridGlobalComplete.check lowerCheck cache
    (fun b=>if b then 0 else 1)

theorem lower_marginal (secret : BitVec 256) (cache : RCache) :
    Ev secret checks cache (fun r=>if r.1.2 then 0 else 1)≤
      Ev secret lowerCheck cache (fun r=>if r.1 then 0 else 1) := by
  unfold checks
  rw [Ev_bind]
  apply Ev_mono
  intro r
  unfold Ev
  rw [roRun_map,expectedValue_map]
  exact Ev_const_le secret _ _ _

theorem checks_failure (secret : BitVec 256) (cache : RCache) (hg : AllGFresh cache)
    (hf : ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.AllFFresh cache) (hn : OuterGlobalFresh.AllFFresh cache) :
    Ev secret checks cache (fun r=>if r.1.1 && r.1.2 then 0 else 1)≤
      ENNReal.ofReal (1/(2:ℝ)^170)+ENNReal.ofReal (1/(2:ℝ)^150) := by
  calc
    _ ≤ Ev secret checks cache (fun r=>if r.1.1 then 0 else 1)+
        Ev secret checks cache (fun r=>if r.1.2 then 0 else 1) := by
      unfold Ev
      rw [←expectedValue_add]
      apply expectedValue_mono
      rintro ⟨⟨f,l⟩,c⟩
      cases f <;> cases l <;> norm_num
    _ ≤ ENNReal.ofReal (1/(2:ℝ)^170)+ENNReal.ofReal (1/(2:ℝ)^150) :=
      add_le_add ((le_of_eq (fts_marginal secret cache)).trans (OuterHybridGlobalComplete.Ev_check_false secret cache hn))
        ((lower_marginal secret cache).trans (Ev_lowerCheck_false secret cache hg hf))

#print axioms checks_failure

#print axioms check_hashOnly
#print axioms checks_hashOnly
#print axioms buildTopTree_fresh
end OuterCodecChecks
