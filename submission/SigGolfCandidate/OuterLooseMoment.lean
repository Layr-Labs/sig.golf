import SigGolfCandidate.OuterLooseHashOnly
import SigGolfCandidate.OuterCodecChecks
import SigGolfCandidate.OuterLooseReplay
import SigGolfCandidate.OuterExpansionWorst
import SigGolfCandidate.OuterExpansionMoment
import SigGolfCandidate.OuterLooseBudget
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterLooseMoment
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Correctness (Answers builtTree treeValue)
open SigGolfCandidate.T3.SourceReplay
open SigGolfCandidate.T3.CountedReplay (hashOnly_countBlocks support_replay)
open SigGolfCandidate.T3.ExpansionClosure (jointCounts)
open SigGolfCandidate.Research.SharedExpansionV6 (keygenRest keygen_split jointCounts_bind eval_joint_cost_le_add Ev_presample_fst)
open ClaudeWCT.W9.T3.TopMoment
open OuterExpansionMoment (fields)
attribute [local instance] Classical.propDecidable

def joint (message : Message) : M (Nat × Nat) :=
  jointCounts keygen (fun keys=>OuterLooseSource.signCompact keys.2 message) (fun keys sig=>OuterExpand.expandCompact message keys.1 sig)

def afterKeys (message : Message) (keys : Digest × SigGolfCandidate.T3.Cache) : M (Nat × Nat) :=
  jointCounts (pure keys) (fun keys=>OuterLooseSource.signCompact keys.2 message) (fun keys sig=>OuterExpand.expandCompact message keys.1 sig)

def jointL (message : Message) : M ((Nat × Nat) × List (List Digest)) :=
  buildTopTree >>= fun levels=>(fun c=>(c,levels)) <$> (keygenRest levels >>= afterKeys message)

noncomputable def jointLB (message : Message) : M (((Nat × Nat) × List (List Digest)) × (Bool × Bool)) :=
  buildTopTree >>= fun levels=>OuterCodecChecks.checks >>= fun b=>
    (fun a=>(a,b)) <$> ((fun c=>(c,levels)) <$> (keygenRest levels >>= afterKeys message))

theorem joint_eq (message : Message) : joint message=Prod.fst <$> jointL message := by
  unfold joint
  rw [jointCounts_bind,keygen_split]
  unfold jointL afterKeys
  simp only [bind_assoc,map_bind,Functor.map_map,id_map']

theorem checked_eval (answers : Answers) (message : Message) : evalWithAnswerFn answers (jointLB message)=
    ((evalWithAnswerFn answers (joint message),builtTree answers 0 0),evalWithAnswerFn answers OuterCodecChecks.checks) := by
  rw [joint_eq]
  unfold jointLB jointL
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_map,SigGolfCandidate.T3.Correctness.eval_buildTopTree]

theorem afterKeys_hashOnly (message : Message) (keys : Digest × SigGolfCandidate.T3.Cache) : HashOnly (afterKeys message keys) := by
  unfold afterKeys jointCounts
  simp only [pure_bind]
  refine hashOnly_bind (hashOnly_countBlocks _ (OuterLooseHashOnly.signCompact ..)) fun signed=>?_
  cases signed.1
  · exact hashOnly_pure _
  · exact hashOnly_bind (hashOnly_countBlocks _ (OuterHashOnly.expandCompact ..)) (fun _=>hashOnly_pure _)

attribute [local irreducible] afterKeys keygenRest

theorem jointLB_hashOnly (message : Message) : HashOnly (jointLB message) := by
  unfold jointLB
  refine hashOnly_bind hashOnly_buildTopTree ?_
  intro levels
  refine hashOnly_bind OuterCodecChecks.checks_hashOnly ?_
  intro b
  apply hashOnly_map (fun a : (Nat × Nat) × List (List Digest)=>(a,b))
  apply hashOnly_map (fun c : Nat × Nat=>(c,levels))
  refine hashOnly_bind (OuterExpansionMoment.keygenRest_hashOnly levels) ?_
  intro keys
  exact afterKeys_hashOnly message keys

theorem presample (secret : BitVec 256) (message : Message) (F : (Nat × Nat)→ℝ≥0∞) :
    Ev secret (jointL message) ∅ (fun r=>F r.1.1)=
      Ev secret (jointLB message) ∅ (fun r=>F r.1.1.1) := by
  unfold jointL jointLB
  rw [Ev_bind,Ev_bind]
  congr 1
  funext r
  exact Ev_presample_fst secret _ OuterCodecChecks.checks r.2 (fun a : (Nat × Nat) × List (List Digest)=>F a.1)

noncomputable def rareWeight : ℝ≥0∞ := ENNReal.ofReal (2^19)
noncomputable def excess (levels : List (List Digest)) (b : Bool × Bool) : ℝ≥0∞ :=
  OuterExpandSlack.extraWeight (fields levels)+(if TopLevelsOK levels then 0 else 1)*rareWeight+
    (if b.1 && b.2 then 0 else 1)*rareWeight

theorem pointwise (answers : Answers) (message : Message) :
    (2:ℝ≥0∞)^((8/7:ℝ)*(((evalWithAnswerFn answers (joint message)).2-
      (evalWithAnswerFn answers (joint message)).1:Nat):ℝ)/1048576)≤
      excess (builtTree answers 0 0) (evalWithAnswerFn answers OuterCodecChecks.checks) := by
  classical
  let levels := builtTree answers 0 0
  let b := evalWithAnswerFn answers OuterCodecChecks.checks
  by_cases ht : TopLevelsOK levels
  · by_cases hb : (b.1 && b.2) = true
    · have htree : SigGolfCandidate.Research.SharedForest.TopTreeOK answers := ht
      have hf : evalWithAnswerFn answers OuterHybridGlobalComplete.check=true := by
        have hboth : b.1=true ∧ b.2=true := by simpa only [Bool.and_eq_true] using hb
        have := hboth.1
        simpa only [b,OuterCodecChecks.checks_eval] using this
      have hl : evalWithAnswerFn answers ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.lowerCheck=true := by
        have hboth : b.1=true ∧ b.2=true := by simpa only [Bool.and_eq_true] using hb
        have := hboth.2
        simpa only [b,OuterCodecChecks.checks_eval] using this
      have hle := eval_joint_cost_le_add answers keygen (fun keys=>OuterLooseSource.signCompact keys.2 message)
        (fun keys sig=>OuterExpand.expandCompact message keys.1 sig) (137288+fields levels)
        (fun sig hs=>by
          have hc:=OuterLooseReplay.good_excess answers message sig htree
            (ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.eval_lowerCheck_true answers hl)
            (OuterHybridGlobalCorrectness.eval_check_true answers hf) hs
          simpa only [fields,SigGolfCandidate.T3.Correctness.treeValue,Nat.add_assoc,levels] using hc)
      change (evalWithAnswerFn answers (joint message)).2≤
        (evalWithAnswerFn answers (joint message)).1+(137288+fields levels) at hle
      have hsub : (evalWithAnswerFn answers (joint message)).2-
          (evalWithAnswerFn answers (joint message)).1≤137288+fields levels := by omega
      change _≤excess levels b
      simp only [excess,if_pos ht,if_pos hb,zero_mul,add_zero]
      unfold OuterExpandSlack.extraWeight
      simp only [SigGolfCandidate.Research.SharedForest.expandReplayExtra,Nat.reduceAdd]
      apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hsub) (by norm_num)) (by norm_num)
    · have hle := eval_joint_cost_le_add answers keygen (fun keys=>OuterLooseSource.signCompact keys.2 message)
        (fun keys sig=>OuterExpand.expandCompact message keys.1 sig) (2^24)
        (fun sig _=>(OuterExpansionWorst.cost_expandCompact answers message _ sig).trans (Nat.le_add_left _ _))
      change (evalWithAnswerFn answers (joint message)).2≤(evalWithAnswerFn answers (joint message)).1+2^24 at hle
      have hsub : (evalWithAnswerFn answers (joint message)).2-(evalWithAnswerFn answers (joint message)).1≤2^24 := by omega
      refine (OuterExpansionWorst.excess_weight _ hsub).trans ?_
      change rareWeight≤excess levels b
      simp only [excess,if_pos ht,if_neg hb,zero_mul,one_mul,add_zero]
      exact le_add_self
  · have hle := eval_joint_cost_le_add answers keygen (fun keys=>OuterLooseSource.signCompact keys.2 message)
      (fun keys sig=>OuterExpand.expandCompact message keys.1 sig) (2^24)
      (fun sig _=>(OuterExpansionWorst.cost_expandCompact answers message _ sig).trans (Nat.le_add_left _ _))
    change (evalWithAnswerFn answers (joint message)).2≤(evalWithAnswerFn answers (joint message)).1+2^24 at hle
    have hsub : (evalWithAnswerFn answers (joint message)).2-(evalWithAnswerFn answers (joint message)).1≤2^24 := by omega
    refine (OuterExpansionWorst.excess_weight _ hsub).trans ?_
    change rareWeight≤excess levels b
    simp only [excess,if_neg ht,one_mul]
    exact (le_add_self).trans le_self_add

theorem support_excess (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (jointLB message) ∅)
      (fun r=>(2:ℝ≥0∞)^((8/7:ℝ)*((r.1.1.1.2-r.1.1.1.1:Nat):ℝ)/1048576))≤
      Ev secret (jointLB message) ∅ (fun r=>excess r.1.1.2 r.1.2) := by
  apply expectedValue_mono_of_support
  intro r hr
  obtain ⟨hash,_,heval⟩:=support_replay secret _ (jointLB_hashOnly message) ∅ r hr
  rw [heval,checked_eval]
  exact pointwise (fixedAnswers secret hash) message

#print axioms pointwise
#print axioms support_excess

#print axioms checked_eval
#print axioms jointLB_hashOnly
#print axioms presample
end OuterLooseMoment
