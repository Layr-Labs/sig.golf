import SigGolfCandidate.OuterHashOnly
import SigGolfCandidate.OuterExpandSlack
import SigGolfCandidate.OuterSigningEnvelope
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterExpansionMoment
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Correctness (Answers builtTree treeValue)
open SigGolfCandidate.T3.SourceReplay
open SigGolfCandidate.T3.CountedReplay (hashOnly_countBlocks support_replay)
open SigGolfCandidate.T3.ExpansionClosure (jointCounts)
open SigGolfCandidate.Research.SharedExpansionV6 (keygenRest payloadTail keygen_split jointCounts_bind eval_joint_cost_le_add TopPrefixOK)
open ClaudeWCT.W9.T3.TopMoment
open SigGolfCandidate.Research.SharedForest (topField)

def joint (message : Message) : M (Nat × Nat) :=
  jointCounts keygen (fun keys=>OuterSigning.sign keys.2 message) (fun keys sig=>OuterExpand.expandN message keys.1 sig)

def afterKeys (message : Message) (keys : Digest × SigGolfCandidate.T3.Cache) : M (Nat × Nat) :=
  jointCounts (pure keys) (fun keys=>OuterSigning.sign keys.2 message) (fun keys sig=>OuterExpand.expandN message keys.1 sig)

def jointL (message : Message) : M ((Nat × Nat) × List (List Digest)) :=
  buildTopTree >>= fun levels=>(fun c=>(c,levels)) <$> (keygenRest levels >>= afterKeys message)

theorem joint_eq (message : Message) : joint message=Prod.fst <$> jointL message := by
  unfold joint
  rw [jointCounts_bind,keygen_split]
  unfold jointL afterKeys
  simp only [bind_assoc,map_bind,Functor.map_map,id_map']

theorem joint_eval (answers : Answers) (message : Message) : evalWithAnswerFn answers (jointL message)=
    (evalWithAnswerFn answers (joint message),builtTree answers 0 0) := by
  rw [joint_eq]
  unfold jointL
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_map,SigGolfCandidate.T3.Correctness.eval_buildTopTree]

theorem keygenRest_hashOnly (levels : List (List Digest)) : HashOnly (keygenRest levels) := by
  unfold keygenRest payloadTail maskedLevel pairedMask
  hashes

theorem afterKeys_hashOnly (message : Message) (keys : Digest × SigGolfCandidate.T3.Cache) : HashOnly (afterKeys message keys) := by
  unfold afterKeys jointCounts
  simp only [pure_bind]
  refine hashOnly_bind (hashOnly_countBlocks _ (OuterHashOnly.sign ..)) fun signed=>?_
  cases signed.1
  · exact hashOnly_pure _
  · exact hashOnly_bind (hashOnly_countBlocks _ (OuterHashOnly.expandN ..)) (fun _=>hashOnly_pure _)

attribute [local irreducible] keygenRest afterKeys

set_option maxHeartbeats 200000 in
theorem jointL_hashOnly (message : Message) : HashOnly (jointL message) := by
  unfold jointL
  refine hashOnly_bind hashOnly_buildTopTree ?_
  intro levels
  apply hashOnly_map (fun c : Nat × Nat=>(c,levels))
  refine hashOnly_bind (keygenRest_hashOnly levels) ?_
  intro keys
  exact afterKeys_hashOnly message keys

def fields (levels : List (List Digest)) : Nat :=
  max (topField ((levels.getD 11 []).getD 0 0)) (topField ((levels.getD 11 []).getD 1 0))

theorem field_moment (secret : BitVec 256) (message : Message) :
    Ev secret (jointL message) ∅ (fun r=>OuterExpandSlack.extraWeight (fields r.1.2))≤ENNReal.ofReal (194/100) := by
  unfold jointL
  rw [Ev_bind]
  refine le_trans (Ev_mono secret buildTopTree ∅ (F':=fun r=>OuterExpandSlack.extraWeight (fields r.1)) (fun r=>?_)) ?_
  · unfold Ev
    rw [roRun_map,expectedValue_map]
    exact Ev_const_le secret _ _ _
  · obtain ⟨γ,pre,sel,k,heq,hpre⟩:=topPrefixOK secret
    rw [heq]
    refine (Ev_buildTop_rootChildren secret pre sel k hpre OuterExpandSlack.extraWeight).trans ?_
    exact OuterExpandSlack.numeric_extra

theorem excess_moment (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (joint message) ∅)
      (fun r=>(2:ℝ≥0∞)^((8/7:ℝ)*((r.1.2-r.1.1:Nat):ℝ)/1048576))≤ENNReal.ofReal (194/100) := by
  classical
  rw [joint_eq,roRun_map,expectedValue_map]
  have hpt : ∀ r∈support (roRun secret (jointL message) ∅),
      (2:ℝ≥0∞)^((8/7:ℝ)*((r.1.1.2-r.1.1.1:Nat):ℝ)/1048576)≤
        OuterExpandSlack.extraWeight (fields r.1.2) := by
    intro r hr
    obtain ⟨hash,_,heval⟩:=support_replay secret _ (jointL_hashOnly message) ∅ r hr
    let answers:=fixedAnswers secret hash
    have hle : (evalWithAnswerFn answers (joint message)).2≤
        (evalWithAnswerFn answers (joint message)).1+145480+fields (builtTree answers 0 0) := by
      have h:=eval_joint_cost_le_add answers keygen (fun keys=>OuterSigning.sign keys.2 message)
        (fun keys sig=>OuterExpand.expandN message keys.1 sig) (145480+fields (builtTree answers 0 0))
        (fun sig hs=>by
          have hc:=OuterPayloadCost.expand_cost_le_sign_field answers message sig hs
          simpa only [fields,treeValue,Nat.add_assoc] using hc)
      simpa only [joint,Nat.add_assoc] using h
    have hsub : (evalWithAnswerFn answers (joint message)).2-(evalWithAnswerFn answers (joint message)).1≤
        145480+fields (builtTree answers 0 0) := by omega
    rw [heval,joint_eval]
    simp only [OuterExpandSlack.extraWeight,SigGolfCandidate.Research.SharedForest.expandReplayExtra,Nat.reduceAdd]
    apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
    have hc : (((evalWithAnswerFn answers (joint message)).2-(evalWithAnswerFn answers (joint message)).1:Nat):ℝ)≤
        ((145480+fields (builtTree answers 0 0):Nat):ℝ) := Nat.cast_le.mpr hsub
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) (by norm_num)
  exact (expectedValue_mono_of_support hpt).trans (field_moment secret message)

theorem joint_sign_moment (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (joint message) ∅) (fun r=>(2:ℝ≥0∞)^((r.1.1:ℝ)/131072))≤2 := by
  refine le_trans ?_ (OuterSigningEnvelope.honest_sign_exponential_budget secret message)
  simp only [joint,jointCounts,OuterSigningEnvelope.honestSignCount,roRun_bind,expectedValue_bind]
  apply expectedValue_mono
  intro keys
  apply expectedValue_mono
  rintro ⟨⟨sig,signCost⟩,rcache⟩
  cases sig with
  | none => simp only [roRun_pure,expectedValue_pure,le_refl]
  | some sig =>
    simp only [roRun_bind,expectedValue_bind]
    apply expectedValue_le_of_support
    intro expanded _
    simp only [roRun_pure,expectedValue_pure,le_refl]

theorem honest_expand_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (joint message) ∅) (fun r=>(2:ℝ≥0∞)^((r.1.2:ℝ)/1048576))≤2 := by
  have hs:=joint_sign_moment secret message
  have hd : expectedValue (roRun secret (joint message) ∅)
      (fun r=>(2:ℝ≥0∞)^((8/7:ℝ)*((r.1.2-r.1.1:Nat):ℝ)/1048576))≤2 :=
    (excess_moment secret message).trans (by norm_num)
  exact ClaudeWCT.Arith.ExpectHolder.expand_moment_of_holder (roRun secret (joint message) ∅)
    (fun r=>r.1.1) (fun r=>r.1.2) hs hd

#print axioms joint_sign_moment
#print axioms honest_expand_exponential_budget

#print axioms excess_moment

#print axioms joint_eval
#print axioms jointL_hashOnly
#print axioms field_moment
end OuterExpansionMoment
