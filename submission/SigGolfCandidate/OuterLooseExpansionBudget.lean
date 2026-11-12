import SigGolfCandidate.OuterLooseMoment
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterLooseExpansionBudget
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.SourceReplay
open ClaudeWCT.W9.T3.TopMoment
open OuterLooseMoment
open OuterExpansionMoment (fields)
open SigGolfCandidate.Research.SharedExpansionV6 (keygenRest TopPrefixOK)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OuterLooseMoment.afterKeys keygenRest
noncomputable def base (levels : List (List Digest)) : ℝ≥0∞ :=
  OuterExpandSlack.extraWeight (fields levels)+(if TopLevelsOK levels then 0 else 1)*rareWeight

theorem field_moment (secret : BitVec 256) :
    Ev secret buildTopTree ∅ (fun r=>OuterExpandSlack.extraWeight (fields r.1))≤ENNReal.ofReal (194/100) := by
  obtain ⟨γ,pre,sel,k,heq,hpre⟩:=topPrefixOK secret
  rw [heq]
  exact (Ev_buildTop_rootChildren secret pre sel k hpre OuterExpandSlack.extraWeight).trans OuterExpandSlack.numeric_extra

theorem base_moment (secret : BitVec 256) :
    Ev secret buildTopTree ∅ (fun r=>base r.1)≤
      ENNReal.ofReal (194/100)+ENNReal.ofReal (1/(2:ℝ)^135)*rareWeight := by
  unfold Ev base
  rw [expectedValue_add,expectedValue_mul_const]
  exact add_le_add (field_moment secret) (mul_le_mul' (Ev_buildTopTree_bad secret) le_rfl)

theorem checked_moment (secret : BitVec 256) (message : Message) :
    Ev secret (jointLB message) ∅ (fun r=>excess r.1.1.2 r.1.2)≤2 := by
  unfold jointLB
  rw [Ev_bind]
  have hinner : ∀ r∈support (roRun secret buildTopTree ∅),
      Ev secret (OuterCodecChecks.checks >>= fun b=>
        (fun a=>(a,b)) <$> ((fun c=>(c,r.1)) <$> (keygenRest r.1 >>= OuterLooseMoment.afterKeys message))) r.2
        (fun x=>excess x.1.1.2 x.1.2)≤base r.1+
          (ENNReal.ofReal (1/(2:ℝ)^170)+ENNReal.ofReal (1/(2:ℝ)^150))*rareWeight := by
    intro r hr
    rw [Ev_bind]
    have hc : ∀ (b : Bool×Bool) (σ : RCache),
        Ev secret ((fun a=>(a,b)) <$> ((fun c=>(c,r.1)) <$> (keygenRest r.1 >>= OuterLooseMoment.afterKeys message))) σ
          (fun x=>excess x.1.1.2 x.1.2)≤excess r.1 b := by
      intro b σ
      unfold Ev
      rw [roRun_map,expectedValue_map,roRun_map,expectedValue_map]
      exact Ev_const_le secret _ σ _
    refine le_trans (Ev_mono _ _ _ (fun x=>hc x.1 x.2)) ?_
    have hg:=ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.buildTopTree_allGFresh secret ∅
      ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh.allGFresh_empty r hr
    have hf:=ClaudeWCT.W9.T3.Freshness.Paired.FtsComplete.buildTopTree_allFFresh secret ∅
      ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.allFFresh_empty r hr
    have hn:=OuterCodecChecks.buildTopTree_fresh secret r hr
    have hsplit : Ev secret OuterCodecChecks.checks r.2 (fun x=>excess r.1 x.1)=
        Ev secret OuterCodecChecks.checks r.2 (fun _=>base r.1)+
        Ev secret OuterCodecChecks.checks r.2 (fun x=>if x.1.1 && x.1.2 then 0 else 1)*rareWeight := by
      unfold Ev excess base
      rw [←expectedValue_mul_const,←expectedValue_add]
    rw [hsplit]
    exact add_le_add (Ev_const_le secret _ _ _)
      (mul_le_mul' (OuterCodecChecks.checks_failure secret r.2 hg hf hn) le_rfl)
  refine le_trans (expectedValue_mono_of_support hinner) ?_
  change Ev secret buildTopTree ∅ (fun r=>base r.1+
    (ENNReal.ofReal (1/(2:ℝ)^170)+ENNReal.ofReal (1/(2:ℝ)^150))*rareWeight)≤2
  have hadd : Ev secret buildTopTree ∅ (fun r=>base r.1+
      (ENNReal.ofReal (1/(2:ℝ)^170)+ENNReal.ofReal (1/(2:ℝ)^150))*rareWeight)=
      Ev secret buildTopTree ∅ (fun r=>base r.1)+Ev secret buildTopTree ∅
        (fun _=>(ENNReal.ofReal (1/(2:ℝ)^170)+ENNReal.ofReal (1/(2:ℝ)^150))*rareWeight) := by
    unfold Ev
    rw [expectedValue_add]
  rw [hadd]
  calc
    _ ≤ (ENNReal.ofReal (194/100)+ENNReal.ofReal (1/(2:ℝ)^135)*rareWeight)+
        (ENNReal.ofReal (1/(2:ℝ)^170)+ENNReal.ofReal (1/(2:ℝ)^150))*rareWeight :=
      add_le_add (base_moment secret) (Ev_const_le secret _ _ _)
    _ = ENNReal.ofReal (194/100+1/(2:ℝ)^135*2^19+(1/(2:ℝ)^170+1/(2:ℝ)^150)*2^19) := by
      unfold rareWeight
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul (by positivity),
        ←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (by norm_num)
    _ = 2 := by norm_num

theorem excess_moment (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (joint message) ∅)
      (fun r=>(2:ℝ≥0∞)^((8/7:ℝ)*((r.1.2-r.1.1:Nat):ℝ)/1048576))≤2 := by
  rw [OuterLooseMoment.joint_eq,roRun_map,expectedValue_map]
  change Ev secret (jointL message) ∅ (fun r=>(2:ℝ≥0∞)^((8/7:ℝ)*((r.1.1.2-r.1.1.1:Nat):ℝ)/1048576))≤2
  rw [presample secret message (fun c : Nat×Nat=>(2:ℝ≥0∞)^((8/7:ℝ)*((c.2-c.1:Nat):ℝ)/1048576))]
  exact (support_excess secret message).trans (checked_moment secret message)

theorem joint_sign_moment (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (joint message) ∅) (fun r=>(2:ℝ≥0∞)^((r.1.1:ℝ)/131072))≤2 := by
  refine le_trans ?_ (OuterLooseBudget.honest_sign_exponential_budget secret message)
  simp only [joint,SigGolfCandidate.T3.ExpansionClosure.jointCounts,OuterLooseBudget.honestSignCount,roRun_bind,expectedValue_bind]
  apply expectedValue_mono
  intro keys
  apply expectedValue_mono
  rintro ⟨⟨sig,signCost⟩,rcache⟩
  cases sig with
  | none=>simp only [roRun_pure,expectedValue_pure,le_refl]
  | some sig=>
    simp only [roRun_bind,expectedValue_bind]
    apply expectedValue_le_of_support
    intro expanded _
    simp only [roRun_pure,expectedValue_pure,le_refl]

theorem honest_expand_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (joint message) ∅) (fun r=>(2:ℝ≥0∞)^((r.1.2:ℝ)/1048576))≤2 :=
  ClaudeWCT.Arith.ExpectHolder.expand_moment_of_holder (roRun secret (joint message) ∅)
    (fun r=>r.1.1) (fun r=>r.1.2) (joint_sign_moment secret message) (excess_moment secret message)

#print axioms excess_moment
#print axioms joint_sign_moment
#print axioms honest_expand_exponential_budget

#print axioms field_moment
#print axioms base_moment
#print axioms checked_moment
end OuterLooseExpansionBudget
