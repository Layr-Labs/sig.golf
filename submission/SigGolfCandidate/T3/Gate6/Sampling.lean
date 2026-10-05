import SigGolfCandidate.SphincsSecurity.Proof.Fts.CachedIndexHashMoments
import SigGolfCandidate.T3.Gate6.BPORSPrefix
import SigGolfCandidate.SphincsSecurity.Proof.Event.TruncatedCharge

section




section
namespace SigGolfResearch.Gate6.Cache
open OracleComp ENNReal
set_option maxHeartbeats 200000
attribute [local instance] Classical.propDecidable
abbrev Output := BitVec 256
abbrev History (Input : Type) := List (Input × Output)
structure Cache (Input : Type) where
  entries : List (Input × Output)
  unique : (entries.map Prod.fst).Nodup
def empty {Input : Type} : Cache Input := ⟨[],by simp⟩
def lookup {Input : Type} [DecidableEq Input] (cache : Cache Input) (input : Input) : Option Output :=
  cache.entries.lookup input
def insert {Input : Type} [DecidableEq Input] (cache : Cache Input) (input : Input) (output : Output)
    (fresh : lookup cache input=none) : Cache Input :=
  ⟨(input,output)::cache.entries,by
    rw [List.map_cons,List.nodup_cons]
    refine ⟨?_,cache.unique⟩
    intro hi
    obtain ⟨pair,hpair,heq⟩ := List.mem_map.mp hi
    have h := List.lookup_eq_none_iff.mp fresh pair hpair
    simp [heq] at h⟩
def Matches (mark : MarkedLabel) (output : Output) : Prop :=
  DigestAccepted output ∧ (digestRecord output).1=mark
noncomputable def count {Input : Type} (mark : MarkedLabel) (cache : Cache Input) : Nat :=
  cache.entries.countP (fun pair => decide (Matches mark pair.2))
noncomputable def eRate : ENNReal := acceptance/2^59
noncomputable def rate : ℝ := eRate.toReal
noncomputable def Bad {Input : Type} (cache : Cache Input) : Prop :=
  ∃ mark : MarkedLabel, (cache.entries.length : ℝ)*rate+2^47 < count mark cache
theorem probability_matches (mark : MarkedLabel) :
    Pr[Matches mark | ($ᵗ Output : ProbComp Output)] = eRate := digest_mark_joint_exact mark
theorem eRate_finite : eRate ≠ ⊤ := by unfold eRate acceptance;finiteness
theorem eRate_le_one : eRate ≤ 1 := by
  rw [← probability_matches (0,fun _ => 0)]
  exact probEvent_le_one
theorem rate_value : rate =
    (6963897326262647489342145 : ℝ)/(19807040628566084398385987584*2^59) := by
  norm_num [rate,eRate,acceptance,ENNReal.toReal_div,ENNReal.toReal_pow,
    ENNReal.toReal_ofNat,ENNReal.toReal_ofReal]
theorem rate_nonneg : 0≤rate := ENNReal.toReal_nonneg
theorem rate_le_one : rate≤1 := by
  exact (ENNReal.toReal_mono (by finiteness) eRate_le_one).trans_eq ENNReal.toReal_one
theorem count_insert {Input : Type} [DecidableEq Input] (mark : MarkedLabel)
    (cache : Cache Input) (input : Input) (output : Output) (fresh : lookup cache input=none) :
    count mark (insert cache input output fresh) = count mark cache + if Matches mark output then 1 else 0 := by
  by_cases h : Matches mark output <;> simp [count,insert,List.countP_cons,h]
theorem insert_length {Input : Type} [DecidableEq Input] (cache : Cache Input) (input : Input)
    (output : Output) (fresh : lookup cache input=none) :
    (insert cache input output fresh).entries.length=cache.entries.length+1 := rfl
theorem not_bad_empty {Input : Type} : ¬Bad (empty : Cache Input) := by
  rintro ⟨mark,h⟩
  norm_num [empty,count] at h
noncomputable def run {Input : Type} [DecidableEq Input]
    (policy : History Input → ProbComp Input) : Nat → History Input → Cache Input → ProbComp Bool
  | 0,_,cache => pure (decide (Bad cache))
  | steps+1,history,cache =>
    if Bad cache then pure true else do
      let input ← policy history
      match fresh : lookup cache input with
      | some output => run policy steps ((input,output)::history) cache
      | none => do
          let output ← ($ᵗ Output : ProbComp Output)
          run policy steps ((input,output)::history) (insert cache input output fresh)
end SigGolfResearch.Gate6.Cache
#print axioms SigGolfResearch.Gate6.Cache.count_insert
#print axioms SigGolfResearch.Gate6.Cache.probability_matches
end
section
namespace SigGolfResearch.Gate6.Cache
open OracleComp ENNReal
set_option maxHeartbeats 200000
noncomputable def theta : ℝ := 1/4096
noncomputable def growth : ℝ := rate*theta/(1-theta)
theorem theta_pos : 0<theta := by norm_num [theta]
theorem theta_lt_one : theta<1 := by norm_num [theta]
theorem growth_ge_center : theta*rate≤growth := by
  unfold growth
  apply (le_div_iff₀ (by linarith [theta_lt_one])).mpr
  nlinarith [mul_nonneg rate_nonneg (sq_nonneg theta)]
theorem bernoulli_mgf_real : rate*Real.exp theta+(1-rate)≤Real.exp growth := by
  have he := (Real.exp_bound_div_one_sub_of_interval' theta_pos theta_lt_one).le
  calc
    _ ≤ rate*(1/(1-theta))+(1-rate) := by gcongr;exact rate_nonneg
    _ = 1+growth := by unfold growth;field_simp [(sub_pos.mpr theta_lt_one).ne'];ring
    _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp growth
theorem centered_initial_exponent (q : Nat) (hq : q≤2^127) :
    (q : ℝ)*(growth-theta*rate)-theta*2^47≤-1000 := by
  have hqR : (q : ℝ)≤2^127 := by exact_mod_cast hq
  calc
    _ ≤ (2^127 : ℝ)*(growth-theta*rate)-theta*2^47 := by
      gcongr
      exact sub_nonneg.mpr growth_ge_center
    _ ≤ -1000 := by norm_num [growth,theta,rate_value]
theorem initial_tail_real (q : Nat) (hq : q≤2^127) :
    Real.exp ((q : ℝ)*(growth-theta*rate)-theta*2^47)≤(2^759 : ℝ)⁻¹ := by
  have hlog : Real.log (2 : ℝ)≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at h ⊢
    exact h
  calc
    _ ≤ Real.exp (-759*Real.log 2) := Real.exp_le_exp.mpr (by linarith [centered_initial_exponent q hq])
    _ = _ := by
      rw [neg_mul,Real.exp_neg]
      have he : Real.exp (759*Real.log 2)=(2 : ℝ)^759 := by
        simpa using (Real.exp_nat_mul (Real.log 2) 759).trans (congrArg (fun x : ℝ => x^759) (Real.exp_log (by norm_num : (0 : ℝ)<2)))
      rw [he]
theorem bernoulli_shift_real (x : ℝ) :
    rate*Real.exp (x+theta-growth)+(1-rate)*Real.exp (x-growth)≤Real.exp x := by
  have h := mul_le_mul_of_nonneg_left bernoulli_mgf_real (Real.exp_pos (x-growth)).le
  have he : Real.exp (x+theta-growth)=Real.exp (x-growth)*Real.exp theta := by rw [←Real.exp_add];congr 1;ring
  have hcancel : Real.exp (x-growth)*Real.exp growth=Real.exp x := by rw [←Real.exp_add];congr 1;ring
  rw [hcancel] at h
  rw [he]
  nlinarith
end SigGolfResearch.Gate6.Cache
#print axioms SigGolfResearch.Gate6.Cache.bernoulli_mgf_real
#print axioms SigGolfResearch.Gate6.Cache.initial_tail_real
end
section
namespace SigGolfResearch.Gate6.Cache
open OracleComp ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
set_option maxHeartbeats 300000
noncomputable def score {Input : Type} (q : Nat) (mark : MarkedLabel) (cache : Cache Input) : ℝ :=
  theta*(count mark cache : ℝ)+growth*((q : ℝ)-cache.entries.length)-theta*(rate*q+2^47)
noncomputable def weight {Input : Type} (q : Nat) (mark : MarkedLabel) (cache : Cache Input) : ENNReal :=
  ENNReal.ofReal (Real.exp (score q mark cache))
noncomputable def totalWeight {Input : Type} (q : Nat) (cache : Cache Input) : ENNReal :=
  ∑ mark : MarkedLabel,weight q mark cache
theorem expected_choice (mark : MarkedLabel) (yes no : ENNReal) :
    (∑' output,Pr[=output | ($ᵗ Output : ProbComp Output)]*(if Matches mark output then yes else no)) =
      eRate*yes+(1-eRate)*no := by
  have hnot : Pr[fun d => ¬Matches mark d | ($ᵗ Output : ProbComp Output)] = 1-eRate := by
    have h := probEvent_compl ($ᵗ Output : ProbComp Output) (Matches mark)
    rw [probFailure_of_liftM_PMF,tsub_zero,probability_matches,add_comm] at h
    exact ENNReal.eq_sub_of_add_eq' (by simp) h
  have hs (output : Output) : Pr[=output | ($ᵗ Output : ProbComp Output)]*(if Matches mark output then yes else no) =
      (if Matches mark output then Pr[=output | ($ᵗ Output : ProbComp Output)] else 0)*yes+
      (if ¬Matches mark output then Pr[=output | ($ᵗ Output : ProbComp Output)] else 0)*no := by
    by_cases h : Matches mark output <;> simp [h]
  simp_rw [hs,ENNReal.tsum_add,ENNReal.tsum_mul_right,←probEvent_eq_tsum_ite,probability_matches,hnot]
theorem weight_insert {Input : Type} [DecidableEq Input] (q : Nat) (mark : MarkedLabel)
    (cache : Cache Input) (input : Input) (output : Output) (fresh : lookup cache input=none) :
    weight q mark (insert cache input output fresh) =
      if Matches mark output then ENNReal.ofReal (Real.exp (score q mark cache+theta-growth))
      else ENNReal.ofReal (Real.exp (score q mark cache-growth)) := by
  unfold weight score
  rw [count_insert,insert_length]
  by_cases h : Matches mark output <;> simp only [h,if_true,if_false,Nat.cast_add,Nat.cast_one,Nat.cast_zero]
  all_goals congr 2 <;> ring
theorem expected_weight_insert {Input : Type} [DecidableEq Input] (q : Nat) (mark : MarkedLabel)
    (cache : Cache Input) (input : Input) (fresh : lookup cache input=none) :
    (∑' output,Pr[=output | ($ᵗ Output : ProbComp Output)]*
      weight q mark (insert cache input output fresh))≤weight q mark cache := by
  simp_rw [weight_insert]
  rw [expected_choice]
  have heFinite := eRate_finite
  apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold weight;finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_sub_of_le eRate_le_one (by finiteness),ENNReal.toReal_one,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,weight]
  exact bernoulli_shift_real (score q mark cache)
theorem expected_totalWeight_insert {Input : Type} [DecidableEq Input] (q : Nat)
    (cache : Cache Input) (input : Input) (fresh : lookup cache input=none) :
    (∑' output,Pr[=output | ($ᵗ Output : ProbComp Output)]*
      totalWeight q (insert cache input output fresh))≤totalWeight q cache := by
  simp only [totalWeight,Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact Finset.sum_le_sum fun mark _ => expected_weight_insert q mark cache input fresh
theorem weight_bad {Input : Type} (q : Nat) (mark : MarkedLabel) (cache : Cache Input)
    (hq : cache.entries.length≤q)
    (hbad : (cache.entries.length : ℝ)*rate+2^47 < count mark cache) : 1≤weight q mark cache := by
  have hqR : 0≤(q : ℝ)-cache.entries.length := sub_nonneg.mpr (by exact_mod_cast hq)
  have hprod := mul_nonneg (sub_nonneg.mpr growth_ge_center) hqR
  have hpositive := mul_nonneg theta_pos.le (sub_nonneg.mpr hbad.le)
  have hs : 0 ≤ score q mark cache := by unfold score;nlinarith
  calc
    1 = ENNReal.ofReal (Real.exp 0) := by simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hs)
theorem totalWeight_bad {Input : Type} (q : Nat) (cache : Cache Input)
    (hq : cache.entries.length≤q) (hbad : Bad cache) : 1≤totalWeight q cache := by
  obtain ⟨mark,hmark⟩ := hbad
  exact (weight_bad q mark cache hq hmark).trans
    (show weight q mark cache≤totalWeight q cache from
      Finset.single_le_sum (f:=fun m => weight q m cache) (fun _ _ => zero_le) (Finset.mem_univ mark))
theorem totalWeight_empty {Input : Type} (q : Nat) :
    totalWeight q (empty : Cache Input) =
      (2^59 : ENNReal)*ENNReal.ofReal (Real.exp ((q : ℝ)*(growth-theta*rate)-theta*2^47)) := by
  have hw (mark : MarkedLabel) : weight q mark (empty : Cache Input) =
      ENNReal.ofReal (Real.exp ((q : ℝ)*(growth-theta*rate)-theta*2^47)) := by
    unfold weight score count empty
    simp only [List.countP_nil,List.length_nil,Nat.cast_zero,mul_zero,zero_add,sub_zero]
    congr 2
    ring
  simp only [totalWeight,hw,Finset.sum_const,Finset.card_univ,markedLabel_card,nsmul_eq_mul,
    Nat.cast_pow,Nat.cast_ofNat]
theorem initial_totalWeight_le {Input : Type} (q : Nat) (hq : q≤2^127) :
    totalWeight q (empty : Cache Input)≤(2^700 : ENNReal)⁻¹ := by
  rw [totalWeight_empty]
  calc
    _ ≤ (2^59 : ENNReal)*ENNReal.ofReal ((2^759 : ℝ)⁻¹) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (initial_tail_real q hq))
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_inv,ENNReal.toReal_ofNat,
        ENNReal.toReal_ofReal (show (0 : ℝ)≤(2^759 : ℝ)⁻¹ by positivity)]
      rw [show (2 : ℝ)^759=2^59*2^700 by rw [←pow_add]]
      field_simp
end SigGolfResearch.Gate6.Cache
#print axioms SigGolfResearch.Gate6.Cache.expected_totalWeight_insert
#print axioms SigGolfResearch.Gate6.Cache.initial_totalWeight_le
end
section
namespace SigGolfResearch.Gate6.NativeCache
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SphincsSecurity (Finite)
abbrev RCache := SigGolfCandidate.T3.Sampling.RCache
open SphincsSecurity.Concrete (enncard_cacheQuery_of_fresh)
open scoped BigOperators
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
noncomputable def entry (mark : MarkedLabel) (cache : RCache) (input : HashInput) : ENNReal :=
  (cache input).elim 0 (fun output => if Cache.Matches mark output then 1 else 0)
noncomputable def count (mark : MarkedLabel) (cache : RCache) : ENNReal := ∑' input,entry mark cache input
theorem count_empty (mark : MarkedLabel) : count mark ∅=0 := by simp [count,entry]
theorem count_cacheQuery (mark : MarkedLabel) (cache : RCache) (input : HashInput)
    (output : HashOutput) (hfresh : cache input=none) :
    count mark (cache.cacheQuery input output)=count mark cache+
      if Cache.Matches mark output then 1 else 0 := by
  unfold count
  rw [ENNReal.tsum_eq_add_tsum_ite (f := entry mark (cache.cacheQuery input output)) input,
    ENNReal.tsum_eq_add_tsum_ite (f := entry mark cache) input]
  simp only [entry,QueryCache.cacheQuery_self,hfresh,Option.elim_none,Option.elim_some,zero_add]
  rw [add_comm]
  congr 1
  apply tsum_congr
  intro other
  by_cases heq : other=input
  · simp [heq]
  · simp only [heq,if_false,QueryCache.cacheQuery_of_ne cache output heq]
theorem count_le_enncard (mark : MarkedLabel) (cache : RCache) (hfinite : Finite cache) :
    count mark cache ≤ QueryCache.enncard cache := by
  unfold count
  rw [tsum_eq_sum (s := hfinite.toFinset) (fun input hnot => by
    have hn : cache input=none := by
      by_contra h
      exact hnot (hfinite.mem_toFinset.mpr h)
    simp [entry,hn])]
  calc
    _ ≤ ∑ _input ∈ hfinite.toFinset,(1 : ENNReal) := by
      apply Finset.sum_le_sum
      intro input _
      unfold entry
      cases cache input <;> simp only [Option.elim_none,Option.elim_some]
      · exact bot_le
      · split_ifs <;> norm_num
    _ = _ := by
      rw [Finset.sum_const,nsmul_eq_mul,mul_one,
        ← Set.ncard_eq_toFinset_card {input | cache input ≠ none} hfinite]
      exact hfinite.cachedInputs_ncard_toENNReal_eq_enncard
theorem enncard_ne_top (cache : RCache) (hfinite : Finite cache) : QueryCache.enncard cache ≠ ⊤ := by
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness
theorem count_ne_top (mark : MarkedLabel) (cache : RCache) (hfinite : Finite cache) :
    count mark cache ≠ ⊤ := ne_top_of_le_ne_top (enncard_ne_top cache hfinite) (count_le_enncard mark cache hfinite)
noncomputable def Bad (cache : RCache) : Prop :=
  ∃ mark : MarkedLabel,(QueryCache.enncard cache).toReal*Cache.rate+2^47 < (count mark cache).toReal
noncomputable def score (q : Nat) (mark : MarkedLabel) (cache : RCache) : ℝ :=
  Cache.theta*(count mark cache).toReal+Cache.growth*((q : ℝ)-(QueryCache.enncard cache).toReal)-
    Cache.theta*(Cache.rate*q+2^47)
noncomputable def weight (q : Nat) (mark : MarkedLabel) (cache : RCache) : ENNReal :=
  ENNReal.ofReal (Real.exp (score q mark cache))
noncomputable def totalWeight (q : Nat) (cache : RCache) : ENNReal := ∑ mark : MarkedLabel,weight q mark cache
theorem score_cacheQuery (q : Nat) (mark : MarkedLabel) (cache : RCache) (hfinite : Finite cache)
    (input : HashInput) (output : HashOutput) (hfresh : cache input=none) :
    score q mark (cache.cacheQuery input output)=score q mark cache+
      (if Cache.Matches mark output then Cache.theta else 0)-Cache.growth := by
  unfold score
  rw [count_cacheQuery mark cache input output hfresh,enncard_cacheQuery_of_fresh cache input output hfresh,
    ENNReal.toReal_add (enncard_ne_top cache hfinite) (by finiteness),ENNReal.toReal_one]
  have hsum : (count mark cache+1).toReal=(count mark cache).toReal+1 := by
    rw [ENNReal.toReal_add (count_ne_top mark cache hfinite) ENNReal.one_ne_top,ENNReal.toReal_one]
  have hsum' : (1+count mark cache).toReal=1+(count mark cache).toReal := by
    rw [ENNReal.toReal_add ENNReal.one_ne_top (count_ne_top mark cache hfinite),ENNReal.toReal_one]
  split_ifs <;> (try rw [hsum]) <;> (try rw [hsum']) <;> (try simp only [add_zero]) <;> ring
theorem expected_weight_fresh (q : Nat) (mark : MarkedLabel) (cache : RCache) (hfinite : Finite cache)
    (input : HashInput) (hfresh : cache input=none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun output => weight q mark (cache.cacheQuery input output)) ≤ weight q mark cache := by
  have he (output : HashOutput) : weight q mark (cache.cacheQuery input output)=
      if Cache.Matches mark output then ENNReal.ofReal (Real.exp (score q mark cache+Cache.theta-Cache.growth))
      else ENNReal.ofReal (Real.exp (score q mark cache-Cache.growth)) := by
    unfold weight
    rw [score_cacheQuery q mark cache hfinite input output hfresh]
    split_ifs <;> simp
  simp_rw [he]
  change (∑' output,Pr[=output | ($ᵗ Cache.Output : ProbComp Cache.Output)]*_)≤_
  rw [Cache.expected_choice]
  have heFinite := Cache.eRate_finite
  apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold weight;finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_sub_of_le Cache.eRate_le_one (by finiteness),ENNReal.toReal_one,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,weight]
  exact Cache.bernoulli_shift_real (score q mark cache)
theorem expected_totalWeight_fresh (q : Nat) (cache : RCache) (hfinite : Finite cache)
    (input : HashInput) (hfresh : cache input=none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun output => totalWeight q (cache.cacheQuery input output)) ≤ totalWeight q cache := by
  unfold totalWeight
  rw [expectedValue_finsetSum]
  exact Finset.sum_le_sum fun mark _ => expected_weight_fresh q mark cache hfinite input hfresh
theorem totalWeight_bad (q : Nat) (cache : RCache) (hq : QueryCache.enncard cache≤q)
    (hbad : Bad cache) : 1≤totalWeight q cache := by
  obtain ⟨mark,hmark⟩ := hbad
  have hqR : 0≤(q : ℝ)-(QueryCache.enncard cache).toReal := by
    apply sub_nonneg.mpr
    exact_mod_cast ENNReal.toReal_mono (by finiteness) hq
  have hprod := mul_nonneg (sub_nonneg.mpr Cache.growth_ge_center) hqR
  have hpositive := mul_nonneg Cache.theta_pos.le (sub_nonneg.mpr hmark.le)
  have hs : 0 ≤ score q mark cache := by unfold score;nlinarith
  have hw : 1≤weight q mark cache := by
    calc
      1 = ENNReal.ofReal (Real.exp 0) := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hs)
  exact hw.trans (Finset.single_le_sum (f:=fun m => weight q m cache) (fun _ _ => zero_le) (Finset.mem_univ mark))
theorem totalWeight_empty (q : Nat) : totalWeight q ∅ =
    (2^59 : ENNReal)*ENNReal.ofReal (Real.exp ((q : ℝ)*(Cache.growth-Cache.theta*Cache.rate)-Cache.theta*2^47)) := by
  have hw (mark : MarkedLabel) : weight q mark ∅=
      ENNReal.ofReal (Real.exp ((q : ℝ)*(Cache.growth-Cache.theta*Cache.rate)-Cache.theta*2^47)) := by
    unfold weight score
    simp only [count_empty,ENNReal.toReal_zero,QueryCache.enncard_empty,mul_zero,zero_add,sub_zero]
    congr 2
    ring
  simp only [totalWeight,hw,Finset.sum_const,Finset.card_univ,markedLabel_card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
theorem initial_totalWeight_le (q : Nat) (hq : q≤2^127) : totalWeight q ∅≤(2^700 : ENNReal)⁻¹ := by
  rw [totalWeight_empty,← Cache.totalWeight_empty (Input := HashInput)]
  exact Cache.initial_totalWeight_le q hq
theorem not_bad_empty : ¬Bad ∅ := by
  rintro ⟨mark,h⟩
  norm_num [count_empty,QueryCache.enncard] at h
theorem clean_point_bound_arithmetic (cache : RCache) (hfinite : Finite cache)
    (budget : Nat) (hsize : QueryCache.enncard cache≤budget) (hbudget : budget≤2^127)
    (hclean : ¬Bad cache) (mark : MarkedLabel) :
    1/(2 : ENNReal)^59+count mark cache/(2 : ENNReal)^128 ≤
      (1025/1024 : ENNReal)/(2 : ENNReal)^59 := by
  have hex : (count mark cache).toReal ≤ (QueryCache.enncard cache).toReal*Cache.rate+2^47 :=
    le_of_not_gt (fun h => hclean ⟨mark,h⟩)
  have hcache : (QueryCache.enncard cache).toReal≤(budget : ℝ) := by
    exact_mod_cast ENNReal.toReal_mono (by finiteness) hsize
  have hbudgetR : (budget : ℝ)≤2^127 := by exact_mod_cast hbudget
  have hscale := mul_le_mul_of_nonneg_right (hcache.trans hbudgetR) Cache.rate_nonneg
  apply (ENNReal.toReal_le_toReal (by have := count_ne_top mark cache hfinite;finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (ENNReal.div_ne_top (count_ne_top mark cache hfinite) (by norm_num))]
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  calc
    _ ≤ 1/(2 : ℝ)^59+((2 : ℝ)^127*Cache.rate+2^47)/(2 : ℝ)^128 := by
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    _ ≤ _ := by norm_num [Cache.rate_value]
end SigGolfResearch.Gate6.NativeCache
#print axioms SigGolfResearch.Gate6.NativeCache.expected_totalWeight_fresh
#print axioms SigGolfResearch.Gate6.NativeCache.initial_totalWeight_le
#print axioms SigGolfResearch.Gate6.NativeCache.clean_point_bound_arithmetic
end
section
namespace SigGolfResearch.Gate6.NativeSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness (searchLoop failMass failMass_eq_probEvent)
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
noncomputable def acceptedWeight {β : Type} (decoder : HashOutput → Option β)
    (payoff : β → ENNReal) : ENNReal :=
  expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
    (fun answer => (decoder answer).elim 0 payoff)
theorem uniform_decoder_weight {β : Type} (decoder : HashOutput → Option β)
    (payoff : β → ENNReal) (rejected : ENNReal) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => (decoder answer).elim rejected payoff)=
      acceptedWeight decoder payoff+failMass decoder*rejected := by
  classical
  have hp (answer : HashOutput) :
      (decoder answer).elim rejected payoff=(decoder answer).elim 0 payoff+
        (if decoder answer=none then 1 else 0)*rejected := by
    cases decoder answer <;> simp
  simp_rw [hp]
  rw [expectedValue_add,expectedValue_mul_const,expectedValue_ite_one]
  have hf : failMass decoder=Pr[fun answer : HashOutput => decoder answer=none |
      ($ᵗ HashOutput : ProbComp HashOutput)] := failMass_eq_probEvent decoder
  rw [← hf]
  rfl
def CachedTrialScoresBound {β : Type} (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (weight : β → ENNReal) (price : ENNReal)
    (counter bound : Nat) (cache : RCache) : Prop :=
  ∀ c,counter ≤ c → c < bound → ∀ answer,cache (inputs c)=some answer →
    (decoder answer).elim 0 weight ≤ price
theorem expected_publicSearch_completed_le_of_cached_scores {β γ : Type} (secret : BitVec 256)
    (inputs : Nat → HashInput) (decoder : HashOutput → Option β)
    (result : Nat → β → γ) (payoff : γ → ENNReal) (weight : β → ENNReal)
    (hweight : ∀ counter value,payoff (result counter value)=weight value)
    (price : ENNReal) (hstep : acceptedWeight decoder weight+failMass decoder*price ≤ price)
    (bound : Nat)
    (hinj : ∀ left right,left < bound → right < bound → inputs left=inputs right → left=right) :
    ∀ fuel counter,counter+fuel ≤ bound → ∀ cache : RCache,
      CachedTrialScoresBound inputs decoder weight price counter bound cache →
      expectedValue (roRun secret
        (publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache)
        (fun output => output.1.elim price payoff) ≤ price := by
  intro fuel
  induction fuel with
  | zero => intro counter _ cache _;simp [searchLoop,publicProgram]
  | succ fuel ih =>
      intro counter hlimit cache hcache
      rw [publicSearch_succ,roRun_bind,roRun_publicQuery,expectedValue_bind]
      cases hc : cache (inputs counter) with
      | some answer =>
          have hp := hcache counter le_rfl (by omega) answer hc
          rw [randomOracle.run_eq,hc]
          simp only [expectedValue_pure]
          cases hd : decoder answer with
          | none =>
              exact ih (counter+1) (by omega) cache
                (fun c hstart hbound answer ha => hcache c (by omega) hbound answer ha)
          | some value =>
              simpa only [roRun_pure,expectedValue_pure,Option.elim_some,hweight,hd] using hp
      | none =>
          rw [expectedValue_fresh _ _ hc]
          calc
            _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                (fun answer => (decoder answer).elim price weight) := by
              apply expectedValue_mono
              intro answer
              cases hd : decoder answer with
              | some value => simp [hweight]
              | none =>
                  apply ih (counter+1) (by omega) _
                  intro c hstart hbound output ho
                  have hne : inputs c ≠ inputs counter := by
                    intro he
                    have hh := hinj c counter hbound (by omega) he
                    omega
                  have hh : cache (inputs c)=some output :=
                    (QueryCache.cacheQuery_of_ne cache answer hne).symm.trans ho
                  exact hcache c (by omega) hbound output hh
            _ = acceptedWeight decoder weight+failMass decoder*price :=
              uniform_decoder_weight decoder weight price
            _ ≤ price := hstep
theorem digestTrial_nonce_injective {rho rho' : Digest} {message message' : Message}
    {counter counter' : Nat}
    (he : digestTrial rho message counter=digestTrial rho' message' counter') : rho=rho' := by
  have h := pad64_inj_of_length (by simp [digestInput,SphincsSecurity.bytesLE_length]) he
  exact (digestInput_injective h).1
noncomputable def decode (answer : HashOutput) : Option HashOutput :=
  if DigestAccepted answer then some answer else none
noncomputable def search (rho : Digest) (message : Message) (fuel : Nat) : M (Option (BitVec 32 × HashOutput)) :=
  publicProgram (searchLoop (digestTrial rho message) decode
    (fun c output => pure (BitVec.ofNat 32 c,output)) fuel 0)
noncomputable def hit (mark : MarkedLabel) (output : HashOutput) : ENNReal :=
  if (digestRecord output).1=mark then 1 else 0
noncomputable def completedScore (mark : MarkedLabel) (found : Option (BitVec 32 × HashOutput)) : ENNReal :=
  found.elim (1/2^59) (fun value => hit mark value.2)
theorem acceptance_le_one : acceptance≤1 := by
  rw [← digest_acceptance_exact]
  exact probEvent_le_one
theorem decoder_failure : failMass decode=1-acceptance := by
  rw [failMass_eq_probEvent]
  change Pr[fun output : HashOutput => decode output=none | ($ᵗ HashOutput : ProbComp HashOutput)] = _
  have he : (fun output => decode output=none)=(fun output => ¬DigestAccepted output) := by
    funext output
    simp [decode]
  rw [he]
  have h := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) DigestAccepted
  rw [probFailure_of_liftM_PMF,tsub_zero,digest_acceptance_exact,add_comm] at h
  exact ENNReal.eq_sub_of_add_eq' (by simp) h
theorem accepted_hit (mark : MarkedLabel) : acceptedWeight decode (hit mark)=acceptance/2^59 := by
  unfold acceptedWeight
  have he (output : HashOutput) : (decode output).elim 0 (hit mark)=
      if DigestAccepted output ∧ (digestRecord output).1=mark then 1 else 0 := by
    simp only [decode,hit]
    split_ifs <;> simp_all [hit]
  simp_rw [he]
  rw [expectedValue_ite_one]
  exact digest_mark_joint_exact mark
theorem completedScore_le_one (mark : MarkedLabel) (found : Option (BitVec 32 × HashOutput)) :
    completedScore mark found≤1 := by
  cases found with
  | none => norm_num [completedScore]
  | some value => unfold completedScore hit;simp only [Option.elim_some];split_ifs <;> norm_num
noncomputable def CachedHit (rho : Digest) (message : Message) (fuel : Nat)
    (cache : RCache) (mark : MarkedLabel) : Prop :=
  ∃ c,c<fuel ∧ ∃ output,cache (digestTrial rho message c)=some output ∧
    Cache.Matches mark output
theorem completed_search_no_cached_hit (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel : Nat) (hlimit : fuel≤2^32) (cache : RCache) (mark : MarkedLabel)
    (hno : ¬CachedHit rho message fuel cache mark) :
    expectedValue (roRun secret (search rho message fuel) cache)
      (fun result => completedScore mark result.1)≤1/2^59 := by
  unfold search completedScore
  apply expected_publicSearch_completed_le_of_cached_scores secret (digestTrial rho message) decode
    (fun c output => (BitVec.ofNat 32 c,output)) (fun found => hit mark found.2)
    (hit mark) (fun _ _ => rfl) (1/2^59) _ fuel
    (fun _ _ hl hr he => digestTrial_injective rho message (lt_of_lt_of_le hl hlimit)
      (lt_of_lt_of_le hr hlimit) he) fuel 0 (by omega) cache
  · intro c hc hf output ha
    by_cases hadm : DigestAccepted output
    · have hnot : (digestRecord output).1≠mark := fun ht => hno ⟨c,hf,output,ha,hadm,ht⟩
      simp [decode,hadm,hit,hnot]
    · simp [decode,hadm]
  · rw [accepted_hit,decoder_failure]
    calc
      _ = (acceptance+(1-acceptance))*(1/2^59) := by simp only [div_eq_mul_inv,one_mul];ring
      _ = 1/2^59 := by rw [add_tsub_cancel_of_le acceptance_le_one,one_mul]
      _ ≤ _ := le_rfl
theorem completed_search_cached_event (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel : Nat) (hlimit : fuel≤2^32) (cache : RCache) (mark : MarkedLabel) :
    expectedValue (roRun secret (search rho message fuel) cache)
      (fun result => completedScore mark result.1)≤
      1/2^59+if CachedHit rho message fuel cache mark then 1 else 0 := by
  by_cases h : CachedHit rho message fuel cache mark
  · rw [if_pos h]
    exact (expectedValue_le_of_le _ fun _ => completedScore_le_one mark _).trans (le_add_left le_rfl)
  · rw [if_neg h,add_zero]
    exact completed_search_no_cached_hit secret rho message fuel hlimit cache mark h
noncomputable def cachedNonces (message : Message) (fuel : Nat) (cache : RCache)
    (mark : MarkedLabel) : Finset Digest := Finset.univ.filter fun rho => CachedHit rho message fuel cache mark
theorem cachedNonces_card_le_count (message : Message) (fuel : Nat) (cache : RCache) (mark : MarkedLabel) :
    ((cachedNonces message fuel cache mark).card : ENNReal)≤NativeCache.count mark cache := by
  classical
  let nonces := cachedNonces message fuel cache mark
  have hw : ∀ rho : nonces,∃ counter,counter<fuel ∧ ∃ output,
      cache (digestTrial rho.val message counter)=some output ∧ Cache.Matches mark output := by
    intro rho
    exact (Finset.mem_filter.mp rho.property).2
  choose counter hc output ha htarget using hw
  let inputs (rho : nonces) := digestTrial rho.val message (counter rho)
  have hinj : Function.Injective inputs := by
    intro left right he
    exact Subtype.ext (digestTrial_nonce_injective he)
  have hentry (rho : nonces) : NativeCache.entry mark cache (inputs rho)=1 := by
    simp only [NativeCache.entry,inputs,ha,Option.elim_some,htarget,if_true]
  calc
    _ = ∑ rho : nonces,NativeCache.entry mark cache (inputs rho) := by
      simp only [hentry,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one,nonces]
    _ ≤ ∑' input,NativeCache.entry mark cache input := by
      simpa only [tsum_fintype] using
        (ENNReal.tsum_comp_le_tsum_of_injective hinj (NativeCache.entry mark cache))
    _ = _ := rfl
theorem uniform_nonce_completed_point (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel≤2^32) (cache : RCache) (mark : MarkedLabel) :
    expectedValue (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
      roRun secret (search rho message fuel) cache) (fun result => completedScore mark result.1) ≤
      1/(2 : ENNReal)^59+NativeCache.count mark cache/(2 : ENNReal)^128 := by
  rw [expectedValue_bind]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
        1/(2 : ENNReal)^59+if CachedHit rho message fuel cache mark then 1 else 0) :=
      expectedValue_mono _ fun rho => completed_search_cached_event secret rho message fuel hlimit cache mark
    _ = 1/(2 : ENNReal)^59+(cachedNonces message fuel cache mark).card/(2 : ENNReal)^128 := by
      rw [expectedValue_add,expectedValue_const (by simp),expectedValue_ite_one,probEvent_uniformSample]
      simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat,cachedNonces]
    _ ≤ _ := add_le_add le_rfl (ENNReal.div_le_div_right (cachedNonces_card_le_count message fuel cache mark) _)
theorem uniform_nonce_completed_cap (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel≤2^32) (cache : RCache) (hfinite : SphincsSecurity.Finite cache)
    (q : Nat) (hsize : QueryCache.enncard cache≤q) (hq : q≤2^127)
    (hclean : ¬NativeCache.Bad cache) (mark : MarkedLabel) :
    expectedValue (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
      roRun secret (search rho message fuel) cache) (fun result => completedScore mark result.1) ≤
      (1025/1024 : ENNReal)/(2 : ENNReal)^59 :=
  (uniform_nonce_completed_point secret message fuel hlimit cache mark).trans
    (NativeCache.clean_point_bound_arithmetic cache hfinite q hsize hq hclean mark)
end SigGolfResearch.Gate6.NativeSearch
#print axioms SigGolfResearch.Gate6.NativeSearch.uniform_nonce_completed_cap
end
section
namespace SigGolfResearch.Gate6.NativeSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Sampling
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
noncomputable def completeLabel (found : Option (BitVec 32 × HashOutput)) : ProbComp MarkedLabel :=
  found.elim ($ᵗ MarkedLabel) (fun value => pure (digestRecord value.2).1)
noncomputable def complete {Record : Type} (observed : Record → Option (BitVec 32 × HashOutput))
    (program : ProbComp Record) : ProbComp (Record × MarkedLabel) := do
  let record ← program
  let label ← completeLabel (observed record)
  pure (record,label)
theorem complete_erasure {Record : Type} (observed : Record → Option (BitVec 32 × HashOutput))
    (program : ProbComp Record) : 𝒮[Prod.fst <$> complete observed program]=𝒮[program] := by
  unfold complete
  simp only [map_bind,map_pure]
  trans 𝒮[program >>= fun record => pure record]
  · apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
    intro record
    exact OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _ (by simp) _
  · simp
theorem completeLabel_point (found : Option (BitVec 32 × HashOutput)) (mark : MarkedLabel) :
    Pr[=mark | completeLabel found]=completedScore mark found := by
  cases found with
  | none => norm_num [completeLabel,completedScore,probOutput_uniformSample,markedLabel_card]
  | some value => simp only [completeLabel,completedScore,Option.elim_some,probOutput_pure,hit,eq_comm]
theorem complete_point {Record : Type} (observed : Record → Option (BitVec 32 × HashOutput))
    (program : ProbComp Record) (mark : MarkedLabel) :
    Pr[fun result => result.2=mark | complete observed program]=
      expectedValue program (fun record => completedScore mark (observed record)) := by
  rw [complete,probEvent_bind_eq_expectedValue]
  congr 1
  funext record
  rw [probEvent_bind_eq_expectedValue]
  simp only [probEvent_pure]
  rw [expectedValue_ite_one]
  rw [probEvent_eq_eq_probOutput]
  exact completeLabel_point (observed record) mark
noncomputable def recordLaw (secret : BitVec 256) (message : Message) (fuel : Nat) (cache : RCache) :
    PMF (((Option (BitVec 32 × HashOutput)) × RCache) × MarkedLabel) :=
  liftM (complete Prod.fst (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
    roRun secret (search rho message fuel) cache))
theorem recordLaw_scaled_cap (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel≤2^32) (cache : RCache) (hfinite : SphincsSecurity.Finite cache)
    (q : Nat) (hsize : QueryCache.enncard cache≤q) (hq : q≤2^127)
    (hclean : ¬NativeCache.Bad cache) (mark : MarkedLabel) :
    (1024/1025 : ENNReal)*((recordLaw secret message fuel cache).map Prod.snd) mark ≤
      (PMF.uniformOfFintype MarkedLabel) mark := by
  have hpoint := uniform_nonce_completed_cap secret message fuel hlimit cache hfinite q hsize hq hclean mark
  rw [← complete_point Prod.fst _ mark] at hpoint
  rw [← PMF.monad_map_eq_map,← PMF.probOutput_eq_apply,probOutput_map,
    PMF.uniformOfFintype_apply,markedLabel_card,Nat.cast_pow,Nat.cast_ofNat]
  change (1024/1025 : ENNReal)*Pr[fun result => result.2=mark | complete Prod.fst
    (($ᵗ Digest : ProbComp Digest) >>= fun rho => roRun secret (search rho message fuel) cache)]≤_
  calc
    _ ≤ (1024/1025 : ENNReal)*((1025/1024 : ENNReal)/(2 : ENNReal)^59) := mul_le_mul' le_rfl hpoint
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow]
end SigGolfResearch.Gate6.NativeSearch
#print axioms SigGolfResearch.Gate6.NativeSearch.complete_erasure
#print axioms SigGolfResearch.Gate6.NativeSearch.recordLaw_scaled_cap
end
section
namespace SigGolfResearch.Gate6.Source
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Sampling
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem actual_decoder_eq (output : HashOutput) :
    NativeSearch.decode output=SigGolfCandidate.T3.Sampling.digestDecode output := by
  unfold NativeSearch.decode SigGolfCandidate.T3.Sampling.digestDecode
  by_cases h : digestAdmissible output=true
  · simp [h,(actual_predicate_iff output).mp h]
  · have hn : ¬DigestAccepted output := fun hg => h ((actual_predicate_iff output).mpr hg)
    simp [h,hn]
theorem actual_search_eq (rho : Digest) (message : Message) (fuel : Nat) :
    NativeSearch.search rho message fuel=digestSearch rho message 0 fuel := by
  rw [digestSearch_public]
  unfold NativeSearch.search
  have he : NativeSearch.decode=SigGolfCandidate.T3.Sampling.digestDecode := funext actual_decoder_eq
  rw [he]
theorem actual_uniform_nonce_completed_cap (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (hfinite : SphincsSecurity.Finite cache)
    (q : Nat) (hsize : QueryCache.enncard cache ≤ q) (hq : q ≤ 2^127)
    (hclean : ¬NativeCache.Bad cache) (mark : MarkedLabel) :
    expectedValue (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
      roRun secret (digestSearch rho message 0 fuel) cache)
      (fun result => NativeSearch.completedScore mark result.1) ≤
      (1025/1024 : ENNReal)/(2 : ENNReal)^59 := by
  simpa only [actual_search_eq] using
    NativeSearch.uniform_nonce_completed_cap secret message fuel hlimit cache hfinite q hsize hq hclean mark
noncomputable def actualRecordLaw (secret : BitVec 256) (message : Message) (fuel : Nat) (cache : RCache) :
    PMF (((Option (BitVec 32 × HashOutput)) × RCache) × MarkedLabel) :=
  liftM (NativeSearch.complete Prod.fst (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
    roRun secret (digestSearch rho message 0 fuel) cache))
theorem actual_recordLaw_eq (secret : BitVec 256) (message : Message) (fuel : Nat) (cache : RCache) :
    actualRecordLaw secret message fuel cache=NativeSearch.recordLaw secret message fuel cache := by
  simp only [actualRecordLaw,NativeSearch.recordLaw,actual_search_eq]
theorem actual_recordLaw_scaled_cap (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (hfinite : SphincsSecurity.Finite cache)
    (q : Nat) (hsize : QueryCache.enncard cache ≤ q) (hq : q ≤ 2^127)
    (hclean : ¬NativeCache.Bad cache) (mark : MarkedLabel) :
    (1024/1025 : ENNReal)*((actualRecordLaw secret message fuel cache).map Prod.snd) mark ≤
      (PMF.uniformOfFintype MarkedLabel) mark := by
  rw [actual_recordLaw_eq]
  exact NativeSearch.recordLaw_scaled_cap secret message fuel hlimit cache hfinite q hsize hq hclean mark
end SigGolfResearch.Gate6.Source
#print axioms SigGolfResearch.Gate6.Source.actual_search_eq
#print axioms SigGolfResearch.Gate6.Source.actual_uniform_nonce_completed_cap
#print axioms SigGolfResearch.Gate6.Source.actual_recordLaw_scaled_cap
end
end

section



namespace SigGolfCandidate.T3.Sampling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Completeness (searchLoop failMass failMass_eq_probEvent)
open SigGolfCandidate.T3.DigestSampling
open SigGolfCandidate.T3.BPORS (finiteAverage expected_uniform_eq_finiteAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable def acceptedWeight {β : Type} (decoder : HashOutput → Option β)
    (payoff : β → ENNReal) : ENNReal :=
  expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
    (fun answer => (decoder answer).elim 0 payoff)
noncomputable def geometricWeight (failure accepted : ENNReal) : Nat → ENNReal
  | 0 => 0
  | n+1 => accepted+failure*geometricWeight failure accepted n
theorem uniform_decoder_weight {β : Type} (decoder : HashOutput → Option β)
    (payoff : β → ENNReal) (rejected : ENNReal) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => (decoder answer).elim rejected payoff)=
      acceptedWeight decoder payoff+failMass decoder*rejected := by
  classical
  have hp (answer : HashOutput) :
      (decoder answer).elim rejected payoff=(decoder answer).elim 0 payoff+
        (if decoder answer=none then 1 else 0)*rejected := by
    cases decoder answer <;> simp
  simp_rw [hp]
  rw [expectedValue_add,expectedValue_mul_const,expectedValue_ite_one]
  have hf : failMass decoder=Pr[fun answer : HashOutput => decoder answer=none |
      ($ᵗ HashOutput : ProbComp HashOutput)] := failMass_eq_probEvent decoder
  rw [← hf]
  rfl
theorem expected_publicSearch {β γ : Type} (secret : BitVec 256)
    (inputs : Nat → HashInput) (decoder : HashOutput → Option β)
    (result : Nat → β → γ) (payoff : γ → ENNReal) (weight : β → ENNReal)
    (hweight : ∀ counter value,payoff (result counter value)=weight value)
    (bound : Nat)
    (hinj : ∀ left right,left < bound → right < bound → inputs left=inputs right → left=right) :
    ∀ fuel counter,counter+fuel ≤ bound → ∀ cache : RCache,
      (∀ c,counter ≤ c → c < bound → cache (inputs c)=none) →
      expectedValue (roRun secret
        (publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache)
        (fun output => output.1.elim 0 payoff)=
      geometricWeight (failMass decoder) (acceptedWeight decoder weight) fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter _ cache _
      simp [searchLoop,publicProgram,geometricWeight]
  | succ fuel ih =>
      intro counter hlimit cache hfresh
      rw [publicSearch_succ,roRun_bind,roRun_publicQuery,expectedValue_bind,
        expectedValue_fresh _ _ (hfresh counter le_rfl (by omega))]
      have hbranch (answer : HashOutput) :
          expectedValue
            (roRun secret (match decoder answer with
              | none => publicProgram (searchLoop inputs decoder
                  (fun c v => pure (result c v)) fuel (counter+1))
              | some value => pure (some (result counter value)))
              (cache.cacheQuery (inputs counter) answer))
            (fun output => output.1.elim 0 payoff)=
          (decoder answer).elim
            (geometricWeight (failMass decoder) (acceptedWeight decoder weight) fuel) weight := by
        cases hd : decoder answer with
        | some value => simp [hweight]
        | none =>
            apply ih (counter+1) (by omega) _
            intro c hstart hc
            rw [QueryCache.cacheQuery_of_ne]
            · exact hfresh c (by omega) hc
            · intro he
              have hh := hinj c counter hc (by omega) he
              omega
      calc
        _ = expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun answer =>
            (decoder answer).elim
              (geometricWeight (failMass decoder) (acceptedWeight decoder weight) fuel) weight) := by
          congr 1
          funext answer
          exact hbranch answer
        _ = _ := uniform_decoder_weight decoder weight _
theorem geometricWeight_mul (failure accepted factor : ENNReal) (fuel : Nat) :
    geometricWeight failure (factor*accepted) fuel=
      factor*geometricWeight failure accepted fuel := by
  induction fuel with
  | zero => simp [geometricWeight]
  | succ fuel ih => simp only [geometricWeight,ih];ring
theorem digest_acceptedWeight (payoff : IndexBuckets → ENNReal) :
    acceptedWeight digestDecode (fun output => payoff (samplingData output).1)=
      finiteAverage payoff*acceptanceProbability := by
  unfold acceptedWeight
  calc
    _ = expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun output => if digestAdmissible output then payoff (samplingData output).1 else 0) := by
      congr 1
      funext output
      unfold digestDecode
      split <;> rfl
    _ = _ := accepted_samplingData payoff
theorem digestSearch_label_weight (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel counter : Nat) (hlimit : counter+fuel ≤ 2^32) (cache : RCache)
    (hfresh : ∀ c,counter ≤ c → c < 2^32 → cache (digestTrial rho message c)=none)
    (payoff : IndexBuckets → ENNReal) :
    expectedValue (roRun secret (digestSearch rho message counter fuel) cache)
      (fun result => result.1.elim 0 (fun found => payoff (samplingData found.2).1))=
      finiteAverage payoff*geometricWeight (failMass digestDecode) acceptanceProbability fuel := by
  rw [digestSearch_public]
  rw [expected_publicSearch secret (digestTrial rho message) digestDecode
    (fun c output => (BitVec.ofNat 32 c,output))
    (fun found => payoff (samplingData found.2).1)
    (fun output => payoff (samplingData output).1) (fun _ _ => rfl) (2^32)
    (fun _ _ hl hr he => digestTrial_injective rho message hl hr he)
    fuel counter hlimit cache hfresh]
  rw [digest_acceptedWeight,geometricWeight_mul]
theorem digest_acceptanceProbability :
    Pr[fun output : HashOutput => digestAdmissible output=true |
      ($ᵗ HashOutput : ProbComp HashOutput)]=acceptanceProbability := by
  rw [← expectedValue_ite_one]
  have h := accepted_samplingData (fun _ => (1 : ENNReal))
  rw [BPORS.History.finiteAverage_constant,one_mul] at h
  exact h
theorem digest_acceptanceProbability_le_one : acceptanceProbability ≤ 1 := by
  rw [← digest_acceptanceProbability]
  exact probEvent_le_one
theorem digest_failMass : failMass digestDecode=1-acceptanceProbability := by
  have hf : failMass digestDecode=Pr[fun answer : HashOutput => digestDecode answer=none |
      ($ᵗ HashOutput : ProbComp HashOutput)] := failMass_eq_probEvent digestDecode
  rw [hf]
  have he (answer : HashOutput) : digestDecode answer=none ↔ ¬digestAdmissible answer=true := by
    by_cases h : digestAdmissible answer=true
    · simp only [digestDecode,h,ite_true,reduceCtorEq,not_true_eq_false]
    · simp only [digestDecode,h,Bool.false_eq_true,ite_false,not_false_eq_true]
  simp_rw [he]
  rw [probEvent_not,digest_acceptanceProbability]
theorem geometricWeight_le_one (failure accepted : ENNReal) (hmass : accepted+failure ≤ 1)
    (fuel : Nat) : geometricWeight failure accepted fuel ≤ 1 := by
  induction fuel with
  | zero => exact bot_le
  | succ fuel ih =>
      exact (add_le_add le_rfl (mul_le_of_le_one_right' ih)).trans hmass
theorem digestSearch_label_weight_le (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel counter : Nat) (hlimit : counter+fuel ≤ 2^32) (cache : RCache)
    (hfresh : ∀ c,counter ≤ c → c < 2^32 → cache (digestTrial rho message c)=none)
    (payoff : IndexBuckets → ENNReal) :
    expectedValue (roRun secret (digestSearch rho message counter fuel) cache)
      (fun result => result.1.elim 0 (fun found => payoff (samplingData found.2).1)) ≤
      finiteAverage payoff := by
  rw [digestSearch_label_weight secret rho message fuel counter hlimit cache hfresh payoff]
  apply mul_le_of_le_one_right'
  apply geometricWeight_le_one
  rw [digest_failMass,add_tsub_cancel_of_le digest_acceptanceProbability_le_one]
theorem digestSearch_label_probability_le (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel counter : Nat) (hlimit : counter+fuel ≤ 2^32) (cache : RCache)
    (hfresh : ∀ c,counter ≤ c → c < 2^32 → cache (digestTrial rho message c)=none)
    (targets : Finset IndexBuckets) :
    Pr[fun result => ∃ found,result.1=some found ∧ (samplingData found.2).1 ∈ targets |
      roRun secret (digestSearch rho message counter fuel) cache] ≤
      targets.card/(2 : ENNReal)^59 := by
  classical
  have h := digestSearch_label_weight_le secret rho message fuel counter hlimit cache hfresh
    (fun label => if label ∈ targets then 1 else 0)
  have hs (result : Option (BitVec 32 × HashOutput) × RCache) :
      result.1.elim 0 (fun found => if (samplingData found.2).1 ∈ targets then (1 : ENNReal) else 0)=
      if ∃ found,result.1=some found ∧ (samplingData found.2).1 ∈ targets then 1 else 0 := by
    cases result.1 <;> simp
  simp_rw [hs] at h
  rw [expectedValue_ite_one] at h
  have hc : finiteAverage (fun label : IndexBuckets => if label ∈ targets then (1 : ENNReal) else 0)=
      targets.card/(2 : ENNReal)^59 := by
    rw [← expected_uniform_eq_finiteAverage,expectedValue_ite_one,probEvent_uniformSample]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
    have hcard : Fintype.card IndexBuckets=2^59 := by
      norm_num [IndexBuckets,Fintype.card_prod,Fintype.card_fun]
    rw [hcard]
    rw [Nat.cast_pow,Nat.cast_ofNat]
  rwa [hc] at h
def CachedTrialsReject {β : Type} (inputs : Nat → HashInput) (decoder : HashOutput → Option β)
    (counter bound : Nat) (cache : RCache) : Prop :=
  ∀ c,counter ≤ c → c < bound → ∀ answer,cache (inputs c)=some answer → decoder answer=none
theorem expected_publicSearch_le_of_cached_reject {β γ : Type} (secret : BitVec 256)
    (inputs : Nat → HashInput) (decoder : HashOutput → Option β)
    (result : Nat → β → γ) (payoff : γ → ENNReal) (weight : β → ENNReal)
    (hweight : ∀ counter value,payoff (result counter value)=weight value)
    (price : ENNReal) (hstep : acceptedWeight decoder weight+failMass decoder*price ≤ price)
    (bound : Nat)
    (hinj : ∀ left right,left < bound → right < bound → inputs left=inputs right → left=right) :
    ∀ fuel counter,counter+fuel ≤ bound → ∀ cache : RCache,
      CachedTrialsReject inputs decoder counter bound cache →
      expectedValue (roRun secret
        (publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache)
        (fun output => output.1.elim 0 payoff) ≤ price := by
  intro fuel
  induction fuel with
  | zero => intro counter _ cache _;simp [searchLoop,publicProgram]
  | succ fuel ih =>
      intro counter hlimit cache hcache
      rw [publicSearch_succ,roRun_bind,roRun_publicQuery,expectedValue_bind]
      cases hc : cache (inputs counter) with
      | some answer =>
          have hd := hcache counter le_rfl (by omega) answer hc
          rw [randomOracle.run_eq,hc]
          simp only [expectedValue_pure,hd]
          exact ih (counter+1) (by omega) cache
            (fun c hstart hbound answer ha => hcache c (by omega) hbound answer ha)
      | none =>
          rw [expectedValue_fresh _ _ hc]
          calc
            _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                (fun answer => (decoder answer).elim price weight) := by
              apply expectedValue_mono
              intro answer
              cases hd : decoder answer with
              | some value => simp [hweight]
              | none =>
                  apply ih (counter+1) (by omega) _
                  intro c hstart hbound output ho
                  have hne : inputs c ≠ inputs counter := by
                    intro he
                    have hh := hinj c counter hbound (by omega) he
                    omega
                  have hh : cache (inputs c)=some output :=
                    (QueryCache.cacheQuery_of_ne cache answer hne).symm.trans ho
                  exact hcache c (by omega) hbound output hh
            _ = acceptedWeight decoder weight+failMass decoder*price :=
              uniform_decoder_weight decoder weight price
            _ ≤ price := hstep
theorem digestSearch_label_weight_le_of_cached_reject
    (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel counter : Nat) (hlimit : counter+fuel ≤ 2^32) (cache : RCache)
    (hcache : CachedTrialsReject (digestTrial rho message) digestDecode counter (2^32) cache)
    (payoff : IndexBuckets → ENNReal) :
    expectedValue (roRun secret (digestSearch rho message counter fuel) cache)
      (fun result => result.1.elim 0 (fun found => payoff (samplingData found.2).1)) ≤
      finiteAverage payoff := by
  rw [digestSearch_public]
  apply expected_publicSearch_le_of_cached_reject secret (digestTrial rho message) digestDecode
    (fun c output => (BitVec.ofNat 32 c,output))
    (fun found => payoff (samplingData found.2).1)
    (fun output => payoff (samplingData output).1) (fun _ _ => rfl) (finiteAverage payoff) _ (2^32)
    (fun _ _ hl hr he => digestTrial_injective rho message hl hr he)
    fuel counter hlimit cache hcache
  rw [digest_acceptedWeight]
  calc
    _ = finiteAverage payoff*(acceptanceProbability+failMass digestDecode) := by ring
    _ = finiteAverage payoff := by
      rw [digest_failMass,add_tsub_cancel_of_le digest_acceptanceProbability_le_one,mul_one]
    _ ≤ finiteAverage payoff := le_rfl
end SigGolfCandidate.T3.Sampling
namespace SigGolfCandidate.T3.Sampling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Completeness (searchLoop failMass)
open SigGolfCandidate.T3.DigestSampling
open SigGolfCandidate.T3.BPORS (finiteAverage expected_uniform_eq_finiteAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
def CachedTrialScoresBound {β : Type} (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (weight : β → ENNReal) (price : ENNReal)
    (counter bound : Nat) (cache : RCache) : Prop :=
  ∀ c,counter ≤ c → c < bound → ∀ answer,cache (inputs c)=some answer →
    (decoder answer).elim 0 weight ≤ price
theorem expected_publicSearch_le_of_cached_scores {β γ : Type} (secret : BitVec 256)
    (inputs : Nat → HashInput) (decoder : HashOutput → Option β)
    (result : Nat → β → γ) (payoff : γ → ENNReal) (weight : β → ENNReal)
    (hweight : ∀ counter value,payoff (result counter value)=weight value)
    (price : ENNReal) (hstep : acceptedWeight decoder weight+failMass decoder*price ≤ price)
    (bound : Nat)
    (hinj : ∀ left right,left < bound → right < bound → inputs left=inputs right → left=right) :
    ∀ fuel counter,counter+fuel ≤ bound → ∀ cache : RCache,
      CachedTrialScoresBound inputs decoder weight price counter bound cache →
      expectedValue (roRun secret
        (publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache)
        (fun output => output.1.elim 0 payoff) ≤ price := by
  intro fuel
  induction fuel with
  | zero => intro counter _ cache _;simp [searchLoop,publicProgram]
  | succ fuel ih =>
      intro counter hlimit cache hcache
      rw [publicSearch_succ,roRun_bind,roRun_publicQuery,expectedValue_bind]
      cases hc : cache (inputs counter) with
      | some answer =>
          have hp := hcache counter le_rfl (by omega) answer hc
          rw [randomOracle.run_eq,hc]
          simp only [expectedValue_pure]
          cases hd : decoder answer with
          | none =>
              exact ih (counter+1) (by omega) cache
                (fun c hstart hbound answer ha => hcache c (by omega) hbound answer ha)
          | some value =>
              simpa only [roRun_pure,expectedValue_pure,Option.elim_some,hweight,hd] using hp
      | none =>
          rw [expectedValue_fresh _ _ hc]
          calc
            _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                (fun answer => (decoder answer).elim price weight) := by
              apply expectedValue_mono
              intro answer
              cases hd : decoder answer with
              | some value => simp [hweight]
              | none =>
                  apply ih (counter+1) (by omega) _
                  intro c hstart hbound output ho
                  have hne : inputs c ≠ inputs counter := by
                    intro he
                    have hh := hinj c counter hbound (by omega) he
                    omega
                  have hh : cache (inputs c)=some output :=
                    (QueryCache.cacheQuery_of_ne cache answer hne).symm.trans ho
                  exact hcache c (by omega) hbound output hh
            _ = acceptedWeight decoder weight+failMass decoder*price :=
              uniform_decoder_weight decoder weight price
            _ ≤ price := hstep
def CachedTarget (rho : Digest) (message : Message) (fuel : Nat) (cache : RCache)
    (targets : Finset IndexBuckets) : Prop :=
  ∃ c,c < fuel ∧ ∃ answer,cache (digestTrial rho message c)=some answer ∧
    digestAdmissible answer=true ∧ (samplingData answer).1 ∈ targets
noncomputable def targetWeight (targets : Finset IndexBuckets) (label : IndexBuckets) : ENNReal :=
  if label ∈ targets then 1 else 0
theorem targetWeight_average (targets : Finset IndexBuckets) :
    finiteAverage (targetWeight targets)=targets.card/(2 : ENNReal)^59 := by
  classical
  unfold targetWeight
  rw [← expected_uniform_eq_finiteAverage,expectedValue_ite_one,probEvent_uniformSample]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  have hcard : Fintype.card IndexBuckets=2^59 := by
    norm_num [IndexBuckets,Fintype.card_prod,Fintype.card_fun]
  rw [hcard,Nat.cast_pow,Nat.cast_ofNat]
theorem targetWeight_probability (targets : Finset IndexBuckets)
    (program : ProbComp (Option (BitVec 32 × HashOutput) × RCache)) :
    expectedValue program (fun result => result.1.elim 0
      (fun found => targetWeight targets (samplingData found.2).1))=
    Pr[fun result => ∃ found,result.1=some found ∧ (samplingData found.2).1 ∈ targets | program] := by
  classical
  have he (result : Option (BitVec 32 × HashOutput) × RCache) :
      result.1.elim 0 (fun found => targetWeight targets (samplingData found.2).1)=
      if ∃ found,result.1=some found ∧ (samplingData found.2).1 ∈ targets then 1 else 0 := by
    cases result.1 <;> simp [targetWeight]
  simp_rw [he]
  rw [expectedValue_ite_one]
theorem digestSearch_target_le_of_no_cached_hit (secret : BitVec 256) (rho : Digest)
    (message : Message) (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache)
    (targets : Finset IndexBuckets) (hno : ¬CachedTarget rho message fuel cache targets) :
    Pr[fun result => ∃ found,result.1=some found ∧ (samplingData found.2).1 ∈ targets |
      roRun secret (digestSearch rho message 0 fuel) cache] ≤ targets.card/(2 : ENNReal)^59 := by
  classical
  rw [← targetWeight_probability,← targetWeight_average,digestSearch_public]
  apply expected_publicSearch_le_of_cached_scores secret (digestTrial rho message) digestDecode
    (fun c output => (BitVec.ofNat 32 c,output))
    (fun found => targetWeight targets (samplingData found.2).1)
    (fun output => targetWeight targets (samplingData output).1) (fun _ _ => rfl)
    (finiteAverage (targetWeight targets)) _ fuel
    (fun _ _ hl hr he => digestTrial_injective rho message (lt_of_lt_of_le hl hlimit)
      (lt_of_lt_of_le hr hlimit) he) fuel 0 (by omega) cache
  · intro c hc hf answer ha
    by_cases hadm : digestAdmissible answer=true
    · have hnot : (samplingData answer).1 ∉ targets :=
        fun ht => hno ⟨c,hf,answer,ha,hadm,ht⟩
      simp only [digestDecode,hadm,ite_true,Option.elim_some,targetWeight,hnot,ite_false]
      exact bot_le
    · simp only [digestDecode,hadm,Bool.false_eq_true,ite_false,Option.elim_none]
      exact bot_le
  · rw [digest_acceptedWeight]
    calc
      _ = finiteAverage (targetWeight targets)*(acceptanceProbability+failMass digestDecode) := by ring
      _ = finiteAverage (targetWeight targets) := by
        rw [digest_failMass,add_tsub_cancel_of_le digest_acceptanceProbability_le_one,mul_one]
      _ ≤ finiteAverage (targetWeight targets) := le_rfl
theorem digestSearch_target_le_cached_event (secret : BitVec 256) (rho : Digest)
    (message : Message) (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache)
    (targets : Finset IndexBuckets) :
    Pr[fun result => ∃ found,result.1=some found ∧ (samplingData found.2).1 ∈ targets |
      roRun secret (digestSearch rho message 0 fuel) cache] ≤
      targets.card/(2 : ENNReal)^59 + if CachedTarget rho message fuel cache targets then 1 else 0 := by
  classical
  by_cases h : CachedTarget rho message fuel cache targets
  · rw [if_pos h]
    exact probEvent_le_one.trans (le_add_left le_rfl)
  · rw [if_neg h,add_zero]
    exact digestSearch_target_le_of_no_cached_hit secret rho message fuel hlimit cache targets h
noncomputable def cachedTargetNonces (message : Message) (fuel : Nat) (cache : RCache)
    (targets : Finset IndexBuckets) : Finset Digest := by
  classical
  exact Finset.univ.filter fun rho => CachedTarget rho message fuel cache targets
theorem uniform_nonce_target_bound (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (targets : Finset IndexBuckets) :
    Pr[fun result => ∃ found,result.1=some found ∧ (samplingData found.2).1 ∈ targets |
      (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
        roRun secret (digestSearch rho message 0 fuel) cache)] ≤
      targets.card/(2 : ENNReal)^59+
        (cachedTargetNonces message fuel cache targets).card/(2 : ENNReal)^128 := by
  classical
  rw [probEvent_bind_eq_expectedValue]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
        targets.card/(2 : ENNReal)^59+if CachedTarget rho message fuel cache targets then 1 else 0) :=
      expectedValue_mono _ fun rho => digestSearch_target_le_cached_event secret rho message fuel hlimit cache targets
    _ = _ := by
      rw [expectedValue_add,expectedValue_const (by simp),expectedValue_ite_one,probEvent_uniformSample]
      simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat,cachedTargetNonces]
end SigGolfCandidate.T3.Sampling
namespace SigGolfCandidate.T3.Sampling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
open SphincsSecurity (Finite positiveScoreMoment positiveScoreMoment_ne_top)
open SphincsSecurity.Concrete (bernoulliExcess_secondMoment_ennreal enncard_cacheQuery_of_fresh)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] digestSearch Finset.univ
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def AcceptedTarget (targets : Finset IndexBuckets) (answer : HashOutput) : Prop :=
  digestAdmissible answer=true ∧ (samplingData answer).1 ∈ targets
noncomputable def targetRate (targets : Finset IndexBuckets) : ENNReal :=
  targets.card/(2 : ENNReal)^59*acceptanceProbability
theorem acceptedTarget_probability (targets : Finset IndexBuckets) :
    Pr[AcceptedTarget targets | ($ᵗ HashOutput : ProbComp HashOutput)]=targetRate targets := by
  have h := accepted_samplingData (targetWeight targets)
  have hi (answer : HashOutput) :
      (if digestAdmissible answer then targetWeight targets (samplingData answer).1 else 0)=
      if AcceptedTarget targets answer then (1 : ENNReal) else 0 := by
    simp only [targetWeight,AcceptedTarget]
    split_ifs <;> simp_all
  simp_rw [hi] at h
  rw [expectedValue_ite_one,targetWeight_average] at h
  exact h
theorem targetRate_le_one (targets : Finset IndexBuckets) : targetRate targets ≤ 1 := by
  rw [← acceptedTarget_probability]
  exact probEvent_le_one
theorem digestTrial_nonce_injective {rho rho' : Digest} {message message' : Message}
    {counter counter' : Nat}
    (he : digestTrial rho message counter=digestTrial rho' message' counter') : rho=rho' := by
  have h := pad64_inj_of_length (by simp [digestInput,SphincsSecurity.bytesLE_length]) he
  exact (digestInput_injective h).1
noncomputable def cachedTargetEntry (targets : Finset IndexBuckets) (cache : RCache)
    (input : HashInput) : ENNReal :=
  (cache input).elim 0 (fun answer => if AcceptedTarget targets answer then 1 else 0)
noncomputable def cachedTargetCount (targets : Finset IndexBuckets) (cache : RCache) : ENNReal :=
  ∑' input,cachedTargetEntry targets cache input
theorem cachedTargetCount_empty (targets : Finset IndexBuckets) :
    cachedTargetCount targets ∅=0 := by
  simp [cachedTargetCount,cachedTargetEntry]
theorem cachedTargetCount_cacheQuery (targets : Finset IndexBuckets) (cache : RCache)
    (input : HashInput) (answer : HashOutput) (hfresh : cache input=none) :
    cachedTargetCount targets (cache.cacheQuery input answer)=cachedTargetCount targets cache+
      if AcceptedTarget targets answer then 1 else 0 := by
  unfold cachedTargetCount
  rw [ENNReal.tsum_eq_add_tsum_ite (f := cachedTargetEntry targets (cache.cacheQuery input answer)) input,
    ENNReal.tsum_eq_add_tsum_ite (f := cachedTargetEntry targets cache) input]
  simp only [cachedTargetEntry,QueryCache.cacheQuery_self,hfresh,Option.elim_none,Option.elim_some,zero_add]
  rw [add_comm]
  congr 1
  apply tsum_congr
  intro other
  by_cases heq : other=input
  · simp [heq]
  · simp only [heq,if_false,QueryCache.cacheQuery_of_ne cache answer heq]
theorem cachedTargetCount_le_enncard (targets : Finset IndexBuckets) (cache : RCache)
    (hfinite : Finite cache) : cachedTargetCount targets cache ≤ QueryCache.enncard cache := by
  unfold cachedTargetCount
  rw [tsum_eq_sum (s := hfinite.toFinset) (fun input hnot => by
    have hn : cache input=none := by
      by_contra h
      exact hnot (hfinite.mem_toFinset.mpr h)
    simp [cachedTargetEntry,hn])]
  calc
    _ ≤ ∑ _input ∈ hfinite.toFinset,(1 : ENNReal) := by
      apply Finset.sum_le_sum
      intro input _
      unfold cachedTargetEntry
      cases cache input <;> simp only [Option.elim_none,Option.elim_some]
      · exact bot_le
      · split_ifs <;> norm_num
    _ = _ := by
      rw [Finset.sum_const,nsmul_eq_mul,mul_one,
        ← Set.ncard_eq_toFinset_card {input | cache input ≠ none} hfinite]
      exact hfinite.cachedInputs_ncard_toENNReal_eq_enncard
theorem cachedTargetCount_ne_top (targets : Finset IndexBuckets) (cache : RCache)
    (hfinite : Finite cache) : cachedTargetCount targets cache ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (cachedTargetCount_le_enncard targets cache hfinite)
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness
theorem cachedTargetNonces_card_le_count (message : Message) (fuel : Nat) (cache : RCache)
    (targets : Finset IndexBuckets) :
    ((cachedTargetNonces message fuel cache targets).card : ENNReal) ≤
      cachedTargetCount targets cache := by
  classical
  let nonces := cachedTargetNonces message fuel cache targets
  have hw : ∀ rho : nonces,∃ counter,counter < fuel ∧ ∃ answer,
      cache (digestTrial rho.val message counter)=some answer ∧ AcceptedTarget targets answer := by
    intro rho
    exact (Finset.mem_filter.mp rho.property).2
  choose counter hc answer ha htarget using hw
  let inputs (rho : nonces) := digestTrial rho.val message (counter rho)
  have hinj : Function.Injective inputs := by
    intro left right he
    exact Subtype.ext (digestTrial_nonce_injective he)
  have hentry (rho : nonces) : cachedTargetEntry targets cache (inputs rho)=1 := by
    simp only [cachedTargetEntry,inputs,ha,Option.elim_some,htarget,if_true]
  calc
    _ = ∑ rho : nonces,cachedTargetEntry targets cache (inputs rho) := by
      simp only [hentry,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one,nonces]
    _ ≤ ∑' input,cachedTargetEntry targets cache input := by
      simpa only [tsum_fintype] using
        (ENNReal.tsum_comp_le_tsum_of_injective hinj (cachedTargetEntry targets cache))
    _ = _ := rfl
theorem uniform_nonce_target_bound_count (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (targets : Finset IndexBuckets) :
    Pr[fun result => ∃ found,result.1=some found ∧ (samplingData found.2).1 ∈ targets |
      (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
        roRun secret (digestSearch rho message 0 fuel) cache)] ≤
      targets.card/(2 : ENNReal)^59+cachedTargetCount targets cache/(2 : ENNReal)^128 :=
  by
    have h := uniform_nonce_target_bound secret message fuel hlimit cache targets
    apply h.trans
    apply add_le_add le_rfl
    exact ENNReal.div_le_div_right (cachedTargetNonces_card_le_count message fuel cache targets) _
noncomputable def targetExcess (targets : Finset IndexBuckets) (cache : RCache) : ℝ :=
  (cachedTargetCount targets cache).toReal -
    (QueryCache.enncard cache).toReal*(targetRate targets).toReal
theorem targetExcess_cacheQuery (targets : Finset IndexBuckets) (cache : RCache)
    (hfinite : Finite cache) (input : HashInput) (answer : HashOutput)
    (hfresh : cache input=none) :
    targetExcess targets (cache.cacheQuery input answer)=targetExcess targets cache+
      (if AcceptedTarget targets answer then 1 else 0)-(targetRate targets).toReal := by
  have hc := cachedTargetCount_ne_top targets cache hfinite
  have hn : QueryCache.enncard cache ≠ ⊤ := by
    rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
    finiteness
  unfold targetExcess
  rw [cachedTargetCount_cacheQuery targets cache input answer hfresh,
    enncard_cacheQuery_of_fresh cache input answer hfresh,
    ENNReal.toReal_add hn (by finiteness),ENNReal.toReal_one]
  split_ifs <;> simp only [add_zero,ENNReal.toReal_add hc (by finiteness),ENNReal.toReal_one] <;> ring
theorem expected_acceptedTarget_choice (targets : Finset IndexBuckets) (yes no : ENNReal) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => if AcceptedTarget targets answer then yes else no)=
      targetRate targets*yes+(1-targetRate targets)*no := by
  have hnot : Pr[fun answer => ¬AcceptedTarget targets answer |
      ($ᵗ HashOutput : ProbComp HashOutput)]=1-targetRate targets := by
    have h := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) (AcceptedTarget targets)
    rw [probFailure_of_liftM_PMF,tsub_zero,acceptedTarget_probability,add_comm] at h
    exact ENNReal.eq_sub_of_add_eq' (by simp) h
  have hsplit (answer : HashOutput) :
      (if AcceptedTarget targets answer then yes else no)=
      (if AcceptedTarget targets answer then (1 : ENNReal) else 0)*yes+
        (if ¬AcceptedTarget targets answer then (1 : ENNReal) else 0)*no := by
    by_cases h : AcceptedTarget targets answer <;>
      simp only [h,if_true,if_false,not_true_eq_false,not_false_eq_true,one_mul,zero_mul,zero_add,add_zero]
  simp_rw [hsplit]
  rw [expectedValue_add,expectedValue_mul_const,expectedValue_mul_const,
    expectedValue_ite_one,expectedValue_ite_one,acceptedTarget_probability,hnot]
theorem expected_targetExcess_second_le (targets : Finset IndexBuckets) (cache : RCache)
    (hfinite : Finite cache) (input : HashInput) (hfresh : cache input=none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => positiveScoreMoment (targetExcess targets (cache.cacheQuery input answer)) 2) ≤
      positiveScoreMoment (targetExcess targets cache) 2+targetRate targets := by
  simp_rw [targetExcess_cacheQuery targets cache hfinite input _ hfresh]
  have hchoice (answer : HashOutput) :
      positiveScoreMoment (targetExcess targets cache+
        (if AcceptedTarget targets answer then 1 else 0)-(targetRate targets).toReal) 2=
      if AcceptedTarget targets answer then
        positiveScoreMoment (targetExcess targets cache+(1-(targetRate targets).toReal)) 2
      else positiveScoreMoment (targetExcess targets cache+(-(targetRate targets).toReal)) 2 := by
    split_ifs <;> congr 1 <;> ring
  simp_rw [hchoice]
  rw [expected_acceptedTarget_choice]
  exact bernoulliExcess_secondMoment_ennreal _ _ (targetRate_le_one targets)
theorem singleton_targetRate_sum :
    (∑ point : IndexBuckets,targetRate {point})=acceptanceProbability := by
  simp only [targetRate,Finset.card_singleton,Nat.cast_one,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  have hc : Fintype.card IndexBuckets=2^59 := by
    norm_num [IndexBuckets,Fintype.card_prod,Fintype.card_fun]
  rw [hc,Nat.cast_pow,Nat.cast_ofNat,← mul_assoc]
  rw [one_div,ENNReal.mul_inv_cancel (by norm_num) (by finiteness),one_mul]
noncomputable def allTargetMoment (cache : RCache) : ENNReal :=
  ∑ point : IndexBuckets,positiveScoreMoment (targetExcess {point} cache) 2
attribute [local irreducible] allTargetMoment cachedTargetCount targetExcess targetRate acceptanceProbability
theorem allTargetMoment_empty : allTargetMoment ∅=0 := by
  simp [allTargetMoment,targetExcess,cachedTargetCount_empty,positiveScoreMoment]
theorem expected_allTargetMoment_fresh (cache : RCache) (hfinite : Finite cache)
    (input : HashInput) (hfresh : cache input=none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => allTargetMoment (cache.cacheQuery input answer)) ≤
      allTargetMoment cache+acceptanceProbability := by
  calc
    _ = ∑ point : IndexBuckets,expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun answer => positiveScoreMoment (targetExcess {point} (cache.cacheQuery input answer)) 2) := by
      unfold allTargetMoment
      exact expectedValue_finsetSum _ _ _
    _ ≤ ∑ point : IndexBuckets,(positiveScoreMoment (targetExcess {point} cache) 2+targetRate {point}) :=
      Finset.sum_le_sum (fun point _ => expected_targetExcess_second_le {point} cache hfinite input hfresh)
    _ = _ := by
      rw [Finset.sum_add_distrib,singleton_targetRate_sum]
      unfold allTargetMoment
      rfl
private theorem constant_hashQueryCharge (rate : ENNReal) (query : SphincsSecurity.OracleWorld.Domain)
    (cache : RCache) :
    SphincsSecurity.hashQueryCharge (fun _ _ => rate) cache query=
      (if query matches .inr _ then rate else 0) := by
  cases query <;> rfl
theorem expected_allTargetMoment_step (query : SphincsSecurity.OracleWorld.Domain)
    (cache : RCache) (hfinite : Finite cache) :
    (∑' result,Pr[= result | (SphincsSecurity.romImpl query).run cache]*allTargetMoment result.2) ≤
      allTargetMoment cache+(if query matches .inr _ then acceptanceProbability else 0) := by
  have h := SphincsSecurity.expected_potential_romImpl_le_charge allTargetMoment
    (fun _ _ => acceptanceProbability) (fun current hc input hf =>
      expected_allTargetMoment_fresh current hc input hf) query cache hfinite
  rw [constant_hashQueryCharge] at h
  exact h
theorem cachedTargetCount_singleton_native (cache : RCache) (point : IndexBuckets) :
    cachedTargetCount {point} cache=SigGolfResearch.Gate6.NativeCache.count point cache := by
  unfold cachedTargetCount SigGolfResearch.Gate6.NativeCache.count
  apply tsum_congr
  intro input
  unfold cachedTargetEntry SigGolfResearch.Gate6.NativeCache.entry
  cases cache input with
  | none => rfl
  | some output =>
      change (if AcceptedTarget {point} output then (1 : ENNReal) else 0)=
        if SigGolfResearch.Gate6.Cache.Matches point output then 1 else 0
      have he : AcceptedTarget {point} output ↔ SigGolfResearch.Gate6.Cache.Matches point output := by
        simp only [AcceptedTarget,Finset.mem_singleton,SigGolfResearch.Gate6.Cache.Matches,
          samplingData_mark,SigGolfResearch.Gate6.Source.actual_predicate_iff]
      by_cases hh : AcceptedTarget {point} output
      · rw [if_pos hh,if_pos (he.mp hh)]
      · rw [if_neg hh,if_neg (fun hn => hh (he.mpr hn))]
theorem singleton_targetRate_native (point : IndexBuckets) :
    targetRate {point}=SigGolfResearch.Gate6.Cache.eRate := by
  simp only [targetRate,Finset.card_singleton,Nat.cast_one,acceptanceProbability,
    SigGolfResearch.Gate6.Cache.eRate,div_eq_mul_inv]
  ring
def TargetCacheExceptional (cache : RCache) : Prop :=
  ∃ point : IndexBuckets,(2^47 : ℝ) < targetExcess {point} cache
theorem targetCacheExceptional_iff_native (cache : RCache) :
    TargetCacheExceptional cache ↔ SigGolfResearch.Gate6.NativeCache.Bad cache := by
  unfold TargetCacheExceptional SigGolfResearch.Gate6.NativeCache.Bad
  apply exists_congr
  intro point
  rw [targetExcess,cachedTargetCount_singleton_native,singleton_targetRate_native]
  change (2^47 : ℝ)<(SigGolfResearch.Gate6.NativeCache.count point cache).toReal-
    (QueryCache.enncard cache).toReal*SigGolfResearch.Gate6.Cache.rate ↔ _
  constructor <;> intro h <;> linarith
theorem targetCacheExceptional_moment (cache : RCache) (hbad : TargetCacheExceptional cache) :
    (2^94 : ENNReal) ≤ allTargetMoment cache := by
  obtain ⟨point,hpoint⟩ := hbad
  have hpower : (2^94 : ℝ) ≤ max (targetExcess {point} cache) 0^2 := by
    calc
      _ = (2^47 : ℝ)^2 := by rw [← pow_mul]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (hpoint.le.trans (le_max_left _ _)) 2
  have hreal := ENNReal.ofReal_le_ofReal hpower
  rw [ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_ofNat] at hreal
  unfold allTargetMoment
  apply hreal.trans
  exact (Finset.single_le_sum (s := Finset.univ)
    (f := fun point => positiveScoreMoment (targetExcess {point} cache) 2)
    (fun _ _ => bot_le) (Finset.mem_univ point))
theorem adaptive_targetCache_exception {Result : Type}
    (program : OracleComp SphincsSecurity.OracleWorld Result) (budget : Nat) :
    Pr[fun result => result.1.2 ≤ budget ∧ TargetCacheExceptional result.2 |
      (simulateQ SphincsSecurity.romImpl (SphincsSecurity.countHashQueries program)).run ∅] ≤
      acceptanceProbability*budget/(2 : ENNReal)^94 := by
  have h := SphincsSecurity.expected_truncatedPotential_le allTargetMoment acceptanceProbability
    expected_allTargetMoment_step program ∅ SphincsSecurity.finite_empty budget
  rw [allTargetMoment_empty,zero_add] at h
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by finiteness))]
  calc
    _ = expectedValue
        ((simulateQ SphincsSecurity.romImpl (SphincsSecurity.countHashQueries program)).run ∅)
        (fun result => if result.1.2 ≤ budget ∧ TargetCacheExceptional result.2 then (2 : ENNReal)^94 else 0) := by
      rw [← expectedValue_ite_one,← expectedValue_mul_const]
      congr 1
      funext result
      split_ifs <;> simp
    _ ≤ expectedValue
        ((simulateQ SphincsSecurity.romImpl (SphincsSecurity.countHashQueries program)).run ∅)
        (fun result => SphincsSecurity.truncatedPotential allTargetMoment acceptanceProbability
          budget result.1.2 result.2) := by
      apply expectedValue_mono
      intro result
      by_cases hb : result.1.2 ≤ budget ∧ TargetCacheExceptional result.2
      · rw [if_pos hb,SphincsSecurity.truncatedPotential,if_pos hb.1]
        exact (targetCacheExceptional_moment result.2 hb.2).trans le_self_add
      · rw [if_neg hb]
        exact bot_le
    _ ≤ _ := h
theorem targetCount_bound_of_no_exception (cache : RCache) (hfinite : Finite cache)
    (budget : Nat) (hsize : QueryCache.enncard cache ≤ budget)
    (hclean : ¬TargetCacheExceptional cache) (point : IndexBuckets) :
    cachedTargetCount {point} cache ≤ (budget : ENNReal)*targetRate {point}+(2 : ENNReal)^47 := by
  have hc := cachedTargetCount_ne_top {point} cache hfinite
  have hn : QueryCache.enncard cache ≠ ⊤ := by
    rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
    finiteness
  have hr : targetRate {point} ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) (targetRate_le_one {point})
  apply (ENNReal.toReal_le_toReal hc (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),ENNReal.toReal_mul]
  have hcache := ENNReal.toReal_mono (by finiteness) hsize
  have hex : targetExcess {point} cache ≤ (2^47 : ℝ) :=
    le_of_not_gt (fun h => hclean ⟨point,h⟩)
  have hscale := mul_le_mul_of_nonneg_right hcache (ENNReal.toReal_nonneg (a := targetRate {point}))
  simp only [targetExcess] at hex
  norm_num at hcache hscale ⊢
  linarith
theorem uniform_nonce_point_bound_clean (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (hfinite : Finite cache)
    (budget : Nat) (hsize : QueryCache.enncard cache ≤ budget)
    (hclean : ¬TargetCacheExceptional cache) (point : IndexBuckets) :
    Pr[fun result => ∃ found,result.1=some found ∧ (samplingData found.2).1=point |
      (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
        roRun secret (digestSearch rho message 0 fuel) cache)] ≤
      1/(2 : ENNReal)^59+
        ((budget : ENNReal)*targetRate {point}+(2 : ENNReal)^47)/(2 : ENNReal)^128 := by
  have h := uniform_nonce_target_bound_count secret message fuel hlimit cache {point}
  simp only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one] at h
  apply h.trans
  apply add_le_add le_rfl
  exact ENNReal.div_le_div_right (targetCount_bound_of_no_exception cache hfinite budget hsize hclean point) _
theorem uniform_nonce_point_cap (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (hfinite : Finite cache)
    (budget : Nat) (hsize : QueryCache.enncard cache ≤ budget) (hbudget : budget ≤ 2^127)
    (hclean : ¬TargetCacheExceptional cache) (haccept : acceptanceProbability ≤ 1/16)
    (point : IndexBuckets) :
    Pr[fun result => ∃ found,result.1=some found ∧ (samplingData found.2).1=point |
      (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
        roRun secret (digestSearch rho message 0 fuel) cache)] ≤
      (1025/1024 : ENNReal)/(2 : ENNReal)^59 := by
  have h := uniform_nonce_target_bound_count secret message fuel hlimit cache {point}
  simp only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one] at h
  apply h.trans
  rw [cachedTargetCount_singleton_native]
  exact SigGolfResearch.Gate6.NativeCache.clean_point_bound_arithmetic cache hfinite budget hsize hbudget
    (fun h => hclean ((targetCacheExceptional_iff_native cache).mpr h)) point
end SigGolfCandidate.T3.Sampling
namespace SigGolfCandidate.T3.Sampling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Completeness (searchLoop failMass)
open SigGolfCandidate.T3.DigestSampling
open SigGolfCandidate.T3.BPORS (finiteAverage expected_uniform_eq_finiteAverage)
open SphincsSecurity (Finite)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] digestSearch Finset.univ BPORS.finiteAverage DigestSampling.samplingData
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem expected_publicSearch_completed_le_of_cached_scores {β γ : Type} (secret : BitVec 256)
    (inputs : Nat → HashInput) (decoder : HashOutput → Option β)
    (result : Nat → β → γ) (payoff : γ → ENNReal) (weight : β → ENNReal)
    (hweight : ∀ counter value,payoff (result counter value)=weight value)
    (price : ENNReal) (hstep : acceptedWeight decoder weight+failMass decoder*price ≤ price)
    (bound : Nat)
    (hinj : ∀ left right,left < bound → right < bound → inputs left=inputs right → left=right) :
    ∀ fuel counter,counter+fuel ≤ bound → ∀ cache : RCache,
      CachedTrialScoresBound inputs decoder weight price counter bound cache →
      expectedValue (roRun secret
        (publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache)
        (fun output => output.1.elim price payoff) ≤ price := by
  intro fuel
  induction fuel with
  | zero => intro counter _ cache _;simp [searchLoop,publicProgram]
  | succ fuel ih =>
      intro counter hlimit cache hcache
      rw [publicSearch_succ,roRun_bind,roRun_publicQuery,expectedValue_bind]
      cases hc : cache (inputs counter) with
      | some answer =>
          have hp := hcache counter le_rfl (by omega) answer hc
          rw [randomOracle.run_eq,hc]
          simp only [expectedValue_pure]
          cases hd : decoder answer with
          | none =>
              exact ih (counter+1) (by omega) cache
                (fun c hstart hbound answer ha => hcache c (by omega) hbound answer ha)
          | some value =>
              simpa only [roRun_pure,expectedValue_pure,Option.elim_some,hweight,hd] using hp
      | none =>
          rw [expectedValue_fresh _ _ hc]
          calc
            _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                (fun answer => (decoder answer).elim price weight) := by
              apply expectedValue_mono
              intro answer
              cases hd : decoder answer with
              | some value => simp [hweight]
              | none =>
                  apply ih (counter+1) (by omega) _
                  intro c hstart hbound output ho
                  have hne : inputs c ≠ inputs counter := by
                    intro he
                    have hh := hinj c counter hbound (by omega) he
                    omega
                  have hh : cache (inputs c)=some output :=
                    (QueryCache.cacheQuery_of_ne cache answer hne).symm.trans ho
                  exact hcache c (by omega) hbound output hh
            _ = acceptedWeight decoder weight+failMass decoder*price :=
              uniform_decoder_weight decoder weight price
            _ ≤ price := hstep
noncomputable def completedTargetScore (targets : Finset IndexBuckets)
    (found : Option (BitVec 32 × HashOutput)) : ENNReal :=
  found.elim (finiteAverage (targetWeight targets))
    (fun value => targetWeight targets (samplingData value.2).1)
theorem targetWeight_average_le_one (targets : Finset IndexBuckets) :
    finiteAverage (targetWeight targets) ≤ 1 := by
  rw [← expected_uniform_eq_finiteAverage]
  apply expectedValue_le_of_le
  intro label
  unfold targetWeight
  split_ifs <;> norm_num
private theorem option_weight_le_one {Value : Type} (found : Option Value)
    (fallback : ENNReal) (weight : Value → ENNReal)
    (hmiss : fallback ≤ 1) (hvalue : ∀ value,weight value ≤ 1) :
    found.elim fallback weight ≤ 1 := by
  cases found with
  | none => exact hmiss
  | some value => exact hvalue value
theorem completedTargetScore_le_one (targets : Finset IndexBuckets)
    (found : Option (BitVec 32 × HashOutput)) : completedTargetScore targets found ≤ 1 := by
  apply option_weight_le_one found _ _ (targetWeight_average_le_one targets)
  intro value
  unfold targetWeight
  split_ifs <;> norm_num
theorem completed_search_target_le_of_no_cached_hit (secret : BitVec 256) (rho : Digest)
    (message : Message) (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache)
    (targets : Finset IndexBuckets) (hno : ¬CachedTarget rho message fuel cache targets) :
    expectedValue (roRun secret (digestSearch rho message 0 fuel) cache)
      (fun result => completedTargetScore targets result.1) ≤ finiteAverage (targetWeight targets) := by
  rw [digestSearch_public]
  apply expected_publicSearch_completed_le_of_cached_scores secret (digestTrial rho message) digestDecode
    (fun c output => (BitVec.ofNat 32 c,output))
    (fun found => targetWeight targets (samplingData found.2).1)
    (fun output => targetWeight targets (samplingData output).1) (fun _ _ => rfl)
    (finiteAverage (targetWeight targets)) _ fuel
    (fun _ _ hl hr he => digestTrial_injective rho message (lt_of_lt_of_le hl hlimit)
      (lt_of_lt_of_le hr hlimit) he) fuel 0 (by omega) cache
  · intro c hc hf answer ha
    by_cases hadm : digestAdmissible answer=true
    · have hnot : (samplingData answer).1 ∉ targets :=
        fun ht => hno ⟨c,hf,answer,ha,hadm,ht⟩
      simp only [digestDecode,hadm,ite_true,Option.elim_some,targetWeight,hnot,ite_false]
      exact bot_le
    · simp only [digestDecode,hadm,Bool.false_eq_true,ite_false,Option.elim_none]
      exact bot_le
  · rw [digest_acceptedWeight]
    calc
      _ = finiteAverage (targetWeight targets)*(acceptanceProbability+failMass digestDecode) := by ring
      _ = finiteAverage (targetWeight targets) := by
        rw [digest_failMass,add_tsub_cancel_of_le digest_acceptanceProbability_le_one,mul_one]
      _ ≤ _ := le_rfl
theorem completed_search_target_le_cached_event (secret : BitVec 256) (rho : Digest)
    (message : Message) (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache)
    (targets : Finset IndexBuckets) :
    expectedValue (roRun secret (digestSearch rho message 0 fuel) cache)
      (fun result => completedTargetScore targets result.1) ≤
      finiteAverage (targetWeight targets)+if CachedTarget rho message fuel cache targets then 1 else 0 := by
  by_cases h : CachedTarget rho message fuel cache targets
  · rw [if_pos h]
    exact (expectedValue_le_of_le _ (fun _ => completedTargetScore_le_one targets _)).trans
      (le_add_left le_rfl)
  · rw [if_neg h,add_zero]
    exact completed_search_target_le_of_no_cached_hit secret rho message fuel hlimit cache targets h
theorem uniform_nonce_completed_target_bound (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (targets : Finset IndexBuckets) :
    expectedValue (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
      roRun secret (digestSearch rho message 0 fuel) cache)
      (fun result => completedTargetScore targets result.1) ≤
      targets.card/(2 : ENNReal)^59+cachedTargetCount targets cache/(2 : ENNReal)^128 := by
  rw [expectedValue_bind]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
        finiteAverage (targetWeight targets)+if CachedTarget rho message fuel cache targets then 1 else 0) :=
      expectedValue_mono _ fun rho => completed_search_target_le_cached_event secret rho message fuel hlimit cache targets
    _ = targets.card/(2 : ENNReal)^59+
        (cachedTargetNonces message fuel cache targets).card/(2 : ENNReal)^128 := by
      rw [expectedValue_add,expectedValue_const (by simp),expectedValue_ite_one,
        probEvent_uniformSample,targetWeight_average]
      simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat,cachedTargetNonces]
    _ ≤ _ := add_le_add le_rfl (ENNReal.div_le_div_right
      (cachedTargetNonces_card_le_count message fuel cache targets) _)
noncomputable def completeLabel (observed : Option HashOutput) : ProbComp IndexBuckets :=
  observed.elim ($ᵗ IndexBuckets) (fun output => pure (samplingData output).1)
private theorem expectedValue_option {Value Label : Type} (observed : Option Value)
    (fallback : ProbComp Label) (next : Value → ProbComp Label) (payoff : Label → ENNReal) :
    expectedValue (observed.elim fallback next) payoff=
      observed.elim (expectedValue fallback payoff) (fun value => expectedValue (next value) payoff) := by
  cases observed <;> rfl
theorem completeLabel_expected (observed : Option HashOutput) (payoff : IndexBuckets → ENNReal) :
    expectedValue (completeLabel observed) payoff=
      observed.elim (finiteAverage payoff) (fun output => payoff (samplingData output).1) := by
  rw [completeLabel,expectedValue_option,expected_uniform_eq_finiteAverage]
  simp only [expectedValue_pure]
noncomputable def completeRecord {Record : Type} (observed : Record → Option HashOutput)
    (program : ProbComp Record) : ProbComp (Record × IndexBuckets) := do
  let record ← program
  let label ← completeLabel (observed record)
  pure (record,label)
theorem completeRecord_erasure {Record : Type} (observed : Record → Option HashOutput)
    (program : ProbComp Record) :
    𝒮[Prod.fst <$> completeRecord observed program]=𝒮[program] := by
  unfold completeRecord
  simp only [map_bind,map_pure]
  trans 𝒮[program >>= fun record => pure record]
  · apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
    intro record
    exact OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _ (by simp) _
  · simp
theorem completeRecord_expected {Record : Type} (observed : Record → Option HashOutput)
    (program : ProbComp Record) (payoff : IndexBuckets → ENNReal) :
    expectedValue (completeRecord observed program) (fun result => payoff result.2)=
      expectedValue program (fun record =>
        (observed record).elim (finiteAverage payoff) (fun output => payoff (samplingData output).1)) := by
  rw [completeRecord,expectedValue_bind]
  apply congrArg
  funext record
  rw [expectedValue_bind]
  simp only [expectedValue_pure]
  exact completeLabel_expected _ payoff
theorem clean_point_bound_arithmetic (cache : RCache) (hfinite : Finite cache)
    (budget : Nat) (hsize : QueryCache.enncard cache ≤ budget) (hbudget : budget ≤ 2^127)
    (hclean : ¬TargetCacheExceptional cache) (haccept : acceptanceProbability ≤ 1/16)
    (point : IndexBuckets) :
    1/(2 : ENNReal)^59+cachedTargetCount {point} cache/(2 : ENNReal)^128 ≤
      (1025/1024 : ENNReal)/(2 : ENNReal)^59 := by
  rw [cachedTargetCount_singleton_native]
  exact SigGolfResearch.Gate6.NativeCache.clean_point_bound_arithmetic cache hfinite budget hsize hbudget
    (fun h => hclean ((targetCacheExceptional_iff_native cache).mpr h)) point
end SigGolfCandidate.T3.Sampling
#print axioms SigGolfCandidate.T3.Sampling.targetCacheExceptional_iff_native
#print axioms SigGolfCandidate.T3.Sampling.clean_point_bound_arithmetic
end
