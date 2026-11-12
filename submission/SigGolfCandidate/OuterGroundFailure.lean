import SigGolfCandidate.OuterGroundCore
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option backward.isDefEq.respectTransparency false
namespace OuterGroundFailure
open OracleComp OracleSpec OracleComp.EvalDist ENNReal OuterGroundCore
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open ClaudeWCT.W9.T3.TopMoment (Ev Ev_pure Ev_publicQuery_fresh)
theorem Ev_search_fuel {β : Type} (secret : BitVec 256) (coord index heap : Nat) (left right : Digest)
    (next : Nat × Digest → M β) (F : β × RCache → ℝ≥0∞) (G : RCache → Prop) (w : Digest → ℝ≥0∞) (b : Nat → ℝ≥0∞)
    (hG : ∀ cache, G cache → ∀ k answer, G (cache.cacheQuery (trial coord index heap k left right) answer))
    (hnext : ∀ cache, G cache → ∀ k answer,
      Ev secret (next (k, value coord heap answer)) (cache.cacheQuery (trial coord index heap k left right) answer) F ≤
        w (value coord heap answer))
    (hstep : ∀ k, expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => if zeroOk coord (value coord heap answer) then w (value coord heap answer) else b k) ≤ b (k + 1))
    (htail : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun answer => w (value coord heap answer)) ≤ b 0) :
    ∀ fuel n, n + fuel < 2 ^ 64 → ∀ cache, G cache →
      (∀ k, n ≤ k → k ≤ n + fuel → cache (trial coord index heap k left right) = none) →
      Ev secret (search coord index heap left right fuel n >>= next) cache F ≤ b fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro n hn cache hg hfresh
      rw [search_zero_bind, Ev_publicQuery_fresh _ _ _ (hfresh n le_rfl (by omega))]
      exact (expectedValue_mono _ fun answer => hnext cache hg n answer).trans htail
  | succ fuel ih =>
      intro n hn cache hg hfresh
      rw [search_succ_bind, Ev_publicQuery_fresh _ _ _ (hfresh n le_rfl (by omega))]
      refine le_trans (expectedValue_mono _ fun answer => ?_) (hstep fuel)
      split
      · exact hnext cache hg n answer
      · apply ih (n + 1) (by omega) _ (hG cache hg n answer)
        intro k hk1 hk2
        have hne : trial coord index heap k left right ≠ trial coord index heap n left right := by
          intro he
          have := trial_injective coord index heap left right (by omega) (by omega) he
          omega
        exact (QueryCache.cacheQuery_of_ne (cache := cache) answer hne).trans (hfresh k (by omega) (by omega))


theorem Ev_search_failure (secret : BitVec 256) (coord index heap : Nat) (l r : Digest)
    (fuel n : Nat) (hn : n+fuel<2^64) (cache : RCache)
    (hfresh : ∀ k,n≤k→k≤n+fuel→cache (trial coord index heap k l r)=none) :
    Ev secret (search coord index heap l r fuel n) cache
      (fun out => if zeroOk coord out.1.2 then 0 else 1)≤
        (1-((2:ENNReal)^width coord)⁻¹)^(fuel+1) := by
  have h:=Ev_search_fuel secret coord index heap l r pure
    (fun out => if zeroOk coord out.1.2 then 0 else 1) (fun _ => True)
    (fun v => if zeroOk coord v then 0 else 1)
    (fun k => (1-((2:ENNReal)^width coord)⁻¹)^(k+1))
    (by intros;trivial) (by intros;simp [Ev_pure]) ?_ ?_ fuel n hn cache trivial hfresh
  · simpa using h
  · intro k
    have he : (fun a : HashOutput => if zeroOk coord (value coord heap a) then
        (if zeroOk coord (value coord heap a) then (0:ENNReal) else 1) else
        (1-((2:ENNReal)^width coord)⁻¹)^(k+1))=
        (fun a => if zeroOk coord (value coord heap a) then 0 else
          (1-((2:ENNReal)^width coord)⁻¹)^(k+1)) := by
      funext a;split <;> simp_all
    rw [he,ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.expectedValue_uniform_ite_F
      (fun a => zeroOk coord (value coord heap a)=true),prob_accept]
    simp [pow_succ']
  · rw [ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.expectedValue_uniform_ite_F
      (fun a => zeroOk coord (value coord heap a)=true),prob_accept]
    simp

theorem cap_bound (coord : Nat) :
    (1-((2:ENNReal)^width coord)⁻¹)^cap coord≤((2:ENNReal)^210)⁻¹ := by
  have key : (1-((2:ENNReal)^width coord)⁻¹)^cap coord=
      ENNReal.ofReal ((1-1/2^width coord:ℝ)^cap coord) := by
    have hx : (0:ℝ)≤1/2^width coord := by positivity
    have hx1 : 1/2^width coord≤(1:ℝ) := by
      rw [div_le_one (by positivity)];exact one_le_pow₀ (by norm_num)
    rw [ENNReal.ofReal_pow (show (0:ℝ)≤1-1/2^width coord by linarith),ENNReal.ofReal_sub _ hx,
      ENNReal.ofReal_one,ENNReal.ofReal_div_of_pos (show (0:ℝ)<2^width coord by positivity),ENNReal.ofReal_one,
      ENNReal.ofReal_pow (show (0:ℝ)≤2 by norm_num),ENNReal.ofReal_ofNat,one_div]
  have hi : ((2:ENNReal)^210)⁻¹=ENNReal.ofReal (1/(2:ℝ)^210) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_one,ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat,one_div]
  rw [key,hi]
  apply ENNReal.ofReal_le_ofReal
  unfold cap OuterGroundCore.width
  split_ifs <;> norm_num

theorem Ev_node_failure (secret : BitVec 256) (coord index heap : Nat) (l r : Digest) (cache : RCache)
    (hfresh : ∀ k,cache (trial coord index heap k l r)=none) :
    Ev secret (nodeAt coord index heap l r) cache (fun out => if zeroOk coord out.1.2 then 0 else 1)≤
      ((2:ENNReal)^210)⁻¹ := by
  have hc : 0<cap coord := by unfold cap;positivity
  have hn : cap coord-1<2^64 := by
    have hw:=width_bounds coord
    have hp : 2^width coord≤2^4 := Nat.pow_le_pow_right (by decide) hw.2
    unfold cap;omega
  have h:=Ev_search_failure secret coord index heap l r (cap coord-1) 0 (by simpa using hn) cache
    (fun k _ _ => hfresh k)
  have he : cap coord-1+1=cap coord := Nat.sub_add_cancel hc
  have hh : Ev secret (nodeAt coord index heap l r) cache
      (fun out => if zeroOk coord out.1.2 then 0 else 1)≤(1-((2:ENNReal)^width coord)⁻¹)^cap coord := by
    simpa only [nodeAt,he] using h
  exact hh.trans (cap_bound coord)

#print axioms cap_bound
#print axioms Ev_node_failure
#print axioms Ev_search_failure
#print axioms Ev_search_fuel
end OuterGroundFailure
