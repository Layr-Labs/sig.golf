import SigGolfCandidate.T3.FullCache.NativeBudget
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.EnvelopesV5

namespace ClaudeWCT.W9.T3.Budgets.V5
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass)
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3.Budgets (failMass_eq_one_sub_accept rejection_power_le ofReal_inv_two_pow)
open ClaudeWCT.W9.T3.BaseAudit
theorem failure_power_of_rate {β : Type} (decoder : HashOutput → Option β) (p : ℚ) (L bits : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hacc : ENNReal.ofReal (p : ℝ) ≤ Pr[fun answer => (decoder answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)])
    (hrate : (bits : ℚ) * 0.6931471808 ≤ L * p) :
    failMass decoder ^ L ≤ 1 / (2 : ENNReal) ^ bits := by
  have hp0' : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp0
  have hp1' : (p : ℝ) ≤ 1 := by exact_mod_cast hp1
  have hm : failMass decoder ≤ ENNReal.ofReal (1 - (p : ℝ)) := by
    rw [failMass_eq_one_sub_accept, ENNReal.ofReal_sub 1 hp0', ENNReal.ofReal_one]
    exact tsub_le_tsub_left hacc 1
  refine (pow_le_pow_left₀ zero_le hm L).trans ?_
  rw [← ENNReal.ofReal_pow (by linarith)]
  have hreal := rejection_power_le (p : ℝ) hp1' L bits (by
    have hl := Real.log_two_lt_d9
    have hr := (Rat.cast_le (K := ℝ)).mpr hrate
    push_cast at hr
    have hb : (0 : ℝ) ≤ bits := Nat.cast_nonneg _
    nlinarith)
  have hcast := ENNReal.ofReal_le_ofReal hreal
  simpa only [ofReal_inv_two_pow] using hcast
theorem ofReal_count_div (n : ℕ) :
    ENNReal.ofReal (((n : ℚ) / 2 ^ 128 : ℚ) : ℝ) = (n : ENNReal) / 2 ^ 128 := by
  push_cast
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]
theorem top_failure_power {β : Type} (decoder : HashOutput → Option β)
    (hacc : Pr[fun answer => (decoder answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (V5.topCount129 : ENNReal) / 2 ^ 128) :
    failMass decoder ^ (2 ^ 22) ≤ 1 / (2 : ENNReal) ^ 1000 :=
  failure_power_of_rate decoder V5.p1 (2 ^ 22) 1000 (by norm_num [V5.p1, V5.topCount129])
    (by norm_num [V5.p1, V5.topCount129])
    (by rw [hacc, V5.p1, ofReal_count_div])
    (by exact_mod_cast V5.rate_top_1000)
theorem lower197_failure_power {β : Type} (decoder : HashOutput → Option β)
    (hacc : Pr[fun answer => (decoder answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (V5.lowerCount198 : ENNReal) / 2 ^ 128) :
    failMass decoder ^ (2 ^ 21) ≤ 1 / (2 : ENNReal) ^ 1000 :=
  failure_power_of_rate decoder V5.p2 (2 ^ 21) 1000 (by norm_num [V5.p2, V5.lowerCount198])
    (by norm_num [V5.p2, V5.lowerCount198])
    (by rw [hacc, V5.p2, ofReal_count_div])
    (by exact_mod_cast V5.rate_lower197_1000)
theorem lower198_failure_power {β : Type} (decoder : HashOutput → Option β)
    (hacc : Pr[fun answer => (decoder answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (V5.lowerCount198 : ENNReal) / 2 ^ 128) :
    failMass decoder ^ (2 ^ 21) ≤ 1 / (2 : ENNReal) ^ 1000 :=
  failure_power_of_rate decoder V5.p4 (2 ^ 21) 1000 (by norm_num [V5.p4, V5.lowerCount198])
    (by norm_num [V5.p4, V5.lowerCount198])
    (by rw [hacc, V5.p4, ofReal_count_div])
    (by exact_mod_cast V5.rate_lower198_1000)
theorem digest_failure_power_1300_of {β : Type} (decoder : HashOutput → Option β)
    (hacc : Pr[fun answer => (decoder answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ENNReal.ofReal (V5.p0 : ℝ)) :
    failMass decoder ^ (2 ^ 21) ≤ 1 / (2 : ENNReal) ^ 1300 :=
  failure_power_of_rate decoder V5.p0 (2 ^ 21) 1300 V5.p0_nonneg V5.p0_le_one hacc.ge
    (by exact_mod_cast V5.rate_digest_1300)
theorem digest_failure_power_450_of {β : Type} (decoder : HashOutput → Option β)
    (hacc : Pr[fun answer => (decoder answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ENNReal.ofReal (V5.p0 : ℝ)) :
    failMass decoder ^ (2 ^ 21) ≤ 1 / (2 : ENNReal) ^ 450 := by
  refine (digest_failure_power_1300_of decoder hacc).trans ?_
  gcongr
  · norm_num
  · norm_num
end ClaudeWCT.W9.T3.Budgets.V5
