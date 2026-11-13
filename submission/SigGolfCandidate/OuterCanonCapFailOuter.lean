import SigGolfCandidate.OuterCanonCapFailCore
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonBase.Paired.CapFailBound
open ClaudeWCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
attribute [local instance low] Classical.propDecidable
attribute [local instance] OuterCanonBase.Paired.instSampleableTypeLabels_capFail
theorem outerFail_le (coord : Nat) : (1-(1/2:ℝ)^OuterGroundCore.width coord)^OuterGroundCore.cap coord≤(36788/100000:ℝ)^128 := by
  have h0 : 0≤1-(1/2:ℝ)^OuterGroundCore.width coord := by have := pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1) (n:=OuterGroundCore.width coord);linarith
  have h1 : 1-(1/2:ℝ)^OuterGroundCore.width coord≤1 := by have := pow_nonneg (by norm_num : (0:ℝ)≤1/2) (OuterGroundCore.width coord);linarith
  have hc : 128*2^OuterGroundCore.width coord≤OuterGroundCore.cap coord := by
    unfold OuterGroundCore.cap OuterGroundCore.width
    split_ifs <;> norm_num
  exact (pow_le_pow_of_le_one h0 h1 hc).trans (lowFail_le (OuterGroundCore.width coord))
theorem outer_width_le (coord heap : Nat) : OuterGroundCore.width coord ≤ 5 := by
  unfold OuterGroundCore.width; split_ifs <;> omega

theorem card_pass_digest_outer (coord heap : Nat) :
    2 ^ (128 - OuterGroundCore.width coord) ≤
      (Finset.univ.filter (fun d : BitVec 128 => OuterGroundCore.zeroOk coord d = true)).card := by
  have hb := outer_width_le coord heap
  have hlt : 2 ^ (128 - OuterGroundCore.width coord) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by decide) (by omega)
  have hc : (Finset.range (2 ^ (128 - OuterGroundCore.width coord))).card = 2 ^ (128 - OuterGroundCore.width coord) :=
    Finset.card_range _
  rw [← hc]
  apply Finset.card_le_card_of_injOn (fun x : Nat => (BitVec.ofNat 128 x : BitVec 128))
  · intro x hx
    simp only [Finset.coe_range, Set.mem_Iio] at hx
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    unfold OuterGroundCore.zeroOk
    simp only [BitVec.toNat_ofNat, beq_iff_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact Nat.div_eq_of_lt hx
  · intro x hx y hy heq
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    have := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

theorem card_fail_hash_outer (p : Extract.Pos) (coord heap : Nat) :
    (Finset.univ.filter (fun v : BitVec 256 =>
        OuterGroundCore.zeroOk coord (p.proj v) = false)).card +
      2 ^ (256 - OuterGroundCore.width coord) ≤ 2 ^ 256 := by
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (BitVec 256))) (fun v => OuterGroundCore.zeroOk coord (p.proj v) = false)
  rw [Finset.card_univ, Fintype.card_bitVec] at hsum
  have := card_pass_hash_of p (OuterGroundCore.zeroOk coord)
    (by have := outer_width_le coord heap; omega) (card_pass_digest_outer coord heap)
  change _ = 2 ^ 256 at hsum
  omega

theorem prob_outerFail_le (p : Extract.Pos) (coord heap : Nat) (S : Finset Node)
    (hS : S.card = OuterGroundCore.cap coord) :
    Pr[fun labels : Labels => ∀ a ∈ S,
        (fun v => OuterGroundCore.zeroOk coord (p.proj v) = false) (labels a) |
      ($ᵗ Labels : ProbComp Labels)] ≤ ENNReal.ofReal ((36788 / 100000 : ℝ) ^ 128) := by
  classical
  refine (le_of_eq (prob_forall_mem (α := Node) (β := HashOutput) (inst := instSampleableTypeLabels_capFail)
    S (fun v => OuterGroundCore.zeroOk coord (p.proj v) = false))).trans ?_
  rw [hS, Fintype.card_bitVec]
  have hb := outer_width_le coord heap
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal (outerFail_le coord))
  rw [ENNReal.ofReal_pow (by
    have : (1 / 2 : ℝ) ^ OuterGroundCore.width coord ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith)]
  gcongr
  have hf := card_fail_hash_outer p coord heap
  have := ratio_le hf (by omega)
  convert this using 2


#print axioms prob_outerFail_le
end OuterCanonBase.Paired.CapFailBound
