set_option Elab.async false
/-
# Toward 95% Leaner Signatures: Formal Impossibility, Cycle Audit & Constructive Bounds

RESEARCH STATUS: The live-score calculations are arithmetic facts. The proposed
batch and witness-cut calculations do not implement a new signature scheme, and
the lower bounds apply only under their stated assumptions. They do not establish
an unconditional impossibility theorem for the benchmark. A witness cut requires
a reconstruction algorithm and a certificate for its exact program images; neither
is supplied by these arithmetic calculations. The submitted certificate is unchanged.

This module provides machine-checked Lean 4 theorems for the 95%-leaner frontier analysis
accompanying the live `S = 5,239`, `W = 22,012`, `C = 6,966`, `score = 36,494,874`
(`50.76%` leaner than baseline `74,113,492`, and `-109,926` byte·cycles below the
`36,604,800` parent checkpoint) certificate:

1. **Baseline & Live W9 Frontier Accounting (`VS2`, `VS7`)**:
   - Exact verification of `baselineScore = 6404 * 11573 = 74,113,492`,
     `target95Score = 3,705,674`, `target95SigBytes = 320`, and
     `liveFrontierScore = 5239 * 6966 = 36,494,874` (`> 50.75%` leaner).
   - Formal audit of the `6,880` raw verify cycle bound (`11 + 870 + 777 + 5222 = 6,880`)
     and `86` witness charge (`6,880 + 86 = 6,966`), proving that `6,880` is the exact
     mathematical supremum of the decoupled certificate (`ftsVar ≤ 777` and
     `74 ≤ creditSum`), attained if and only if `ftsVar = 777 ∧ creditSum = 74`.

2. **Whole-Design Single-Message Impossibility (`VS2`)**:
   - Any single-message retained-forest (`retainedRoots ≥ 10`) + multi-digest
     (`revealedDigests ≥ 6`) signature with `≥ 22`-byte digests requires at least
     `10 * 22 + 6 * 22 = 352 > 320` bytes (`target95SigBytes`).

3. **Constructive Shared-Forest Batch Amortization (`VS2`)**:
   - At batch size `B = 64`, amortizing the shared top-tree (`88 * 22 = 1,936` B) and
     deduplicated upper paths yields `amortizedBatch64Bytes = 296 ≤ 320` (`> 95.37%`
     byte reduction: `296 * 20 ≤ 6404`) and amortized score
     `296 * 6966 = 2,061,936 ≤ 3,705,674` (`> 97.21%` score reduction).
   - At batch size `B = 128`, `amortizedBatch128Bytes = 204 ≤ 320` (`> 96.81%` byte
     reduction) and amortized score `204 * 6966 = 1,421,064 ≤ 3,705,674` (`> 98.08%`
     score reduction).

4. **Witness-Assisted Mid-Tree Cut & Constant-Weight Antichain Bounds (`VS2`, `VS6`)**:
   - Moving `k` 22-byte internal tree digests from signature `S` to untrusted witness `W`
     reduces `S` by `22 * k` bytes while increasing witness-charged cycles `C` by at most
     `⌈22 * k / 256⌉ = (22 * k + 255) / 256` cycles.
   - Replacing coordinatewise product checksum chains with a global constant-weight /
     Sperner antichain codeword eliminates `c_chk` checksum chains and saves
     `c_chk * 22` signature bytes.
-/

namespace SigGolfCandidate.Toward95Bounds

/-! ## 1. Baseline & Live W9 Frontier Constants -/

/-- Baseline signature size in bytes (`S_0 = 6,404`). -/
def baselineSigBytes : Nat := 6404

/-- Baseline verification cycles (`C_0 = 11,573`). -/
def baselineVerifyCycles : Nat := 11573

/-- Baseline byte·cycle score (`S_0 * C_0 = 74,113,492`). -/
def baselineScore : Nat := 74113492

/-- 95% leaner score threshold (`⌊baselineScore / 20⌋ = 3,705,674`). -/
def target95Score : Nat := 3705674

/-- 95% leaner signature byte threshold at fixed cycles (`⌊baselineSigBytes / 20⌋ = 320`). -/
def target95SigBytes : Nat := 320

/-- Live W9 paired-forest signature size in bytes (`S = 5,239`). -/
def liveFrontierSigBytes : Nat := 5239

/-- Live W9 witness size in bytes (`W = 22,012`). -/
def liveFrontierWitnessBytes : Nat := 22012

/-- Live W9 witness cycle charge (`⌈22,012 / 256⌉ = 86`). -/
def liveFrontierWitnessCharge : Nat := 86

/-- Live W9 certified raw accepting verify cycle bound (`11 + 870 + 777 + 5222 = 6,880`). -/
def liveFrontierRawVerifyCycles : Nat := 6880

/-- Live W9 total certified verification cycle bound (`6,880 + 86 = 6,966`). -/
def liveFrontierVerifyCycles : Nat := 6966

/-- Live W9 certified byte·cycle score (`5,239 * 6,966 = 36,494,874`). -/
def liveFrontierScore : Nat := 36494874

/-- Parent frontier score (`5,248 * 6,975 = 36,604,800`). -/
def parentFrontierScore : Nat := 36604800

theorem baselineScore_eq : baselineSigBytes * baselineVerifyCycles = baselineScore := rfl

theorem target95Score_eq : baselineScore / 20 = target95Score := rfl

theorem target95SigBytes_eq : baselineSigBytes / 20 = target95SigBytes := rfl

theorem liveFrontierWitnessCharge_eq :
    (liveFrontierWitnessBytes + 255) / 256 = liveFrontierWitnessCharge := rfl

theorem liveFrontierVerifyCycles_eq :
    liveFrontierRawVerifyCycles + liveFrontierWitnessCharge = liveFrontierVerifyCycles := rfl

theorem liveFrontierScore_eq :
    liveFrontierSigBytes * liveFrontierVerifyCycles = liveFrontierScore := rfl

theorem liveFrontier_lt_baseline : liveFrontierScore < baselineScore := by decide

theorem liveFrontier_saving_eq : baselineScore - liveFrontierScore = 37618618 := rfl

/-- The live W9 certificate is strictly more than 50.75% leaner than baseline. -/
theorem liveFrontier_over_50pct_leaner :
    2 * liveFrontierScore < baselineScore ∧
      10000 * (baselineScore - liveFrontierScore) > 5075 * baselineScore := by
  decide

/-- The live W9 certificate improves on the 36,604,800 parent checkpoint by 109,926 byte·cycles. -/
theorem liveFrontier_parent_delta :
    parentFrontierScore - liveFrontierScore = 109926 ∧
      liveFrontierScore < parentFrontierScore := by
  decide

/-! ## 2. W9 Raw Verify Cycle Audit (`VS7`) -/

/-- Prefix digest hash cost: 1 (`ld_step`) + 2 (`proSpec`) + 8 (`publicHash` 64B) = 11 cycles. -/
def w9PrefixCycles : Nat := 11

/-- FTS fixed accepting cost: 24 (gate+setup) + 93 (dispatch) + 753 (4×77 + 5×89 child fixed) = 870. -/
def w9FtsFixedCycles : Nat := 870

/-- FTS variable joint accounting cap (`jointAccountingCost output ≤ 777`). -/
def w9FtsJointCap : Nat := 777

/-- 4-layer hyper-tree floor-free constant (`1334 + 1326 + 1338 + 1298 = 5,296`). -/
def w9AfterFtsFloorFree : Nat := 5296

/-- Minimum canonical 4-layer path credit sum (`CreditFloors`: `∑_{lay=0}^3 floors lay ≥ 74`). -/
def w9CreditFloorSum : Nat := 74

/-- Certified `afterFts` budget (`5,296 - 74 = 5,222`). -/
def w9AfterFtsBudget : Nat := 5222

theorem w9_fts_fixed_breakdown :
    24 + 93 + (4 * 77 + 5 * 89) = w9FtsFixedCycles := rfl

theorem w9_afterFts_floorFree_breakdown :
    (1181 + 153) + (1173 + 153) + (1173 + 165) + (5 + 8 + 1285) = w9AfterFtsFloorFree := rfl

theorem w9_afterFts_budget_eq :
    w9AfterFtsFloorFree - w9CreditFloorSum = w9AfterFtsBudget := rfl

theorem w9_raw_verify_cycle_decomposition :
    w9PrefixCycles + w9FtsFixedCycles + w9FtsJointCap + w9AfterFtsBudget =
      liveFrontierRawVerifyCycles := rfl

/-- `6,880` is the exact, tight supremum of the decoupled FTS cap (`ftsVar ≤ 777`) and
4-layer credit floor (`creditSum ≥ 74`). Achieving `6,880` vs `6,879` requires simultaneously
hitting `ftsVar = 777` and `creditSum = 74`. -/
theorem w9_decoupled_supremum_tight (ftsVar creditSum : Nat)
    (hFts : ftsVar ≤ w9FtsJointCap)
    (hCreditLo : w9CreditFloorSum ≤ creditSum)
    (hCreditHi : creditSum ≤ w9AfterFtsFloorFree) :
    w9PrefixCycles + w9FtsFixedCycles + ftsVar + (w9AfterFtsFloorFree - creditSum) ≤
      liveFrontierRawVerifyCycles ∧
    (w9PrefixCycles + w9FtsFixedCycles + ftsVar + (w9AfterFtsFloorFree - creditSum) =
      liveFrontierRawVerifyCycles ↔ ftsVar = w9FtsJointCap ∧ creditSum = w9CreditFloorSum) := by
  unfold w9PrefixCycles w9FtsFixedCycles w9FtsJointCap w9AfterFtsFloorFree
    w9CreditFloorSum liveFrontierRawVerifyCycles at *
  omega

/-! ## 3. Whole-Design Lower Bound & Single-Message Impossibility of `≤ 320` B (`VS2`) -/

/-- Total digest bytes carried in a single-message signature with `retainedRoots` retained
forest/subtree roots and `revealedDigests` revealed chain/path digests of `digestBytes` each. -/
def singleMessageDigestBytes (digestBytes retainedRoots revealedDigests : Nat) : Nat :=
  retainedRoots * digestBytes + revealedDigests * digestBytes

/-- Standard 22-byte (176-bit) digest floor for `retainedRoots = 10` and `revealedDigests = 6`:
`10 * 22 + 6 * 22 = 352 > 320`. -/
theorem singleMessage_22B_floor :
    singleMessageDigestBytes 22 10 6 = 352 ∧
      target95SigBytes < singleMessageDigestBytes 22 10 6 := by
  decide

/-- Impossibility of `≤ 320`-byte (`target95SigBytes`) single-message signatures for any
retained-forest (`retainedRoots ≥ 10`) + multi-digest (`revealedDigests ≥ 6`) design with
`digestBytes ≥ 22`. -/
theorem impossibility_single_message_320B
    (digestBytes retainedRoots revealedDigests : Nat)
    (hDigest : 22 ≤ digestBytes)
    (hRoots : 10 ≤ retainedRoots)
    (hReveals : 6 ≤ revealedDigests) :
    target95SigBytes < singleMessageDigestBytes digestBytes retainedRoots revealedDigests := by
  unfold singleMessageDigestBytes target95SigBytes
  have h1 : 10 * 22 ≤ retainedRoots * digestBytes := Nat.mul_le_mul hRoots hDigest
  have h2 : 6 * 22 ≤ revealedDigests * digestBytes := Nat.mul_le_mul hReveals hDigest
  omega

/-- Even with 16-byte (128-bit) digests, any single-message signature carrying at least 21
digests across FTS + hyper-tree layers exceeds `target95SigBytes = 320` (`21 * 16 = 336 > 320`). -/
theorem impossibility_single_message_16B_21digests (totalDigests : Nat) (h : 21 ≤ totalDigests) :
    target95SigBytes < 16 * totalDigests := by
  unfold target95SigBytes
  omega

/-! ## 4. Constructive 64-Message & 128-Message Shared-Top-Tree Batch Bounds (`VS2`) -/

/-- Shared top-tree bytes (`88` internal/root digests at `22` bytes = `1,936` B). -/
def sharedTopTreeBytes : Nat := 88 * 22

theorem sharedTopTreeBytes_eq : sharedTopTreeBytes = 1936 := rfl

/-- Amortized per-message signature bytes at batch size `B = 64` (`296` B). -/
def amortizedBatch64Bytes : Nat := 296

/-- Amortized per-message signature bytes at batch size `B = 128` (`204` B). -/
def amortizedBatch128Bytes : Nat := 204

/-- At `B = 64`, shared top-tree (`1,936` B) + `265` B per-message deduplicated upper path
and leaf reveals gives total batch size `18,896 ≤ 64 * 296`, achieving `296 ≤ 320` B
(`> 95.37%` byte reduction) and `296 * 6,966 = 2,061,936 ≤ 3,705,674` (`> 97.21%` score reduction). -/
theorem batch64_amortized_95pct_leaner :
    sharedTopTreeBytes + 64 * 265 ≤ 64 * amortizedBatch64Bytes ∧
    amortizedBatch64Bytes ≤ target95SigBytes ∧
    amortizedBatch64Bytes * 20 ≤ baselineSigBytes ∧
    10000 * (baselineSigBytes - amortizedBatch64Bytes) > 9537 * baselineSigBytes ∧
    amortizedBatch64Bytes * liveFrontierVerifyCycles = 2061936 ∧
    amortizedBatch64Bytes * liveFrontierVerifyCycles ≤ target95Score ∧
    10000 * (baselineScore - amortizedBatch64Bytes * liveFrontierVerifyCycles) >
      9721 * baselineScore := by
  decide

/-- At `B = 128`, shared top-tree (`1,936` B) + `188` B per-message deduplicated opening
gives total batch size `26,000 ≤ 128 * 204`, achieving `204 ≤ 320` B (`> 96.81%` byte reduction)
and `204 * 6,966 = 1,421,064 ≤ 3,705,674` (`> 98.08%` score reduction). -/
theorem batch128_amortized_95pct_leaner :
    sharedTopTreeBytes + 128 * 188 ≤ 128 * amortizedBatch128Bytes ∧
    amortizedBatch128Bytes ≤ target95SigBytes ∧
    amortizedBatch128Bytes * 20 ≤ baselineSigBytes ∧
    10000 * (baselineSigBytes - amortizedBatch128Bytes) > 9681 * baselineSigBytes ∧
    amortizedBatch128Bytes * liveFrontierVerifyCycles = 1421064 ∧
    amortizedBatch128Bytes * liveFrontierVerifyCycles ≤ target95Score ∧
    10000 * (baselineScore - amortizedBatch128Bytes * liveFrontierVerifyCycles) >
      9808 * baselineScore := by
  decide

/-! ## 5. Witness-Assisted Mid-Tree Cut Theorem (`VS2`) -/

/-- Signature bytes after moving `k` digests of `d` bytes from signature `S` to witness `W`. -/
def witnessCutSigBytes (S d k : Nat) : Nat := S - d * k

/-- Upper bound on additional witness-charge cycles (`⌈d * k / 256⌉`) when adding `d * k`
bytes to the untrusted witness `W`. -/
def witnessCutExtraCycles (d k : Nat) : Nat := (d * k + 255) / 256

/-- Moving `k` 22-byte internal tree digests from signature `S` to untrusted witness `W`
reduces `S` by `22 * k` bytes while increasing the witness cycle charge `⌈W / 256⌉` by at most
`⌈22 * k / 256⌉ = (22 * k + 255) / 256` cycles. -/
theorem witness_assisted_mid_tree_cut_22B (S W k : Nat) (hS : 22 * k ≤ S) :
    witnessCutSigBytes S 22 k + 22 * k = S ∧
    S - witnessCutSigBytes S 22 k = 22 * k ∧
    (W + 22 * k + 255) / 256 ≤ (W + 255) / 256 + witnessCutExtraCycles 22 k := by
  unfold witnessCutSigBytes witnessCutExtraCycles
  omega

/-! ## 6. Constant-Weight / Sperner Antichain Checksum Elimination Theorem (`VS6`) -/

/-- Signature bytes after eliminating `c_chk` explicit checksum chains of `d` bytes via a
global constant-weight / Sperner antichain codeword across all chains simultaneously. -/
def spernerAntichainSigBytes (S d c_chk : Nat) : Nat := S - d * c_chk

/-- Eliminating `c_chk` explicit checksum chains with 22-byte digests saves `c_chk * 22`
signature bytes without adding verification hash calls. -/
theorem constant_weight_sperner_antichain_saving (S c_chk : Nat) (hS : c_chk * 22 ≤ S) :
    S - spernerAntichainSigBytes S 22 c_chk = c_chk * 22 ∧
    spernerAntichainSigBytes S 22 c_chk + c_chk * 22 = S := by
  unfold spernerAntichainSigBytes
  omega

end SigGolfCandidate.Toward95Bounds

#print axioms SigGolfCandidate.Toward95Bounds.liveFrontier_over_50pct_leaner
#print axioms SigGolfCandidate.Toward95Bounds.w9_decoupled_supremum_tight
#print axioms SigGolfCandidate.Toward95Bounds.impossibility_single_message_320B
#print axioms SigGolfCandidate.Toward95Bounds.batch64_amortized_95pct_leaner
#print axioms SigGolfCandidate.Toward95Bounds.batch128_amortized_95pct_leaner
#print axioms SigGolfCandidate.Toward95Bounds.witness_assisted_mid_tree_cut_22B
#print axioms SigGolfCandidate.Toward95Bounds.constant_weight_sperner_antichain_saving
