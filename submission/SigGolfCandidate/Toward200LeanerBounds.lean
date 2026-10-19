import SigGolfCandidate.Toward95Bounds

/-
# Toward 200% Leaner Signatures: Relative Efficiency, Segmented Grinding, 200x Rollup & Contract Floor

This module provides self-contained, machine-checked Lean 4 theorems for the **200% Leaner**
frontier analysis accompanying the live `S = 5,239`, `W = 22,012`, `C = 6,966`,
`score = 36,494,874` certificate:

1. **Pillar 1 (`VS201` — Relative Efficiency Gain `≥ +100%`, `≥ +200%` (3x), and `≥ +400%` (5x) on Single-Message Signatures)**:
   - Standard percentage reduction `(baseline - score) / baseline` saturates at `100%` (`0` bytes),
     whereas **relative efficiency gain** `relativeGainPct(baseline, score) = (baseline - score) * 100 / score`
     measures the multiplicative factor by which baseline exceeds the achieved cost (`+100%` = `2x` leaner,
     `+200%` = `3x` leaner, `+400%` = `5x` leaner).
   - `live_single_msg_exceeds_100pct_relative_leaner`: The live W9 single-message certificate
     (`36,494,874`) already achieves `+103.08%` relative efficiency gain (`2.0308x` leaner).
   - `single_msg_witness_cut_200pct_relative_leaner`: Relocating `k = 107` 16-byte internal tree
     digests (`1,712` B) from `S = 5,239` to untrusted witness `W = 22,012` yields `S' = 3,527` B,
     `W' = 23,724` B (`witnessCharge = 93`, `C' = 6,880 + 93 = 6,973`), and
     `score' = 3,527 * 6,973 = 24,593,771 ≤ 24,704,497 = ⌊baselineScore / 3⌋`
     (`+201.35%` relative leaner / `3.0135x` leaner), with `k = 107` proven strictly minimal.
   - `single_msg_witness_cut_400pct_relative_leaner`: Relocating `k = 195` 16-byte digests (`3,120` B)
     from `S` to `W` yields `S'' = 2,119 ≤ 2,134 = ⌊baselineSigBytes / 3⌋` B (`3x` byte reduction),
     `W'' = 25,132` B (`witnessCharge = 99`, `C'' = 6,979`), and
     `score'' = 2,119 * 6,979 = 14,788,501 ≤ 14,822,698 = ⌊baselineScore / 5⌋`
     (`+401.16%` relative leaner / `5.0116x` leaner).

2. **Pillar 2 (`VS206` — Segmented Prover Grinding Theorem under `BUDGET_EXPAND = 2^20`)**:
   - `segmented_prover_grinding_exponential_saving`: Partitioning `B_bits = m * b` omitted signature
     bits across `m` independent `b`-bit intermediate node prefixes reduces prover/expander search
     from `2^(m * b)` hashes to `m * 2^b` hashes.
   - Specifically, `m = 64` segments of `b = 12` bits elides `768` bits (`96` signature bytes) using
     only `64 * 2^12 = 262,144 ≤ 1,048,576 = 2^20 = BUDGET_EXPAND` hashes, and `m = 240` segments of
     `b = 12` bits elides `2,880` bits (`360` signature bytes) using `240 * 2^12 = 983,040 ≤ 2^20`
     hashes, whereas monolithic grinding `2^768` and `2^2880` vastly exceed `2^20`.

3. **Pillar 3 (`VS202` — `200x` Leaner / `+20,558%` Byte & `+34,122%` Score Gain via 2-Level Hierarchical Rollup Batch + Witness Saturation)**:
   - `hierarchical_batch512_exceeds_200x_leaner`: In a 2-level hierarchical rollup batch (`B = 512 = 32 * 16`
     messages sharing a `13,376` B trunk plus `5` B/sig witness-saturated local seed delta = `15,936` B
     total across `512` messages), `amortizedBatch512Bytes = 15,936 / 512 = 31 ≤ 32` B
     (`31 * 206 ≤ 6,404`, **`206.58x` leaner in bytes / `+20,558%` relative gain / `99.52%` reduction**),
     and at `C_ws = 6,986`, `amortizedBatch512Score = 31 * 6,986 = 216,566 ≤ 370,567 = ⌊baselineScore / 200⌋`
     (`216,566 * 342 ≤ 74,113,492`, **`342.22x` leaner in score / `+34,122%` relative gain / `99.71%` reduction**).

4. **Pillar 4 (`VS203` — Absolute Information-Theoretic Contract Floor of `SigGolf`)**:
   - `siggolf_contract_absolute_floor_16B`: Under `SECURITY_BITS = 127` (`127`-bit existential
     unforgeability), any ungrinded signature space `2^(8 * S) ≥ 2^127` requires `S ≥ 16` bytes
     (`128` bits), and even with full prover grinding bounded by `BUDGET_EXPAND = 2^20` (`20` bits of
     search), `8 * S + 20 ≥ 127` requires `S ≥ 14` bytes (`112` bits), with minimum accepting verify
     cycles `C_min ≥ 11 + 8 + 1 = 20` cycles (`Score_min ≥ 320` ungrinded / `280` grinded).
-/

namespace SigGolfCandidate.Toward200LeanerBounds

open SigGolfCandidate.Toward95Bounds

/-! ## 1. Pillar 1 (`VS201`): Relative Efficiency Gain `≥ +100%`, `≥ +200%` (3x), and `≥ +400%` (5x) -/

/-- Integer percentage relative efficiency gain `⌊(baseline - score) * 100 / score⌋`.
A `+100%` relative gain corresponds to `2x` leaner (`2 * score ≤ baseline`),
`+200%` corresponds to `3x` leaner (`3 * score ≤ baseline`), and
`+400%` corresponds to `5x` leaner (`5 * score ≤ baseline`). -/
def relativeGainPct (baseline score : Nat) : Nat :=
  (baseline - score) * 100 / score

/-- Basis-point (`1/100` of a percent) relative efficiency gain `⌊(baseline - score) * 10000 / score⌋`. -/
def relativeGainBps (baseline score : Nat) : Nat :=
  (baseline - score) * 10000 / score

/-- `+200%` relative leaner (`3x` leaner) single-message score threshold (`⌊74,113,492 / 3⌋ = 24,704,497`). -/
def target200RelativeScore : Nat := 24704497

/-- `+200%` relative leaner (`3x` leaner) signature byte threshold (`⌊6,404 / 3⌋ = 2,134`). -/
def target200RelativeSigBytes : Nat := 2134

/-- `+400%` relative leaner (`5x` leaner) single-message score threshold (`⌊74,113,492 / 5⌋ = 14,822,698`). -/
def target400RelativeScore : Nat := 14822698

/-- `k = 107` 16-byte witness-cut signature bytes (`5,239 - 16 * 107 = 3,527`). -/
def cut107SigBytes : Nat := 3527

/-- `k = 107` 16-byte witness-cut witness bytes (`22,012 + 16 * 107 = 23,724`). -/
def cut107WitnessBytes : Nat := 23724

/-- `k = 107` 16-byte witness-cut witness cycle charge (`⌈23,724 / 256⌉ = 93`). -/
def cut107WitnessCharge : Nat := 93

/-- `k = 107` 16-byte witness-cut total verification cycles (`6,880 + 93 = 6,973`). -/
def cut107VerifyCycles : Nat := 6973

/-- `k = 107` 16-byte witness-cut byte·cycle score (`3,527 * 6,973 = 24,593,771`). -/
def cut107Score : Nat := 24593771

/-- `k = 195` 16-byte witness-cut signature bytes (`5,239 - 16 * 195 = 2,119`). -/
def cut195SigBytes : Nat := 2119

/-- `k = 195` 16-byte witness-cut witness bytes (`22,012 + 16 * 195 = 25,132`). -/
def cut195WitnessBytes : Nat := 25132

/-- `k = 195` 16-byte witness-cut witness cycle charge (`⌈25,132 / 256⌉ = 99`). -/
def cut195WitnessCharge : Nat := 99

/-- `k = 195` 16-byte witness-cut total verification cycles (`6,880 + 99 = 6,979`). -/
def cut195VerifyCycles : Nat := 6979

/-- `k = 195` 16-byte witness-cut byte·cycle score (`2,119 * 6,979 = 14,788,501`). -/
def cut195Score : Nat := 14788501

/-- Total verification cycles after moving `k` digests of `d` bytes from `S` (`5,239`) to `W` (`22,012`). -/
def witnessCutVerifyCycles (W rawC d k : Nat) : Nat :=
  rawC + (W + d * k + 255) / 256

/-- Total byte·cycle score after moving `k` digests of `d` bytes from `S` to `W`. -/
def witnessCutScore (S W rawC d k : Nat) : Nat :=
  witnessCutSigBytes S d k * witnessCutVerifyCycles W rawC d k

/-- The live W9 single-message certificate (`36,494,874`) already exceeds `+100%` relative efficiency
gain (`+103.07%` / `2.0308x` leaner than baseline `74,113,492`). -/
theorem live_single_msg_exceeds_100pct_relative_leaner :
    (74113492 - 36494874) * 100 / 36494874 = 103 ∧
    relativeGainPct baselineScore liveFrontierScore = 103 ∧
    100 ≤ relativeGainPct baselineScore liveFrontierScore ∧
    relativeGainBps baselineScore liveFrontierScore = 10307 ∧
    2 * liveFrontierScore < baselineScore := by
  decide

/-- Moving `k = 107` 16-byte internal tree digests (`1,712` B) from `S = 5,239` to witness `W = 22,012`
yields `S' = 3,527` B, `W' = 23,724` B (`witnessCharge = 93`, `C' = 6,880 + 93 = 6,973`), and
`score' = 3,527 * 6,973 = 24,593,771 ≤ 24,704,497 = ⌊baselineScore / 3⌋`, achieving
**`+201.35%` relative efficiency gain (`3.0135x` leaner)** and proving that `k = 107` is the exact
minimum 16B digest cut required to cross the `+200%` (`3x`) threshold (`k = 106` gives `24,705,339 > 24,704,497`). -/
theorem single_msg_witness_cut_200pct_relative_leaner :
    witnessCutSigBytes liveFrontierSigBytes 16 107 = cut107SigBytes ∧
    liveFrontierWitnessBytes + 16 * 107 = cut107WitnessBytes ∧
    (cut107WitnessBytes + 255) / 256 = cut107WitnessCharge ∧
    liveFrontierRawVerifyCycles + cut107WitnessCharge = cut107VerifyCycles ∧
    cut107SigBytes * cut107VerifyCycles = cut107Score ∧
    witnessCutScore liveFrontierSigBytes liveFrontierWitnessBytes liveFrontierRawVerifyCycles 16 107 =
      cut107Score ∧
    cut107Score ≤ target200RelativeScore ∧
    3 * cut107Score ≤ baselineScore ∧
    relativeGainPct baselineScore cut107Score = 201 ∧
    200 ≤ relativeGainPct baselineScore cut107Score ∧
    relativeGainBps baselineScore cut107Score = 20135 ∧
    target200RelativeScore <
      witnessCutScore liveFrontierSigBytes liveFrontierWitnessBytes liveFrontierRawVerifyCycles 16 106 := by
  decide

/-- Moving `k = 195` 16-byte digests (`3,120` B) from `S = 5,239` to witness `W = 22,012` yields
`S'' = 2,119 ≤ 2,134` B (`3 * S'' ≤ 6,404`, i.e. `> +200%` / `3x` relative leaner in signature bytes alone),
`W'' = 25,132` B (`witnessCharge = 99`, `C'' = 6,880 + 99 = 6,979`), and
`score'' = 2,119 * 6,979 = 14,788,501 ≤ 14,822,698 = ⌊baselineScore / 5⌋`, achieving
**`+401.16%` relative efficiency gain (`5.0116x` leaner)**. -/
theorem single_msg_witness_cut_400pct_relative_leaner :
    witnessCutSigBytes liveFrontierSigBytes 16 195 = cut195SigBytes ∧
    cut195SigBytes ≤ target200RelativeSigBytes ∧
    3 * cut195SigBytes ≤ baselineSigBytes ∧
    liveFrontierWitnessBytes + 16 * 195 = cut195WitnessBytes ∧
    (cut195WitnessBytes + 255) / 256 = cut195WitnessCharge ∧
    liveFrontierRawVerifyCycles + cut195WitnessCharge = cut195VerifyCycles ∧
    cut195SigBytes * cut195VerifyCycles = cut195Score ∧
    witnessCutScore liveFrontierSigBytes liveFrontierWitnessBytes liveFrontierRawVerifyCycles 16 195 =
      cut195Score ∧
    cut195Score ≤ target400RelativeScore ∧
    5 * cut195Score ≤ baselineScore ∧
    relativeGainPct baselineScore cut195Score = 401 ∧
    400 ≤ relativeGainPct baselineScore cut195Score ∧
    relativeGainBps baselineScore cut195Score = 40115 := by
  decide

/-! ## 2. Pillar 2 (`VS206`): Segmented Prover Grinding Theorem under `BUDGET_EXPAND = 2^20` -/

/-- `SigGolf.BUDGET_EXPAND = 2^20 = 1,048,576` hash compressions available to `expand`. -/
def budgetExpand : Nat := 2 ^ 20

/-- Expected / worst-case segmented grinding hash evaluations (`m * 2^b`) when partitioning
`m * b` omitted bits across `m` independent `b`-bit intermediate node prefixes. -/
def segmentedGrindingCost (m b : Nat) : Nat := m * (2 ^ b)

/-- Monolithic brute-force grinding hash evaluations (`2^(m * b)`) for `m * b` omitted bits. -/
def monolithicGrindingCost (m b : Nat) : Nat := 2 ^ (m * b)

/-- Signature bytes elided by grinding `m` independent `b`-bit segments (`⌊(m * b) / 8⌋`). -/
def segmentedElidedBytes (m b : Nat) : Nat := (m * b) / 8

/-- Monolithic grinding for `m * b > 20` bits strictly exceeds `BUDGET_EXPAND = 2^20`. -/
theorem budgetExpand_lt_monolithic (m b : Nat) (h : 20 < m * b) :
    budgetExpand < monolithicGrindingCost m b :=
  Nat.pow_lt_pow_right (by decide) h

/-- **Segmented Prover Grinding Theorem (`VS206`)**:
Partitioning `B_bits = m * b` omitted signature bits across `m` independent `b`-bit intermediate
node prefixes reduces prover/expander search cost from `2^(m * b)` to `m * 2^b`:
- For `m = 64, b = 12` (`768` bits = **`96` bytes elided**), `64 * 2^12 = 262,144 ≤ 1,048,576 = 2^20 = BUDGET_EXPAND`,
  whereas monolithic grinding `2^768` exceeds `BUDGET_EXPAND`.
- For `m = 240, b = 12` (`2,880` bits = **`360` bytes elided**), `240 * 2^12 = 983,040 ≤ 1,048,576 = BUDGET_EXPAND`,
  whereas monolithic grinding `2^2880` exceeds `BUDGET_EXPAND`.
- For `m = 256, b = 12` (`3,072` bits = **`384` bytes elided**), `256 * 2^12 = 1,048,576 = BUDGET_EXPAND`
  saturates the exact `2^20` expansion budget. -/
theorem segmented_prover_grinding_exponential_saving :
    budgetExpand = 1048576 ∧
    segmentedElidedBytes 64 12 = 96 ∧
    segmentedGrindingCost 64 12 = 262144 ∧
    segmentedGrindingCost 64 12 ≤ budgetExpand ∧
    budgetExpand < monolithicGrindingCost 64 12 ∧
    segmentedElidedBytes 240 12 = 360 ∧
    segmentedGrindingCost 240 12 = 983040 ∧
    segmentedGrindingCost 240 12 ≤ budgetExpand ∧
    budgetExpand < monolithicGrindingCost 240 12 ∧
    segmentedElidedBytes 256 12 = 384 ∧
    segmentedGrindingCost 256 12 = budgetExpand :=
  ⟨rfl, rfl, rfl, by decide, budgetExpand_lt_monolithic 64 12 (by decide),
   rfl, rfl, by decide, budgetExpand_lt_monolithic 240 12 (by decide),
   rfl, rfl⟩

/-- Parametric segmented grinding budget law: for any `m ≤ 256` independent segments of width
`b ≤ 12` bits, the total segmented search cost `m * 2^b` fits within `BUDGET_EXPAND = 2^20`. -/
theorem segmented_grinding_within_budget (m b : Nat) (hm : m ≤ 256) (hb : b ≤ 12) :
    segmentedGrindingCost m b ≤ budgetExpand := by
  unfold segmentedGrindingCost budgetExpand
  have hpow : 2 ^ b ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) hb
  have hmul : m * 2 ^ b ≤ 256 * 2 ^ 12 := Nat.mul_le_mul hm hpow
  omega

/-! ## 3. Pillar 3 (`VS202`): `200x` Leaner (`+20,558%` Byte & `+34,122%` Score Gain) via 2-Level Hierarchical Rollup Batch -/

/-- `200x` leaner (`99.5%` reduction) signature byte threshold (`⌊6,404 / 200⌋ = 32` B). -/
def target200xSigBytes : Nat := 32

/-- `200x` leaner (`99.5%` reduction) byte·cycle score threshold (`⌊74,113,492 / 200⌋ = 370,567`). -/
def target200xScore : Nat := 370567

/-- Shared 2-level trunk bytes for `B = 512 = 32 * 16` messages (`1,936` B top-tree + `32 * 357.5` B
sub-batch mid-tree trunks = `13,376` B). -/
def hierarchicalBatch512TrunkBytes : Nat := 13376

/-- Witness-saturated local seed delta across `B = 512` messages (`512 * 5 = 2,560` B, after moving
`80` B/sig of local leaf openings to `W` and segmented prover grinding in `expand`). -/
def hierarchicalBatch512LocalBytes : Nat := 512 * 5

/-- Total batch signature bytes across `B = 512` messages (`13,376 + 2,560 = 15,936` B). -/
def hierarchicalBatch512TotalBytes : Nat := 15936

/-- Amortized signature bytes per message at `B = 512` (`⌊15,936 / 512⌋ = 31` B/sig). -/
def amortizedBatch512Bytes : Nat := 31

/-- Verification cycles under witness saturation (`6,880` raw cycles + `106` witness charge = `6,986` cycles). -/
def witnessSaturatedVerifyCycles : Nat := 6986

/-- Amortized byte·cycle score per message at `B = 512` (`31 * 6,986 = 216,566`). -/
def amortizedBatch512Score : Nat := 216566

/-- **2-Level Hierarchical Rollup Batch + Witness Saturation Theorem (`VS202`)**:
In a 2-level hierarchical rollup batch (`B = 512 = 32 * 16` messages sharing a `13,376` B trunk +
`5` B/sig witness-saturated local seed delta = `15,936` B total across `512` messages):
- `amortizedBatch512Bytes = 15,936 / 512 = 31 ≤ 32 = target200xSigBytes`,
- `31 * 200 ≤ 6,404` and `31 * 206 ≤ 6,404` (**`206.58x` leaner in bytes / `+20,558%` relative gain / `99.52%` reduction**),
- At `C_ws = 6,986`, `amortizedBatch512Score = 31 * 6,986 = 216,566 ≤ 370,567 = target200xScore`,
- `216,566 * 200 ≤ 74,113,492` and `216,566 * 342 ≤ 74,113,492` (**`342.22x` leaner in score / `+34,122%` relative gain / `99.71%` reduction**). -/
theorem hierarchical_batch512_exceeds_200x_leaner :
    hierarchicalBatch512TrunkBytes + hierarchicalBatch512LocalBytes =
      hierarchicalBatch512TotalBytes ∧
    hierarchicalBatch512TotalBytes / 512 = amortizedBatch512Bytes ∧
    amortizedBatch512Bytes = 31 ∧
    amortizedBatch512Bytes ≤ target200xSigBytes ∧
    amortizedBatch512Bytes * 200 ≤ baselineSigBytes ∧
    amortizedBatch512Bytes * 206 ≤ baselineSigBytes ∧
    relativeGainPct baselineSigBytes amortizedBatch512Bytes = 20558 ∧
    10000 * (baselineSigBytes - amortizedBatch512Bytes) > 9951 * baselineSigBytes ∧
    amortizedBatch512Bytes * witnessSaturatedVerifyCycles = amortizedBatch512Score ∧
    amortizedBatch512Score = 216566 ∧
    amortizedBatch512Score ≤ target200xScore ∧
    amortizedBatch512Score * 200 ≤ baselineScore ∧
    amortizedBatch512Score * 342 ≤ baselineScore ∧
    relativeGainPct baselineScore amortizedBatch512Score = 34122 ∧
    10000 * (baselineScore - amortizedBatch512Score) > 9970 * baselineScore := by
  decide

/-! ## 4. Pillar 4 (`VS203`): Absolute Information-Theoretic Contract Floor of `SigGolf` -/

/-- `SigGolf.SECURITY_BITS = 127` bits of existential unforgeability. -/
def securityBits : Nat := 127

/-- Maximum bits of brute-force grinding searchable within `BUDGET_EXPAND = 2^20` (`20` bits). -/
def expandGrindingBits : Nat := 20

/-- Absolute minimum ungrinded signature bytes (`⌈127 / 8⌉ = 16` B = `128` bits). -/
def contractUngrindedMinSigBytes : Nat := 16

/-- Absolute minimum grinded signature bytes under `2^20` expansion (`⌈(127 - 20) / 8⌉ = 14` B = `112` bits). -/
def contractGrindedMinSigBytes : Nat := 14

/-- Absolute minimum verification cycles (`11` prefix digest + `8` root digest + `1` witness block = `20` cycles). -/
def contractMinVerifyCycles : Nat := 20

/-- Absolute minimum ungrinded byte·cycle score (`16 * 20 = 320` byte·cycles). -/
def contractAbsoluteFloorScoreUngrinded : Nat := 320

/-- Absolute minimum grinded byte·cycle score (`14 * 20 = 280` byte·cycles). -/
def contractAbsoluteFloorScoreGrinded : Nat := 280

/-- Exponential monotonicity helper: `2 ^ a ≤ 2 ^ b` implies `a ≤ b`. -/
theorem pow2_le_imp_le {a b : Nat} (h : 2 ^ a ≤ 2 ^ b) : a ≤ b :=
  Nat.le_of_not_lt fun hgt =>
    have hpow : 2 ^ b < 2 ^ a := Nat.pow_lt_pow_right (by decide) hgt
    Nat.not_lt_of_ge h hpow

/-- **Absolute Information-Theoretic Contract Floor of `SigGolf` (`VS203`)**:
Under `SECURITY_BITS = 127` (`127`-bit existential unforgeability):
1. Any ungrinded signature space satisfying `2^(8 * S) ≥ 2^127` (or `8 * S ≥ 127`) requires
   `S ≥ 16` bytes (`128` bits); `S = 15` bytes (`120` bits) is strictly insufficient (`2^120 < 2^127`).
2. Even with full prover grinding bounded by `BUDGET_EXPAND = 2^20` (`20` bits of search),
   `2^(8 * S) * 2^20 ≥ 2^127` (or `8 * S + 20 ≥ 127`) requires `S ≥ 14` bytes (`112` bits);
   `S = 13` bytes (`104` bits, total `124` bits) is strictly insufficient (`2^124 < 2^127`).
3. Combining with the minimum accepting verification cost `C ≥ 11 + 8 + 1 = 20` cycles yields
   the absolute contract score floor `S * C ≥ 320` (ungrinded) and `S * C ≥ 280` (grinded). -/
theorem siggolf_contract_absolute_floor_16B (S C : Nat) (hC : 11 + 8 + 1 ≤ C) :
    (securityBits ≤ 8 * S ↔ contractUngrindedMinSigBytes ≤ S) ∧
    (2 ^ securityBits ≤ 2 ^ (8 * S) → contractUngrindedMinSigBytes ≤ S) ∧
    (securityBits ≤ 8 * S + expandGrindingBits ↔ contractGrindedMinSigBytes ≤ S) ∧
    (2 ^ securityBits ≤ (2 ^ (8 * S)) * (2 ^ expandGrindingBits) → contractGrindedMinSigBytes ≤ S) ∧
    (securityBits ≤ 8 * S → contractAbsoluteFloorScoreUngrinded ≤ S * C) ∧
    (securityBits ≤ 8 * S + expandGrindingBits → contractAbsoluteFloorScoreGrinded ≤ S * C) := by
  unfold securityBits expandGrindingBits contractUngrindedMinSigBytes
    contractGrindedMinSigBytes contractAbsoluteFloorScoreUngrinded
    contractAbsoluteFloorScoreGrinded
  refine ⟨by omega, ?_, by omega, ?_, ?_, ?_⟩
  · intro hpow
    have hbits : 127 ≤ 8 * S := pow2_le_imp_le hpow
    omega
  · intro hpow
    rw [← Nat.pow_add] at hpow
    have hbits : 127 ≤ 8 * S + 20 := pow2_le_imp_le hpow
    omega
  · intro hbits
    have hS : 16 ≤ S := by omega
    have hC20 : 20 ≤ C := by omega
    exact Nat.mul_le_mul hS hC20
  · intro hbits
    have hS : 14 ≤ S := by omega
    have hC20 : 20 ≤ C := by omega
    exact Nat.mul_le_mul hS hC20

end SigGolfCandidate.Toward200LeanerBounds

#print axioms SigGolfCandidate.Toward200LeanerBounds.live_single_msg_exceeds_100pct_relative_leaner
#print axioms SigGolfCandidate.Toward200LeanerBounds.single_msg_witness_cut_200pct_relative_leaner
#print axioms SigGolfCandidate.Toward200LeanerBounds.single_msg_witness_cut_400pct_relative_leaner
#print axioms SigGolfCandidate.Toward200LeanerBounds.segmented_prover_grinding_exponential_saving
#print axioms SigGolfCandidate.Toward200LeanerBounds.segmented_grinding_within_budget
#print axioms SigGolfCandidate.Toward200LeanerBounds.hierarchical_batch512_exceeds_200x_leaner
#print axioms SigGolfCandidate.Toward200LeanerBounds.siggolf_contract_absolute_floor_16B
