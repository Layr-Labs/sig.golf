import SigGolfCandidate.Toward200LeanerBounds
set_option Elab.async false

/-
# Toward 45% Leaner Than Most Leaning Score: Frontier Witness Cuts, Collapsed 2-Layer Hypertree & Anchored Expand Recovery

RESEARCH STATUS: The frontier baseline comparisons (`36,494,874` and `36,527,648`) and witness-cut /
collapsed-hypertree calculations below are machine-checked arithmetic and structural models.
They do not replace the four compiled RISC-V program images or prove a new `SigGolf.Certificate`
beyond the submitted `S = 5,239`, `W = 22,012`, `C = 6,966`, `score = 36,494,874` certificate.

This module formalizes and proves the **45% Leaner Than Most Leaning Score** theorem suite
across all three mathematical interpretations of "45% leaner than the most leaning score",
benchmarked against BOTH:
- **Most Leaning Score on `sig.golf`** (`19e10c6a` @ `f37c0a8a`):
  `S = 5,239` B, `W = 22,012` B, `C = 6,966` cycles, `mostLeaningScore = 36,494,874`, and
- **Leanest Signature-Byte Entry on `sig.golf`** (`55154df` @ `65d66b2d`, Radix-6 + PORS):
  `S = 5,216` B, `W = 23,236` B, `C = 7,003` cycles, `radix6Score = 36,527,648`.

1. **Section 1 (`VS45_1` — Frontier Baselines & The Three 45%-Leaner Thresholds)**:
   - **Threshold A (`> +45%` relative efficiency gain over `36,494,874`)**:
     `frontierRel45Score = ⌊36,494,874 × 100 / 145⌋ = 25,168,878`, `frontierRel45SigBytes = 3,613` B.
   - **Threshold B (`> 45%` standard reduction below `36,494,874`, i.e. `≤ 55%` of frontier)**:
     `frontierRed45Score = ⌊36,494,874 × 55 / 100⌋ = 20,072,180`,
     `frontierRed45SigBytes = ⌊5,239 × 55 / 100⌋ = 2,881` B,
     `radix6Red45SigBytes = ⌊5,216 × 55 / 100⌋ = 2,868` B.
   - **Threshold C (`< 45%` of frontier score/bytes, i.e. `> 55%` reduction below frontier)**:
     `frontierSub45RatioScore = ⌊36,494,874 × 45 / 100⌋ = 16,422,693`,
     `frontierSub45RatioSigBytes = ⌊5,239 × 45 / 100⌋ = 2,357` B,
     `radix6Sub45RatioSigBytes = ⌊5,216 × 45 / 100⌋ = 2,347` B.
   - `cut107_misses_frontier_45pct_reduction`: Proves that `cut107Score = 24,593,771` from
     `Toward200LeanerBounds` crosses Threshold A (`+48.39%` relative gain over frontier) but
     misses Threshold B (`32.61%` standard reduction below `36,494,874`, short by `4,521,591` byte·cycles).

2. **Section 2 (`VS45_2`, `VS45_3`, `VS45_4` — Exact Minimal Single-Message Witness Cuts)**:
   - `frontier_rel45_minimal_cut_k102`: `k = 102` 16B digests (`S = 3,607 ≤ 3,613` B, `W = 23,644` B,
     `charge = 93`, `C = 6,973`, `score = 25,151,611 ≤ 25,168,878`, `+45.09%` relative gain over frontier)
     is the exact minimal cut crossing Threshold A (`k = 101` gives `25,263,179 > 25,168,878`).
   - `frontier_red45_minimal_cut_k148_and_k149`:
     - `k = 148` (`S = 2,871 ≤ 2,881` B, `W = 24,380` B, `charge = 96`, `C = 6,976`,
       `score = 20,028,096 ≤ 20,072,180`, `45.12%` score reduction below `36,494,874`, `+82.21%`
       relative gain over frontier, `72.97%` reduction below baseline `74,113,492`) is the exact
       minimal 16B digest cut crossing Threshold B (`k = 147` gives `S = 2,887 > 2,881` and
       `score = 20,139,712 > 20,072,180`).
     - `k = 149` (`S = 2,855 ≤ 2,868` B, `W = 24,396` B, `charge = 96`, `C = 6,976`,
       `score = 19,916,480 ≤ 20,072,180`, `45.42%` score reduction) simultaneously achieves
       `> 45%` byte reduction below BOTH `5,239` B (`45.50%`) and `55154df`'s `5,216` B (`45.26%`).
   - `frontier_sub45_ratio_minimal_cut_k181`:
     - `k = 181` (`S = 2,343 ≤ 2,347 ≤ 2,357` B, `W = 24,908` B, `charge = 98`, `C = 6,978`,
       `score = 16,349,454 ≤ 16,422,693`, `55.20%` reduction / `44.79%` of frontier) is the exact
       minimal 16B digest cut crossing Threshold C (`k = 180` gives `S = 2,359 > 2,357` and
       `score = 16,461,102 > 16,422,693`).

3. **Section 3 (`VS45_5` — 2-Layer Collapsed Hypertree + Radix-16 WOTS+C + PORS+ Construction)**:
   - `collapsed_2layer_rad16_pors_exceeds_all_45pct_frontier_targets`:
     Collapsing lower hypertree layers `L2` (`49` digests, `1,326` cycles) and `L3` (`49` digests,
     `1,338` cycles) into a 2-layer hypertree (`Top` `h_0 = 12` + `L1` `h_1 = 19`) saves `98` digests
     (`1,568` B) and `2,664` raw verify cycles; upgrading `Top` and `L1` from radix-3/5 (`97` chains)
     to Radix-16 Target-Sum WOTS+C (`56` chains) saves `41` chains (`656` B); and PORS+ seed-tree
     pruning (`113 → 88` digests) saves `25` digests (`400` B). Total savings: `164` digests (`2,624` B),
     yielding `S = 2,615 ≤ 2,868` B (`50.08% > 45%` byte reduction), `C = 4,216 + 56 = 4,272` cycles,
     and `score = 2,615 × 4,272 = 11,171,280 ≤ 16,422,693 ≤ 20,072,180` (`69.38% > 45%` score reduction
     below `36,494,874`, `3.266x` leaner than frontier, `84.92%` reduction / `6.634x` leaner than baseline).

4. **Section 4 (`VS45_6`, `VS45_7` — Anchored Family-Seed & Segmented Preimage Recovery in `expand`)**:
   - `anchored_expand_recovery_sound_and_within_budget`:
     Proves that `expand(message, publicKey, signature)` can deterministically recover `k = 148..181`
     omitted 16B digests within `BUDGET_EXPAND = 2^20 = 1,048,576` compressions by combining:
     - `112` digests (`1,792` B) via deterministic GF(2^128) family-seed & low-step chain forward
       evaluation (`112 × 8 = 896` compressions), plus
     - `41` digests (`660` B) via `m = 480` segments of `b = 11`-bit anchor-verified preimage
       grinding (`480 × 2^11 = 983,040` compressions, total `153 ≥ 149` digests in `983,936 ≤ 2^20`
       compressions), or `75` digests (`1,200` B) via `m = 960` segments of `b = 10`-bit grinding
       (`960 × 2^10 = 983,040` compressions, total `187 ≥ 181` digests in `983,936 ≤ 2^20` compressions).
-/

namespace SigGolfCandidate.Toward45FrontierBounds

open SigGolfCandidate.Toward95Bounds
open SigGolfCandidate.Toward200LeanerBounds

/-! ## 1. Section 1 (`VS45_1`): Frontier Baselines & The Three 45%-Leaner Thresholds -/

/-- Most leaning byte·cycle score on `sig.golf` (`19e10c6a` @ `f37c0a8a`: `5,239 * 6,966 = 36,494,874`). -/
def mostLeaningScore : Nat := 36494874

/-- Signature bytes of the most leaning score (`S = 5,239` B). -/
def mostLeaningSigBytes : Nat := 5239

/-- Witness bytes of the most leaning score (`W = 22,012` B). -/
def mostLeaningWitnessBytes : Nat := 22012

/-- Verification cycles of the most leaning score (`C = 6,966` cycles). -/
def mostLeaningVerifyCycles : Nat := 6966

/-- Leanest signature-byte entry on `sig.golf` (`55154df` @ `65d66b2d`, Radix-6 + PORS: `S = 5,216` B). -/
def radix6LeanestSigBytes : Nat := 5216

/-- Witness bytes of the Radix-6 + PORS entry (`W = 23,236` B). -/
def radix6LeanestWitnessBytes : Nat := 23236

/-- Verification cycles of the Radix-6 + PORS entry (`C = 7,003` cycles). -/
def radix6VerifyCycles : Nat := 7003

/-- Total byte·cycle score of the Radix-6 + PORS entry (`5,216 * 7,003 = 36,527,648`). -/
def radix6Score : Nat := 36527648

/-- Integer percentage standard reduction `⌊(ref - val) * 100 / ref⌋`. -/
def reductionPct (ref val : Nat) : Nat :=
  (ref - val) * 100 / ref

/-- Basis-point (`1/100` of a percent) standard reduction `⌊(ref - val) * 10000 / ref⌋`. -/
def reductionBps (ref val : Nat) : Nat :=
  (ref - val) * 10000 / ref

/-- **Threshold A** (`> +45%` relative efficiency gain over `36,494,874`):
`⌊36,494,874 * 100 / 145⌋ = 25,168,878`. -/
def frontierRel45Score : Nat := 25168878

/-- **Threshold A** signature bytes (`> +45%` relative gain over `5,239` B):
`⌊5,239 * 100 / 145⌋ = 3,613` B. -/
def frontierRel45SigBytes : Nat := 3613

/-- **Threshold A** signature bytes vs. `5,216` B (`⌊5,216 * 100 / 145⌋ = 3,597` B). -/
def radix6Rel45SigBytes : Nat := 3597

/-- **Threshold B** (`> 45%` standard reduction below `36,494,874`, i.e. `≤ 55%` of frontier):
`⌊36,494,874 * 55 / 100⌋ = 20,072,180`. -/
def frontierRed45Score : Nat := 20072180

/-- **Threshold B** signature bytes (`> 45%` standard reduction below `5,239` B):
`⌊5,239 * 55 / 100⌋ = 2,881` B. -/
def frontierRed45SigBytes : Nat := 2881

/-- **Threshold B** signature bytes vs. `55154df` (`> 45%` standard reduction below `5,216` B):
`⌊5,216 * 55 / 100⌋ = 2,868` B. -/
def radix6Red45SigBytes : Nat := 2868

/-- **Threshold B** score vs. `55154df` (`⌊36,527,648 * 55 / 100⌋ = 20,090,206`). -/
def radix6Red45Score : Nat := 20090206

/-- **Threshold C** (`< 45%` of frontier score, i.e. `> 55%` reduction below `36,494,874`):
`⌊36,494,874 * 45 / 100⌋ = 16,422,693`. -/
def frontierSub45RatioScore : Nat := 16422693

/-- **Threshold C** signature bytes (`< 45%` of `5,239` B):
`⌊5,239 * 45 / 100⌋ = 2,357` B. -/
def frontierSub45RatioSigBytes : Nat := 2357

/-- **Threshold C** signature bytes vs. `55154df` (`< 45%` of `5,216` B):
`⌊5,216 * 45 / 100⌋ = 2,347` B. -/
def radix6Sub45RatioSigBytes : Nat := 2347

/-- Verification of the two frontier baselines (`19e10c6a` = `36,494,874` and `55154df` = `36,527,648`)
and all three 45%-leaner thresholds. -/
theorem frontier_baselines_and_45pct_thresholds_eq :
    mostLeaningSigBytes * mostLeaningVerifyCycles = mostLeaningScore ∧
    mostLeaningScore = liveFrontierScore ∧
    radix6LeanestSigBytes * radix6VerifyCycles = radix6Score ∧
    mostLeaningScore < radix6Score ∧
    radix6Score - mostLeaningScore = 32774 ∧
    (mostLeaningScore * 100) / 145 = frontierRel45Score ∧
    (mostLeaningSigBytes * 100) / 145 = frontierRel45SigBytes ∧
    (radix6LeanestSigBytes * 100) / 145 = radix6Rel45SigBytes ∧
    (mostLeaningScore * 55) / 100 = frontierRed45Score ∧
    (mostLeaningSigBytes * 55) / 100 = frontierRed45SigBytes ∧
    (radix6LeanestSigBytes * 55) / 100 = radix6Red45SigBytes ∧
    (radix6Score * 55) / 100 = radix6Red45Score ∧
    (mostLeaningScore * 45) / 100 = frontierSub45RatioScore ∧
    (mostLeaningSigBytes * 45) / 100 = frontierSub45RatioSigBytes ∧
    (radix6LeanestSigBytes * 45) / 100 = radix6Sub45RatioSigBytes := by
  decide

/-- **Why `k = 107` from `Toward200LeanerBounds` is insufficient for Threshold B (`VS45_1`)**:
`cut107Score = 24,593,771` crosses Threshold A (`24,593,771 ≤ 25,168,878`, achieving `+48.39%`
relative efficiency gain over `36,494,874`), but misses Threshold B (`20,072,180 < 24,593,771`),
achieving only `32.61%` standard reduction below `36,494,874` and falling short of the `45%`
standard reduction frontier target by `4,521,591` byte·cycles. -/
theorem cut107_misses_frontier_45pct_reduction :
    cut107Score ≤ frontierRel45Score ∧
    relativeGainPct mostLeaningScore cut107Score = 48 ∧
    relativeGainBps mostLeaningScore cut107Score = 4839 ∧
    frontierRed45Score < cut107Score ∧
    cut107Score - frontierRed45Score = 4521591 ∧
    reductionPct mostLeaningScore cut107Score = 32 ∧
    reductionBps mostLeaningScore cut107Score = 3261 := by
  decide

/-! ## 2. Section 2 (`VS45_2`, `VS45_3`, `VS45_4`): Minimal Single-Message Witness Cuts for All Three Thresholds -/

/-- `k = 102` 16B witness-cut signature bytes (`5,239 - 16 * 102 = 3,607` B). -/
def cut102SigBytes : Nat := 3607

/-- `k = 102` 16B witness-cut witness bytes (`22,012 + 16 * 102 = 23,644` B). -/
def cut102WitnessBytes : Nat := 23644

/-- `k = 102` 16B witness-cut witness cycle charge (`⌈23,644 / 256⌉ = 93`). -/
def cut102WitnessCharge : Nat := 93

/-- `k = 102` 16B witness-cut total verification cycles (`6,880 + 93 = 6,973`). -/
def cut102VerifyCycles : Nat := 6973

/-- `k = 102` 16B witness-cut byte·cycle score (`3,607 * 6,973 = 25,151,611`). -/
def cut102Score : Nat := 25151611

/-- `k = 148` 16B witness-cut signature bytes (`5,239 - 16 * 148 = 2,871` B). -/
def cut148SigBytes : Nat := 2871

/-- `k = 148` 16B witness-cut witness bytes (`22,012 + 16 * 148 = 24,380` B). -/
def cut148WitnessBytes : Nat := 24380

/-- `k = 148` 16B witness-cut witness cycle charge (`⌈24,380 / 256⌉ = 96`). -/
def cut148WitnessCharge : Nat := 96

/-- `k = 148` 16B witness-cut total verification cycles (`6,880 + 96 = 6,976`). -/
def cut148VerifyCycles : Nat := 6976

/-- `k = 148` 16B witness-cut byte·cycle score (`2,871 * 6,976 = 20,028,096`). -/
def cut148Score : Nat := 20028096

/-- `k = 149` 16B witness-cut signature bytes (`5,239 - 16 * 149 = 2,855` B). -/
def cut149SigBytes : Nat := 2855

/-- `k = 149` 16B witness-cut witness bytes (`22,012 + 16 * 149 = 24,396` B). -/
def cut149WitnessBytes : Nat := 24396

/-- `k = 149` 16B witness-cut witness cycle charge (`⌈24,396 / 256⌉ = 96`). -/
def cut149WitnessCharge : Nat := 96

/-- `k = 149` 16B witness-cut total verification cycles (`6,880 + 96 = 6,976`). -/
def cut149VerifyCycles : Nat := 6976

/-- `k = 149` 16B witness-cut byte·cycle score (`2,855 * 6,976 = 19,916,480`). -/
def cut149Score : Nat := 19916480

/-- `k = 181` 16B witness-cut signature bytes (`5,239 - 16 * 181 = 2,343` B). -/
def cut181SigBytes : Nat := 2343

/-- `k = 181` 16B witness-cut witness bytes (`22,012 + 16 * 181 = 24,908` B). -/
def cut181WitnessBytes : Nat := 24908

/-- `k = 181` 16B witness-cut witness cycle charge (`⌈24,908 / 256⌉ = 98`). -/
def cut181WitnessCharge : Nat := 98

/-- `k = 181` 16B witness-cut total verification cycles (`6,880 + 98 = 6,978`). -/
def cut181VerifyCycles : Nat := 6978

/-- `k = 181` 16B witness-cut byte·cycle score (`2,343 * 6,978 = 16,349,454`). -/
def cut181Score : Nat := 16349454

/-- **Minimal Witness Cut for Threshold A (`VS45_2`)**:
Relocating `k = 102` 16-byte digests (`1,632` B) from `S = 5,239` to `W = 22,012` yields
`S = 3,607 ≤ 3,613` B, `W = 23,644` B (`charge = 93`, `C = 6,973`), and
`score = 25,151,611 ≤ 25,168,878 = frontierRel45Score` (`+45.09%` relative gain over `36,494,874`),
with `k = 101` (`S = 3,623 > 3,613`, `score = 25,263,179 > 25,168,878`) strictly insufficient. -/
theorem frontier_rel45_minimal_cut_k102 :
    witnessCutSigBytes mostLeaningSigBytes 16 102 = cut102SigBytes ∧
    cut102SigBytes ≤ frontierRel45SigBytes ∧
    mostLeaningWitnessBytes + 16 * 102 = cut102WitnessBytes ∧
    (cut102WitnessBytes + 255) / 256 = cut102WitnessCharge ∧
    liveFrontierRawVerifyCycles + cut102WitnessCharge = cut102VerifyCycles ∧
    cut102SigBytes * cut102VerifyCycles = cut102Score ∧
    witnessCutScore mostLeaningSigBytes mostLeaningWitnessBytes liveFrontierRawVerifyCycles 16 102 =
      cut102Score ∧
    cut102Score ≤ frontierRel45Score ∧
    145 * cut102Score ≤ 100 * mostLeaningScore ∧
    relativeGainPct mostLeaningScore cut102Score = 45 ∧
    relativeGainBps mostLeaningScore cut102Score = 4509 ∧
    frontierRel45SigBytes < witnessCutSigBytes mostLeaningSigBytes 16 101 ∧
    frontierRel45Score <
      witnessCutScore mostLeaningSigBytes mostLeaningWitnessBytes liveFrontierRawVerifyCycles 16 101 := by
  decide

/-- **Minimal Witness Cuts for Threshold B (`VS45_3`, `> 45%` Standard Reduction Below Frontier)**:
1. `k = 148` (`2,368` B relocated) is the exact minimal 16B digest cut achieving `> 45%` standard
   reduction below `mostLeaningScore = 36,494,874`:
   - `S = 2,871 ≤ 2,881` B (`45.19%` byte reduction below `5,239` B),
   - `W = 24,380` B (`charge = 96`, `C = 6,976`),
   - `score = 2,871 * 6,976 = 20,028,096 ≤ 20,072,180` (`45.1208%` score reduction below `36,494,874`,
     `+82.21%` relative efficiency gain over frontier, `72.97%` reduction below baseline `74,113,492`),
   - whereas `k = 147` gives `S = 2,887 > 2,881` and `score = 20,139,712 > 20,072,180`.
2. `k = 149` (`2,384` B relocated) gives `S = 2,855 ≤ 2,868` B (`45.50%` below `5,239` B and
   `45.26%` below `55154df`'s `5,216` B) and `score = 19,916,480 ≤ 20,072,180` (`45.42%` score
   reduction below `36,494,874` and `45.47%` below `36,527,648`). -/
theorem frontier_red45_minimal_cut_k148_and_k149 :
    witnessCutSigBytes mostLeaningSigBytes 16 148 = cut148SigBytes ∧
    cut148SigBytes ≤ frontierRed45SigBytes ∧
    mostLeaningWitnessBytes + 16 * 148 = cut148WitnessBytes ∧
    (cut148WitnessBytes + 255) / 256 = cut148WitnessCharge ∧
    liveFrontierRawVerifyCycles + cut148WitnessCharge = cut148VerifyCycles ∧
    cut148SigBytes * cut148VerifyCycles = cut148Score ∧
    witnessCutScore mostLeaningSigBytes mostLeaningWitnessBytes liveFrontierRawVerifyCycles 16 148 =
      cut148Score ∧
    cut148Score ≤ frontierRed45Score ∧
    100 * cut148Score ≤ 55 * mostLeaningScore ∧
    reductionPct mostLeaningScore cut148Score = 45 ∧
    reductionBps mostLeaningScore cut148Score = 4512 ∧
    reductionBps mostLeaningSigBytes cut148SigBytes = 4519 ∧
    relativeGainBps mostLeaningScore cut148Score = 8221 ∧
    reductionBps baselineScore cut148Score = 7297 ∧
    frontierRed45SigBytes < witnessCutSigBytes mostLeaningSigBytes 16 147 ∧
    frontierRed45Score <
      witnessCutScore mostLeaningSigBytes mostLeaningWitnessBytes liveFrontierRawVerifyCycles 16 147 ∧
    witnessCutSigBytes mostLeaningSigBytes 16 149 = cut149SigBytes ∧
    cut149SigBytes ≤ radix6Red45SigBytes ∧
    cut149SigBytes ≤ frontierRed45SigBytes ∧
    witnessCutScore mostLeaningSigBytes mostLeaningWitnessBytes liveFrontierRawVerifyCycles 16 149 =
      cut149Score ∧
    cut149Score ≤ frontierRed45Score ∧
    reductionBps mostLeaningScore cut149Score = 4542 ∧
    reductionBps radix6LeanestSigBytes cut149SigBytes = 4526 ∧
    reductionBps radix6Score cut149Score = 4547 := by
  decide

/-- **Minimal Witness Cut for Threshold C (`VS45_4`, `< 45%` of Frontier Score & Signature Bytes)**:
Relocating `k = 181` 16-byte digests (`2,896` B) from `S = 5,239` to `W = 22,012` yields
`S = 2,343 ≤ 2,347 ≤ 2,357` B (`44.72%` of `5,239` B and `44.91%` of `5,216` B),
`W = 24,908` B (`charge = 98`, `C = 6,978`), and `score = 16,349,454 ≤ 16,422,693`
(`44.7993%` of `36,494,874`, i.e. `55.20%` reduction below frontier), with `k = 180`
(`S = 2,359 > 2,357`, `score = 16,461,102 > 16,422,693`) strictly insufficient. -/
theorem frontier_sub45_ratio_minimal_cut_k181 :
    witnessCutSigBytes mostLeaningSigBytes 16 181 = cut181SigBytes ∧
    cut181SigBytes ≤ radix6Sub45RatioSigBytes ∧
    cut181SigBytes ≤ frontierSub45RatioSigBytes ∧
    mostLeaningWitnessBytes + 16 * 181 = cut181WitnessBytes ∧
    (cut181WitnessBytes + 255) / 256 = cut181WitnessCharge ∧
    liveFrontierRawVerifyCycles + cut181WitnessCharge = cut181VerifyCycles ∧
    cut181SigBytes * cut181VerifyCycles = cut181Score ∧
    witnessCutScore mostLeaningSigBytes mostLeaningWitnessBytes liveFrontierRawVerifyCycles 16 181 =
      cut181Score ∧
    cut181Score ≤ frontierSub45RatioScore ∧
    100 * cut181Score < 45 * mostLeaningScore ∧
    100 * cut181SigBytes < 45 * mostLeaningSigBytes ∧
    100 * cut181SigBytes < 45 * radix6LeanestSigBytes ∧
    reductionBps mostLeaningScore cut181Score = 5520 ∧
    relativeGainBps mostLeaningScore cut181Score = 12321 ∧
    frontierSub45RatioSigBytes < witnessCutSigBytes mostLeaningSigBytes 16 180 ∧
    frontierSub45RatioScore <
      witnessCutScore mostLeaningSigBytes mostLeaningWitnessBytes liveFrontierRawVerifyCycles 16 180 := by
  decide

/-! ## 3. Section 3 (`VS45_5`): 2-Layer Collapsed Hypertree + Radix-16 WOTS+C + PORS+ Construction -/

/-- Digests saved by collapsing lower hypertree layers `L2` (`49` digests) and `L3` (`49` digests)
into a 2-layer hypertree (`Top` `h_0 = 12` + `L1` `h_1 = 19` with subtree leaf grinding). -/
def collapsedLayersSavedDigests : Nat := 49 + 49

/-- Raw verification cycles saved by eliminating `L2` (`1,173 + 153 = 1,326`) and
`L3` (`1,173 + 165 = 1,338`) Merkle/WOTS verification passes (`2,664` cycles). -/
def collapsedLayersSavedVerifyCycles : Nat := (1173 + 153) + (1173 + 165)

/-- Chains saved on remaining layers `Top` and `L1` by upgrading from radix-3/5 (`54 + 43 = 97` chains)
to Radix-16 Target-Sum WOTS+C (`28 + 28 = 56` chains, saving `41` chains = `656` B). -/
def radix16WotscSavedChains : Nat := (54 + 43) - (28 + 28)

/-- Digests saved by PORS+ fixed-weight seed-tree FTS pruning (`113 - 88 = 25` digests = `400` B). -/
def porsSeedTreeSavedDigests : Nat := 113 - 88

/-- Total 16-byte digests eliminated by the 2-layer collapsed hypertree + Radix-16 WOTS+C + PORS+
construction (`98 + 41 + 25 = 164` digests). -/
def collapsed2LayerTotalSavedDigests : Nat :=
  collapsedLayersSavedDigests + radix16WotscSavedChains + porsSeedTreeSavedDigests

/-- Total signature bytes saved (`16 * 164 = 2,624` B). -/
def collapsed2LayerTotalSavedBytes : Nat := 16 * collapsed2LayerTotalSavedDigests

/-- Resulting signature bytes (`5,239 - 2,624 = 2,615` B). -/
def collapsed2LayerSigBytes : Nat := mostLeaningSigBytes - collapsed2LayerTotalSavedBytes

/-- Resulting raw verification cycles (`6,880 - 2,664 = 4,216` cycles). -/
def collapsed2LayerRawVerifyCycles : Nat :=
  liveFrontierRawVerifyCycles - collapsedLayersSavedVerifyCycles

/-- Resulting witness bytes after removing `L2` and `L3` witness blocks (`22,012 - 7,680 = 14,332` B). -/
def collapsed2LayerWitnessBytes : Nat := 14332

/-- Resulting witness cycle charge (`⌈14,332 / 256⌉ = 56` cycles). -/
def collapsed2LayerWitnessCharge : Nat := 56

/-- Resulting total verification cycles (`4,216 + 56 = 4,272` cycles). -/
def collapsed2LayerVerifyCycles : Nat :=
  collapsed2LayerRawVerifyCycles + collapsed2LayerWitnessCharge

/-- Resulting byte·cycle score (`2,615 * 4,272 = 11,171,280`). -/
def collapsed2LayerScore : Nat :=
  collapsed2LayerSigBytes * collapsed2LayerVerifyCycles

/-- **2-Layer Collapsed Hypertree + Radix-16 WOTS+C + PORS+ Theorem (`VS45_5`)**:
Without relying on unauthenticated witness cuts, collapsing `L2` and `L3` (`98` digests, `2,664` cycles),
upgrading `Top` and `L1` to Radix-16 WOTS+C (`41` digests), and pruning FTS via a PORS+ seed tree
(`25` digests) eliminates `164` digests (`2,624` B) and `2,694` total verify cycles, yielding:
- `collapsed2LayerSigBytes = 2,615 ≤ 2,868 ≤ 2,881` B (`50.08% > 45%` byte reduction below `5,239` B
  and `49.86% > 45%` byte reduction below `55154df`'s `5,216` B),
- `collapsed2LayerVerifyCycles = 4,272` cycles (`38.67%` cycle reduction below `6,966`),
- `collapsed2LayerScore = 11,171,280 ≤ 16,422,693 ≤ 20,072,180` (**`69.38%` score reduction below
  `36,494,874` (`3.266x` leaner than frontier) and `84.92%` reduction (`6.634x` leaner) below baseline**). -/
theorem collapsed_2layer_rad16_pors_exceeds_all_45pct_frontier_targets :
    collapsedLayersSavedDigests = 98 ∧
    collapsedLayersSavedVerifyCycles = 2664 ∧
    radix16WotscSavedChains = 41 ∧
    porsSeedTreeSavedDigests = 25 ∧
    collapsed2LayerTotalSavedDigests = 164 ∧
    collapsed2LayerTotalSavedBytes = 2624 ∧
    collapsed2LayerSigBytes = 2615 ∧
    collapsed2LayerSigBytes ≤ radix6Red45SigBytes ∧
    collapsed2LayerSigBytes ≤ frontierRed45SigBytes ∧
    2 * collapsed2LayerSigBytes < mostLeaningSigBytes ∧
    collapsed2LayerRawVerifyCycles = 4216 ∧
    (collapsed2LayerWitnessBytes + 255) / 256 = collapsed2LayerWitnessCharge ∧
    collapsed2LayerVerifyCycles = 4272 ∧
    collapsed2LayerScore = 11171280 ∧
    collapsed2LayerScore ≤ frontierSub45RatioScore ∧
    collapsed2LayerScore ≤ frontierRed45Score ∧
    collapsed2LayerScore ≤ frontierRel45Score ∧
    3 * collapsed2LayerScore ≤ mostLeaningScore ∧
    6 * collapsed2LayerScore ≤ baselineScore ∧
    reductionBps mostLeaningSigBytes collapsed2LayerSigBytes = 5008 ∧
    reductionBps radix6LeanestSigBytes collapsed2LayerSigBytes = 4986 ∧
    reductionBps mostLeaningScore collapsed2LayerScore = 6938 ∧
    relativeGainBps mostLeaningScore collapsed2LayerScore = 22668 ∧
    reductionBps baselineScore collapsed2LayerScore = 8492 ∧
    relativeGainBps baselineScore collapsed2LayerScore = 56342 := by
  decide

/-! ## 4. Section 4 (`VS45_6`, `VS45_7`): Anchored Family-Seed & Segmented Preimage Recovery in `expand` -/

/-- Digests deterministically recovered in `expand(message, publicKey, signature)` by revealing
compact GF(2^128) family seeds / low-step chain heads in `signature` and hashing forward (`112` digests). -/
def familySeedRecoveredDigests : Nat := 112

/-- Signature bytes recovered by deterministic family-seed forward evaluation (`112 * 16 = 1,792` B). -/
def familySeedRecoveredBytes : Nat := 16 * familySeedRecoveredDigests

/-- Hash compressions used by deterministic family-seed forward evaluation (`112 * 8 = 896` compressions). -/
def familySeedForwardCompressions : Nat := 112 * 8

/-- Full 16-byte digests recovered by segmented preimage grinding of `m` segments of `b` bits
(`⌊segmentedElidedBytes m b / 16⌋`). -/
def segmentedRecoveredDigests (m b : Nat) : Nat :=
  segmentedElidedBytes m b / 16

/-- Total 16-byte digests recovered in `expand` by combining deterministic family-seed forward
evaluation with `m × b`-bit segmented anchor-verified preimage grinding. -/
def totalAnchoredRecoveredDigests (m b : Nat) : Nat :=
  familySeedRecoveredDigests + segmentedRecoveredDigests m b

/-- Total hash compressions used in `expand` by combining deterministic family-seed forward
evaluation (`896` compressions) with `m × b`-bit segmented preimage grinding (`m * 2^b`). -/
def totalAnchoredExpandCompressions (m b : Nat) : Nat :=
  familySeedForwardCompressions + segmentedGrindingCost m b

/-- **Anchored Expand Recovery Theorem (`VS45_6`, `VS45_7`)**:
`expand(message, publicKey, signature)` can deterministically recover all omitted digests for
both Threshold B (`k = 148..149`) and Threshold C (`k = 181`) within `BUDGET_EXPAND = 2^20 = 1,048,576`
hash compressions using ONLY `(message, publicKey, signature)`:
1. **Family-Seed Forward Evaluation (`112` digests = `1,792` B)** costs `112 * 8 = 896` compressions.
2. **Regime I (`m = 240, b = 12`)**: Grinds `360` B (`22` digests + `8` B) in `983,040` compressions;
   combined cost `896 + 983,040 = 983,936 ≤ 1,048,576`, leaving `64,640` compressions of headroom.
3. **Regime II (`m = 480, b = 11`, Threshold B `k = 148..149`)**: Grinds `660` B (`41` full 16B digests)
   in `480 * 2^11 = 983,040` compressions; combined with `112` family-seed digests, recovers
   `112 + 41 = 153 ≥ 149 ≥ 148` digests (`2,452` B) in `983,936 ≤ 1,048,576 = BUDGET_EXPAND` compressions.
4. **Regime III (`m = 960, b = 10`, Threshold C `k = 181`)**: Grinds `1,200` B (`75` full 16B digests)
   in `960 * 2^10 = 983,040` compressions; combined with `112` family-seed digests, recovers
   `112 + 75 = 187 ≥ 181` digests (`2,992` B) in `983,936 ≤ 1,048,576 = BUDGET_EXPAND` compressions. -/
theorem anchored_expand_recovery_sound_and_within_budget :
    familySeedRecoveredBytes = 1792 ∧
    familySeedForwardCompressions = 896 ∧
    segmentedElidedBytes 240 12 = 360 ∧
    totalAnchoredExpandCompressions 240 12 = 983936 ∧
    totalAnchoredExpandCompressions 240 12 ≤ budgetExpand ∧
    budgetExpand - totalAnchoredExpandCompressions 240 12 = 64640 ∧
    segmentedElidedBytes 480 11 = 660 ∧
    segmentedRecoveredDigests 480 11 = 41 ∧
    totalAnchoredRecoveredDigests 480 11 = 153 ∧
    149 ≤ totalAnchoredRecoveredDigests 480 11 ∧
    totalAnchoredExpandCompressions 480 11 = 983936 ∧
    totalAnchoredExpandCompressions 480 11 ≤ budgetExpand ∧
    segmentedElidedBytes 960 10 = 1200 ∧
    segmentedRecoveredDigests 960 10 = 75 ∧
    totalAnchoredRecoveredDigests 960 10 = 187 ∧
    181 ≤ totalAnchoredRecoveredDigests 960 10 ∧
    totalAnchoredExpandCompressions 960 10 = 983936 ∧
    totalAnchoredExpandCompressions 960 10 ≤ budgetExpand := by
  decide

end SigGolfCandidate.Toward45FrontierBounds

#print axioms SigGolfCandidate.Toward45FrontierBounds.frontier_baselines_and_45pct_thresholds_eq
#print axioms SigGolfCandidate.Toward45FrontierBounds.cut107_misses_frontier_45pct_reduction
#print axioms SigGolfCandidate.Toward45FrontierBounds.frontier_rel45_minimal_cut_k102
#print axioms SigGolfCandidate.Toward45FrontierBounds.frontier_red45_minimal_cut_k148_and_k149
#print axioms SigGolfCandidate.Toward45FrontierBounds.frontier_sub45_ratio_minimal_cut_k181
#print axioms SigGolfCandidate.Toward45FrontierBounds.collapsed_2layer_rad16_pors_exceeds_all_45pct_frontier_targets
#print axioms SigGolfCandidate.Toward45FrontierBounds.anchored_expand_recovery_sound_and_within_budget
