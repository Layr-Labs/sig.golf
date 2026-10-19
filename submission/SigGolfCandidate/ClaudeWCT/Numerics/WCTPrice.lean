import SigGolfCandidate.ClaudeWCT.Numerics.WCTEnvelope
import SigGolfCandidate.ClaudeWCT.Bank.WCTHonest
import SigGolfCandidate.ClaudeWCT.Numerics.RouteCRows

/-! Route C for the FTS bank at gate 804 (R6 campaign, stream RC; sec-rc/RC_SPEC.txt): binned row
bounds, envelope moments, and the route-C excess theorems that replace main's winsorized-Chernoff
certificate (removed). The theorems `excess_{middle,high,low,large,tiny}_certified` keep their
installed names and conclusions; their former fee premise is gone. At the middle threshold the
certified excess is `1097/10^6`, 6.7 % below the closing budget `147/125000`. -/

namespace ClaudeWCT.Numerics.RouteCBank
open Finset Polynomial
open ClaudeWCT.Numerics ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.RouteCData
open ClaudeWCT.Numerics.RouteCRows
open ClaudeWCT.Numerics.SharedMoments (forestMoment alphabetSize fieldSize)
open ClaudeWCT.Numerics.SharedCoverage (ForestHistory forestCoverage)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem forestN_eq (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ 18) : forestN r = SharedPathPacked.forest r := by
  interval_cases r
  · exact forest_small_1.symm
  · exact forest_small_2.symm
  · exact forest_small_3.symm
  · exact forest_small_4.symm
  · exact SharedGeneratedForest.forest_5_checked.symm
  · exact SharedGeneratedForest.forest_6_checked.symm
  · exact SharedGeneratedForest.forest_7_checked.symm
  · exact SharedGeneratedForest.forest_8_checked.symm
  · exact SharedGeneratedForest.forest_9_checked.symm
  · exact SharedGeneratedForest.forest_10_checked.symm
  · exact SharedGeneratedForest.forest_11_checked.symm
  · exact SharedGeneratedForest.forest_12_checked.symm
  · exact SharedGeneratedForest.forest_13_checked.symm
  · exact SharedGeneratedForest.forest_14_checked.symm
  · exact SharedGeneratedForest.forest_15_checked.symm
  · exact SharedGeneratedForest.forest_16_checked.symm
  · exact SharedGeneratedForest.forest_17_checked.symm
  · exact SharedGeneratedForest.forest_18_checked.symm

theorem runEntries_length (runs : List (ℕ × ℕ × ℕ))
    (hidx : (runEntries runs).map Prod.fst = List.range 7210) : (runEntries runs).length = 7210 := by
  have := congrArg List.length hidx
  simpa using this

theorem packRuns_tree (runs : List (ℕ × ℕ × ℕ)) (hlen : (runEntries runs).length = 7210) :
    packRuns runs = SharedFees.packTree 4096 13 0
      (fun i => if i < 7210 then runFee runs (7209 - i) else 0) := by
  rw [packRuns, SharedFees.packList_eq_tree]
  apply SharedFees.packTree_congr
  intro i hi
  simp only [Nat.zero_add]
  have hl : ((runEntries runs).map Prod.snd).length = 7210 := by simp [hlen]
  by_cases h : i < 7210
  · rw [List.getElem?_reverse (by rw [hl]; exact h), hl, if_pos h]
    simp only [runFee, List.getElem?_map]
  · have hh : ((runEntries runs).map Prod.snd).reverse.length ≤ i := by
      rw [List.length_reverse, hl]; omega
    rw [List.getElem?_eq_none hh, if_neg h]
    rfl

theorem packedDot_runs (P : ℕ[X]) (runs : List (ℕ × ℕ × ℕ)) (hlen : (runEntries runs).length = 7210)
    (G : ℕ) (hfee : ∀ i, i < 7210 → runFee runs i ≤ G) (hG : G ≤ 2 ^ 900) (hmass : P.eval 1 ≤ 2 ^ 3072) :
    SharedFees.packedDot (P.eval (2 ^ 4096)) (packRuns runs) =
      ∑ i ∈ range 7210, P.coeff i * runFee runs i := by
  rw [packRuns_tree runs hlen]
  unfold SharedFees.packedDot
  rw [SharedFees.packTree_reversed 4096 13 7210 (runFee runs) (by decide)]
  have hs : (∑ i ∈ range 7210, runFee runs i) ≤ 7210 * 2 ^ 900 := by
    calc (∑ i ∈ range 7210, runFee runs i) ≤ ∑ _i ∈ range 7210, 2 ^ 900 :=
          Finset.sum_le_sum fun i hi => (hfee i (Finset.mem_range.mp hi)).trans hG
      _ = 7210 * 2 ^ 900 := by simp
  have hm : P.eval 1 * (∑ i ∈ range 7210, runFee runs i) < 2 ^ 4096 :=
    (Nat.mul_le_mul hmass hs).trans_lt (by decide +kernel)
  exact SharedFees.convolution_shift P 4096 7210 (runFee runs) hm

theorem massDot (P : ℕ[X]) (hmass : P.eval 1 ≤ 2 ^ 3072) :
    SharedFees.packedDot (P.eval (2 ^ 4096)) SharedGeneratedFeeVector.MassFee =
      ∑ i ∈ range 7210, P.coeff i := by
  rw [← SharedGeneratedFeeVector.packedFee_0_checked]
  have hs : (∑ i ∈ range 7210, SharedFees.feeValue 0 i) = 7210 := by
    simp [SharedFees.feeValue]
  rw [SharedFees.packedDot_fee P _ 0 rfl (by rw [hs]; exact (Nat.mul_le_mul_right _ hmass).trans_lt (by decide +kernel))]
  simp [SharedFees.feeValue]

theorem runsOk_mem {k : ℕ} {runs : List (ℕ × ℕ × ℕ)} {G : ℕ} (h : runsOk k runs G = true)
    (e : ℕ × ℕ × ℕ) (he : e ∈ runs) :
    e.1 ≤ e.2.1 ∧ okOf k rcPar (lowerQ rcPar.g e.1) (upperQ rcPar.g e.2.1) e.2.2 = true ∧ e.2.2 ≤ G := by
  unfold runsOk at h
  have := List.all_eq_true.mp h e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- Binned row bound of kind `k`: the cost summed over the histories of row `r` is paid by the row
dot product. -/
theorem row_bound (k : ℕ) (runs : List (ℕ × ℕ × ℕ)) (G : ℕ) (hP : ParFacts rcPar)
    (hidx : (runEntries runs).map Prod.fst = List.range 7210) (hruns : runsOk k runs G = true)
    (hglob : globOk k rcPar G = true) (hG : G ≤ 2 ^ 900) (r : ℕ) (h1 : 1 ≤ r) (h18 : r ≤ 18) :
    (∑ h : ForestHistory (Fin 563) r, ENNReal.ofReal
      (costOf k rcPar ((rcPar.g : ℝ) / 2 ^ 66 * (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)))) ≤
      ENNReal.ofReal ((rcPar.g : ℝ) / 2 ^ 66) / (feeScale : ENNReal) *
        (dotRow (packRuns runs) G r (forestN r) : ENNReal) := by
  classical
  have hord : ∀ e ∈ runs, e.1 ≤ e.2.1 := fun e he => (runsOk_mem hruns e he).1
  have hlen := runEntries_length runs hidx
  have hp : ∀ K, K ∈ [64, 128] → ∀ u, u ≤ r → ∀ j, (SharedCoverage.coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K × Fin 563 =>
        N600.coordinateCoverage ClaudeWCT.WCT9.wordDigit E = j).card :=
    fun K hK u hu j => SharedCoverage.wordDigit_coordinate_coeff K hK u (by omega) j
  set P := SharedPathForest.actualPoly r with hPdef
  have henc : SharedPathPacked.forest r = P.eval (2 ^ 4096) :=
    SharedPathForest.actual_encoding ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r (by omega) hp
  have hmass : P.eval 1 ≤ 2 ^ 3072 :=
    (SharedPathForest.actual_mass_le ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r (by omega) hp).trans
      (SharedFees.forest_mass_3072 r (by omega))
  have hfeeG : ∀ j, j < 7210 → runFee runs j ≤ G := by
    intro j hj
    obtain ⟨e, he, _, _, hf⟩ := runFee_lookup runs 7210 hord hidx j hj
    rw [hf]; exact (runsOk_mem hruns e he).2.2
  rw [forestN_eq r h1 h18, henc]
  unfold dotRow
  rw [packedDot_runs P runs hlen G hfeeG hG hmass, massDot P hmass]
  have hκ : (0 : ℝ) ≤ (rcPar.g : ℝ) / 2 ^ 66 := by positivity
  have hS := feeScale_pos
  apply SharedFees.ofReal_sum_nat_bound _ _ _ feeScale hκ (by norm_num [feeScale])
    (fun h => costOf_nonneg k rcPar hP _ (by positivity))
  have hreal := SharedFees.histogram_moment_bound 7210 (forestMoment r) G
    (SharedPathForest.actualGood ClaudeWCT.WCT9.wordDigit) (SharedPathForest.actualBin ClaudeWCT.WCT9.wordDigit)
    (forestCoverage ClaudeWCT.WCT9.wordDigit) P
    (SharedPathForest.actual_histogram ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r (by omega) hp)
    (SharedCoverage.forest_coverage_data ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563)
      WCTEnvelope.w1Table_wordDigit SharedMoments.rows_checked r (by omega))
    (fun h => costOf k rcPar ((rcPar.g : ℝ) / 2 ^ 66 * (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)))
    (runFee runs) ((rcPar.g : ℝ) / 2 ^ 66 / feeScale) (by positivity) hfeeG
    (fun h => by
      have := glob_sound k rcPar hP G hglob _ (by positivity : (0 : ℝ) ≤ (rcPar.g : ℝ) / 2 ^ 66 *
        (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ))
      calc _ ≤ _ := this
        _ = _ := by ring)
    (fun h hg hb => by
      obtain ⟨e, he, hlo, hhi, hf⟩ := runFee_lookup runs 7210 hord hidx _ hb
      obtain ⟨_, hok, _⟩ := runsOk_mem hruns e he
      have hb' := bin_bounds rcPar.g (SharedPathForest.actual_interval ClaudeWCT.WCT9.wordDigit
        (by omega) h hg)
      have hx0 : (0 : ℝ) ≤ (rcPar.g : ℝ) / 2 ^ 66 * (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ) := by
        positivity
      have := ok_sound k rcPar hP _ _ e.2.2 hok _ hx0 ((lowerQ_mono rcPar.g hlo).trans hb'.1)
        (hb'.2.trans (upperQ_mono rcPar.g hhi))
      rw [hf]
      calc _ ≤ _ := this
        _ = _ := by ring)
  simpa only [mul_comm] using hreal

end ClaudeWCT.Numerics.RouteCBank

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.RouteCData ClaudeWCT.Numerics.RouteCRows
open ClaudeWCT.Numerics.RouteCBank
open ClaudeWCT.Numerics.SharedMoments (forestMoment alphabetSize fieldSize priceScaleTotal)
open ClaudeWCT.Numerics.SharedCoverage (ForestHistory forestCoverage)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The installed price coefficient is the route-C data gate. -/
theorem rc_coef_real : feeCoefficient.toReal = (rcPar.g : ℝ) / 2 ^ 66 := by
  rw [feeCoefficient_real]; rfl

theorem rc_coef : ENNReal.ofReal ((rcPar.g : ℝ) / 2 ^ 66) = feeCoefficient := by
  rw [← rc_coef_real, ENNReal.ofReal_toReal (by unfold feeCoefficient; finiteness)]

theorem rc_pst : priceScaleTotal = pst := rfl

/-- Envelope bound for a coordinate average at a general rate and horizon (the conditional law
uses rate `(2^31-1)⁻¹` and horizon `2^32 - r`). -/
theorem rc_envelope (rate : ENNReal) (hrate : rate ≤ 1) (T : ℕ)
    (hlam : (T : ENNReal) * rate * kappa ≤ ((805 : ℕ) : ENNReal) / ((400 : ℕ) : ENNReal))
    (hu : (1 - rate) ^ (T - 80) ≤ ((13533530 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal))
    (G : ℕ) (hG0 : 0 < G) (row : ℕ → ℕ) (f : List Alphabet → ENNReal)
    (g : (r : ℕ) → ForestHistory (Fin 563) r → ENNReal)
    (hfg : ∀ r ≤ 80, ∀ h : Fin r → Alphabet, f (List.ofFn h) ≤ g r (splitHistory h))
    (hfees : ∀ r ≤ 80, (∑ h, g r h) ≤ feeCoefficient / (feeScale : ENNReal) * (row r : ENNReal))
    (hpoint : ∀ W, f W ≤ (G : ENNReal) * feeCoefficient * alphabetSize / (feeScale : ENNReal))
    (Mn Md : ℕ) (hMd : 0 < Md)
    (hcheck : N600.poissonCheckQ fieldSize 13533530 100000000 805 400 (fun r => 16 ^ r * row r)
      (G * alphabetSize) (G * priceScaleTotal) feeScale Mn Md 80 = true) :
    (2 ^ 31 : ENNReal) * Law.coordAverage rate honestCoordLaw T f ≤ (Mn : ENNReal) / Md := by
  have hS : 0 < feeScale := by norm_num [feeScale]
  let C : ENNReal := (G : ENNReal) * feeCoefficient * alphabetSize / (feeScale : ENNReal)
  have hC0 : C ≠ 0 := by
    have hMc : (G : ENNReal) ≠ 0 := by exact_mod_cast hG0.ne'
    have hfc : feeCoefficient ≠ 0 := by norm_num [feeCoefficient]
    have hDc : (alphabetSize : ENNReal) ≠ 0 := by norm_num [alphabetSize]
    exact ENNReal.div_ne_zero.mpr ⟨mul_ne_zero (mul_ne_zero hMc hfc) hDc, ENNReal.natCast_ne_top _⟩
  have hCt : C ≠ ⊤ := by dsimp [C, feeCoefficient]; finiteness
  let v : ℕ → ENNReal := fun r => Law.lawAvg honestCoordLaw r (fun W => f W / C)
  have hv1 : ∀ r ≤ 80, v r ≤ kappa ^ r * (((16 ^ r * row r : ℕ) : ENNReal) /
      ((G * alphabetSize * fieldSize ^ (9 * r) : ℕ) : ENNReal)) := by
    intro r hr
    have h := law_normalized_history_row r G feeScale (row r) hG0 hS f (g r) (hfg r hr) (hfees r hr)
    exact h.trans_eq (mul_div_assoc _ _ _)
  have hv2 : ∀ r, 80 < r → v r ≤ 1 := fun r _ => law_normalized_le_one r f C hC0 hCt hpoint
  have hkey := N600.poissonCheckQ_sound_tilt hcheck (by norm_num [fieldSize]) (by norm_num) (by norm_num)
    (Nat.mul_pos hG0 (by norm_num [alphabetSize])) (by norm_num [feeScale]) hMd hrate kappa kappa_one_le hlam hu v
    hv1 hv2
  calc (2 ^ 31 : ENNReal) * Law.coordAverage rate honestCoordLaw T f =
      ((2 ^ 31 : ENNReal) * C) * Law.coordAverage rate honestCoordLaw T (fun W => f W / C) :=
        (coordAverage_scaled honestCoordLaw T f C (2 ^ 31) rate hC0 hCt).symm
    _ = ((G * priceScaleTotal : ℕ) : ENNReal) / (feeScale : ENNReal) *
        SphincsSecurity.Concrete.binomialAverage rate T v := by
      rw [show (2 ^ 31 : ENNReal) * C = ((G * priceScaleTotal : ℕ) : ENNReal) / (feeScale : ENNReal) from
        normalizer_scale G feeScale]
      rfl
    _ ≤ (Mn : ENNReal) / Md := hkey

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.RouteCData ClaudeWCT.Numerics.RouteCRows
open ClaudeWCT.Numerics.RouteCBank
open ClaudeWCT.Numerics.SharedMoments (forestMoment alphabetSize fieldSize priceScaleTotal)
open ClaudeWCT.Numerics.SharedCoverage (ForestHistory forestCoverage)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem rc_price_real {r : ℕ} (h : Fin r → Alphabet) :
    (priceBucket (List.ofFn h)).toReal =
      (rcPar.g : ℝ) / 2 ^ 66 * (forestCoverage ClaudeWCT.WCT9.wordDigit (splitHistory h) : ℝ) := by
  rw [priceBucket_ofFn, ENNReal.toReal_mul, rc_coef_real, ENNReal.toReal_natCast]

theorem rc_price_bound (W : List Alphabet) :
    (priceBucket W).toReal ≤ (rcPar.g : ℝ) / 2 ^ 66 * alphabetSize := by
  have h := ENNReal.toReal_mono (by unfold feeCoefficient; finiteness) (priceBucket_le W)
  rwa [ENNReal.toReal_mul, rc_coef_real, ENNReal.toReal_natCast] at h

/-- Global fee row: every row is paid at the global fee on its first moment. -/
theorem rc_global_row (k : ℕ) (hP : ParFacts rcPar) (G : ℕ) (hglob : globOk k rcPar G = true)
    (r : ℕ) (hr : r ≤ 80) :
    (∑ h : ForestHistory (Fin 563) r, ENNReal.ofReal
      (costOf k rcPar ((rcPar.g : ℝ) / 2 ^ 66 * (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)))) ≤
      ENNReal.ofReal ((rcPar.g : ℝ) / 2 ^ 66) / (feeScale : ENNReal) * ((G * forestMoment r : ℕ) : ENNReal) := by
  have hκ : (0 : ℝ) ≤ (rcPar.g : ℝ) / 2 ^ 66 := by positivity
  have hS := feeScale_pos
  apply SharedFees.ofReal_sum_nat_bound _ _ _ feeScale hκ (by norm_num [feeScale])
    (fun h => costOf_nonneg k rcPar hP _ (by positivity))
  have htot := SharedCoverage.forest_coverage_data ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563)
    WCTEnvelope.w1Table_wordDigit SharedMoments.rows_checked r (by omega)
  have htotR : (∑ h : ForestHistory (Fin 563) r, (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)) =
      (forestMoment r : ℝ) := by exact_mod_cast htot
  calc _ ≤ ∑ h : ForestHistory (Fin 563) r, (rcPar.g : ℝ) / 2 ^ 66 *
        (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ) * G / feeScale :=
      Finset.sum_le_sum fun h _ => glob_sound k rcPar hP G hglob _ (by positivity)
    _ = _ := by
      rw [← Finset.sum_div, ← Finset.sum_mul, ← Finset.mul_sum, htotR]
      push_cast
      ring

theorem rc_point (k : ℕ) (hP : ParFacts rcPar) (G : ℕ) (hglob : globOk k rcPar G = true) (W : List Alphabet) :
    ENNReal.ofReal (costOf k rcPar (priceBucket W).toReal) ≤
      (G : ENNReal) * feeCoefficient * alphabetSize / (feeScale : ENNReal) := by
  have hS := feeScale_pos
  have h1 := glob_sound k rcPar hP G hglob (priceBucket W).toReal ENNReal.toReal_nonneg
  have h2 : (priceBucket W).toReal * G / feeScale ≤ (rcPar.g : ℝ) / 2 ^ 66 * alphabetSize * G / feeScale := by
    gcongr; exact rc_price_bound W
  calc ENNReal.ofReal (costOf k rcPar (priceBucket W).toReal)
      ≤ ENNReal.ofReal ((rcPar.g : ℝ) / 2 ^ 66 * alphabetSize * G / feeScale) :=
        ENNReal.ofReal_le_ofReal (h1.trans h2)
    _ = _ := by
      rw [← rc_coef, ENNReal.ofReal_div_of_pos hS, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]
      ring

/-- A route-C moment of kind `k` (0 mean, 1 second moment, 2 count, 3 over, 4 clipped mgf). -/
theorem rc_kind_all (k : ℕ) (runs : List (ℕ × ℕ × ℕ)) (G pack : ℕ) (hpack : packRuns runs = pack)
    (hP : ParFacts rcPar) (hidx : (runEntries runs).map Prod.fst = List.range 7210)
    (hruns : runsOk k runs G = true) (hglob : globOk k rcPar G = true) (hG : G ≤ 2 ^ 900) (hG0 : 0 < G)
    (rate : ENNReal) (hrate : rate ≤ 1) (T : ℕ)
    (hlam : (T : ENNReal) * rate * kappa ≤ ((805 : ℕ) : ENNReal) / ((400 : ℕ) : ENNReal))
    (hu : (1 - rate) ^ (T - 80) ≤ ((13533530 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal))
    (Mn Md : ℕ) (hMd : 0 < Md)
    (hcheck : N600.poissonCheckQ fieldSize 13533530 100000000 805 400 (fun r => 16 ^ r * rowAll pack G r)
      (G * alphabetSize) (G * pst) feeScale Mn Md 80 = true) :
    (2 ^ 31 : ENNReal) * Law.coordAverage rate honestCoordLaw T
      (fun L => ENNReal.ofReal (costOf k rcPar (priceBucket L).toReal)) ≤ (Mn : ENNReal) / Md := by
  apply rc_envelope rate hrate T hlam hu G hG0 (rowAll pack G) _
    (fun r h => ENNReal.ofReal (costOf k rcPar ((rcPar.g : ℝ) / 2 ^ 66 *
      (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)))) _ _ (rc_point k hP G hglob) Mn Md hMd
    (by rw [rc_pst]; exact hcheck)
  · intro r _ h
    rw [rc_price_real]
  · intro r hr
    by_cases hrow : 1 ≤ r ∧ r ≤ 18
    · have h := row_bound k runs G hP hidx hruns hglob hG r hrow.1 hrow.2
      rw [hpack, rc_coef] at h
      unfold rowAll
      rwa [if_pos hrow, dotRowC_eq _ _ _ hrow.2]
    · have h := rc_global_row k hP G hglob r hr
      rw [rc_coef] at h
      unfold rowAll
      rwa [if_neg hrow]

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.RouteCData ClaudeWCT.Numerics.RouteCRows
open ClaudeWCT.Numerics.RouteCBank
open ClaudeWCT.Numerics.SharedMoments (forestMoment alphabetSize fieldSize priceScaleTotal)
open ClaudeWCT.Numerics.SharedCoverage (ForestHistory forestCoverage)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem forestMoment_zero : forestMoment 0 = 0 := by decide +kernel

/-- The Scarf payment on short rows (kind 5). -/
theorem rc_kind_short (runs : List (ℕ × ℕ × ℕ)) (G pack : ℕ) (hpack : packRuns runs = pack)
    (hP : ParFacts rcPar) (hidx : (runEntries runs).map Prod.fst = List.range 7210)
    (hruns : runsOk 5 runs G = true) (hglob : globOk 5 rcPar G = true) (hG : G ≤ 2 ^ 900) (hG0 : 0 < G)
    (rate : ENNReal) (hrate : rate ≤ 1) (T : ℕ)
    (hlam : (T : ENNReal) * rate * kappa ≤ ((805 : ℕ) : ENNReal) / ((400 : ℕ) : ENNReal))
    (hu : (1 - rate) ^ (T - 80) ≤ ((13533530 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal))
    (Mn Md : ℕ) (hMd : 0 < Md)
    (hcheck : N600.poissonCheckQ fieldSize 13533530 100000000 805 400 (fun r => 16 ^ r * rowShort pack G r)
      (G * alphabetSize) (G * pst) feeScale Mn Md 80 = true) :
    (2 ^ 31 : ENNReal) * Law.coordAverage rate honestCoordLaw T
      (fun L => if L.length ≤ 18 then ENNReal.ofReal (costOf 5 rcPar (priceBucket L).toReal) else 0) ≤
        (Mn : ENNReal) / Md := by
  apply rc_envelope rate hrate T hlam hu G hG0 (rowShort pack G) _
    (fun r h => if r ≤ 18 then ENNReal.ofReal (costOf 5 rcPar ((rcPar.g : ℝ) / 2 ^ 66 *
      (forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ))) else 0) _ _ _ Mn Md hMd
    (by rw [rc_pst]; exact hcheck)
  · intro r _ h
    simp only [List.length_ofFn, rc_price_real]
    exact le_rfl
  · intro r hr
    by_cases hrow : 1 ≤ r ∧ r ≤ 18
    · have h := row_bound 5 runs G hP hidx hruns hglob hG r hrow.1 hrow.2
      rw [hpack, rc_coef] at h
      unfold rowShort
      rw [if_pos hrow, dotRowC_eq _ _ _ hrow.2, Finset.sum_congr rfl (fun x _ => if_pos hrow.2)]
      exact h
    · unfold rowShort
      rw [if_neg hrow]
      by_cases h18 : r ≤ 18
      · have h0 : r = 0 := by omega
        subst h0
        have h := rc_global_row 5 hP G hglob 0 (by norm_num)
        rw [rc_coef, forestMoment_zero, Nat.mul_zero] at h
        rw [Finset.sum_congr rfl (fun x _ => if_pos h18)]
        exact h
      · rw [Finset.sum_congr rfl (fun x _ => if_neg h18), Finset.sum_const_zero]
        exact zero_le
  · intro W
    split_ifs
    · exact rc_point 5 hP G hglob W
    · exact zero_le

/-- The long-row first moment (bucket price on rows above 18). -/
theorem rc_long (rate : ENNReal) (hrate : rate ≤ 1) (T : ℕ)
    (hlam : (T : ENNReal) * rate * kappa ≤ ((805 : ℕ) : ENNReal) / ((400 : ℕ) : ENNReal))
    (hu : (1 - rate) ^ (T - 80) ≤ ((13533530 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal))
    (Mn Md : ℕ) (hMd : 0 < Md)
    (hcheck : N600.poissonCheckQ fieldSize 13533530 100000000 805 400 (fun r => 16 ^ r * rowLong r)
      (feeScale * alphabetSize) (feeScale * pst) feeScale Mn Md 80 = true) :
    (2 ^ 31 : ENNReal) * Law.coordAverage rate honestCoordLaw T
      (fun L => if 18 < L.length then priceBucket L else 0) ≤ (Mn : ENNReal) / Md := by
  have hS : (0 : ENNReal) < feeScale := by norm_num [feeScale]
  have hSt : (feeScale : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  apply rc_envelope rate hrate T hlam hu feeScale (by norm_num [feeScale]) rowLong _
    (fun r h => if 18 < r then feeCoefficient * (forestCoverage ClaudeWCT.WCT9.wordDigit h : ENNReal) else 0)
    _ _ _ Mn Md hMd (by rw [rc_pst]; exact hcheck)
  · intro r _ h
    simp only [List.length_ofFn, priceBucket_ofFn]
    exact le_rfl
  · intro r hr
    unfold rowLong
    split_ifs with h18
    · rw [← Finset.mul_sum, ← Nat.cast_sum, SharedCoverage.forest_coverage_data ClaudeWCT.WCT9.wordDigit
        (Fintype.card_fin 563) WCTEnvelope.w1Table_wordDigit SharedMoments.rows_checked r (by omega)]
      rw [Nat.cast_mul, ← mul_assoc, ENNReal.div_mul_cancel hS.ne' hSt]
    · rw [Finset.sum_const_zero]
      exact zero_le
  · intro W
    split_ifs
    · rw [mul_assoc, mul_comm, mul_div_assoc, ENNReal.div_self hS.ne' hSt, mul_one]
      calc priceBucket W ≤ feeCoefficient * alphabetSize := priceBucket_le W
        _ = _ := by ring
    · exact zero_le

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
set_option maxHeartbeats 4000000

/-! ### Envelope rates (RC_SPEC E3 / L4): unconditional and one-index conditional laws -/

theorem rc_kappa_uncond : ((2 ^ 32 : ℕ) : ENNReal) * (2 ^ 31 : ENNReal)⁻¹ * kappa ≤
    ((805 : ℕ) : ENNReal) / ((400 : ℕ) : ENNReal) := by
  rw [kappa_exact]
  unfold SharedFtsCount.total SharedFtsCount.count
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]

theorem rc_kappa_cond (r : ℕ) (hr : 1 ≤ r) :
    ((2 ^ 32 - r : ℕ) : ENNReal) * ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹ * kappa ≤
      ((805 : ℕ) : ENNReal) / ((400 : ℕ) : ENNReal) := by
  have hle : ((2 ^ 32 - r : ℕ) : ENNReal) ≤ ((2 ^ 32 - 1 : ℕ) : ENNReal) := by
    exact_mod_cast Nat.sub_le_sub_left hr _
  refine le_trans (mul_le_mul' (mul_le_mul' hle le_rfl) le_rfl) ?_
  rw [kappa_exact]
  unfold SharedFtsCount.total SharedFtsCount.count
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]

theorem rc_rejection_real (n q : ℕ) (hq : 1 < q) (c a0 : ℝ) (hc : 0 < c) (ha0 : a0 * q ≤ n)
    (h : 1 / c ≤ (2.7182818283 : ℝ) ^ 2 * (a0 - 1)) : (1 - 1 / (q : ℝ)) ^ n ≤ c := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one hq0]; exact_mod_cast hq.le
  have hp : (1 - 1 / (q : ℝ)) ≤ Real.exp (-(1 / q)) := Real.one_sub_le_exp_neg _
  have h0 : (0 : ℝ) ≤ 1 - 1 / q := by linarith
  have hpow : (1 - 1 / (q : ℝ)) ^ n ≤ Real.exp (-(n / q)) := by
    calc (1 - 1 / (q : ℝ)) ^ n ≤ Real.exp (-(1 / q)) ^ n := pow_le_pow_left₀ h0 hp n
      _ = Real.exp (-(n / q)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have ha : a0 ≤ n / q := by rw [le_div_iff₀ hq0]; exact ha0
  have hexp : 1 / c ≤ Real.exp (n / q) :=
    h.trans ((PoissonReflect.exp_lower a0).trans (Real.exp_le_exp.mpr ha))
  rw [Real.exp_neg] at hpow
  refine hpow.trans ?_
  rw [one_div] at hexp
  exact inv_le_of_inv_le₀ hc hexp

theorem rc_u_cond (r : ℕ) (hr : r ≤ 18) :
    (1 - ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹) ^ (2 ^ 32 - r - 80) ≤
      ((13533530 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal) := by
  have hq : (1 : ℕ) < 2 ^ 31 - 1 := by norm_num
  have hrate : ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹ ≤ 1 := ENNReal.inv_le_one.2 (by exact_mod_cast hq.le)
  -- monotone in the exponent
  have hmono : (1 - ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹) ^ (2 ^ 32 - r - 80) ≤
      (1 - ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹) ^ (2 ^ 32 - 98) :=
    pow_le_pow_right_of_le_one' tsub_le_self (by omega)
  refine hmono.trans ?_
  have hfin : (1 - ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹) ^ (2 ^ 32 - 98) ≠ ⊤ :=
    ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  apply (ENNReal.toReal_le_toReal hfin (by finiteness)).mp
  rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hrate ENNReal.one_ne_top, ENNReal.toReal_inv,
    ENNReal.toReal_div]
  simp only [ENNReal.toReal_one, ENNReal.toReal_natCast]
  have := rc_rejection_real (2 ^ 32 - 98) (2 ^ 31 - 1) hq ((13533530 : ℝ) / 100000000)
    (((2 ^ 32 - 98 : ℕ) : ℝ) / ((2 ^ 31 - 1 : ℕ) : ℝ)) (by norm_num)
    (by rw [div_mul_cancel₀ _ (by norm_num)]) (by norm_num)
  simpa [one_div] using this

theorem rc_u_uncond :
    (1 - (2 ^ 31 : ENNReal)⁻¹) ^ (2 ^ 32 - 80) ≤ ((13533530 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal) := by
  refine (PoissonReflect.rejection_window_sharp (2 ^ 32) le_rfl).trans ?_
  apply ENNReal.div_le_div_right
  norm_num

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.RouteCData ClaudeWCT.Numerics.RouteCRows
open ClaudeWCT.Numerics.RouteCBank
open ClaudeWCT.Numerics.SharedMoments (forestMoment alphabetSize fieldSize priceScaleTotal)
open ClaudeWCT.Numerics.SharedCoverage (ForestHistory forestCoverage)
open SigGolfCandidate.T3.BPORS.History (atIndex)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem rc_c0 : (rcPar.c0 : ℝ) = 11 / 20 := by norm_num [rcPar]
theorem rc_a : (rcPar.a : ℝ) = 103 / 10 := by norm_num [rcPar]
theorem rc_θ : (rcPar.θ : ℝ) = 99847 / 50000 - 1 / 1024 := by norm_num [rcPar]
theorem rc_m : (rcPar.m : ℝ) = 459 / 500 := by norm_num [rcPar]
theorem rc_vv : (rcPar.vv : ℝ) = 151 / 20000 := by norm_num [rcPar]

theorem rc_frac (n d : ℕ) (hd : 0 < d) : ENNReal.ofReal ((n : ℝ) / d) = (n : ENNReal) / d := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hd), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

theorem priceBucket_nil : priceBucket [] = 0 := by
  have htot := SharedCoverage.forest_coverage_data ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563)
    WCTEnvelope.w1Table_wordDigit SharedMoments.rows_checked 0 (by norm_num)
  rw [forestMoment_zero] at htot
  let h0 : Fin 0 → Alphabet := Fin.elim0
  have hc : forestCoverage ClaudeWCT.WCT9.wordDigit (splitHistory h0) = 0 :=
    (Finset.sum_eq_zero_iff.mp htot) _ (Finset.mem_univ _)
  have hl : List.ofFn h0 = [] := List.ofFn_zero
  have := priceBucket_ofFn h0
  rw [hl, hc] at this
  simpa using this

theorem rc_conv_mean (L : List Alphabet) :
    min (priceBucket L) (ENNReal.ofReal rcPar.c0) = ENNReal.ofReal (costOf 0 rcPar (priceBucket L).toReal) := by
  show _ = ENNReal.ofReal (min (priceBucket L).toReal rcPar.c0)
  have hc : (0 : ℝ) ≤ rcPar.c0 := by rw [rc_c0]; norm_num
  rw [← ENNReal.toReal_ofReal hc, ← ENNReal.toReal_min (priceBucket_ne_top L) ENNReal.ofReal_ne_top,
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top (priceBucket_ne_top L) (min_le_left _ _)), ENNReal.toReal_ofReal hc]

theorem rc_conv_sec (L : List Alphabet) :
    min (priceBucket L) (ENNReal.ofReal rcPar.c0) ^ 2 = ENNReal.ofReal (costOf 1 rcPar (priceBucket L).toReal) := by
  show _ = ENNReal.ofReal (min (priceBucket L).toReal rcPar.c0 ^ 2)
  have hc : (0 : ℝ) ≤ rcPar.c0 := by rw [rc_c0]; norm_num
  rw [ENNReal.ofReal_pow (le_min ENNReal.toReal_nonneg hc)]
  exact congrArg (· ^ 2) (rc_conv_mean L)

theorem rc_conv_count (L : List Alphabet) :
    (if ENNReal.ofReal rcPar.c0 < priceBucket L then (1 : ENNReal) else 0) =
      ENNReal.ofReal (costOf 2 rcPar (priceBucket L).toReal) := by
  show _ = ENNReal.ofReal (if (rcPar.c0 : ℝ) < (priceBucket L).toReal then 1 else 0)
  have hc : (0 : ℝ) ≤ rcPar.c0 := by rw [rc_c0]; norm_num
  have hiff : ENNReal.ofReal rcPar.c0 < priceBucket L ↔ (rcPar.c0 : ℝ) < (priceBucket L).toReal :=
    ENNReal.ofReal_lt_iff_lt_toReal hc (priceBucket_ne_top L)
  by_cases h : (rcPar.c0 : ℝ) < (priceBucket L).toReal
  · rw [if_pos (hiff.mpr h), if_pos h, ENNReal.ofReal_one]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, ENNReal.ofReal_zero]

theorem rc_conv_over (L : List Alphabet) :
    priceBucket L - ENNReal.ofReal rcPar.c0 = ENNReal.ofReal (costOf 3 rcPar (priceBucket L).toReal) := by
  show _ = ENNReal.ofReal (max 0 ((priceBucket L).toReal - rcPar.c0))
  have hc : (0 : ℝ) ≤ rcPar.c0 := by rw [rc_c0]; norm_num
  rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_right zero_le, ENNReal.ofReal_sub _ hc,
    ENNReal.ofReal_toReal (priceBucket_ne_top L)]

theorem rc_conv_mgf (L : List Alphabet) :
    ENNReal.ofReal (Real.exp (rcPar.a * (min (priceBucket L) (ENNReal.ofReal rcPar.c0)).toReal)) - 1 =
      ENNReal.ofReal (costOf 4 rcPar (priceBucket L).toReal) := by
  show _ = ENNReal.ofReal (Real.exp (rcPar.a * min (priceBucket L).toReal rcPar.c0) - 1)
  have hc : (0 : ℝ) ≤ rcPar.c0 := by rw [rc_c0]; norm_num
  rw [ENNReal.toReal_min (priceBucket_ne_top L) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc,
    ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_one]

theorem rc_conv_scarf (L : List Alphabet) :
    (if L.length ≤ 18 ∧ ENNReal.ofReal rcPar.c0 < priceBucket L then
      ENNReal.ofReal (RouteC.scarf ((rcPar.θ : ℝ) - (priceBucket L).toReal) rcPar.m rcPar.vv) else 0) =
    (if L.length ≤ 18 then ENNReal.ofReal (costOf 5 rcPar (priceBucket L).toReal) else 0) := by
  have hc : (0 : ℝ) ≤ rcPar.c0 := by rw [rc_c0]; norm_num
  have hiff : ENNReal.ofReal rcPar.c0 < priceBucket L ↔ (rcPar.c0 : ℝ) < (priceBucket L).toReal :=
    ENNReal.ofReal_lt_iff_lt_toReal hc (priceBucket_ne_top L)
  show _ = (if L.length ≤ 18 then ENNReal.ofReal (if (rcPar.c0 : ℝ) < (priceBucket L).toReal then
    RouteC.scarf (rcPar.θ - (priceBucket L).toReal) rcPar.m rcPar.vv else 0) else 0)
  by_cases h18 : L.length ≤ 18
  · by_cases h : (rcPar.c0 : ℝ) < (priceBucket L).toReal
    · rw [if_pos ⟨h18, hiff.mpr h⟩, if_pos h18, if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h'.2)), if_pos h18, if_neg h, ENNReal.ofReal_zero]
  · rw [if_neg (fun h' => h18 h'.1), if_neg h18]

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.RouteCData ClaudeWCT.Numerics.RouteCRows
open ClaudeWCT.Numerics.RouteCBank
open ClaudeWCT.Numerics.SharedMoments (forestMoment alphabetSize fieldSize priceScaleTotal)
open SigGolfCandidate.T3.BPORS.History (atIndex)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem rc_card : (Fintype.card (Fin (2 ^ 31)) : ENNReal) = 2 ^ 31 := by
  rw [Fintype.card_fin]; norm_num


theorem rc_cardm1 : Fintype.card (Fin (2 ^ 31)) - 1 = 2 ^ 31 - 1 := by rw [Fintype.card_fin]

theorem rc_rate_cond : ((Fintype.card (Fin (2 ^ 31)) - 1 : ℕ) : ENNReal)⁻¹ ≤ 1 := by
  rw [rc_cardm1]; exact ENNReal.inv_le_one.2 (by norm_num)

theorem rc_prefactor (X : ENNReal) :
    ((Fintype.card (Fin (2 ^ 31)) - 1 : ℕ) : ENNReal) * X ≤ (2 ^ 31 : ENNReal) * X := by
  rw [rc_cardm1]
  exact mul_le_mul' (by norm_num) le_rfl

/-- Route C bank excess at the middle threshold (gate 804, `rcPar`): `≤ 1097/10^6 ≤ 147/125000`. -/
theorem rc_excess_middle :
    Law.lawAvg honestLaw (2 ^ 32) (fun W => price W - ENNReal.ofReal ((99847 : ℝ) / 50000 - 1 / 1024)) ≤
      ENNReal.ofReal ((147 : ℝ) / 125000) := by
  have hP := parFacts_of_ok rcPar par_ok
  have hc0 : (0 : ℝ) ≤ rcPar.c0 := hP.c0.le
  have he : (fun W : List Proposal => price W - ENNReal.ofReal ((99847 : ℝ) / 50000 - 1 / 1024)) =
      fun W => (∑ i : Fin (2 ^ 31), priceBucket (atIndex i W)) - ENNReal.ofReal (rcPar.θ : ℝ) := by
    funext W; rw [price_eq_sum, rc_θ]
  rw [he]
  have hcard : 1 < Fintype.card (Fin (2 ^ 31)) := by rw [Fintype.card_fin]; norm_num
  -- the seven envelope moments
  have hmgf : (∑ _i : Fin (2 ^ 31), Law.coordAverage (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹ honestCoordLaw
      (2 ^ 32) (fun L => ENNReal.ofReal (Real.exp (rcPar.a * (min (priceBucket L)
        (ENNReal.ofReal rcPar.c0)).toReal)) - 1)) ≤ ENNReal.ofReal ((118600 : ℕ) / (10000 : ℕ) : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, rc_card]
    simp_rw [rc_conv_mgf]
    rw [rc_frac _ _ (by norm_num)]
    exact rc_kind_all 4 runs4 glob4 Pack4 pack4_eq hP entries4 runs4_ok glob4_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ PoissonReflect.rate_le_one (2 ^ 32) rc_kappa_uncond rc_u_uncond 118600 10000 (by norm_num)
      env_mgf
  have hmean : ∀ r, 1 ≤ r → r ≤ 18 →
      ((Fintype.card (Fin (2 ^ 31)) - 1 : ℕ) : ENNReal) * Law.coordAverage
        ((Fintype.card (Fin (2 ^ 31)) - 1 : ℕ) : ENNReal)⁻¹ honestCoordLaw (2 ^ 32 - r)
        (fun L => min (priceBucket L) (ENNReal.ofReal rcPar.c0)) ≤ ENNReal.ofReal (rcPar.m : ℝ) := by
    intro r h1 h18
    simp_rw [rc_conv_mean]
    refine (rc_prefactor _).trans ?_
    rw [rc_m, show ((459 : ℝ) / 500) = ((459 : ℕ) : ℝ) / ((500 : ℕ) : ℝ) by norm_num, rc_frac _ _ (by norm_num)]
    exact rc_kind_all 0 runs0 glob0 Pack0 pack0_eq hP entries0 runs0_ok glob0_ok (by decide +kernel)
      (by decide +kernel) _ rc_rate_cond (2 ^ 32 - r) (by rw [rc_cardm1]; exact rc_kappa_cond r h1)
      (by rw [rc_cardm1]; exact rc_u_cond r h18) 459 500 (by norm_num) env_mean
  have hsecond : ∀ r, 1 ≤ r → r ≤ 18 →
      ((Fintype.card (Fin (2 ^ 31)) - 1 : ℕ) : ENNReal) * Law.coordAverage
        ((Fintype.card (Fin (2 ^ 31)) - 1 : ℕ) : ENNReal)⁻¹ honestCoordLaw (2 ^ 32 - r)
        (fun L => min (priceBucket L) (ENNReal.ofReal rcPar.c0) ^ 2) ≤ ENNReal.ofReal (rcPar.vv : ℝ) := by
    intro r h1 h18
    simp_rw [rc_conv_sec]
    refine (rc_prefactor _).trans ?_
    rw [rc_vv, show ((151 : ℝ) / 20000) = ((7550 : ℕ) : ℝ) / ((1000000 : ℕ) : ℝ) by norm_num, rc_frac _ _ (by norm_num)]
    exact rc_kind_all 1 runs1 glob1 Pack1 pack1_eq hP entries1 runs1_ok glob1_ok (by decide +kernel)
      (by decide +kernel) _ rc_rate_cond (2 ^ 32 - r) (by rw [rc_cardm1]; exact rc_kappa_cond r h1)
      (by rw [rc_cardm1]; exact rc_u_cond r h18) 7550 1000000 (by norm_num) env_sec
  have hK1 : (Fintype.card (Fin (2 ^ 31)) : ENNReal) * Law.coordAverage (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹
      honestCoordLaw (2 ^ 32) (fun L => if L.length ≤ 18 ∧ ENNReal.ofReal rcPar.c0 < priceBucket L then
        ENNReal.ofReal (RouteC.scarf ((rcPar.θ : ℝ) - (priceBucket L).toReal) rcPar.m rcPar.vv) else 0) ≤
      ENNReal.ofReal ((104145 : ℕ) / (100000000 : ℕ) : ℝ) := by
    simp_rw [rc_conv_scarf]
    rw [rc_card, rc_frac _ _ (by norm_num)]
    exact rc_kind_short runs5 glob5 Pack5 pack5_eq hP entries5 runs5_ok glob5_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ PoissonReflect.rate_le_one (2 ^ 32) rc_kappa_uncond rc_u_uncond 104145 100000000 (by norm_num)
      env_scarf
  have hover : (Fintype.card (Fin (2 ^ 31)) : ENNReal) * Law.coordAverage (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹
      honestCoordLaw (2 ^ 32) (fun L => priceBucket L - ENNReal.ofReal rcPar.c0) ≤
      ENNReal.ofReal ((22238 : ℕ) / (10000000 : ℕ) : ℝ) := by
    simp_rw [rc_conv_over]
    rw [rc_card, rc_frac _ _ (by norm_num)]
    exact rc_kind_all 3 runs3 glob3 Pack3 pack3_eq hP entries3 runs3_ok glob3_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ PoissonReflect.rate_le_one (2 ^ 32) rc_kappa_uncond rc_u_uncond 22238 10000000 (by norm_num)
      env_over
  have hcount : (Fintype.card (Fin (2 ^ 31)) : ENNReal) * Law.coordAverage (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹
      honestCoordLaw (2 ^ 32) (fun L => if ENNReal.ofReal rcPar.c0 < priceBucket L then 1 else 0) ≤
      ENNReal.ofReal ((48906 : ℕ) / (10000000 : ℕ) : ℝ) := by
    simp_rw [rc_conv_count]
    rw [rc_card, rc_frac _ _ (by norm_num)]
    exact rc_kind_all 2 runs2 glob2 Pack2 pack2_eq hP entries2 runs2_ok glob2_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ PoissonReflect.rate_le_one (2 ^ 32) rc_kappa_uncond rc_u_uncond 48906 10000000 (by norm_num)
      env_count
  have htail : (Fintype.card (Fin (2 ^ 31)) : ENNReal) * Law.coordAverage (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹
      honestCoordLaw (2 ^ 32) (fun L => if 18 < L.length then priceBucket L else 0) ≤
      ENNReal.ofReal ((37451 : ℕ) / (1000000000 : ℕ) : ℝ) := by
    rw [rc_card, rc_frac _ _ (by norm_num)]
    exact rc_long (2 ^ 31 : ENNReal)⁻¹ PoissonReflect.rate_le_one (2 ^ 32) rc_kappa_uncond rc_u_uncond 37451 1000000000 (by norm_num) env_long
  have key := RouteC.excess_route_c honestCoordLaw honestCoordLaw_sum hcard (2 ^ 32) 18 priceBucket
    priceBucket_ne_top (fun L b R => priceBucket_insert L R b) (rcPar.c0 : ℝ) (rcPar.θ : ℝ) (rcPar.a : ℝ)
    ((118600 : ℕ) / (10000 : ℕ) : ℝ) (rcPar.m : ℝ) (rcPar.vv : ℝ) ((104145 : ℕ) / (100000000 : ℕ) : ℝ)
    ((22238 : ℕ) / (10000000 : ℕ) : ℝ) ((48906 : ℕ) / (10000000 : ℕ) : ℝ) ((37451 : ℕ) / (1000000000 : ℕ) : ℝ)
    (by rw [rc_θ]; norm_num) (by rw [rc_a]; norm_num) (by positivity) hP.m hP.vv (by positivity) (by positivity)
    (by positivity) (by positivity) (by rw [priceBucket_nil]; exact zero_le) hmgf hmean hsecond hK1 hover hcount htail
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [rc_a, rc_θ]
  set E := Real.exp (((118600 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) - 103 / 10 * (99847 / 50000 - 1 / 1024)) with hEdef
  have hE : E ≤ 1 / 5300 := by
    have h86 : ((118600 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) - 103 / 10 * (99847 / 50000 - 1 / 1024) ≤
        -(8 + 6 / 10) := by
      norm_num
    refine (Real.exp_le_exp.mpr h86).trans ?_
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num), Real.exp_add]
    have he1 := Real.exp_one_gt_d9
    have h81 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : (2.7182818283 : ℝ) ^ 8 ≤ Real.exp 8 := by
      rw [h81]; exact pow_le_pow_left₀ (by norm_num) he1.le 8
    have h6 : 1 + 6 / 10 + (6 / 10 : ℝ) ^ 2 / 2 ≤ Real.exp (6 / 10) :=
      Real.quadratic_le_exp_of_nonneg (by norm_num)
    have h3 : ((1 : ℝ) / 5300)⁻¹ ≤ (2.7182818283 : ℝ) ^ 8 * (1 + 6 / 10 + (6 / 10 : ℝ) ^ 2 / 2) := by
      norm_num
    exact h3.trans (mul_le_mul h2 h6 (by norm_num) (Real.exp_pos 8).le)
  have hk : (3 : ℝ) / (8 * (103 / 10)) * E ≤ 3 / (8 * (103 / 10)) * (1 / 5300) :=
    mul_le_mul_of_nonneg_left hE (by norm_num)
  have hc : (3 : ℝ) / (8 * (103 / 10)) * (1 / 5300) + ((104145 : ℕ) : ℝ) / ((100000000 : ℕ) : ℝ) +
      ((22238 : ℕ) : ℝ) / ((10000000 : ℕ) : ℝ) * (((48906 : ℕ) : ℝ) / ((10000000 : ℕ) : ℝ)) +
      ((37451 : ℕ) : ℝ) / ((1000000000 : ℕ) : ℝ) ≤ 1097 / 1000000 := by norm_num
  have hb : (1097 : ℝ) / 1000000 ≤ 147 / 125000 := by norm_num
  linarith

#print axioms rc_excess_middle
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.RouteCData ClaudeWCT.Numerics.RouteCRows
open ClaudeWCT.Numerics.RouteCBank
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem rc_excess_high :
    Law.lawAvg honestLaw (2 ^ 32) (fun W => price W - ENNReal.ofReal ((2 : ℝ) - 6 / 2500 - 1 / 1024)) ≤
      ENNReal.ofReal ((147 : ℝ) / 125000) :=
  (Law.lawAvg_mono _ _ (fun W => tsub_le_tsub_left
    (ENNReal.ofReal_le_ofReal (by norm_num : (99847 : ℝ) / 50000 - 1 / 1024 ≤ 2 - 6 / 2500 - 1 / 1024)) _)).trans
    rc_excess_middle

/-- The low threshold through the clipped Chernoff bound plus the excess over the clip. -/
theorem rc_excess_low :
    Law.lawAvg honestLaw (2 ^ 32) (fun W => price W - ENNReal.ofReal ((1 : ℝ) - 1 / 1024)) ≤
      ENNReal.ofReal ((49 : ℝ) / 100) := by
  have hP := parFacts_of_ok rcPar par_ok
  apply price_excess_of_bucket_bounds (2 ^ 32) (ENNReal.ofReal rcPar.c0) ENNReal.ofReal_ne_top
    (1 - 1 / 1024) (rcPar.a : ℝ) ((118600 : ℕ) / (10000 : ℕ) : ℝ) ((22238 : ℕ) / (10000000 : ℕ) : ℝ) (49 / 100)
    (by norm_num) (by rw [rc_a]; norm_num) (by positivity) (by positivity)
  · simp_rw [rc_conv_mgf]
    rw [rc_frac _ _ (by norm_num)]
    exact rc_kind_all 4 runs4 glob4 Pack4 pack4_eq hP entries4 runs4_ok glob4_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ PoissonReflect.rate_le_one (2 ^ 32) rc_kappa_uncond rc_u_uncond
      118600 10000 (by norm_num) env_mgf
  · simp_rw [rc_conv_over]
    rw [rc_frac _ _ (by norm_num)]
    exact rc_kind_all 3 runs3 glob3 Pack3 pack3_eq hP entries3 runs3_ok glob3_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ PoissonReflect.rate_le_one (2 ^ 32) rc_kappa_uncond rc_u_uncond
      22238 10000000 (by norm_num) env_over
  · rw [rc_a]
    set E := Real.exp (((118600 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) - 103 / 10 * (1 - 1 / 1024)) with hEdef
    have hE : E ≤ 8 := by
      have h1 : ((118600 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) - 103 / 10 * (1 - 1 / 1024) ≤ 2 := by norm_num
      have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have h3 : Real.exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
      have h4 : (2.7182818286 : ℝ) ^ 2 ≤ 8 := by norm_num
      exact (Real.exp_le_exp.mpr h1).trans (by rw [h2]; linarith)
    have hk : (3 : ℝ) / (8 * (103 / 10)) * E ≤ 3 / (8 * (103 / 10)) * 8 :=
      mul_le_mul_of_nonneg_left hE (by norm_num)
    have hc : (3 : ℝ) / (8 * (103 / 10)) * 8 + ((22238 : ℕ) : ℝ) / ((10000000 : ℕ) : ℝ) ≤ 49 / 100 := by
      norm_num
    linarith

/-! Installed names (now proved by route C). -/

theorem excess_middle_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((99847:ℝ)/50000-1/1024)) ≤
        ENNReal.ofReal ((147:ℝ)/125000) := rc_excess_middle

theorem excess_high_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((2:ℝ)-6/2500-1/1024)) ≤
        ENNReal.ofReal ((147:ℝ)/125000) := rc_excess_high

theorem excess_low_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((1:ℝ)-1/1024)) ≤
        ENNReal.ofReal ((49:ℝ)/100) := rc_excess_low

theorem excess_large_certified (y : ℝ)
    (hy0 : 3/2500 ≤ y) (hy1 : y ≤ 1/2) :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal (2-2*y-1/1024)) ≤
        ENNReal.ofReal ((49/50)*y) := by
  let t : ℝ := (y-3/2500)/(1/2-3/2500)
  have ht0 : 0≤t := div_nonneg (sub_nonneg.mpr hy0) (by norm_num)
  have ht1 : t≤1 := (div_le_one (by norm_num : (0:ℝ)<1/2-3/2500)).2 (by linarith)
  have h := price_excess_affine (2^32) (2-6/2500-1/1024) (1-1/1024)
    (147/125000) (49/100) t (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ht0 ht1 excess_high_certified excess_low_certified
  have harg : (1-t)*(2-6/2500-1/1024)+t*(1-1/1024) = 2-2*y-1/1024 := by
    dsimp [t]; ring
  have hval : (1-t)*(147/125000)+t*(49/100)=(49/50)*y := by dsimp [t]; ring
  simpa only [harg,hval] using h

theorem excess_tiny_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W=>price W-ENNReal.ofReal ((249:ℝ)/125-1/1024)) ≤
        ENNReal.ofReal ((18:ℝ)/5000) := by
  have h:=price_excess_affine (2^32) (99847/50000-1/1024) (1-1/1024)
    (147/125000) (49/100) (247/49847) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    excess_middle_certified excess_low_certified
  have ht:(1-(247:ℝ)/49847)*(99847/50000-1/1024)+(247/49847)*(1-1/1024)=249/125-1/1024:=by norm_num
  rw[ht] at h
  exact h.trans (ENNReal.ofReal_le_ofReal (by norm_num))

#print axioms rc_excess_low
#print axioms excess_large_certified
#print axioms excess_tiny_certified
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Numerics.WCTPrice
open Finset ENNReal
open ClaudeWCT.Numerics.Law (lawAvg marked)
open SphincsSecurity.Concrete (uniformWordAverage)
open ClaudeWCT.Bank.WCT (WProposal price ExcessBound)
open ClaudeWCT.WCT9 (wordDigit Coord Child Rank)
open ClaudeWCT.Numerics.WCTEnvelope
theorem price_fun_eq : price = N600.priceN wordDigit := funext price_eq
section Window
variable {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32)
include hT1 hT2
theorem wct_price_excess_law {law : (Coord → Child × Rank) → ENNReal} {κ : ENNReal} (hlaw : N600.LawOK law κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) law) T (fun W : List WProposal => price W - 1023 / 1024) ≤
      247 / 100000 := by
  rw [price_fun_eq]
  exact N600.law_price_excess_le wordDigit hT1 hT2 card_rank card_child w1Table_wordDigit w2Table_wordDigit hlaw
theorem wct_price_excess_law_54 {law : (Coord → Child × Rank) → ENNReal} {κ : ENNReal} (hlaw : N600.LawOK law κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) law) T (fun W : List WProposal => price W - 2031 / 1024) ≤
      23 / 100000 := by
  rw [price_fun_eq]
  exact N600.law_price_excess_winsor wordDigit wordsOf_wordDigit ClaudeWCT.WCT9.wordDigit_le_four card_rank w1Table_wordDigit hlaw T hT1 hT2
theorem wct_near_law {law : (Coord → Child × Rank) → ENNReal} {κ : ENNReal} (hlaw : N600.LawOK law κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) law) T (N600.nearPriceN (C := Child) wordDigit) ≤ 300 - 1 / 16 :=
  (N600.law_nearPrice_le wordDigit hT1 hT2 card_rank card_child w1Table_wordDigit wfTable_wordDigit hlaw).trans
    N600.near_le_sub
theorem wct_excessBound_window : ExcessBound T (247 / 100000) :=
  ClaudeWCT.Bank.WCT.excessBound_of_honest (wct_price_excess_law hT1 hT2 N600Cap.lawOK_honest)
end Window
theorem wct_excessBound_2_32 : ExcessBound (2 ^ 32) (247 / 100000) :=
  wct_excessBound_window le_rfl (by norm_num)
theorem wct_excess_honest_2_32_54 :
    lawAvg (marked (α := Fin (2 ^ 31)) N600Cap.honestLaw) (2 ^ 32)
      (fun W : List WProposal => price W - 2031 / 1024) ≤ 23 / 100000 :=
  wct_price_excess_law_54 le_rfl (by norm_num) N600Cap.lawOK_honest
theorem wct_near_honest_2_32 :
    lawAvg (marked (α := Fin (2 ^ 31)) N600Cap.honestLaw) (2 ^ 32) (N600.nearPriceN (C := Child) wordDigit) ≤
      300 - 1 / 16 :=
  wct_near_law le_rfl (by norm_num) N600Cap.lawOK_honest
end ClaudeWCT.Numerics.WCTPrice
