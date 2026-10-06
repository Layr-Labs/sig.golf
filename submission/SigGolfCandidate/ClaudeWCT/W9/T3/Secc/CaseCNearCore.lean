import SigGolfCandidate.ClaudeWCT.Numerics.WCTPrice
import SigGolfCandidate.ClaudeWCT.GuessV2.NearScore
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCFull

section
namespace ClaudeWCT.W9.T3.Security.CaseC
open Finset ENNReal
open ClaudeWCT.Numerics.Thinning (ListCovExcept nearEnv)
open SigGolfResearch.Gate6.Moments (finiteAverage)
open SigGolfCandidate.T3.BPORS.History (atIndex)
open SigGolfCandidate.T3 (HashOutput)
open ClaudeWCT.Bank.WCT (WProposal proposal outIdx SlotCoveredP)
open ClaudeWCT.WCT9 (wordDigit Child)
open ClaudeWCT.Guess (nearScore nearPrice NearCoveredAt)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
theorem guess_slotCovered_iff (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 7) :
    ClaudeWCT.Guess.SlotCovered X N k t ↔ ClaudeWCT.Bank.WCT.SlotCovered X N k t := by
  unfold ClaudeWCT.Guess.SlotCovered ClaudeWCT.Bank.WCT.SlotCovered
  refine exists_congr fun x => and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  simp only [outIdx, Fin.mk.injEq]
theorem slotCoveredP_iff_atIndex (W : List WProposal) (N : HashOutput) (k : Fin 9) (t : Fin 7) :
    SlotCoveredP W N k t ↔
      ∃ e ∈ atIndex (outIdx N) W, (e k).1 = ((proposal N).2 k).1 ∧
        wordDigit ((proposal N).2 k).2 t ≤ wordDigit (e k).2 t := by
  constructor
  · rintro ⟨p, hp, h1, h2, h3⟩
    refine ⟨p.2, (ClaudeWCT.Numerics.WCTEnvelope.mem_atIndex _ _ _).mpr ?_, h2, h3⟩
    rw [← h1]
    exact hp
  · rintro ⟨e, he, h2, h3⟩
    exact ⟨(outIdx N, e), (ClaudeWCT.Numerics.WCTEnvelope.mem_atIndex _ _ _).mp he, rfl, h2, h3⟩
theorem nearCoveredAt_iff (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 7) :
    NearCoveredAt X N k t ↔
      ListCovExcept wordDigit k t (atIndex (outIdx N) (X.map proposal)) (proposal N).2 := by
  unfold NearCoveredAt ListCovExcept
  refine forall_congr' fun k' => forall_congr' fun t' => imp_congr_right fun _ => ?_
  rw [guess_slotCovered_iff, ClaudeWCT.Bank.WCT.slotCovered_iff, slotCoveredP_iff_atIndex]
noncomputable abbrev nearPriceP (W : List WProposal) : ENNReal :=
  ClaudeWCT.Numerics.N600.nearPriceN (C := Child) wordDigit W
theorem nearPrice_eq_nearPriceP (X : List HashOutput) :
    nearPrice X = nearPriceP (X.map proposal) := by
  classical
  set W : List WProposal := X.map proposal with hW
  set g : WProposal → ENNReal := fun p => ∑ k : Fin 9, ∑ t : Fin 7,
    if ListCovExcept wordDigit k t (atIndex p.1 W) p.2 then 1 else 0 with hg
  have hs : ∀ N, nearScore X N = if ClaudeWCT.WCT9.admissible N = true then g (proposal N) else 0 := by
    intro N
    unfold nearScore
    by_cases hadm : ClaudeWCT.WCT9.admissible N = true
    · simp only [hadm, if_true, hg]
      exact sum_congr rfl fun k _ => sum_congr rfl fun t _ =>
        if_congr (nearCoveredAt_iff X N k t) rfl rfl
    · simp [hadm]
  have hsum : ∑ p, g p = ((ClaudeWCT.Numerics.N600.Q ^ 9 : ℕ) : ENNReal) *
      ∑ index : Fin (2 ^ 31), ∑ k : Fin 9, ∑ t : Fin 7, nearEnv wordDigit k t (atIndex index W) := by
    simp only [hg]
    rw [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun index _ => ?_
    rw [Finset.sum_comm, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm, mul_sum]
    refine sum_congr rfl fun t _ => ?_
    unfold nearEnv finiteAverage
    rw [ClaudeWCT.Numerics.WCTEnvelope.card_coords,
      ENNReal.mul_div_cancel (by simp [ClaudeWCT.Numerics.N600.Q]) (by simp)]
  unfold nearPrice SigGolfCandidate.T3.BPORS.finiteAverage
  simp_rw [hs]
  rw [ClaudeWCT.Bank.WCT.sum_admissible g, hsum, Fintype.card_bitVec, nearPriceP,
    ClaudeWCT.Numerics.N600.nearPriceN, ← ClaudeWCT.Numerics.WCTEnvelope.price_scale]
  simp only [div_eq_mul_inv]
  ring
theorem near_bound_add_charge : (6463 / 16 : ENNReal) + 1 / 16 = 404 := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div]
theorem near_bound_eq_sub : (6463 / 16 : ENNReal) = 404 - 1 / 16 := by
  rw [← near_bound_add_charge]
  exact (ENNReal.add_sub_cancel_right (by finiteness)).symm
theorem wct_near_bound_2_32 :
    ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.WCT.honestLaw (2 ^ 32) nearPriceP ≤ 6463 / 16 := by
  rw [near_bound_eq_sub, ClaudeWCT.Bank.WCT.honestLaw_eq_n4]
  exact ClaudeWCT.Numerics.WCTPrice.wct_near_honest_2_32
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (BankCore BankCore.expose expectedValue_add_const_le
  pmf_expectedValue_left_mul expectedValue_list_sum' finiteAverage_expectedValue)
open SphincsSecurity.Concrete (independentProposalWord uniformWordAverage)
open ClaudeWCT.Bank.WCT (WProposal)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable abbrev nearSpec : ClaudeWCT.Bank.FtsBankSpec WProposal := bankSpec.toFtsBankSpec
theorem nearSpec_admissible : nearSpec.admissible = WCT9.admissible := rfl
theorem nearSpec_law : nearSpec.law = ClaudeWCT.Bank.WCT.honestLaw := rfl
theorem nearSpec_proposals (X : List HashOutput) : nearSpec.proposals X = X.map ClaudeWCT.Bank.WCT.proposal := rfl
theorem nearPrice_proposals (X : List HashOutput) :
    Guess.nearPrice X = nearPriceP (nearSpec.proposals X) :=
  nearPrice_eq_nearPriceP X
noncomputable def nearForecast (R : Nat) (X : List HashOutput) (N : HashOutput) : ENNReal :=
  expectedValue (independentProposalWord nearSpec.accepted R) (fun F => Guess.nearScore (X ++ F) N)
theorem nearForecast_step (R : Nat) (X : List HashOutput) (N : HashOutput) :
    expectedValue nearSpec.accepted (fun A => nearForecast R (X ++ [A]) N) = nearForecast (R + 1) X N := by
  unfold nearForecast
  rw [independentProposalWord, ← PMF.monad_bind_eq_bind, expectedValue_bind]
  apply congrArg
  funext A
  rw [← PMF.monad_map_eq_map, expectedValue_map]
  apply congrArg
  funext F
  simp only [List.append_assoc, List.singleton_append]
theorem nearScore_le_forecast (R : Nat) (X : List HashOutput) (N : HashOutput) :
    Guess.nearScore X N ≤ nearForecast R X N := by
  unfold nearForecast
  calc
    Guess.nearScore X N = expectedValue (independentProposalWord nearSpec.accepted R) (fun _ => Guess.nearScore X N) :=
      (expectedValue_const (by simp) _).symm
    _ ≤ _ := expectedValue_mono _ fun F => Guess.nearScore_append_mono X F N
noncomputable def nearPriceForecast (R : Nat) (X : List HashOutput) : ENNReal :=
  ClaudeWCT.Numerics.Law.lawAvg nearSpec.law R (fun W => nearPriceP (nearSpec.proposals X ++ W))
theorem average_nearForecast (R : Nat) (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => nearForecast R X N) = nearPriceForecast R X / 2 ^ 128 := by
  unfold nearForecast nearPriceForecast
  rw [finiteAverage_expectedValue]
  have hav : ∀ F : List HashOutput, BPORS.finiteAverage (fun N : HashOutput => Guess.nearScore (X ++ F) N) =
      nearPriceP (nearSpec.proposals X ++ nearSpec.proposals F) / 2 ^ 128 := by
    intro F
    rw [Guess.average_nearScore, nearPrice_proposals, nearSpec.proposals_append]
  simp_rw [hav]
  refine (nearSpec.expected_word_proposals R
    (fun W => nearPriceP (nearSpec.proposals X ++ W) / 2 ^ 128)).trans ?_
  simp only [div_eq_mul_inv]
  rw [show (fun W => nearPriceP (nearSpec.proposals X ++ W) * (2 ^ 128 : ENNReal)⁻¹) =
      fun W => (2 ^ 128 : ENNReal)⁻¹ * nearPriceP (nearSpec.proposals X ++ W) by
    funext W; exact mul_comm _ _, ClaudeWCT.Numerics.Law.lawAvg_mul_left, mul_comm]
theorem nearPriceForecast_step (R : Nat) (X : List HashOutput) :
    expectedValue nearSpec.accepted (fun A => nearPriceForecast R (X ++ [A])) = nearPriceForecast (R + 1) X := by
  unfold nearPriceForecast
  rw [ClaudeWCT.Numerics.Law.lawAvg_succ]
  have hA (A : HashOutput) : ClaudeWCT.Numerics.Law.lawAvg nearSpec.law R
      (fun W => nearPriceP (nearSpec.proposals (X ++ [A]) ++ W)) =
      (fun p : WProposal => ClaudeWCT.Numerics.Law.lawAvg nearSpec.law R
        (fun W => nearPriceP (nearSpec.proposals X ++ p :: W))) (nearSpec.proposal A) := by
    simp [ClaudeWCT.Bank.FtsBankSpec.proposals, List.map_append, List.append_assoc]
  simp_rw [hA]
  exact nearSpec.expected_accepted_proposal (fun p => ClaudeWCT.Numerics.Law.lawAvg nearSpec.law R
    (fun W => nearPriceP (nearSpec.proposals X ++ p :: W)))
noncomputable def nearLedger (R : Nat) (targets X : List HashOutput) (slack : Nat) : ENNReal :=
  (targets.map fun N => nearForecast R X N).sum + (slack : ENNReal) * nearPriceForecast R X / 2 ^ 128
theorem nearLedger_slack_succ (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    nearLedger R targets X (slack + 1) = nearLedger R targets X slack + nearPriceForecast R X / 2 ^ 128 := by
  unfold nearLedger
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ENNReal.add_div, add_assoc]
theorem nearLedger_slack_mono (R : Nat) (targets X : List HashOutput) {slack slack' : Nat} (h : slack ≤ slack') :
    nearLedger R targets X slack ≤ nearLedger R targets X slack' := by
  unfold nearLedger
  apply add_le_add le_rfl
  apply ENNReal.div_le_div_right
  apply mul_le_mul' _ le_rfl
  exact_mod_cast h
theorem nearLedger_birth (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => nearLedger R (targets ++ [a]) X slack) =
      nearLedger R targets X (slack + 1) := by
  have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => nearForecast R X a) =
      nearPriceForecast R X / 2 ^ 128 := by
    rw [BPORS.expected_uniform_eq_finiteAverage]
    exact average_nearForecast R X
  have hsplit : ∀ a, nearLedger R (targets ++ [a]) X slack = nearLedger R targets X slack + nearForecast R X a := by
    intro a
    simp only [nearLedger, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero]
    ring
  simp_rw [hsplit]
  rw [expectedValue_add, expectedValue_const (by simp : Pr[⊥ | ($ᵗ HashOutput : ProbComp HashOutput)] = 0), hfa,
    nearLedger_slack_succ]
theorem nearLedger_expose (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue nearSpec.accepted (fun A => nearLedger R targets (X ++ [A]) slack) =
      nearLedger (R + 1) targets X slack := by
  unfold nearLedger
  rw [expectedValue_add, expectedValue_list_sum']
  refine congrArg₂ (· + ·) ?_ ?_
  · refine congrArg List.sum ?_
    apply List.map_congr_left
    intro N _
    exact nearForecast_step R X N
  · simp only [div_eq_mul_inv]
    rw [show (fun A : HashOutput => (slack : ENNReal) * nearPriceForecast R (X ++ [A]) * (2 ^ 128 : ENNReal)⁻¹) =
        fun A => (slack : ENNReal) * (2 ^ 128 : ENNReal)⁻¹ * nearPriceForecast R (X ++ [A]) by
      funext A; ring]
    rw [pmf_expectedValue_left_mul, nearPriceForecast_step]
    ring
theorem nearLedger_freshPrice (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    nearSpec.freshPrice (fun A => nearLedger R targets (X ++ [A]) slack) = nearLedger (R + 1) targets X slack := by
  rw [← nearSpec.expected_accepted, nearLedger_expose]
theorem nearLedger_search (secret : BitVec 256) (rho : Digest) (message : Message) (fuel : Nat)
    (hlimit : fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hreject : Sampling.CachedTrialsReject (Sampling.digestTrial rho message) nearSpec.decode 0 (2 ^ 32) cache)
    (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue (Sampling.roRun secret (nearSpec.search rho message 0 fuel) cache)
      (fun result => result.1.elim (nearLedger (R + 1) targets X slack)
        (fun found => nearLedger R targets (X ++ [found.2]) slack)) ≤ nearLedger (R + 1) targets X slack :=
  nearSpec.search_le_price secret rho message fuel hlimit cache hreject _ _ _ le_rfl
    (nearLedger_freshPrice R targets X slack).le
theorem nearLedger_win (R : Nat) (targets X : List HashOutput) (slack : Nat) (N : HashOutput) (hN : N ∈ targets)
    (hadm : WCT9.admissible N = true) (hcov : Guess.NearCoveredBy X N) : 1 ≤ nearLedger R targets X slack :=
  calc
    (1 : ENNReal) ≤ Guess.nearScore X N := Guess.one_le_nearScore hadm hcov
    _ ≤ nearForecast R X N := nearScore_le_forecast R X N
    _ ≤ (targets.map fun N => nearForecast R X N).sum := List.le_sum_of_mem (List.mem_map_of_mem hN)
    _ ≤ _ := le_self_add
theorem nearLedger_initial (budget : Nat) :
    nearLedger horizon [] [] budget ≤ (budget : ENNReal) * (6463 / 16) / 2 ^ 128 := by
  unfold nearLedger nearPriceForecast
  simp only [List.map_nil, List.sum_nil, zero_add]
  apply ENNReal.div_le_div_right
  apply mul_le_mul' le_rfl
  rw [nearSpec_law]
  exact wct_near_bound_2_32
noncomputable def nearPotential (b : BankCore) : ENNReal :=
  if horizon < b.exposures.length then 0
  else if b.reused = true then 1 + b.reuse
  else nearLedger (horizon - b.exposures.length) b.targets b.exposures b.slack + b.reuse
theorem nearPotential_mono (b b' : BankCore) (ht : b'.targets = b.targets) (hx : b'.exposures = b.exposures)
    (hr : b'.reused = b.reused) (hC : b'.reuse ≤ b.reuse) (hs : b'.slack ≤ b.slack) :
    nearPotential b' ≤ nearPotential b := by
  unfold nearPotential
  rw [ht, hx, hr]
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl hC
  · exact add_le_add (nearLedger_slack_mono _ _ _ hs) hC
theorem expected_admInd_sixteenth :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) nearSpec.admInd ≤ 1 / 16 :=
  nearSpec.expected_admInd_tight.trans (ENNReal.div_le_div_left (by norm_num) 1)
theorem near_birth (b : BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + nearSpec.admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => nearPotential { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      nearPotential b + (1 / 16) / 2 ^ 128 := by
  have hadm : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun N => nearSpec.admInd N / 2 ^ 128) ≤
      (1 / 16) / 2 ^ 128 := by
    simp only [div_eq_mul_inv]
    rw [expectedValue_mul_const]
    exact mul_le_mul' (by simpa [div_eq_mul_inv] using expected_admInd_sixteenth) le_rfl
  unfold nearPotential
  simp only
  by_cases hd : horizon < b.exposures.length
  · simp only [hd, if_true]
    exact (expectedValue_le_of_le _ fun _ => le_rfl).trans bot_le
  simp only [hd, if_false]
  by_cases hr : b.reused = true
  · simp only [hr, if_true]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => nearSpec.admInd N / 2 ^ 128 + (1 + b.reuse)) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ (1 / 16) / 2 ^ 128 + (1 + b.reuse) := (expectedValue_add_const_le _ _ _).trans (add_le_add hadm le_rfl)
      _ = _ := add_comm _ _
  · simp only [hr, Bool.false_eq_true, if_false]
    set R := horizon - b.exposures.length
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => (nearLedger R (b.targets ++ [N]) b.exposures s + nearSpec.admInd N / 2 ^ 128) + b.reuse) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => nearLedger R (b.targets ++ [N]) b.exposures s + nearSpec.admInd N / 2 ^ 128) + b.reuse :=
        expectedValue_add_const_le _ _ _
      _ ≤ (nearLedger R b.targets b.exposures (s + 1) + (1 / 16) / 2 ^ 128) + b.reuse := by
        rw [expectedValue_add, nearLedger_birth]
        exact add_le_add (add_le_add le_rfl hadm) le_rfl
      _ = _ := by
        rw [hs]
        ring
theorem near_sign (b : BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + nearSpec.reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat) (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if nearSpec.Reuse cache rho m then nearPotential { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (nearSpec.search rho m 0 fuel) cache)
        (fun result => nearPotential (b.expose C' (result.1.map Prod.snd)))) ≤ nearPotential b := by
  have hlenA : ∀ (o : Option HashOutput), b.exposures.length ≤ (b.exposures ++ o.toList).length := by
    intro o; simp
  by_cases hd : horizon < b.exposures.length
  · apply expectedValue_le_of_le
    intro rho
    have h0 : ∀ (o : Option HashOutput), nearPotential (b.expose C' o) = 0 := by
      intro o
      unfold nearPotential BankCore.expose
      simp only
      rw [if_pos (lt_of_lt_of_le hd (hlenA o))]
    split_ifs
    · unfold nearPotential; simp only; rw [if_pos hd]; exact bot_le
    · exact (expectedValue_le_of_le _ fun result => (h0 _).le).trans bot_le
  by_cases hr : b.reused = true
  · have hb : nearPotential b = 1 + b.reuse := by unfold nearPotential; simp [hd, hr]
    rw [hb]
    apply expectedValue_le_of_le
    intro rho
    have hle : ∀ (o : Option HashOutput), nearPotential (b.expose C' o) ≤ 1 + b.reuse := by
      intro o
      unfold nearPotential BankCore.expose
      simp only [hr, if_true]
      split_ifs
      · exact bot_le
      · exact add_le_add le_rfl (le_of_add_le_left hC)
    split_ifs
    · unfold nearPotential; simp only [hd, if_false, if_true]; exact add_le_add le_rfl (le_of_add_le_left hC)
    · exact expectedValue_le_of_le _ fun result => hle _
  have hr' : b.reused = false := by simpa using hr
  set R0 := horizon - b.exposures.length with hR0
  have hb : nearPotential b = nearLedger R0 b.targets b.exposures b.slack + b.reuse := by
    unfold nearPotential; simp only [hd, hr', if_false, Bool.false_eq_true]; rfl
  have hsearch : ∀ rho, ¬nearSpec.Reuse cache rho m →
      expectedValue (Sampling.roRun secret (nearSpec.search rho m 0 fuel) cache)
        (fun result => nearPotential (b.expose C' (result.1.map Prod.snd))) ≤
          nearLedger R0 b.targets b.exposures b.slack + C' := by
    intro rho hnr
    have hrej : Sampling.CachedTrialsReject (Sampling.digestTrial rho m) nearSpec.decode 0 (2 ^ 32) cache := by
      unfold ClaudeWCT.Bank.FtsBankSpec.Reuse at hnr; push Not at hnr; exact hnr
    by_cases hlen : b.exposures.length < horizon
    · obtain ⟨R, hR⟩ : ∃ R, R0 = R + 1 := ⟨R0 - 1, by omega⟩
      calc
        _ ≤ expectedValue (Sampling.roRun secret (nearSpec.search rho m 0 fuel) cache)
            (fun result => result.1.elim (nearLedger (R + 1) b.targets b.exposures b.slack)
              (fun found => nearLedger R b.targets (b.exposures ++ [found.2]) b.slack) + C') := by
          apply expectedValue_mono
          intro result
          rcases result with ⟨_ | found, cache'⟩
          · unfold nearPotential BankCore.expose
            simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr',
              Bool.false_eq_true, Option.elim_none]
            rw [← hR]
          · unfold nearPotential BankCore.expose
            have hnd : ¬horizon < (b.exposures ++ [found.2]).length := by simp; omega
            simp only [Option.map_some, Option.toList_some, hnd, if_false, hr', Bool.false_eq_true,
              Option.elim_some]
            rw [show horizon - (b.exposures ++ [found.2]).length = R by simp; omega]
        _ ≤ nearLedger (R + 1) b.targets b.exposures b.slack + C' :=
          (expectedValue_add_const_le _ _ _).trans
            (add_le_add (nearLedger_search secret rho m fuel hfuel cache hrej R b.targets b.exposures b.slack) le_rfl)
        _ = _ := by rw [hR]
    · apply expectedValue_le_of_le
      intro result
      rcases result with ⟨_ | found, cache'⟩
      · unfold nearPotential BankCore.expose
        simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr', Bool.false_eq_true]
        exact le_rfl
      · unfold nearPotential BankCore.expose
        have hnd : horizon < (b.exposures ++ [found.2]).length := by simp; omega
        simp only [Option.map_some, Option.toList_some, hnd, if_true]
        exact bot_le
  rw [hb]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest)
        (fun rho => (if nearSpec.Reuse cache rho m then 1 else 0) + (nearLedger R0 b.targets b.exposures b.slack + C')) := by
      apply expectedValue_mono
      intro rho
      by_cases hre : nearSpec.Reuse cache rho m
      · rw [if_pos hre, if_pos hre]
        unfold nearPotential
        simp only [hd, if_false, if_true]
        exact add_le_add le_rfl le_add_self
      · rw [if_neg hre, if_neg hre, zero_add]
        exact hsearch rho hre
    _ ≤ nearSpec.reuseMass cache m + (nearLedger R0 b.targets b.exposures b.slack + C') :=
      (expectedValue_add_const_le _ _ _).trans (add_le_add (nearSpec.reuse_probability_le cache m) le_rfl)
    _ ≤ _ := by
      rw [add_comm (nearLedger _ _ _ _), ← add_assoc, add_comm (nearSpec.reuseMass cache m),
        add_comm _ (nearLedger _ _ _ _)]
      exact add_le_add le_rfl hC
theorem near_win (b : BankCore) (halive : ¬horizon < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, WCT9.admissible N = true ∧ Guess.NearCoveredBy b.exposures N) :
    1 ≤ nearPotential b := by
  unfold nearPotential
  rw [if_neg halive]
  by_cases hr : b.reused = true
  · rw [if_pos hr]; exact le_self_add
  · rw [if_neg hr]
    obtain ⟨N, hN, hadm, hcov⟩ := h.resolve_left hr
    exact (nearLedger_win _ _ _ _ N hN hadm hcov).trans le_self_add
theorem near_initial (budget : Nat) :
    nearPotential ⟨[], [], false, 0, budget⟩ ≤ (budget : ENNReal) * (6463 / 16) / 2 ^ 128 := by
  unfold nearPotential
  simp only [List.length_nil, Nat.not_lt_zero, if_false, Bool.false_eq_true, Nat.sub_zero, add_zero]
  exact nearLedger_initial budget
end ClaudeWCT.W9.T3.Security.CaseC
end
