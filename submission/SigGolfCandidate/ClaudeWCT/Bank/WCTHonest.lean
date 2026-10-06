import SigGolfCandidate.ClaudeWCT.Bank.WCTAccept
import SigGolfCandidate.ClaudeWCT.Numerics.N600Cap

namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open ClaudeWCT.WCT9 (Coord Child Rank child rank)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
theorem capOk_eq_capOkC (x : HashOutput) : WCT9.capOk x = capOkC (proposal x).2 := by
  unfold WCT9.capOk capOkC
  rw [WCT9.jointCost_eq_sum]
  rfl
theorem producerAdmissible_eq (x : HashOutput) :
    WCT9.producerAdmissible x = (WCT9.admissible x && capOkC (proposal x).2) := by
  unfold WCT9.producerAdmissible
  rw [capOk_eq_capOkC]
theorem sum_producer (g : WProposal → ENNReal) :
    (∑ x : HashOutput, if WCT9.producerAdmissible x = true then g (proposal x) else 0) =
      ((27 ^ 9 * 1137 * 2 ^ 15 : Nat) : ENNReal) * ∑ p : WProposal, if capOkC p.2 = true then g p else 0 := by
  rw [← sum_admissible (fun p => if capOkC p.2 = true then g p else 0)]
  apply Finset.sum_congr rfl
  intro x _
  rw [producerAdmissible_eq]
  cases WCT9.admissible x <;> cases capOkC (proposal x).2 <;> rfl
theorem capSet_mem (c : Coords) : c ∈ capSet ↔ capOkC c = true := by
  simp [capSet]
theorem routineCost_zero : WCT9.routineCost 0 = 67 := rfl
theorem capOkC_of_rank_zero (c : Coords) (hc : ∀ k, (c k).2 = 0) : capOkC c = true := by
  unfold capOkC
  rw [decide_eq_true_iff]
  simp only [hc, routineCost_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  decide
theorem capOkC_zero : capOkC (fun _ => ((0 : Child), (0 : Rank))) = true :=
  capOkC_of_rank_zero _ fun _ => rfl
theorem capSet_nonempty : capSet.Nonempty := by
  refine ⟨fun _ => ((0 : Child), (0 : Rank)), ?_⟩
  rw [capSet_mem]
  exact capOkC_zero
theorem capSet_card_ne_zero : (capSet.card : ENNReal) ≠ 0 := by
  exact_mod_cast (Finset.card_pos.mpr capSet_nonempty).ne'
theorem capSet_card_ne_top : (capSet.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
theorem sum_capOkC (h : Coords → ENNReal) :
    (∑ c : Coords, if capOkC c = true then h c else 0) = ∑ c ∈ capSet, h c := by
  rw [← Finset.sum_filter]
  rfl
theorem sum_capOkC_one : (∑ c : Coords, if capOkC c = true then (1 : ENNReal) else 0) = capSet.card := by
  rw [Finset.sum_boole]
  rfl
theorem honestCoordLaw_sum : ∑ c, honestCoordLaw c = 1 := by
  unfold honestCoordLaw
  rw [sum_capOkC (fun _ => (capSet.card : ENNReal)⁻¹), Finset.sum_const, nsmul_eq_mul,
    ENNReal.mul_inv_cancel capSet_card_ne_zero capSet_card_ne_top]
theorem honestLawSum : HonestLawSum := by
  have h := ClaudeWCT.Numerics.Law.sum_marked (α' := Fin (2 ^ 31)) honestCoordLaw (fun _ => (1 : ENNReal))
  simp only [mul_one] at h
  unfold HonestLawSum honestLaw
  rw [h, honestCoordLaw_sum, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)]
theorem honestLaw_apply (p : WProposal) :
    honestLaw p = ((2 ^ 31 : Nat) : ENNReal)⁻¹ * honestCoordLaw p.2 := by
  unfold honestLaw ClaudeWCT.Numerics.Law.marked
  rw [Fintype.card_fin]
theorem sum_honestLaw (g : WProposal → ENNReal) :
    (∑ p, honestLaw p * g p) =
      (((2 ^ 31 : Nat) : ENNReal) * (capSet.card : ENNReal))⁻¹ * ∑ p : WProposal, if capOkC p.2 = true then g p else 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [honestLaw_apply]
  unfold honestCoordLaw
  rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _))]
  split_ifs <;> ring
theorem sum_capOkC_prod_one :
    (∑ p : WProposal, if capOkC p.2 = true then (1 : ENNReal) else 0) =
      ((2 ^ 31 : Nat) : ENNReal) * (capSet.card : ENNReal) := by
  rw [Fintype.sum_prod_type]
  simp only [sum_capOkC_one, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
theorem producer_acceptance_eq :
    Pr[fun x : HashOutput => WCT9.producerAdmissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ((27 ^ 9 * 1137 * 2 ^ 15 : Nat) : ENNReal) * (((2 ^ 31 : Nat) : ENNReal) * (capSet.card : ENNReal)) /
        (Fintype.card HashOutput : ENNReal) := by
  rw [← expectedValue_ite_one, BPORS.expected_uniform_eq_finiteAverage]
  unfold SigGolfResearch.Gate6.Moments.finiteAverage
  rw [sum_producer (fun _ => 1), sum_capOkC_prod_one]
theorem acceptedProposalHonest : AcceptedProposalHonest := by
  intro g
  rw [producer_acceptance_eq, BPORS.expected_uniform_eq_finiteAverage]
  unfold SigGolfResearch.Gate6.Moments.finiteAverage
  rw [sum_producer, sum_honestLaw]
  have hK : ((2 ^ 31 : Nat) : ENNReal) * (capSet.card : ENNReal) ≠ 0 :=
    mul_ne_zero (by positivity) capSet_card_ne_zero
  have hK' : ((2 ^ 31 : Nat) : ENNReal) * (capSet.card : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) capSet_card_ne_top
  set K := ((2 ^ 31 : Nat) : ENNReal) * (capSet.card : ENNReal)
  set S := ∑ p : WProposal, if capOkC p.2 = true then g p else 0
  simp only [div_eq_mul_inv]
  calc ((27 ^ 9 * 1137 * 2 ^ 15 : Nat) : ENNReal) * S * (Fintype.card HashOutput : ENNReal)⁻¹
      = ((27 ^ 9 * 1137 * 2 ^ 15 : Nat) : ENNReal) * S * (Fintype.card HashOutput : ENNReal)⁻¹ * (K⁻¹ * K) := by
        rw [ENNReal.inv_mul_cancel hK hK', mul_one]
    _ = _ := by ring
theorem producer_le_admissible :
    Pr[fun x : HashOutput => WCT9.producerAdmissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      Pr[fun x : HashOutput => WCT9.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] :=
  probEvent_mono fun x _ h => WCT9.admissible_of_producer h
theorem producerAcceptanceBound : ProducerAcceptanceBound :=
  producer_le_admissible.trans acceptanceBound
theorem producerAdmissible_zero : WCT9.producerAdmissible 0 = true := by
  rw [producerAdmissible_eq, admissible_zero, Bool.true_and]
  exact capOkC_of_rank_zero _ fun k => by fin_cases k <;> rfl
theorem exists_producer : ∃ x, WCT9.producerAdmissible x = true := ⟨0, producerAdmissible_zero⟩
noncomputable def wctSpec' (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate) :
    FtsBankSpec WProposal :=
  wctSpec honestLawSum acceptedProposalHonest producerAcceptanceBound exists_producer horizon rate hexc
theorem wctSpec'_eq (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate) :
    wctSpec' horizon rate hexc =
      wctSpec honestLawSum acceptedProposalHonest producerAcceptanceBound exists_producer horizon rate hexc := rfl
theorem capSet_eq_n4 : capSet = ClaudeWCT.Numerics.N600Cap.capSet := by
  ext c
  rw [capSet_mem, ClaudeWCT.Numerics.N600Cap.mem_capSet]
  unfold capOkC ClaudeWCT.Numerics.N600Cap.rankCost
  simp only [decide_eq_true_eq]
set_option linter.constructorNameAsVariable false in
theorem honestCoordLaw_eq_n4 : honestCoordLaw = ClaudeWCT.Numerics.N600Cap.honestLaw := by
  funext c
  unfold ClaudeWCT.Numerics.N600Cap.honestLaw
  rw [← capSet_eq_n4]
  unfold honestCoordLaw ClaudeWCT.Numerics.N600.uniformOn
  by_cases h1 : capOkC c = true
  · have h2 : c ∈ capSet := by rw [capSet_mem]; exact h1
    simp only [h1, h2, if_true]
  · have h2 : c ∉ capSet := by rw [capSet_mem]; exact h1
    simp only [h1, h2, if_false, Bool.false_eq_true]
theorem honestLaw_eq_n4 : honestLaw = ClaudeWCT.Numerics.Law.marked (α := Fin (2 ^ 31))
    ClaudeWCT.Numerics.N600Cap.honestLaw := by
  unfold honestLaw
  rw [honestCoordLaw_eq_n4]
theorem excessBound_of_honest {T : Nat} {rate : ENNReal}
    (h : ClaudeWCT.Numerics.Law.lawAvg (ClaudeWCT.Numerics.Law.marked (α := Fin (2 ^ 31))
      ClaudeWCT.Numerics.N600Cap.honestLaw) T (fun W : List WProposal => price W - 63 / 64) ≤ rate) :
    ExcessBound T rate := by
  unfold ExcessBound
  rw [honestLaw_eq_n4]
  exact h
end ClaudeWCT.Bank.WCT
