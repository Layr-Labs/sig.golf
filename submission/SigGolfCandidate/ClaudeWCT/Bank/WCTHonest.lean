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
      ((WCT9.gateLimit * 2 ^ 58 : Nat) : ENNReal) * ∑ p : WProposal, if capOkC p.2 = true then g p else 0 := by
  rw [← sum_admissible (fun p => if capOkC p.2 = true then g p else 0)]
  apply Finset.sum_congr rfl
  intro x _
  rw [producerAdmissible_eq]
  cases WCT9.admissible x <;> cases capOkC (proposal x).2 <;> rfl
theorem capSet_mem (c : Coords) : c ∈ capSet ↔ capOkC c = true := by
  simp [capSet]
theorem routineCost_zero : WCT9.routineCost 0 = 76 := rfl
theorem childExtra_zero : WCT9.childExtra 0 = 5 := rfl
theorem capOkC_zero : capOkC (fun _ => ((0 : Child), (0 : Rank))) = true := by
  unfold capOkC
  rw [decide_eq_true_iff]
  simp only [routineCost_zero, childExtra_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  decide
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
      ((WCT9.gateLimit * 2 ^ 58 : Nat) : ENNReal) * (((2 ^ 31 : Nat) : ENNReal) * (capSet.card : ENNReal)) /
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
  calc ((WCT9.gateLimit * 2 ^ 58 : Nat) : ENNReal) * S * (Fintype.card HashOutput : ENNReal)⁻¹
      = ((WCT9.gateLimit * 2 ^ 58 : Nat) : ENNReal) * S * (Fintype.card HashOutput : ENNReal)⁻¹ * (K⁻¹ * K) := by
        rw [ENNReal.inv_mul_cancel hK hK', mul_one]
    _ = _ := by ring
theorem producer_le_admissible :
    Pr[fun x : HashOutput => WCT9.producerAdmissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      Pr[fun x : HashOutput => WCT9.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] :=
  probEvent_mono fun x _ h => WCT9.admissible_of_producer h
theorem capSet_eq_n4 : capSet = ClaudeWCT.Numerics.N600Cap.capSet := by
  ext c
  rw [capSet_mem, ClaudeWCT.Numerics.N600Cap.mem_capSet]
  unfold capOkC ClaudeWCT.Numerics.N600Cap.pairCost
  simp only [decide_eq_true_eq]
theorem capSet_card : capSet.card = ClaudeWCT.Numerics.N600Cap.J := by
  rw [capSet_eq_n4, ClaudeWCT.Numerics.N600Cap.card_capSet]
theorem producerAcceptanceBound : ProducerAcceptanceBound := by
  unfold ProducerAcceptanceBound
  rw [producer_acceptance_eq, capSet_card]
  simp only [Fintype.card_bitVec]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [WCT9.gateLimit, ClaudeWCT.Numerics.N600Cap.J, ENNReal.toReal_div,
    ENNReal.toReal_mul, ENNReal.toReal_pow]
theorem producerAdmissible_zero : WCT9.producerAdmissible 0 = true := by
  rw [producerAdmissible_eq, admissible_zero, Bool.true_and]
  have hz : (proposal 0).2 = fun _ => ((0 : Child), (0 : Rank)) := by
    funext k; fin_cases k <;> rfl
  rw [hz]
  exact capOkC_zero
theorem exists_producer : ∃ x, WCT9.producerAdmissible x = true := ⟨0, producerAdmissible_zero⟩
noncomputable def wctSpec' (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate) :
    FtsBankSpec WProposal :=
  wctSpec honestLawSum acceptedProposalHonest producerAcceptanceBound exists_producer horizon rate hexc
theorem wctSpec'_eq (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate) :
    wctSpec' horizon rate hexc =
      wctSpec honestLawSum acceptedProposalHonest producerAcceptanceBound exists_producer horizon rate hexc := rfl
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
      ClaudeWCT.Numerics.N600Cap.honestLaw) T (fun W : List WProposal => price W - 1023 / 1024) ≤ rate) :
    ExcessBound T rate := by
  unfold ExcessBound
  rw [honestLaw_eq_n4]
  exact h
end ClaudeWCT.Bank.WCT

/-! Exact cap-conditioned law for the paired shared forest. -/
namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
noncomputable def capSet : Finset Alphabet := Finset.univ.filter fun c => capOk c = true
noncomputable def honestCoordLaw (c : Alphabet) : ENNReal :=
  if capOk c = true then (capSet.card : ENNReal)⁻¹ else 0
noncomputable def honestLaw : Proposal → ENNReal :=
  ClaudeWCT.Numerics.Law.marked (α := Fin (2^31)) honestCoordLaw

theorem sum_producer (g : Proposal → ENNReal) :
    (∑ a : HashOutput, if producer a = true then g (proposal a) else 0) =
      ((734*2^62 : Nat) : ENNReal) * ∑ p : Proposal, if capOk p.2 = true then g p else 0 := by
  rw [← sum_admissible (fun p => if capOk p.2 = true then g p else 0)]
  apply Finset.sum_congr rfl
  intro a _
  unfold producer
  cases admissible a <;> cases capOk (proposal a).2 <;> rfl

theorem capSet_mem (c : Alphabet) : c ∈ capSet ↔ capOk c = true := by simp [capSet]
def zeroAlphabet : Alphabet := ((fun _ => (0,0,0),0),fun _ => 0)
theorem capOk_zero : capOk zeroAlphabet = true := by decide +kernel

theorem capSet_nonempty : capSet.Nonempty := by
  refine ⟨zeroAlphabet, ?_⟩
  rw [capSet_mem]
  exact capOk_zero
theorem capSet_card_ne_zero : (capSet.card : ENNReal) ≠ 0 := by
  exact_mod_cast (Finset.card_pos.mpr capSet_nonempty).ne'
theorem capSet_card_ne_top : (capSet.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
theorem sum_capOk (h : Alphabet → ENNReal) :
    (∑ c : Alphabet, if capOk c = true then h c else 0) = ∑ c ∈ capSet, h c := by
  rw [← Finset.sum_filter]
  rfl

theorem sum_capOk_one : (∑ c : Alphabet, if capOk c = true then (1 : ENNReal) else 0) = capSet.card := by
  rw [Finset.sum_boole]
  rfl

theorem honestCoordLaw_sum : ∑ c, honestCoordLaw c = 1 := by
  unfold honestCoordLaw
  rw [sum_capOk (fun _ => (capSet.card : ENNReal)⁻¹), Finset.sum_const, nsmul_eq_mul,
    ENNReal.mul_inv_cancel capSet_card_ne_zero capSet_card_ne_top]

theorem honestLaw_sum : ∑ p, honestLaw p = 1 := by
  have h := ClaudeWCT.Numerics.Law.sum_marked (α' := Fin (2^31)) honestCoordLaw (fun _ => (1 : ENNReal))
  simp only [mul_one] at h
  unfold honestLaw
  rw [h, honestCoordLaw_sum, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)]

theorem honestLaw_apply (p : Proposal) :
    honestLaw p = ((2^31 : Nat) : ENNReal)⁻¹ * honestCoordLaw p.2 := by
  unfold honestLaw ClaudeWCT.Numerics.Law.marked
  rw [Fintype.card_fin]

theorem sum_honestLaw (g : Proposal → ENNReal) :
    (∑ p, honestLaw p * g p) =
      (((2^31 : Nat) : ENNReal) * (capSet.card : ENNReal))⁻¹ *
        ∑ p : Proposal, if capOk p.2 = true then g p else 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [honestLaw_apply]
  unfold honestCoordLaw
  rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _))]
  split_ifs <;> ring

theorem sum_capOk_prod_one :
    (∑ p : Proposal, if capOk p.2 = true then (1 : ENNReal) else 0) =
      ((2^31 : Nat) : ENNReal) * (capSet.card : ENNReal) := by
  rw [Fintype.sum_prod_type]
  simp only [sum_capOk_one, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]

theorem producer_acceptance_eq :
    Pr[fun a : HashOutput => producer a = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ((734*2^62 : Nat) : ENNReal) * (((2^31 : Nat) : ENNReal) * (capSet.card : ENNReal)) /
        (Fintype.card HashOutput : ENNReal) := by
  rw [← expectedValue_ite_one, BPORS.expected_uniform_eq_finiteAverage]
  unfold SigGolfResearch.Gate6.Moments.finiteAverage
  rw [sum_producer (fun _ => 1), sum_capOk_prod_one]

theorem acceptedProposalHonest (g : Proposal → ENNReal) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun a => if producer a = true then g (proposal a) else 0) =
      (∑ p, honestLaw p*g p) *
        Pr[fun a : HashOutput => producer a = true | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  rw [producer_acceptance_eq, BPORS.expected_uniform_eq_finiteAverage]
  unfold SigGolfResearch.Gate6.Moments.finiteAverage
  rw [sum_producer, sum_honestLaw]
  have hK : ((2^31 : Nat) : ENNReal)*(capSet.card : ENNReal) ≠ 0 :=
    mul_ne_zero (by positivity) capSet_card_ne_zero
  have hK' : ((2^31 : Nat) : ENNReal)*(capSet.card : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) capSet_card_ne_top
  set K := ((2^31 : Nat) : ENNReal)*(capSet.card : ENNReal)
  set S := ∑ p : Proposal, if capOk p.2 = true then g p else 0
  simp only [div_eq_mul_inv]
  calc ((734*2^62 : Nat) : ENNReal)*S*(Fintype.card HashOutput : ENNReal)⁻¹
      = ((734*2^62 : Nat) : ENNReal)*S*(Fintype.card HashOutput : ENNReal)⁻¹*(K⁻¹*K) := by
        rw [ENNReal.inv_mul_cancel hK hK', mul_one]
    _ = _ := by ring

theorem accepted_source (g : Proposal → ENNReal) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun a => if SigGolfCandidate.Research.SharedForest.digestAccepted a = true then g (proposal a) else 0) =
      (∑ p, honestLaw p*g p) *
        Pr[fun a : HashOutput => SigGolfCandidate.Research.SharedForest.digestAccepted a = true |
          ($ᵗ HashOutput : ProbComp HashOutput)] := by
  simpa only [producer_source] using acceptedProposalHonest g

theorem producer_zero : producer 0 = true := by
  have ha : admissible 0 = true := by decide +kernel
  have hp : (proposal 0).2 = zeroAlphabet := by
    apply Prod.ext
    · apply Prod.ext
      · funext p; fin_cases p <;> rfl
      · rfl
    · funext k; fin_cases k <;> rfl
  rw [producer, ha, Bool.true_and, hp, capOk_zero]

theorem producerAcceptanceBound :
    Pr[fun a : HashOutput => producer a = true | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1/1024 := by
  calc _ ≤ Pr[fun a : HashOutput => admissible a = true | ($ᵗ HashOutput : ProbComp HashOutput)] :=
        probEvent_mono (fun a _ h => (Bool.and_eq_true_iff.mp h).1)
       _ ≤ 1/1024 := by
        rw [acceptance_eq]
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow]

noncomputable def kappa : ENNReal := (Fintype.card Alphabet : ENNReal)/(capSet.card : ENNReal)
theorem kappa_one_le : 1≤kappa := by
  have h : (capSet.card : ENNReal) ≤ (Fintype.card Alphabet : ENNReal) := by
    exact_mod_cast Finset.card_le_card (Finset.subset_univ capSet)
  exact (ENNReal.div_le_div_right h _).trans' (le_of_eq (ENNReal.div_self capSet_card_ne_zero capSet_card_ne_top).symm)

theorem honestCoordLaw_density (a : Alphabet) :
    honestCoordLaw a ≤ kappa*(Fintype.card Alphabet : ENNReal)⁻¹ := by
  have hc : (Fintype.card Alphabet : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ht : (Fintype.card Alphabet : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have he : kappa*(Fintype.card Alphabet : ENNReal)⁻¹ = (capSet.card : ENNReal)⁻¹ := by
    unfold kappa
    rw [div_eq_mul_inv, mul_right_comm, ENNReal.mul_inv_cancel hc ht, one_mul]
  rw [he]
  unfold honestCoordLaw
  split_ifs
  · exact le_rfl
  · exact bot_le

theorem lawAvg_le_uniform (r : Nat) (f : List Alphabet → ENNReal) :
    ClaudeWCT.Numerics.Law.lawAvg honestCoordLaw r f ≤ kappa^r*
      SphincsSecurity.Concrete.uniformWordAverage r f :=
  ClaudeWCT.Numerics.Law.lawAvg_le_uniform honestCoordLaw kappa honestCoordLaw_density r f

#print axioms accepted_source
#print axioms lawAvg_le_uniform
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open ClaudeWCT.Numerics
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev AlphabetOf (β : Type) := Selectors × (Fin 9 → β)

def splitHistory {β : Type} {r : Nat} (h : Fin r → AlphabetOf β) : SharedCoverage.ForestHistory β r :=
  (fun p => (fun t => ((h t).1.1 p).1,
    fun t => (((h t).1.1 p).2.1, (h t).2 ⟨2*p.val,by omega⟩),
    fun t => (((h t).1.1 p).2.2, (h t).2 ⟨2*p.val+1,by omega⟩)),
   fun t => ((h t).1.2,(h t).2 8))
def joinHistory {β : Type} {r : Nat} (h : SharedCoverage.ForestHistory β r) : Fin r → AlphabetOf β :=
  fun t => ((fun p => ((h.1 p).1 t, ((h.1 p).2.1 t).1, ((h.1 p).2.2 t).1), (h.2 t).1),
    fun k => if hk : k.val<8 then
      if k.val%2=0 then ((h.1 ⟨k.val/2,by omega⟩).2.1 t).2
      else ((h.1 ⟨k.val/2,by omega⟩).2.2 t).2
    else (h.2 t).2)
def historyEquiv (β : Type) (r : Nat) : (Fin r → AlphabetOf β) ≃ SharedCoverage.ForestHistory β r where
  toFun := splitHistory
  invFun := joinHistory
  left_inv h := by
    funext t
    apply Prod.ext
    · rfl
    · funext k
      fin_cases k <;> rfl
  right_inv h := by
    apply Prod.ext
    · funext p
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · funext t
          apply Prod.ext
          · rfl
          · fin_cases p <;> rfl
        · funext t
          apply Prod.ext
          · rfl
          · fin_cases p <;> rfl
    · funext t
      rfl

theorem alphabet_card {β : Type} [Fintype β] (hβ : Fintype.card β=563) :
    Fintype.card (AlphabetOf β) = SharedMoments.alphabetSize := by
  simp only [AlphabetOf, Selectors, PairSelector, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, hβ, SharedMoments.alphabetSize]
  norm_num

theorem sum_history {β : Type} [Fintype β] (r : Nat)
    {R : Type} [AddCommMonoid R] (f : SharedCoverage.ForestHistory β r → R) :
    (∑ h : Fin r → AlphabetOf β, f (splitHistory h)) = ∑ h, f h :=
  Equiv.sum_comp (historyEquiv β r) f

theorem uniform_history_average {β : Type} [Fintype β] [SampleableType β]
    (r : Nat) (f : List (AlphabetOf β) → ENNReal) (g : SharedCoverage.ForestHistory β r → ENNReal)
    (hfg : ∀ h : Fin r → AlphabetOf β, f (List.ofFn h) = g (splitHistory h)) :
    SphincsSecurity.Concrete.uniformWordAverage r f =
      (∑ h, g h)/(Fintype.card (AlphabetOf β) : ENNReal)^r := by
  rw [SigGolfResearch.Gate6.Moments.word_array_average]
  unfold SigGolfResearch.Gate6.Moments.finiteAverage
  simp_rw [hfg]
  rw [sum_history]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

theorem law_history_le (r : Nat) (f : List Alphabet → ENNReal)
    (g : SharedCoverage.ForestHistory (Fin 563) r → ENNReal)
    (hfg : ∀ h : Fin r → Alphabet, f (List.ofFn h) = g (splitHistory h)) :
    Law.lawAvg honestCoordLaw r f ≤ kappa^r *
      ((∑ h, g h)/(SharedMoments.alphabetSize : ENNReal)^r) := by
  have h := lawAvg_le_uniform r f
  rw [uniform_history_average r f g hfg] at h
  have hc : Fintype.card Alphabet = SharedMoments.alphabetSize := alphabet_card rfl
  simpa only [hc] using h

#print axioms historyEquiv
#print axioms alphabet_card
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

def SlotCoveredP (W : List Proposal) (N : HashOutput) (k : Fin 9) (t : Fin 6) : Prop :=
  ∃ p ∈ W, p.1 = (proposal N).1 ∧ rawChild p.2.1 k = rawChild (proposal N).2.1 k ∧
    ClaudeWCT.WCT9.wordDigit ((proposal N).2.2 k) t ≤ ClaudeWCT.WCT9.wordDigit (p.2.2 k) t
def CoveredP (W : List Proposal) (N : HashOutput) : Prop := ∀ k t, SlotCoveredP W N k t
def Covered (X : List HashOutput) (N : HashOutput) : Prop := CoveredP (X.map proposal) N
noncomputable def scoreP (W : List Proposal) (N : HashOutput) : ENNReal :=
  if admissible N = true ∧ CoveredP W N then 1 else 0
noncomputable def score (X : List HashOutput) (N : HashOutput) : ENNReal := scoreP (X.map proposal) N
noncomputable def price (W : List Proposal) : ENNReal :=
  2^128 * SigGolfCandidate.T3.BPORS.finiteAverage (fun N => scoreP W N)

theorem coveredP_append (W V : List Proposal) (N : HashOutput) (h : CoveredP W N) : CoveredP (W++V) N := by
  intro k t
  obtain ⟨p,hp,h1,h2,h3⟩ := h k t
  exact ⟨p,List.mem_append_left V hp,h1,h2,h3⟩
theorem score_append_mono (X Y : List HashOutput) (N : HashOutput) : score X N ≤ score (X++Y) N := by
  unfold score scoreP
  rw [List.map_append]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1,coveredP_append _ _ N h1.2⟩ h2
  · exact bot_le
  · exact le_rfl

theorem one_le_score (X : List HashOutput) (N : HashOutput)
    (hadm : admissible N = true) (hcov : Covered X N) : 1 ≤ score X N := by
  unfold score scoreP
  rw [if_pos ⟨hadm,hcov⟩]

theorem average_score (X : List HashOutput) :
    SigGolfCandidate.T3.BPORS.finiteAverage (fun N : HashOutput => score X N) =
      price (X.map proposal)/2^128 := by
  unfold price score
  rw [mul_comm, ENNReal.mul_div_cancel_right (by positivity) (by finiteness)]

/-- The law-only bank packages the actual producer and exact proposal law.
Its infinite excess bound is never a security certificate: it is used only
for generic accepted-output and cached-search expectation identities. -/
noncomputable def lawSpec : FtsBankSpec Proposal where
  specTheta := 1023/1024
  admBound := 1/1024
  theta_add_admBound := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness)
      (by unfold SigGolfCandidate.T3.Security.CaseC.theta; finiteness)).mp
    unfold SigGolfCandidate.T3.Security.CaseC.theta
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_inv,
      ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num
  admissible := admissible
  producer := producer
  exists_producer := ⟨0,producer_zero⟩
  acceptance_le := producerAcceptanceBound
  proposal := proposal
  law := honestLaw
  law_sum := honestLaw_sum
  accepted_proposal := acceptedProposalHonest
  score := score
  covered := Covered
  one_le_score := one_le_score
  score_append_mono := score_append_mono
  price := price
  average_score := average_score
  horizon := 2^32
  excessRate := ⊤
  excess_le := le_top

theorem selected_proposal (g : Proposal → ENNReal) :
    expectedValue lawSpec.accepted (fun a => g (proposal a)) = ∑ p, honestLaw p*g p :=
  lawSpec.expected_accepted_proposal g

#print axioms selected_proposal
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open SigGolfCandidate.T3 SigGolfCandidate.Research ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem slotCoveredP_source (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 6) :
    SlotCoveredP (X.map proposal) N k t ↔
      ∃ output ∈ X, digestIndex output=digestIndex N ∧
        SharedForest.rawChildFromOutput output k=SharedForest.rawChildFromOutput N k ∧
        wordDigit (SharedForest.forestRank N k.val) t ≤ wordDigit (SharedForest.forestRank output k.val) t := by
  constructor
  · rintro ⟨p,hp,hi,hc,hd⟩
    obtain ⟨output,ho,rfl⟩ := List.mem_map.mp hp
    refine ⟨output,ho,?_,?_,?_⟩
    · simpa only [Fin.ext_iff,proposal_index] using hi
    · simpa only [proposal_child] using hc
    · simpa only [proposal_rank] using hd
  · rintro ⟨output,ho,hi,hc,hd⟩
    refine ⟨proposal output,List.mem_map_of_mem ho,?_,?_,?_⟩
    · simpa only [Fin.ext_iff,proposal_index] using hi
    · simpa only [proposal_child] using hc
    · simpa only [proposal_rank] using hd

theorem covered_source (X : List HashOutput) (N : HashOutput) :
    Covered X N ↔ ∀ k : Fin 9, ∀ t : Fin 6,
      ∃ output ∈ X, digestIndex output=digestIndex N ∧
        SharedForest.rawChildFromOutput output k=SharedForest.rawChildFromOutput N k ∧
        wordDigit (SharedForest.forestRank N k.val) t ≤ wordDigit (SharedForest.forestRank output k.val) t := by
  exact forall_congr' fun k => forall_congr' fun t => slotCoveredP_source X N k t

#print axioms covered_source
end ClaudeWCT.Bank.Paired


namespace ClaudeWCT.Bank.Paired
open SigGolfCandidate.T3 SigGolfCandidate.Research ClaudeWCT.Numerics.SharedFtsCount
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] Finset.univ

theorem producer_fields_eq : producer = (fun a => SharedDigestFields.accepted (SharedDigestFields.fields a)) :=
    funext (fun a => (producer_source a).trans (SharedDigestFields.accepted_fields a).symm)
#print axioms producer_fields_eq

theorem predicate_card_nat (p : SharedDigestFields.Fields → Prop) [DecidablePred p] :
    Nat.card {a : HashOutput // p (SharedDigestFields.fields a)} =
      Nat.card {f : SharedDigestFields.Fields // p f} * 2^76 := by
  simpa only [Nat.card_eq_fintype_card] using SharedDigestFields.predicate_card p
#print axioms predicate_card_nat

theorem producer_card_fields : Nat.card {a : HashOutput // producer a = true} =
    fieldRetained*2^31*734*2^76 := by
  have he := congrArg (fun p : HashOutput → Bool => Nat.card {a : HashOutput // p a = true}) producer_fields_eq
  calc _ = Nat.card {a : HashOutput // SharedDigestFields.accepted (SharedDigestFields.fields a) = true} := he
       _ = Nat.card {f : SharedDigestFields.Fields // SharedDigestFields.accepted f = true} * 2^76 := predicate_card_nat (fun f => SharedDigestFields.accepted f = true)
       _ = _ := by rw [Nat.card_eq_fintype_card, SharedFtsModel.accepted_fields_card, SharedFtsModel.accepted_card]
#print axioms producer_card_fields
theorem uniform_card_bool {α : Type} [Fintype α] [SampleableType α] (p : α → Bool) :
    Pr[fun x => p x = true | ($ᵗ α : ProbComp α)] =
      (Nat.card {x : α // p x = true} : ENNReal)/Fintype.card α := by
  rw [probEvent_uniformSample, ← Fintype.card_subtype, Nat.card_eq_fintype_card]

theorem producer_card : Nat.card {a : HashOutput // producer a = true} =
    734*2^62*(2^31*capSet.card) := by
  have he := producer_acceptance_eq
  rw [uniform_card_bool producer] at he
  have hn : (Fintype.card HashOutput : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := HashOutput)).ne'
  have ht : (Fintype.card HashOutput : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hc := congrArg (fun x : ENNReal => x * (Fintype.card HashOutput : ENNReal)) he
  rw [ENNReal.div_mul_cancel hn ht, ENNReal.div_mul_cancel hn ht] at hc
  exact_mod_cast hc


theorem capSet_card_fields : capSet.card = fieldRetained*2^14 := by
  have h := producer_card_fields
  rw [producer_card] at h
  have he : (734*2^93)*capSet.card = (734*2^93)*(fieldRetained*2^14) := by
    calc
      _ = 734*2^62*(2^31*capSet.card) := by ring
      _ = fieldRetained*2^31*734*2^76 := h
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0<734*2^93) he

theorem capSet_card_scaled : capSet.card*16 = count := by
  rw [capSet_card_fields]
  calc fieldRetained*2^14*16 = fieldRetained*4^9 := by ring
       _ = count := field_retained_eq

theorem alphabet_card_scaled : Fintype.card Alphabet*16 = total := by
  norm_num [Alphabet, Selectors, PairSelector, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, total]

theorem kappa_exact : kappa = (total : ENNReal)/count := by
  unfold kappa
  rw [ENNReal.div_eq_div_iff (by norm_num [count]) (by simp)
    capSet_card_ne_zero capSet_card_ne_top]
  rw [mul_comm (count : ENNReal), mul_comm (capSet.card : ENNReal)]
  have ha := alphabet_card_scaled
  have hc := capSet_card_scaled
  calc (Fintype.card Alphabet : ENNReal)*count =
        (Fintype.card Alphabet : ENNReal)*((capSet.card*16 : Nat) : ENNReal) := by rw [hc]
       _ = ((Fintype.card Alphabet*16 : Nat) : ENNReal)*capSet.card := by push_cast; ring
       _ = (total : ENNReal)*capSet.card := by rw [ha]

theorem kappa_rate : (2:ENNReal)*kappa ≤ (2013623:ENNReal)/1000000 := by
  rw [kappa_exact]
  unfold total count
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div, ENNReal.toReal_mul]

#print axioms capSet_card_scaled
#print axioms kappa_exact
#print axioms kappa_rate
end ClaudeWCT.Bank.Paired


namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 ClaudeWCT.Numerics.SharedFtsCount ClaudeWCT.Numerics.CanonicalCompression
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem capSet_card_value : capSet.card = 3255680248596076861501897566295512180326400 := by
  have h := capSet_card_scaled
  norm_num [count] at h
  omega

theorem producer_acceptance_exact :
    Pr[fun a => producer a = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (ftsNum : ENNReal)/ftsDen := by
  rw [producer_acceptance_eq, capSet_card_value]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by unfold ftsDen; finiteness)).mp
  norm_num [ftsNum,ftsDen,ENNReal.toReal_div,ENNReal.toReal_mul,HashOutput]

theorem producer_acceptance_lower :
    (1:ENNReal)/5000 ≤ Pr[fun a => producer a = true | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  rw [producer_acceptance_exact]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold ftsDen; finiteness)).mp
  norm_num [ftsNum,ftsDen,ENNReal.toReal_div]

#print axioms producer_acceptance_exact
#print axioms producer_acceptance_lower

theorem digestAccepted_acceptance_exact :
    Pr[fun a => SigGolfCandidate.Research.SharedForest.digestAccepted a = true |
      ($ᵗ HashOutput : ProbComp HashOutput)] = (ftsNum : ENNReal)/ftsDen := by
  have he : producer = SigGolfCandidate.Research.SharedForest.digestAccepted := funext producer_source
  rw [← he]
  exact producer_acceptance_exact

theorem digestAccepted_acceptance_lower :
    (1:ENNReal)/5000 ≤ Pr[fun a => SigGolfCandidate.Research.SharedForest.digestAccepted a = true |
      ($ᵗ HashOutput : ProbComp HashOutput)] := by
  have he : producer = SigGolfCandidate.Research.SharedForest.digestAccepted := funext producer_source
  rw [← he]
  exact producer_acceptance_lower
#print axioms digestAccepted_acceptance_lower
end ClaudeWCT.Bank.Paired
