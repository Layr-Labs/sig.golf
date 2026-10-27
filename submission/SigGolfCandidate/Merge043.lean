import SigGolfCandidate.Merge015
import SigGolfCandidate.Merge017
import SigGolfCandidate.Merge028
import SigGolfCandidate.Merge030
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge042

-- ==== merged from ClaudeWCT_Numerics_N600Cap ====
section

namespace ClaudeWCT.Numerics.N600Cap
open Finset
open ClaudeWCT.WCT9 (Coord Child Rank)
noncomputable def honestLaw : (Coord → Child × Rank) → ENNReal := N600.uniformOn capSet
theorem capSet_nonempty : capSet.Nonempty := by
  rw [← card_pos, card_capSet]; unfold J; positivity
noncomputable def kappaHonest : ENNReal := ((N600.Q ^ 9 : ℕ) : ENNReal) / ((J : ℕ) : ENNReal)
theorem lawOK_honest : N600.LawOK honestLaw kappaHonest :=
  N600.lawOK_uniformOn' capSet capSet_nonempty (N600.Q ^ 9) J
    (N600.card_table (Fintype.card_fin 563) (Fintype.card_fin 128)) card_capSet (by unfold N600.Q J; norm_num)
end ClaudeWCT.Numerics.N600Cap
end
-- ==== merged from ClaudeWCT_Bank_WCTHonest ====
section

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
      ((791*2^62 : Nat) : ENNReal) * ∑ p : Proposal, if capOk p.2 = true then g p else 0 := by
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
      ((791*2^62 : Nat) : ENNReal) * (((2^31 : Nat) : ENNReal) * (capSet.card : ENNReal)) /
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
  calc ((791*2^62 : Nat) : ENNReal)*S*(Fintype.card HashOutput : ENNReal)⁻¹
      = ((791*2^62 : Nat) : ENNReal)*S*(Fintype.card HashOutput : ENNReal)⁻¹*(K⁻¹*K) := by
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

end ClaudeWCT.Bank.Paired


namespace ClaudeWCT.Bank.Paired
open SigGolfCandidate.T3 SigGolfCandidate.Research ClaudeWCT.Numerics.SharedFtsCount
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] Finset.univ

theorem producer_fields_eq : producer = (fun a => SharedDigestFields.accepted (SharedDigestFields.fields a)) :=
    funext (fun a => (producer_source a).trans (SharedDigestFields.accepted_fields a).symm)

theorem predicate_card_nat (p : SharedDigestFields.Fields → Prop) [DecidablePred p] :
    Nat.card {a : HashOutput // p (SharedDigestFields.fields a)} =
      Nat.card {f : SharedDigestFields.Fields // p f} * 2^76 := by
  simpa only [Nat.card_eq_fintype_card] using SharedDigestFields.predicate_card p

theorem producer_card_fields : Nat.card {a : HashOutput // producer a = true} =
    fieldRetained*2^31*791*2^76 := by
  have he := congrArg (fun p : HashOutput → Bool => Nat.card {a : HashOutput // p a = true}) producer_fields_eq
  calc _ = Nat.card {a : HashOutput // SharedDigestFields.accepted (SharedDigestFields.fields a) = true} := he
       _ = Nat.card {f : SharedDigestFields.Fields // SharedDigestFields.accepted f = true} * 2^76 := predicate_card_nat (fun f => SharedDigestFields.accepted f = true)
       _ = _ := by rw [Nat.card_eq_fintype_card, SharedFtsModel.accepted_fields_card, SharedFtsModel.accepted_card]
theorem uniform_card_bool {α : Type} [Fintype α] [SampleableType α] (p : α → Bool) :
    Pr[fun x => p x = true | ($ᵗ α : ProbComp α)] =
      (Nat.card {x : α // p x = true} : ENNReal)/Fintype.card α := by
  rw [probEvent_uniformSample, ← Fintype.card_subtype, Nat.card_eq_fintype_card]

theorem producer_card : Nat.card {a : HashOutput // producer a = true} =
    791*2^62*(2^31*capSet.card) := by
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
  have he : (791*2^93)*capSet.card = (791*2^93)*(fieldRetained*2^14) := by
    calc
      _ = 791*2^62*(2^31*capSet.card) := by ring
      _ = fieldRetained*2^31*791*2^76 := h
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0<791*2^93) he

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

/-- Cap 777: `2 kappa = 2.0188326… ≤ 2.018833` (the thinned Poisson parameter). -/
theorem kappa_rate : (2:ENNReal)*kappa ≤ (2018833:ENNReal)/1000000 := by
  rw [kappa_exact]
  unfold total count
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div, ENNReal.toReal_mul]

end ClaudeWCT.Bank.Paired


namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 ClaudeWCT.Numerics.SharedFtsCount ClaudeWCT.Numerics.CanonicalCompression
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem capSet_card_value : capSet.card = 3245450420714031830069679340740189437804544 := by
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
end ClaudeWCT.Bank.Paired
end
-- ==== merged from T3_Secc_WotsTransportBase ====
section

namespace SigGolfCandidate.T3.Security.Wots.Ref
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def fixedWorld (F : Answers) : QueryImpl T3.Spec ProbComp
  | .inl (.inl n) => liftM (unifSpec.query n)
  | .inl (.inr input) => pure (F (.inl (.inr input)))
  | .inr coordinate => pure (F (.inr coordinate))
noncomputable def fixedRecord {α : Type} (F : Answers) (program : M α) :
    LazyPrivate.State → ProbComp (FirstHit.Recorded α) :=
  OracleComp.construct
    (fun value state => pure ⟨value, [], state⟩)
    (fun input _ next state => do
      let answer ← fixedWorld F input
      (fun last => ⟨last.value, ⟨state, input, answer⟩ :: last.events, last.state⟩) <$>
        next answer (FirstHit.advance state input answer)) program
theorem fixedRecord_pure {α : Type} (F : Answers) (value : α) (state : LazyPrivate.State) :
    fixedRecord F (pure value : M α) state = pure ⟨value, [], state⟩ := rfl
theorem fixedRecord_query_bind {α : Type} (F : Answers) (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) (state : LazyPrivate.State) :
    fixedRecord F (liftM (T3.Spec.query input) >>= next) state = (do
      let answer ← fixedWorld F input
      (fun last => ⟨last.value, ⟨state, input, answer⟩ :: last.events, last.state⟩) <$>
        fixedRecord F (next answer) (FirstHit.advance state input answer)) := rfl
theorem fixedRecord_bind {α β : Type} (F : Answers) (program : M α) (next : α → M β)
    (state : LazyPrivate.State) :
    fixedRecord F (program >>= next) state = (do
      let first ← fixedRecord F program state
      let last ← fixedRecord F (next first.value) first.state
      pure ⟨last.value, first.events ++ last.events, last.state⟩) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [pure_bind, fixedRecord_pure, List.nil_append]; simp
  | query_bind input rest ih =>
      rw [bind_assoc, fixedRecord_query_bind, fixedRecord_query_bind]
      simp only [bind_map_left, bind_assoc]
      apply bind_congr
      intro answer
      rw [ih]
      simp only [map_bind, map_pure]
      apply bind_congr
      intro first
      apply bind_congr
      intro last
      rfl
theorem fixedRecord_map {α β : Type} (F : Answers) (f : α → β) (program : M α) (state : LazyPrivate.State) :
    fixedRecord F (f <$> program) state =
      (fun result : FirstHit.Recorded α => (⟨f result.value, result.events, result.state⟩ : FirstHit.Recorded β)) <$>
        fixedRecord F program state := by
  rw [map_eq_bind_pure_comp, fixedRecord_bind]
  simp only [Function.comp_def, fixedRecord_pure, pure_bind, map_pure, List.append_nil, bind_pure_comp]
noncomputable def pureRecord {α : Type} (F : Answers) (program : M α) :
    LazyPrivate.State → FirstHit.Recorded α :=
  OracleComp.construct
    (fun value state => ⟨value, [], state⟩)
    (fun input _ next state =>
      ⟨(next (F input) (FirstHit.advance state input (F input))).value,
        ⟨state, input, F input⟩ :: (next (F input) (FirstHit.advance state input (F input))).events,
        (next (F input) (FirstHit.advance state input (F input))).state⟩) program
theorem pureRecord_query_bind {α : Type} (F : Answers) (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) (state : LazyPrivate.State) :
    pureRecord F (liftM (T3.Spec.query input) >>= next) state =
      ⟨(pureRecord F (next (F input)) (FirstHit.advance state input (F input))).value,
        ⟨state, input, F input⟩ :: (pureRecord F (next (F input)) (FirstHit.advance state input (F input))).events,
        (pureRecord F (next (F input)) (FirstHit.advance state input (F input))).state⟩ := rfl
theorem eval_query (F : Answers) (input : T3.Spec.Domain) :
    evalWithAnswerFn F (liftM (T3.Spec.query input)) = F input :=
  simulateQ_spec_query F input
theorem fixedWorld_hash (F : Answers) (input : T3.Spec.Domain) (hi : SourceReplay.IsHash input) :
    fixedWorld F input = pure (F input) := by
  rcases input with (n | x) | c
  · exact False.elim hi
  · rfl
  · rfl
theorem fixedRecord_hashOnly {α : Type} (F : Answers) (program : M α) (hp : SourceReplay.HashOnly program)
    (state : LazyPrivate.State) : fixedRecord F program state = pure (pureRecord F program state) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rw [fixedRecord_query_bind, pureRecord_query_bind, fixedWorld_hash F input hi, pure_bind,
        ih (F input) (hn _), map_pure]
theorem pureRecord_value {α : Type} (F : Answers) (program : M α) (state : LazyPrivate.State) :
    (pureRecord F program state).value = evalWithAnswerFn F program := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      rw [pureRecord_query_bind, evalWithAnswerFn_bind, eval_query]
      exact ih (F input) _
theorem pureRecord_inputs {α : Type} (F : Answers) (program : M α) (state : LazyPrivate.State) :
    (pureRecord F program state).events.map FirstHit.QueryEvent.input = SourceReplay.queried F program := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      rw [pureRecord_query_bind, SourceReplay.queried_query_bind, List.map_cons]
      exact congrArg (List.cons input) (ih (F input) _)
def chargeSum (events : List FirstHit.QueryEvent) : Nat :=
  (events.map fun event => FullGame.queryCharge event.input).sum
@[simp] theorem chargeSum_nil : chargeSum [] = 0 := rfl
@[simp] theorem chargeSum_cons (event : FirstHit.QueryEvent) (events : List FirstHit.QueryEvent) :
    chargeSum (event :: events) = FullGame.queryCharge event.input + chargeSum events := by
  simp [chargeSum]
@[simp] theorem chargeSum_append (left right : List FirstHit.QueryEvent) :
    chargeSum (left ++ right) = chargeSum left + chargeSum right := by
  simp [chargeSum]
theorem queryCharge_hash (input : T3.Spec.Domain) (hi : SourceReplay.IsHash input) :
    FullGame.queryCharge input = 1 := by
  simp only [FullGame.queryCharge, if_pos (SourceReplay.hash_charged input hi)]
theorem pureRecord_charge {α : Type} (F : Answers) (program : M α) (hp : SourceReplay.HashOnly program)
    (state : LazyPrivate.State) :
    chargeSum (pureRecord F program state).events = (SourceReplay.queried F program).length := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rw [pureRecord_query_bind, SourceReplay.queried_query_bind, List.length_cons]
      simp only [chargeSum_cons, queryCharge_hash input hi]
      rw [ih (F input) (hn _)]
      omega
theorem fixedRecord_counted {α : Type} (F : Answers) (program : M α) (state : LazyPrivate.State) :
    (fun result : FirstHit.Recorded α => (result.value, chargeSum result.events)) <$> fixedRecord F program state =
      simulateQ (fixedWorld F) (SphincsSecurity.QueryCap.counted Derivation.charged program) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [fixedRecord_pure, SphincsSecurity.QueryCap.counted_pure]
  | query_bind input next ih =>
      rw [fixedRecord_query_bind, SphincsSecurity.QueryCap.counted_query_bind]
      simp only [map_bind, Functor.map_map, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      apply bind_congr
      intro answer
      rw [← ih answer (FirstHit.advance state input answer)]
      simp only [chargeSum_cons, map_eq_bind_pure_comp, Function.comp_def, FullGame.queryCharge, bind_assoc,
        pure_bind]
theorem fixedWorld_counted_hashOnly {α : Type} (F : Answers) (program : M α) (hp : SourceReplay.HashOnly program) :
    simulateQ (fixedWorld F) (SphincsSecurity.QueryCap.counted Derivation.charged program) =
      pure (evalWithAnswerFn F program, (SourceReplay.queried F program).length) := by
  rw [← fixedRecord_counted F program (∅, ∅), fixedRecord_hashOnly F program hp, map_pure,
    pureRecord_value, pureRecord_charge F program hp]
def Agrees (F : Answers) (state : LazyPrivate.State) : Prop :=
  ∀ input answer, SourceReplay.known state input = some answer → F input = answer
theorem agrees_empty (F : Answers) : Agrees F (∅, ∅) := by
  intro input answer h
  rcases input with (n | x) | c <;> cases h
theorem agrees_advance {F : Answers} {state : LazyPrivate.State} (hF : Agrees F state) (input : T3.Spec.Domain) :
    Agrees F (FirstHit.advance state input (F input)) := by
  intro query answer h
  rcases input with (n | x) | c
  · exact hF query answer h
  · rcases query with (m | y) | d
    · cases h
    · change (state.2.cacheQuery x (F (.inl (.inr x)))) y = some answer at h
      by_cases hy : y = x
      · subst y
        rw [QueryCache.cacheQuery_self] at h
        exact Option.some.inj h
      · rw [QueryCache.cacheQuery_of_ne _ _ hy] at h
        exact hF _ _ h
    · exact hF _ _ h
  · rcases query with (m | y) | d
    · cases h
    · exact hF _ _ h
    · change (state.1.cacheQuery c (F (.inr c))) d = some answer at h
      by_cases hd : d = c
      · subst d
        rw [QueryCache.cacheQuery_self] at h
        exact Option.some.inj h
      · rw [QueryCache.cacheQuery_of_ne _ _ hd] at h
        exact hF _ _ h
theorem lazy_query_mem (state : LazyPrivate.State) (input : T3.Spec.Domain) (answer : T3.Spec.Range input)
    (h : ∀ cached, SourceReplay.known state input = some cached → cached = answer) :
    (answer, FirstHit.advance state input answer) ∈ support (LazyPrivate.run (liftM (T3.Spec.query input)) state) := by
  rw [LazyPrivate.run_query]
  rcases input with (n | x) | c
  · simp only [PrivateTable.lazyImpl, StateT.run_mk, mem_support_bind_iff, mem_support_pure_iff]
    refine ⟨(answer, state.2), ?_, rfl⟩
    change (answer, state.2) ∈ support ((fun a => (a, state.2)) <$>
      ($ᵗ (SphincsSecurity.OracleWorld.Range (.inl n)) : ProbComp _))
    rw [support_map]
    exact ⟨answer, mem_support_uniformSample _, rfl⟩
  · simp only [PrivateTable.lazyImpl, StateT.run_mk, mem_support_bind_iff, mem_support_pure_iff]
    cases hc : state.2 x with
    | some cached =>
        have he : cached = answer := h cached hc
        subst he
        refine ⟨(cached, state.2), ?_, ?_⟩
        · change (cached, state.2) ∈ support ((randomOracle (spec := SphincsSecurity.HashSpec) x).run state.2)
          rw [QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff]
        · change (cached, (state.1, state.2.cacheQuery x cached)) = (cached, (state.1, state.2))
          rw [PrivateTable.cacheQuery_cached state.2 x cached hc]
    | none =>
        refine ⟨(answer, state.2.cacheQuery x answer), ?_, rfl⟩
        change (answer, state.2.cacheQuery x answer) ∈
          support ((randomOracle (spec := SphincsSecurity.HashSpec) x).run state.2)
        rw [QueryImpl.withCaching_run_none _ hc, support_map]
        exact ⟨answer, mem_support_uniformSample _, rfl⟩
  · simp only [PrivateTable.lazyImpl, StateT.run_mk, mem_support_bind_iff, mem_support_pure_iff]
    cases hc : state.1 c with
    | some cached =>
        have he : cached = answer := h cached hc
        subst he
        refine ⟨(cached, state.1), ?_, ?_⟩
        · change (cached, state.1) ∈ support ((randomOracle (spec := Coordinate →ₒ HashOutput) c).run state.1)
          rw [QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff]
        · change (cached, (state.1.cacheQuery c cached, state.2)) = (cached, (state.1, state.2))
          rw [PrivateTable.cacheQuery_cached state.1 c cached hc]
    | none =>
        refine ⟨(answer, state.1.cacheQuery c answer), ?_, rfl⟩
        change (answer, state.1.cacheQuery c answer) ∈
          support ((randomOracle (spec := Coordinate →ₒ HashOutput) c).run state.1)
        rw [QueryImpl.withCaching_run_none _ hc, support_map]
        exact ⟨answer, mem_support_uniformSample _, rfl⟩
theorem fixedWorld_mem (F : Answers) (input : T3.Spec.Domain) (answer : T3.Spec.Range input)
    (h : answer ∈ support (fixedWorld F input)) : SourceReplay.IsHash input → answer = F input := by
  intro hi
  rw [fixedWorld_hash F input hi, mem_support_pure_iff] at h
  exact h
theorem fixedRecord_mem_record {α : Type} (F : Answers) (program : M α) (state : LazyPrivate.State)
    (hF : Agrees F state) (result : FirstHit.Recorded α) (hr : result ∈ support (fixedRecord F program state)) :
    result ∈ support (FirstHit.record program state) ∧ Agrees F result.state := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [fixedRecord_pure, mem_support_pure_iff] at hr
      subst result
      exact ⟨by rw [FirstHit.record_pure, mem_support_pure_iff], hF⟩
  | query_bind input next ih =>
      rw [fixedRecord_query_bind, mem_support_bind_iff] at hr
      obtain ⟨answer, hanswer, hr⟩ := hr
      rw [support_map] at hr
      obtain ⟨last, hlast, rfl⟩ := hr
      have hadv : Agrees F (FirstHit.advance state input answer) := by
        rcases input with (n | x) | c
        · exact hF
        · rw [fixedWorld_mem F _ answer hanswer trivial]; exact agrees_advance hF _
        · rw [fixedWorld_mem F _ answer hanswer trivial]; exact agrees_advance hF _
      obtain ⟨hrec, hagree⟩ := ih answer _ hadv last hlast
      refine ⟨?_, hagree⟩
      rw [FirstHit.record_query_bind, mem_support_bind_iff]
      refine ⟨(answer, FirstHit.advance state input answer), lazy_query_mem state input answer ?_, ?_⟩
      · intro cached hc
        rcases input with (n | x) | c
        · cases hc
        · rw [fixedWorld_mem F _ answer hanswer trivial]; exact (hF _ _ hc).symm
        · rw [fixedWorld_mem F _ answer hanswer trivial]; exact (hF _ _ hc).symm
      · rw [support_map]
        exact ⟨last, hrec, rfl⟩
end SigGolfCandidate.T3.Security.Wots.Ref
end
-- ==== merged from T3_Secc_WotsTransportR3 ====
section

namespace SigGolfCandidate.T3.Security.Wots.Ref
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem recorded_bind {ι α β : Type} {spec : OracleSpec ι} (computation : OracleComp spec α)
    (next : α → OracleComp spec β) :
    SphincsSecurity.QueryCap.recorded (computation >>= next) = (do
      let first ← SphincsSecurity.QueryCap.recorded computation
      let second ← SphincsSecurity.QueryCap.recorded (next first.1)
      pure (second.1, first.2 ++ second.2)) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [SphincsSecurity.QueryCap.recorded_pure]
  | query_bind input rest ih =>
      rw [bind_assoc, SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryCap.recorded_query_bind]
      simp only [bind_assoc, pure_bind]
      apply bind_congr
      intro answer
      rw [ih]
      simp only [bind_assoc, pure_bind, List.cons_append]
theorem recorded_map {ι α β : Type} {spec : OracleSpec ι} (f : α → β) (computation : OracleComp spec α) :
    SphincsSecurity.QueryCap.recorded (f <$> computation) =
      (fun result => (f result.1, result.2)) <$> SphincsSecurity.QueryCap.recorded computation := by
  rw [map_eq_bind_pure_comp, recorded_bind]
  simp [SphincsSecurity.QueryCap.recorded_pure]
theorem ticks_succ (n : Nat) : ticks (n + 1) = (liftM (RefWorld.query (.inr ())) >>= fun _ => ticks n) := rfl
theorem ticks_recorded (T : Answers) (n : Nat) :
    simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded (ticks n)) =
      pure ((), List.replicate n (.inr ())) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [ticks_succ, SphincsSecurity.QueryCap.recorded_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, ih]
      change (pure () >>= fun _ => (pure ((), List.replicate n (.inr ())) : ProbComp _) >>= fun result =>
        pure (result.1, (.inr () : RefWorld.Domain) :: result.2)) = _
      simp [List.replicate_succ]
theorem ticks_counted (T : Answers) (n : Nat) :
    simulateQ (refImpl T) (SphincsSecurity.QueryCap.counted RefCharged (ticks n)) = pure ((), n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [ticks_succ, SphincsSecurity.QueryCap.counted_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, ih]
      change (pure () >>= fun _ => (pure ((), n) : ProbComp _) >>= fun result =>
        pure (result.1, (if RefCharged (.inr ()) then 1 else 0) + result.2)) = _
      simp only [pure_bind]
      congr 2
      simp only [RefCharged, if_true]
      omega
theorem calls_replicate_tick (n : Nat) :
    SphincsSecurity.QueryCap.calls RefCharged (List.replicate n (.inr () : RefWorld.Domain)) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, SphincsSecurity.QueryCap.calls_cons, ih]
      simp only [RefCharged, if_true]
      omega
def embed : T3.Spec.Domain → RefWorld.Domain
  | .inl input => .inl input
  | .inr _ => .inr ()
theorem traceOf_map_embed (T : Answers) (queries : List T3.Spec.Domain) :
    traceOf T (queries.map embed) = entriesOf T queries := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
      rcases query with (n | x) | c
      · simpa [traceOf, entriesOf, embed] using ih
      · simp only [List.map_cons, traceOf, entriesOf, embed, List.filterMap_cons] at ih ⊢
        rw [ih]
      · simp [traceOf, entriesOf, embed] at ih ⊢
        exact ih
theorem traceOf_append (T : Answers) (left right : List RefWorld.Domain) :
    traceOf T (left ++ right) = traceOf T left ++ traceOf T right := by
  simp [traceOf, List.filterMap_append]
theorem traceOf_replicate_tick (T : Answers) (n : Nat) :
    traceOf T (List.replicate n (.inr () : RefWorld.Domain)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [traceOf, List.replicate_succ] using ih
theorem calls_map_embed_public {β : Type} (T : Answers) (program : M β) (hp : PublicVerdict.Only program) :
    SphincsSecurity.QueryCap.calls RefCharged ((SourceReplay.queried T program).map embed) =
      (SourceReplay.queried T program).length := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rw [SourceReplay.queried_query_bind, List.map_cons, SphincsSecurity.QueryCap.calls_cons,
        ih (T input) (hn _), List.length_cons]
      rcases input with (n | x) | c
      · exact False.elim hi
      · simp only [embed, RefCharged, if_true]; omega
      · exact False.elim hi
theorem verdict_recorded_fixed {β : Type} (T : Answers) (program : M β) (hp : PublicVerdict.Only program) :
    simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded (simulateQ verdictImpl program)) =
      pure (evalWithAnswerFn T program, (SourceReplay.queried T program).map embed) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rcases input with (n | x) | c
      · exact False.elim hi
      · rw [simulateQ_bind, simulateQ_spec_query]
        change simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded
          (liftM (RefWorld.query (.inl (.inr x))) >>= fun answer => simulateQ verdictImpl (next answer))) = _
        rw [SphincsSecurity.QueryCap.recorded_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
        change (pure (T (.inl (.inr x))) >>= fun answer =>
          simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded (simulateQ verdictImpl (next answer))) >>=
            fun result => pure (result.1, (.inl (.inr x) : RefWorld.Domain) :: result.2)) = _
        rw [pure_bind, ih _ (hn _), pure_bind, SourceReplay.queried_query_bind, evalWithAnswerFn_bind, eval_query]
        rfl
      · exact False.elim hi
theorem probEvent_bind_mono {α β γ : Type} (mx : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
    (p : β → Prop) (r : γ → Prop) (h : ∀ x, Pr[p | f x] ≤ Pr[r | g x]) :
    Pr[p | mx >>= f] ≤ Pr[r | mx >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
theorem cap_recorded_le {ι β : Type} {spec : OracleSpec ι} (selected : ι → Prop) [DecidablePred selected]
    (impl : QueryImpl spec ProbComp) (computation : OracleComp spec β) (budget : Nat)
    (event : List ι → Prop) :
    Pr[fun result => event result.2 ∧ SphincsSecurity.QueryCap.calls selected result.2 ≤ budget |
        simulateQ impl (SphincsSecurity.QueryCap.recorded computation)] ≤
      Pr[fun result => event result.2 |
        simulateQ impl (SphincsSecurity.QueryCap.recorded (SphincsSecurity.QueryCap.run selected computation budget))] := by
  induction computation using OracleComp.inductionOn generalizing budget event with
  | pure value =>
      simp only [SphincsSecurity.QueryCap.recorded_pure, SphincsSecurity.QueryCap.run_pure, simulateQ_pure,
        probEvent_pure]
      split_ifs with h1 h2 <;> simp_all
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryCap.run_query_bind]
      by_cases hs : selected input
      · rw [if_pos hs]
        cases budget with
        | zero =>
            refine le_trans (le_of_eq ?_) zero_le
            rw [probEvent_eq_zero_iff]
            intro result hresult hevent
            simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, mem_support_bind_iff,
              mem_support_pure_iff] at hresult
            obtain ⟨answer, -, tail, -, rfl⟩ := hresult
            have h := hevent.2
            rw [SphincsSecurity.QueryCap.calls_cons, if_pos hs] at h
            omega
        | succ remaining =>
            rw [SphincsSecurity.QueryCap.recorded_query_bind]
            simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
            apply probEvent_bind_mono
            intro answer
            simp only [bind_pure_comp, probEvent_map]
            refine le_trans (le_of_eq (probEvent_ext ?_)) (ih answer remaining (fun tail => event (input :: tail)))
            intro tail _
            simp only [Function.comp_apply, SphincsSecurity.QueryCap.calls_cons, if_pos hs]
            constructor
            · rintro ⟨he, hc⟩; exact ⟨he, by omega⟩
            · rintro ⟨he, hc⟩; exact ⟨he, by omega⟩
      · rw [if_neg hs, SphincsSecurity.QueryCap.recorded_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
        apply probEvent_bind_mono
        intro answer
        simp only [bind_pure_comp, probEvent_map]
        refine le_trans (le_of_eq (probEvent_ext ?_)) (ih answer budget (fun tail => event (input :: tail)))
        intro tail _
        simp only [Function.comp_apply, SphincsSecurity.QueryCap.calls_cons, if_neg hs, Nat.zero_add]
end SigGolfCandidate.T3.Security.Wots.Ref
end
-- ==== merged from T3_Secc_WotsExtractChain ====
section

namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem mem_entriesOf {answers : Answers} {qs : List Spec.Domain} {input : HashInput}
    (h : (.inl (.inr input) : Spec.Domain) ∈ qs) : (input, answers (.inl (.inr input))) ∈ entriesOf answers qs := by
  unfold entriesOf
  exact List.mem_filterMap.mpr ⟨_, h, rfl⟩
theorem mem_entriesOf_iff {answers : Answers} {qs : List Spec.Domain} {input : HashInput} {answer : HashOutput} :
    (input, answer) ∈ entriesOf answers qs ↔
      (.inl (.inr input) : Spec.Domain) ∈ qs ∧ answers (.inl (.inr input)) = answer := by
  unfold entriesOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨q, hq, he⟩
    rcases q with (n | input') | c
    · simp at he
    · simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨hq, rfl⟩
    · simp at he
  · rintro ⟨hq, rfl⟩
    exact ⟨_, hq, rfl⟩
theorem entriesOf_mono {answers : Answers} {qs qs' : List Spec.Domain} (hsub : ∀ q ∈ qs, q ∈ qs') :
    ∀ e ∈ entriesOf answers qs, e ∈ entriesOf answers qs' := by
  rintro ⟨input, answer⟩ he
  obtain ⟨hq, ha⟩ := mem_entriesOf_iff.mp he
  exact mem_entriesOf_iff.mpr ⟨hsub _ hq, ha⟩
theorem seenRow_of_mem {answers : Answers} {qs : List Spec.Domain} {a : ChainAddr} {step : Nat}
    {value out : Digest} (hq : (.inl (.inr (chainRow a step value)) : Spec.Domain) ∈ qs)
    (hout : low (answers (.inl (.inr (chainRow a step value)))) = out) :
    SeenRow (entriesOf answers qs) a step value out :=
  ⟨_, mem_entriesOf hq, hout⟩
theorem hashPath_join_core (answers : Answers) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (target : Nat → Digest) (Good : Nat → Prop)
    (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (shortHash (honestInput step)) = target (step + 1))
    (parse : ∀ step, step < count → ∀ value,
      pad64 (input step value) = pad64 (honestInput step) → value = target step ∧ Good step)
    (reaches : pathValue answers input initial count = target count) :
    (initial = target 0 ∧ ∀ step, step < count →
        Good step ∧ pad64 (pathInput answers input initial step) = pad64 (honestInput step)) ∨
      ∃ step, step < count ∧
        .inl (.inr (pad64 (pathInput answers input initial step))) ∈
          queried answers (hashPath input count initial) ∧
        HashHit answers (pad64 (honestInput step)) (pad64 (pathInput answers input initial step)) ∧
        ∀ later, step < later → later < count →
          Good later ∧ pad64 (pathInput answers input initial later) = pad64 (honestInput later) := by
  induction count with
  | zero => exact Or.inl ⟨reaches, fun step hstep => by omega⟩
  | succ count ih =>
      by_cases heq : pad64 (pathInput answers input initial count) = pad64 (honestInput count)
      · obtain ⟨hprev, hgood⟩ := parse count (by omega) _ heq
        rcases ih (fun step hstep => reference step (by omega))
          (fun step hstep => parse step (by omega)) hprev with ⟨hinit, hall⟩ | ⟨step, hstep, _, hhit, hlater⟩
        · left
          refine ⟨hinit, fun step hstep => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hstep with hlt | rfl
          · exact hall step hlt
          · exact ⟨hgood, heq⟩
        · refine Or.inr ⟨step, by omega, pathInput_queried answers input initial _ _ (by omega), hhit, ?_⟩
          intro later h1 h2
          rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with hlt | rfl
          · exact hlater later h1 hlt
          · exact ⟨hgood, heq⟩
      · right
        refine ⟨count, by omega, pathInput_queried answers input initial _ _ (by omega), ⟨heq, ?_⟩,
          fun later h1 h2 => by omega⟩
        rw [pathValue_succ] at reaches
        exact reaches.trans (reference count (by omega)).symm
theorem pathValue_succ_of_low (answers : Answers) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (initial : Digest) (step : Nat) (next : Digest)
    (href : evalWithAnswerFn answers (shortHash (honestInput step)) = next)
    (hlow : (answers (.inl (.inr (pad64 (pathInput answers input initial step))))).extractLsb' 0 128 =
      (answers (.inl (.inr (pad64 (honestInput step))))).extractLsb' 0 128) :
    pathValue answers input initial (step + 1) = next := by
  rw [pathValue_succ, eval_shortHash, hlow]
  exact href
theorem hashPath_join (answers : Answers) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (target : Nat → Digest) (Good : Nat → Prop)
    (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (shortHash (honestInput step)) = target (step + 1))
    (parse : ∀ step, step < count → ∀ value,
      pad64 (input step value) = pad64 (honestInput step) → value = target step ∧ Good step)
    (reaches : pathValue answers input initial count = target count) :
    (initial = target 0 ∧
      (∀ step, step < count → Good step ∧ pad64 (pathInput answers input initial step) = pad64 (honestInput step)) ∧
      ∀ s, s ≤ count → pathValue answers input initial s = target s) ∨
    ∃ step, step < count ∧
      .inl (.inr (pad64 (pathInput answers input initial step))) ∈ queried answers (hashPath input count initial) ∧
      HashHit answers (pad64 (honestInput step)) (pad64 (pathInput answers input initial step)) ∧
      (∀ later, step < later → later < count →
        Good later ∧ pad64 (pathInput answers input initial later) = pad64 (honestInput later)) ∧
      ∀ s, step < s → s ≤ count → pathValue answers input initial s = target s := by
  rcases hashPath_join_core answers input honestInput target Good initial count reference parse reaches with
    ⟨hinit, hall⟩ | ⟨step, hstep, hq, hhit, hlater⟩
  · refine Or.inl ⟨hinit, hall, ?_⟩
    intro s hs
    induction s with
    | zero => exact hinit
    | succ s ih =>
        exact pathValue_succ_of_low answers input honestInput initial s _ (reference s (by omega))
          (by rw [(hall s (by omega)).2])
  · refine Or.inr ⟨step, hstep, hq, hhit, hlater, ?_⟩
    intro s hs hsc
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    rcases Nat.lt_or_ge step k with hk | hk
    · exact pathValue_succ_of_low answers input honestInput initial k _ (reference k (by omega))
        (by rw [(hlater k hk (by omega)).2])
    · have hk' : k = step := by omega
      subst hk'
      exact pathValue_succ_of_low answers input honestInput initial k _ (reference k (by omega)) hhit.2
theorem chainP_join (answers : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (value seed : Digest)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64)
    (hsteps : count = 0 ∨ start + count ≤ 8)
    (reaches : evalWithAnswerFn answers (chainP lay tree leaf i start count pad0 pad1 headerPad value) =
      honestChainValue answers lay tree leaf i seed (start + count)) :
    (value = honestChainValue answers lay tree leaf i seed start ∧ (0 < count → pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∧
      ∀ s, s ≤ count → pathValue answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value s =
        honestChainValue answers lay tree leaf i seed (start + s)) ∨
    ∃ step, step < count ∧
      .inl (.inr (pad64 (pathInput answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step))) ∈
        queried answers (chainP lay tree leaf i start count pad0 pad1 headerPad value) ∧
      HashHit answers
        (pad64 (chainInput lay tree leaf i (start + step)
          (honestChainValue answers lay tree leaf i seed (start + step))))
        (pad64 (pathInput answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step)) ∧
      (step + 1 < count → pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∧
      (∀ later, step < later → later < count →
        pathInput answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value later =
          chainInput lay tree leaf i (start + later)
            (honestChainValue answers lay tree leaf i seed (start + later))) ∧
      ∀ s, step < s → s ≤ count → pathValue answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value s =
        honestChainValue answers lay tree leaf i seed (start + s) := by
  rw [chainP_eq_hashPath] at reaches ⊢
  have h := hashPath_join answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad)
    (fun step => chainInput lay tree leaf i (start + step)
      (honestChainValue answers lay tree leaf i seed (start + step)))
    (fun step => honestChainValue answers lay tree leaf i seed (start + step))
    (fun _ => pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) value count
    (fun step _ => by simpa only [Nat.add_assoc] using
      honestChainValue_succ answers lay tree leaf i seed (start + step))
    (fun step hstep current heq => by
      have hs : start + step < 8 := by rcases hsteps with hz | hb <;> omega
      simp only [chainPathInput, chainInput_eq_zero _ _ _ _ _ _ ht hl hi hs, pad64_chainInputP] at heq
      have hhp := chainInputP_headerPad_eq heq
      obtain ⟨hp0, _, hp1, hv⟩ := chainInputP_fields heq
      exact ⟨hv, hp0, hp1, hhp⟩) reaches
  rcases h with ⟨hvalue, hpads, hvals⟩ | ⟨step, hstep, hq, hhit, hlater, hvals⟩
  · exact Or.inl ⟨by simpa using hvalue, fun hcount => (hpads 0 hcount).1, hvals⟩
  · refine Or.inr ⟨step, hstep, hq, hhit, fun h => (hlater (step + 1) (by omega) h).1, ?_, hvals⟩
    intro later h1 h2
    have he := (hlater later h1 h2).2
    simp only [pathInput, chainPathInput, chainInput_padded, pad64_chainInputP] at he ⊢
    exact he
theorem chainP_frontier (answers : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (pad0 pad1 : Digest) (headerPad : BitVec 64) (value seed : Digest)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64)
    (hsteps : count = 0 ∨ start + count ≤ 8)
    (reaches : evalWithAnswerFn answers (chainP lay tree leaf i start count pad0 pad1 headerPad value) =
      honestChainValue answers lay tree leaf i seed (start + count))
    (W : Nat) (hW : start < W) (hWc : W ≤ start + count) :
    (∃ step, step < count ∧
      .inl (.inr (pad64 (pathInput answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step))) ∈
        queried answers (chainP lay tree leaf i start count pad0 pad1 headerPad value) ∧
      HashHit answers
        (pad64 (chainInput lay tree leaf i (start + step)
          (honestChainValue answers lay tree leaf i seed (start + step))))
        (pad64 (pathInput answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value step)) ∧
      (¬(pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0) ∨ W ≤ start + step)) ∨
    (pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0 ∧
      pathValue answers (chainPathInput lay tree leaf i start pad0 pad1 headerPad) value (W - start) =
        honestChainValue answers lay tree leaf i seed W) := by
  rcases chainP_join answers lay tree leaf i start count pad0 pad1 headerPad value seed ht hl hi hsteps reaches with
    ⟨_, hpads, hvals⟩ | ⟨step, hstep, hq, hhit, _, _, hvals⟩
  · obtain ⟨h0, h1, hh⟩ := hpads (by omega)
    refine Or.inr ⟨h0, h1, hh, ?_⟩
    rw [hvals (W - start) (by omega), Nat.add_sub_cancel' (le_of_lt hW)]
  · by_cases hp : pad0 = 0 ∧ pad1 = 0 ∧ headerPad = 0
    · by_cases hs : W ≤ start + step
      · exact Or.inl ⟨step, hstep, hq, hhit, Or.inr hs⟩
      · refine Or.inr ⟨hp.1, hp.2.1, hp.2.2, ?_⟩
        rw [hvals (W - start) (by omega) (by omega), Nat.add_sub_cancel' (le_of_lt hW)]
    · exact Or.inl ⟨step, hstep, hq, hhit, Or.inl hp⟩
theorem chainP_row (answers : Answers) (a : ChainAddr) (start count : Nat) (value : Digest) (s : Nat)
    (ht : a.key.tree < 2^31) (hl : a.key.leaf < 4096) (hi : a.chain < 64)
    (hsteps : start + count ≤ 8) (hs : s < count) :
    (.inl (.inr (chainRow a (start + s)
        (pathValue answers (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value s))) :
        Spec.Domain) ∈
      queried answers (chainP a.key.lay a.key.tree a.key.leaf a.chain start count 0 0 0 value) ∧
    low (answers (.inl (.inr (chainRow a (start + s)
        (pathValue answers (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value s))))) =
      pathValue answers (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value (s + 1) := by
  have hrow : pad64 (pathInput answers (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value s) =
      chainRow a (start + s)
        (pathValue answers (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value s) := by
    simp only [pathInput, chainPathInput, pad64_chainInputP, chainRow]
    exact (chainInput_eq_zero a.key.lay a.key.tree a.key.leaf a.chain (start + s) _ ht hl hi (by omega)).symm
  constructor
  · rw [chainP_eq_hashPath, ← hrow]
    exact pathInput_queried answers (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value count s hs
  · rw [pathValue_succ, eval_shortHash, hrow]
    rfl
theorem chain_seen (answers : Answers) (a : ChainAddr) (start count : Nat) (value out : Digest)
    (qs : List Spec.Domain)
    (ht : a.key.tree < 2^31) (hl : a.key.leaf < 4096) (hi : a.chain < 64)
    (hsteps : start + count ≤ 8)
    (hsub : ∀ q ∈ queried answers (chainP a.key.lay a.key.tree a.key.leaf a.chain start count 0 0 0 value), q ∈ qs)
    (W : Nat) (hW : start < W) (hWc : W ≤ start + count)
    (hval : pathValue answers (chainPathInput a.key.lay a.key.tree a.key.leaf a.chain start 0 0 0) value (W - start) = out) :
    (∃ x, SeenRow (entriesOf answers qs) a (W - 1) x out) ∧
      (start + 2 ≤ W → ∃ y x, SeenRow (entriesOf answers qs) a (W - 2) y x ∧
        SeenRow (entriesOf answers qs) a (W - 1) x out) := by
  have hlast := chainP_row answers a start count value (W - 1 - start) ht hl hi hsteps (by omega)
  have hstep1 : start + (W - 1 - start) = W - 1 := by omega
  have hsucc1 : W - 1 - start + 1 = W - start := by omega
  rw [hstep1, hsucc1, hval] at hlast
  have hcontact := seenRow_of_mem (hsub _ hlast.1) hlast.2
  refine ⟨⟨_, hcontact⟩, fun h2 => ?_⟩
  have hprev := chainP_row answers a start count value (W - 2 - start) ht hl hi hsteps (by omega)
  have hstep2 : start + (W - 2 - start) = W - 2 := by omega
  have hsucc2 : W - 2 - start + 1 = W - 1 - start := by omega
  rw [hstep2, hsucc2] at hprev
  exact ⟨_, _, seenRow_of_mem (hsub _ hprev.1) hprev.2, hcontact⟩
def SourceLeaf (L : LeafAddr) : Prop := L.tree < 2 ^ 31 ∧ L.leaf < 2 ^ height L.lay
def SourceChain (a : ChainAddr) : Prop := SourceLeaf a.key ∧ a.chain < chainCount a.key.lay
def PosSource : Extract.Pos → Prop
  | .chain lay tree leaf i step => tree < 2 ^ 31 ∧ leaf < 2 ^ height lay ∧ i < chainCount lay ∧ step + 1 < 2 ^ width lay i
  | .leaf lay tree leaf => tree < 2 ^ 31 ∧ leaf < 2 ^ height lay
  | .node lay tree level node => tree < 2 ^ 31 ∧ level < height lay ∧ node < 2 ^ (height lay - level - 1)
  | .forest index => index < 2 ^ 31
  | .ftsLeaf index coord leaf => index < 2 ^ 31 ∧ coord < 7 ∧ leaf < 2048
  | .ftsNode index coord level node => index < 2 ^ 31 ∧ coord < 7 ∧ level < 11 ∧ node < 2 ^ (11 - level - 1)
theorem height_le' (lay : Layer) : height lay ≤ 12 := by fin_cases lay <;> decide
theorem chainCount_le' (lay : Layer) : chainCount lay ≤ 58 := by fin_cases lay <;> decide
theorem width_le' (lay : Layer) (i : Nat) : width lay i ≤ 3 := by unfold width; omega
end SigGolfCandidate.T3.Security.WotsExtract
end
-- ==== merged from T3_Secc_WotsExtractWord ====
section

namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
/-- T51: the top word of `dummyTop` (`0x818144891224489167818181818181a9`). -/
def dummyDigest0 : Digest := BitVec.ofNat 128 172141607814731047335388003572044104105
def dummyDigestLow : Digest := BitVec.ofNat 128 267364716866451649887797291077026409910
def dummyDigest (lay : Layer) : Digest := if lay.val = 0 then dummyDigest0 else dummyDigestLow
theorem dummyDigest_decode (lay : Layer) : decode lay (dummyDigest lay) = some (dummyDigits lay) := by
  fin_cases lay
  · show decode 0 dummyDigest0 = some (dummyDigits 0)
    decide +kernel
  · show decode 1 dummyDigestLow = some (dummyDigits 1)
    decide +kernel
  · show decode 2 dummyDigestLow = some (dummyDigits 2)
    decide +kernel
  · show decode 3 dummyDigestLow = some (dummyDigits 3)
    decide +kernel
end SigGolfCandidate.T3.Security.WotsExtract
namespace SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.WotsExtract
theorem dummyDigits_valid (lay : Layer) : ∃ value : Digest, decode lay value = some (dummyDigits lay) :=
  ⟨dummyDigest lay, dummyDigest_decode lay⟩
theorem word_cases {lay : Layer} {refDigest candDigest : Digest} {refDigits candDigits : List Nat}
    (hr : decode lay refDigest = some refDigits) (hc : decode lay candDigest = some candDigits) :
    candDigits = refDigits ∨
      (∃ i, MixedCode.UnitNeighborAt (decodedWord hr) (decodedWord hc) i) ∨
      (∃ i, (decodedWord hc i).val + 2 ≤ (decodedWord hr i).val) ∨
      (∃ i j, i ≠ j ∧ (decodedWord hc i).val < (decodedWord hr i).val ∧
        (decodedWord hc j).val < (decodedWord hr j).val) := by
  by_cases he : candDigits = refDigits
  · exact Or.inl he
  right
  have hne : decodedWord hc ≠ decodedWord hr := by
    intro hw
    apply he
    rw [← decodedWord_list hc, ← decodedWord_list hr, hw]
  rcases MixedCode.backwardWork_trichotomy (decodedWord_valid hr) (decodedWord_valid hc) with h | h | h
  · exact (hne h).elim
  · exact Or.inl h
  · exact Or.inr (MixedCode.two_backward_steps h)
end SigGolfCandidate.T3.Security.Wots
namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def routeLeaf (index : Nat) (lay : Layer) : LeafAddr := ⟨lay, (route index lay).2, (route index lay).1⟩
theorem route_split (index b h : Nat) : index / 2 ^ (b + h) * 2 ^ h + index / 2 ^ b % 2 ^ h = index / 2 ^ b := by
  rw [pow_add, ← Nat.div_div_eq_div_mul]
  exact Nat.div_add_mod' (index / 2 ^ b) (2 ^ h)
theorem route_tree_succ (index : Nat) (lay : Layer) (h : lay.val < 3) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 = (route index ⟨lay.val + 1, by omega⟩).2 := by
  fin_cases lay
  · show index / 2 ^ (19 + 12) * 2 ^ 12 + index / 2 ^ 19 % 2 ^ 12 = index / 2 ^ 19
    exact route_split index 19 12
  · show index / 2 ^ (12 + 7) * 2 ^ 7 + index / 2 ^ 12 % 2 ^ 7 = index / 2 ^ 12
    exact route_split index 12 7
  · show index / 2 ^ (6 + 6) * 2 ^ 6 + index / 2 ^ 6 % 2 ^ 6 = index / 2 ^ 6
    exact route_split index 6 6
  · exact absurd h (by decide)
theorem route_forest (index : Nat) (lay : Layer) (h : ¬lay.val < 3) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 = index := by
  fin_cases lay
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · show index / 2 ^ (0 + 6) * 2 ^ 6 + index / 2 ^ 0 % 2 ^ 6 = index
    have := route_split index 0 6
    simpa using this
theorem routeLeaf_source (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31) :
    (routeLeaf index lay).tree < 2 ^ 31 ∧ (routeLeaf index lay).leaf < 2 ^ height (routeLeaf index lay).lay :=
  ⟨lt_of_le_of_lt (Nat.div_le_self _ _) hidx, route_leaf_bound index lay⟩
end SigGolfCandidate.T3.Security.WotsExtract
end
-- ==== merged from T3_Secc_WotsExtractLayer ====
section

namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
section mono
variable {answers : Answers} {trace trace' : List Entry}
theorem seenRow_mono {a : ChainAddr} {step : Nat} {value out : Digest} (h : SeenRow trace a step value out)
    (hsub : ∀ e ∈ trace, e ∈ trace') : SeenRow trace' a step value out := by
  obtain ⟨answer, hm, hl⟩ := h
  exact ⟨answer, hsub _ hm, hl⟩
theorem contactAt_mono {a : ChainAddr} (h : ContactAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    ContactAt answers trace' a := by
  obtain ⟨hd, value, hs⟩ := h
  exact ⟨hd, value, seenRow_mono hs hsub⟩
theorem twoEdgeAt_mono {a : ChainAddr} (h : TwoEdgeAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    TwoEdgeAt answers trace' a := by
  obtain ⟨hd, start, middle, h1, h2⟩ := h
  exact ⟨hd, start, middle, seenRow_mono h1 hsub, seenRow_mono h2 hsub⟩
theorem encodingMatchAt_mono {L : LeafAddr} (h : EncodingMatchAt answers trace L) (hsub : ∀ e ∈ trace, e ∈ trace') :
    EncodingMatchAt answers trace' L := by
  obtain ⟨message, counter, answer, hm, hne, hd⟩ := h
  exact ⟨message, counter, answer, hsub _ hm, hne, hd⟩
theorem markerAt_mono {a : ChainAddr} (h : MarkerAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    MarkerAt answers trace' a := by
  obtain ⟨message, counter, answer, digits, hm, hne, hd, hl, hu⟩ := h
  exact ⟨message, counter, answer, digits, hsub _ hm, hne, hd, hl, hu⟩
end mono
end SigGolfCandidate.T3.Security.WotsExtract
end
-- ==== merged from T3_Secc_WotsExtractVerify ====
section

namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers treeValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
end SigGolfCandidate.T3.Security.WotsExtract
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.WotsExtract
open SigGolfCandidate.T3.Correctness (Answers)
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_WotsTransportShort ====
section

namespace SigGolfCandidate.T3.Security.Wots.Ref
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def ShortQuery : T3.Spec.Domain → Prop
  | .inl (.inl _) => True
  | .inl (.inr input) => input.length ≤ SeccLaw.maxInputLength
  | .inr _ => True
def ShortAgree (A T : Answers) : Prop := ∀ query, ShortQuery query → A query = T query
theorem ShortAgree.symm {A T : Answers} (h : ShortAgree A T) : ShortAgree T A :=
  fun query hq => (h query hq).symm
theorem ShortAgree.public {A T : Answers} (h : ShortAgree A T) (input : HashInput)
    (hinput : input.length ≤ SeccLaw.maxInputLength) : A (.inl (.inr input)) = T (.inl (.inr input)) :=
  h _ hinput
theorem ShortAgree.priv {A T : Answers} (h : ShortAgree A T) (coordinate : Coordinate) :
    A (.inr coordinate) = T (.inr coordinate) := h _ trivial
def ShortRespects {α : Type} (program : M α) : Prop :=
  ∀ A T : Answers, ShortAgree A T → evalWithAnswerFn A program = evalWithAnswerFn T program
theorem ShortRespects.pure' {α : Type} (x : α) : ShortRespects (pure x : M α) := fun _ _ _ => rfl
theorem ShortRespects.bind {α β : Type} {p : M α} {f : α → M β} (hp : ShortRespects p)
    (hf : ∀ x, ShortRespects (f x)) : ShortRespects (p >>= f) := by
  intro A T h
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, hp A T h]
  exact hf _ A T h
theorem ShortRespects.map {α β : Type} {p : M α} (f : α → β) (hp : ShortRespects p) :
    ShortRespects (f <$> p) := by
  intro A T h
  rw [evalWithAnswerFn_map, evalWithAnswerFn_map, hp A T h]
theorem ShortRespects.shortHash (input : HashInput) (h : (pad64 input).length ≤ SeccLaw.maxInputLength) :
    ShortRespects (T3.shortHash input) := by
  intro A T hAT
  rw [eval_shortHash, eval_shortHash, hAT.public _ h]
/-- C4: `T3.projHash` (either half) respects short-input agreement like `shortHash`. -/
theorem ShortRespects.projHash (high : Bool) (input : HashInput)
    (h : (pad64 input).length ≤ SeccLaw.maxInputLength) : ShortRespects (T3.projHash high input) := by
  intro A T hAT
  have e : ∀ X : Answers, evalWithAnswerFn X (T3.projHash high input) =
      T3.projHalf high (X (.inl (.inr (pad64 input)))) := fun _ => rfl
  rw [e, e, hAT.public _ h]
theorem ShortRespects.privatePair (tag lay tree position index : Nat) :
    ShortRespects (T3.privatePair tag lay tree position index) := by
  intro A T hAT
  unfold T3.privatePair T3.privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [show evalWithAnswerFn A (liftM (T3.Spec.query (.inr (.inl (header tag lay tree position index))))) =
      A (.inr (.inl (header tag lay tree position index))) from simulateQ_spec_query A _,
    show evalWithAnswerFn T (liftM (T3.Spec.query (.inr (.inl (header tag lay tree position index))))) =
      T (.inr (.inl (header tag lay tree position index))) from simulateQ_spec_query T _,
    hAT.priv]
theorem ShortRespects.foldlM {β γ : Type} (l : List β) (f : γ → β → M γ)
    (hf : ∀ x ∈ l, ∀ s, ShortRespects (f s x)) : ∀ init, ShortRespects (l.foldlM f init) := by
  induction l with
  | nil => intro init; exact ShortRespects.pure' init
  | cons x xs ih =>
      intro init
      rw [List.foldlM_cons]
      exact ShortRespects.bind (hf x List.mem_cons_self init)
        fun s => ih (fun y hy s => hf y (List.mem_cons_of_mem x hy) s) s
theorem ShortRespects.mapM {α β : Type} (l : List α) (f : α → M β) (hf : ∀ x ∈ l, ShortRespects (f x)) :
    ShortRespects (l.mapM f) := by
  intro A T h
  rw [Correctness.eval_mapM, Correctness.eval_mapM]
  exact List.map_congr_left fun x hx => hf x hx A T h
theorem pad64_length_le (input : HashInput) : (pad64 input).length ≤ input.length + 63 := by
  rw [Cost.pad64_length]
  omega
theorem chainCount_le (lay : Layer) : chainCount lay ≤ 58 := by
  fin_cases lay <;> decide
theorem chainInput_length (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    (chainInput lay tree leaf i step value).length = 64 := by
  simp [chainInput, zero16, bytesLE_length]
theorem listInput_length (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    (Extract.listInput first hdr rest).length = 32 + 16 * rest.length := by
  simp only [Extract.listInput, List.length_append, bytesLE_length, digest_list_bytes_length]
theorem short_of_le (input : HashInput) (h : input.length ≤ 4033) :
    (pad64 input).length ≤ SeccLaw.maxInputLength := by
  have := pad64_length_le input
  unfold SeccLaw.maxInputLength
  omega
theorem chain_respects (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    ShortRespects (chain lay tree leaf i start count value) := by
  unfold chain
  exact ShortRespects.foldlM _ _ (fun step _ v => ShortRespects.shortHash _
    (short_of_le _ (by rw [chainInput_length]; omega))) value
theorem topChain_respects (leaf i start count : Nat) (value : Digest) :
    ShortRespects (topChain leaf i start count value) := by
  unfold topChain
  exact ShortRespects.foldlM _ _ (fun step _ v => ShortRespects.projHash _ _
    (short_of_le _ (by
      have h : (topChainInput leaf i step v).length = 64 := by
        unfold topChainInput; split <;> simp [chainInput, bytesLE_length, zero16]
      rw [h]; omega))) value
theorem layChain_respects (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    ShortRespects (layChain lay tree leaf i start count value) := by
  unfold layChain; split
  · exact topChain_respects _ _ _ _ _
  · exact chain_respects _ _ _ _ _ _ _
theorem leafHash_respects (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : ends.length ≤ 200) :
    ShortRespects (leafHash lay tree leaf ends) := by
  unfold leafHash
  apply ShortRespects.projHash
  apply short_of_le
  rw [leafInput_length]
  split_ifs <;> omega
theorem nodeHash_respects (tag lay tree heap : Nat) (left right : Digest) :
    ShortRespects (nodeHash tag lay tree heap left right) := by
  unfold nodeHash
  apply ShortRespects.projHash
  apply short_of_le
  simp [zero16, bytesLE_length]
theorem buildLevel_respects (tag lay tree h level : Nat) (nodes : List Digest) :
    ShortRespects (buildLevel tag lay tree h level nodes) := by
  unfold buildLevel
  exact ShortRespects.mapM _ _ fun i _ => nodeHash_respects _ _ _ _ _ _
theorem buildLevels_respects (tag lay tree h : Nat) (leaves : List Digest) :
    ShortRespects (buildLevels tag lay tree h leaves) := by
  unfold buildLevels
  exact ShortRespects.foldlM _ _ (fun level _ levels =>
    ShortRespects.bind (buildLevel_respects _ _ _ _ _ _) fun _ => ShortRespects.pure' _) _
theorem ftsLeaf_respects (index coord leaf : Nat) (secret : Digest) :
    ShortRespects (ftsLeaf index coord leaf secret) := by
  unfold ftsLeaf
  apply ShortRespects.shortHash
  apply short_of_le
  simp [zero16, bytesLE_length]
theorem buildFts_respects (index coord : Nat) : ShortRespects (buildFts index coord) := by
  unfold buildFts
  refine ShortRespects.bind (ShortRespects.foldlM _ _ (fun pair _ state => ?_) _) fun state =>
    ShortRespects.bind (buildLevels_respects _ _ _ _ _) fun _ => ShortRespects.pure' _
  refine ShortRespects.bind (ShortRespects.privatePair _ _ _ _ _) fun seeds => ?_
  rcases seeds with ⟨left, right⟩
  exact ShortRespects.bind (ftsLeaf_respects _ _ _ _) fun _ =>
    ShortRespects.bind (ftsLeaf_respects _ _ _ _) fun _ => ShortRespects.pure' _
theorem forestPk_respects (index : Nat) (roots : List Digest) (hlen : roots.length ≤ 200) :
    ShortRespects (forestPk index roots) := by
  unfold forestPk
  apply ShortRespects.shortHash
  apply short_of_le
  simp only [List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop]
  omega
theorem counterSearch_respects (lay : Layer) (tree leaf : Nat) (message : Digest) (counter fuel : Nat) :
    ShortRespects (counterSearch lay tree leaf message counter fuel) := by
  induction fuel generalizing counter with
  | zero => exact ShortRespects.pure' _
  | succ fuel ih =>
      unfold counterSearch
      refine ShortRespects.bind (ShortRespects.shortHash _ (short_of_le _ ?_)) fun answer => ?_
      · simp [encodingInput, bytesLE_length]
      · cases searchDecode lay answer with
        | none => exact ih _
        | some digits => exact ShortRespects.pure' _
section objects
variable {A T : Answers} (hAT : ShortAgree A T)
include hAT
theorem leafSeed_short (lay : Layer) (tree leaf i : Nat) : leafSeed A lay tree leaf i = leafSeed T lay tree leaf i := by
  unfold leafSeed
  split_ifs
  · unfold Correctness.topLeafSeed Correctness.topCoefList
    congr 2
    funext j
    unfold Correctness.topCoef Correctness.topCoefN topSeedPair
    rw [ShortRespects.privatePair 0 0 0 _ 0 A T hAT]
  all_goals rw [ShortRespects.privatePair 0 lay.val tree (i / 2) leaf A T hAT]
theorem chainValue_short (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    evalWithAnswerFn A (chain lay tree leaf i start count value) =
      evalWithAnswerFn T (chain lay tree leaf i start count value) :=
  chain_respects lay tree leaf i start count value A T hAT
theorem honestChainValue_short (lay : Layer) (tree leaf i : Nat) (seed : Digest) (step : Nat) :
    honestChainValue A lay tree leaf i seed step = honestChainValue T lay tree leaf i seed step :=
  chainValue_short hAT lay tree leaf i 0 step seed
theorem leafEnd_short (lay : Layer) (tree leaf i : Nat) : leafEnd A lay tree leaf i = leafEnd T lay tree leaf i := by
  unfold leafEnd
  rw [leafSeed_short hAT]
  exact layChain_respects lay tree leaf i 0 (maxDigit lay i) (leafSeed T lay tree leaf i) A T hAT
theorem leafRoot_short (lay : Layer) (tree leaf : Nat) : leafRoot A lay tree leaf = leafRoot T lay tree leaf := by
  unfold leafRoot
  rw [List.map_congr_left (fun i _ => leafEnd_short hAT lay tree leaf i)]
  apply leafHash_respects
  · simp only [List.length_map, List.length_range]
    have := chainCount_le lay
    omega
  · exact hAT
theorem buildFts_short (index coord : Nat) :
    evalWithAnswerFn A (buildFts index coord) = evalWithAnswerFn T (buildFts index coord) :=
  buildFts_respects index coord A T hAT
end objects
end SigGolfCandidate.T3.Security.Wots.Ref
end
-- ==== merged from T3_Secc_WotsTransportCompletion ====
section

namespace SigGolfCandidate.T3.Security.Wots.Ref
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete (hashInputs finiteHashAnswer)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SphincsSecurity.Concrete.hashInputs
noncomputable local instance instFintypeCoordinate_wotsTransportCompletion : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsTransportCompletion : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable def fillAnswers (inputs : Finset HashInput) (state : LazyPrivate.State)
    (privateTable : FullGame.FullTable) (publicTable : inputs → HashOutput) : Answers
  | .inl (.inl n) => (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inl (.inr input) => (state.2 input).getD (finiteHashAnswer ∅ inputs publicTable input)
  | .inr coordinate => (state.1 coordinate).getD (privateTable coordinate)
theorem fillAnswers_empty (inputs : Finset HashInput) (privateTable : FullGame.FullTable)
    (publicTable : inputs → HashOutput) :
    fillAnswers inputs (∅, ∅) privateTable publicTable = eagerAnswers inputs privateTable publicTable := by
  funext query
  rcases query with (n | x) | c <;> rfl
theorem fillAnswers_known (inputs : Finset HashInput) (state : LazyPrivate.State)
    (privateTable : FullGame.FullTable) (publicTable : inputs → HashOutput) (input : T3.Spec.Domain)
    (answer : T3.Spec.Range input) (h : SourceReplay.known state input = some answer) :
    fillAnswers inputs state privateTable publicTable input = answer := by
  rcases input with (n | x) | c
  · cases h
  · change (state.2 x).getD _ = answer
    change state.2 x = some answer at h
    rw [h, Option.getD_some]
  · change (state.1 c).getD _ = answer
    change state.1 c = some answer at h
    rw [h, Option.getD_some]
theorem fillAnswers_public_update (inputs : Finset HashInput) (state : LazyPrivate.State)
    (privateTable : FullGame.FullTable) (publicTable : inputs → HashOutput) (x : HashInput) (hx : x ∈ inputs)
    (h : state.2 x = none) (value : HashOutput) :
    fillAnswers inputs (state.1, state.2.cacheQuery x value) privateTable publicTable =
      fillAnswers inputs state privateTable (Function.update publicTable ⟨x, hx⟩ value) := by
  funext query
  rcases query with (n | y) | c
  · rfl
  · change ((state.2.cacheQuery x value) y).getD (finiteHashAnswer ∅ inputs publicTable y) =
      (state.2 y).getD (finiteHashAnswer ∅ inputs (Function.update publicTable ⟨x, hx⟩ value) y)
    by_cases hy : y = x
    · subst y
      rw [QueryCache.cacheQuery_self, h, Option.getD_some, Option.getD_none,
        SphincsSecurity.Concrete.finiteHashAnswer_none ∅ inputs _ x hx rfl, Function.update_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ hy]
      cases hc : state.2 y with
      | some v => rfl
      | none =>
          simp only [Option.getD_none]
          by_cases hyi : y ∈ inputs
          · rw [SphincsSecurity.Concrete.finiteHashAnswer_none ∅ inputs _ y hyi rfl,
              SphincsSecurity.Concrete.finiteHashAnswer_none ∅ inputs _ y hyi rfl,
              Function.update_of_ne (fun heq => hy (congrArg Subtype.val heq))]
          · simp [finiteHashAnswer, hyi]
  · rfl
theorem fillAnswers_private_update (inputs : Finset HashInput) (state : LazyPrivate.State)
    (privateTable : FullGame.FullTable) (publicTable : inputs → HashOutput) (c : Coordinate)
    (h : state.1 c = none) (value : HashOutput) :
    fillAnswers inputs (state.1.cacheQuery c value, state.2) privateTable publicTable =
      fillAnswers inputs state (Function.update privateTable c value) publicTable := by
  funext query
  rcases query with (n | y) | d
  · rfl
  · rfl
  · change ((state.1.cacheQuery c value) d).getD (privateTable d) = (state.1 d).getD (Function.update privateTable c value d)
    by_cases hd : d = c
    · subst d
      rw [QueryCache.cacheQuery_self, h, Option.getD_some, Option.getD_none, Function.update_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ hd, Function.update_of_ne hd]
theorem hashInputs_map {α β : Type} (f : α → β) (computation : OracleComp OracleWorld α) :
    hashInputs (f <$> computation) = hashInputs computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [map_pure, SphincsSecurity.Concrete.hashInputs_pure]
  | query_bind input next ih =>
      rw [map_bind, SphincsSecurity.Concrete.hashInputs_query_bind,
        SphincsSecurity.Concrete.hashInputs_query_bind]
      simp only [ih]
      cases input <;> rfl
def InputsIn (inputs : Finset HashInput) {α : Type} (program : M α) (state : LazyPrivate.State) : Prop :=
  ∀ privateTable : FullGame.FullTable, (∀ c v, state.1 c = some v → privateTable c = v) →
    hashInputs (Derivation.tableRun privateTable (FirstHit.sourceRecord program state)) ⊆ inputs
theorem tableRun_sourceRecord_query_bind {α : Type} (privateTable : FullGame.FullTable) (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) (state : LazyPrivate.State) :
    Derivation.tableRun privateTable (FirstHit.sourceRecord (liftM (T3.Spec.query input) >>= next) state) =
      (Derivation.tableHandler privateTable input >>= fun answer =>
        (fun last => (⟨last.value, ⟨state, input, answer⟩ :: last.events, last.state⟩ : FirstHit.Recorded α)) <$>
          Derivation.tableRun privateTable (FirstHit.sourceRecord (next answer) (FirstHit.advance state input answer))) := by
  rw [FirstHit.sourceRecord_query_bind]
  unfold Derivation.tableRun
  rw [simulateQ_bind, simulateQ_spec_query]
  simp only [simulateQ_map]
  rfl
theorem tableHandler_world (privateTable : FullGame.FullTable) (input : OracleWorld.Domain) :
    Derivation.tableHandler privateTable (.inl input) = liftM (OracleWorld.query input) := rfl
theorem tableHandler_private (privateTable : FullGame.FullTable) (c : Coordinate) :
    Derivation.tableHandler privateTable (.inr c) = pure (privateTable c) := rfl
theorem exists_consistent (state : LazyPrivate.State) :
    ∃ privateTable : FullGame.FullTable, ∀ c v, state.1 c = some v → privateTable c = v := by
  refine ⟨fun c => (state.1 c).getD 0, fun c v hc => ?_⟩
  change (state.1 c).getD 0 = v
  rw [hc, Option.getD_some]
theorem InputsIn.public {inputs : Finset HashInput} {α : Type} {x : HashInput}
    {next : T3.Spec.Range (.inl (.inr x)) → M α} {state : LazyPrivate.State}
    (h : InputsIn inputs (liftM (T3.Spec.query (.inl (.inr x))) >>= next) state) :
    x ∈ inputs ∧ ∀ value : T3.Spec.Range (.inl (.inr x)),
      InputsIn inputs (next value) (FirstHit.advance state (.inl (.inr x)) value) := by
  obtain ⟨privateTable, hpriv⟩ := exists_consistent state
  constructor
  · apply h privateTable hpriv
    rw [tableRun_sourceRecord_query_bind, tableHandler_world]
    exact SphincsSecurity.Concrete.mem_hashInputs_hash_bind x _
  · intro value table htable
    have hstate : ∀ c v, state.1 c = some v → table c = v := htable
    have hsub := h table hstate
    rw [tableRun_sourceRecord_query_bind, tableHandler_world] at hsub
    intro row hrow
    apply hsub
    apply SphincsSecurity.Concrete.hashInputs_next_subset (.inr x) _ value
    rw [hashInputs_map]
    exact hrow
theorem InputsIn.coin {inputs : Finset HashInput} {α : Type} {n : Nat}
    {next : Fin (n + 1) → M α} {state : LazyPrivate.State}
    (h : InputsIn inputs (liftM (T3.Spec.query (.inl (.inl n))) >>= next) state) (value : Fin (n + 1)) :
    InputsIn inputs (next value) state := by
  intro table htable row hrow
  apply h table htable
  rw [tableRun_sourceRecord_query_bind, tableHandler_world]
  apply SphincsSecurity.Concrete.hashInputs_next_subset (.inl n) _ value
  rw [hashInputs_map]
  exact hrow
theorem InputsIn.priv {inputs : Finset HashInput} {α : Type} {c : Coordinate}
    {next : T3.Spec.Range (.inr c) → M α} {state : LazyPrivate.State}
    (h : InputsIn inputs (liftM (T3.Spec.query (.inr c)) >>= next) state) (value : T3.Spec.Range (.inr c))
    (hcached : ∀ v, state.1 c = some v → v = value) :
    InputsIn inputs (next value) (FirstHit.advance state (.inr c) value) := by
  intro table htable row hrow
  have hc : table c = value := by
    apply htable c value
    change (state.1.cacheQuery c value) c = some value
    rw [QueryCache.cacheQuery_self]
  have hstate : ∀ d v, state.1 d = some v → table d = v := by
    intro d v hd
    apply htable d v
    change (state.1.cacheQuery c value) d = some v
    by_cases hdc : d = c
    · subst d
      rw [QueryCache.cacheQuery_self, hcached v hd]
    · rw [QueryCache.cacheQuery_of_ne _ _ hdc]
      exact hd
  apply h table hstate
  rw [tableRun_sourceRecord_query_bind, tableHandler_private, pure_bind, hashInputs_map, hc]
  exact hrow
theorem advance_cached (state : LazyPrivate.State) (input : T3.Spec.Domain) (answer : T3.Spec.Range input)
    (h : SourceReplay.known state input = some answer) : FirstHit.advance state input answer = state := by
  rcases input with (n | x) | c
  · rfl
  · change (state.1, state.2.cacheQuery x answer) = state
    rw [PrivateTable.cacheQuery_cached state.2 x answer h]
  · change (state.1.cacheQuery c answer, state.2) = state
    rw [PrivateTable.cacheQuery_cached state.1 c answer h]
noncomputable def completedTail {α : Type} (inputs : Finset HashInput) (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) (state : LazyPrivate.State) (middle : T3.Spec.Range input × LazyPrivate.State) :
    ProbComp (FirstHit.Recorded α × Answers) :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (inputs → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun last => ((⟨last.value, ⟨state, input, middle.1⟩ :: last.events, last.state⟩ : FirstHit.Recorded α),
          fillAnswers inputs middle.2 privateTable publicTable)) <$>
        fixedRecord (fillAnswers inputs middle.2 privateTable publicTable) (next middle.1) middle.2
theorem lazy_coin (state : LazyPrivate.State) (n : Nat) :
    LazyPrivate.run (liftM (T3.Spec.query (.inl (.inl n)))) state =
      (fun c => (c, state)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := by
  rw [LazyPrivate.run_query]
  rfl
theorem lazy_public_fresh (state : LazyPrivate.State) (x : HashInput) (h : state.2 x = none) :
    LazyPrivate.run (liftM (T3.Spec.query (.inl (.inr x)))) state =
      (fun v => (v, (state.1, state.2.cacheQuery x v))) <$> ($ᵗ HashOutput : ProbComp HashOutput) := by
  have hq : liftM (T3.Spec.query (.inl (.inr x))) = (Sampling.publicHandler x : M HashOutput) := rfl
  rw [hq, LazyPrivate.run_publicQuery]
  change ((randomOracle (spec := SphincsSecurity.HashSpec) x).run state.2 >>= fun result =>
    pure (result.1, (state.1, result.2))) = _
  rw [QueryImpl.withCaching_run_none _ h]
  simp only [bind_pure_comp]
  rfl
theorem lazy_private_fresh (state : LazyPrivate.State) (c : Coordinate) (h : state.1 c = none) :
    LazyPrivate.run (liftM (T3.Spec.query (.inr c))) state =
      (fun v => (v, (state.1.cacheQuery c v, state.2))) <$> ($ᵗ HashOutput : ProbComp HashOutput) := by
  have hq : liftM (T3.Spec.query (.inr c)) = (privateHash c : M HashOutput) := rfl
  rw [hq, LazyPrivate.run_privateHash]
  rw [QueryImpl.withCaching_run_none _ h]
  simp only [bind_map_left, bind_pure_comp]
  rfl
theorem fixedWorld_public (F : Answers) (x : HashInput) :
    fixedWorld F (.inl (.inr x)) = pure (F (.inl (.inr x))) := rfl
theorem fixedWorld_private (F : Answers) (c : Coordinate) :
    fixedWorld F (.inr c) = pure (F (.inr c)) := rfl
noncomputable def eagerSide (inputs : Finset HashInput) {α : Type} (program : M α) (state : LazyPrivate.State) :
    ProbComp (FirstHit.Recorded α × Answers) :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (inputs → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun result => (result, fillAnswers inputs state privateTable publicTable)) <$>
        fixedRecord (fillAnswers inputs state privateTable publicTable) program state
theorem eagerSide_query_bind (inputs : Finset HashInput) {α : Type} (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) (state : LazyPrivate.State) :
    eagerSide inputs (liftM (T3.Spec.query input) >>= next) state =
      (($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
        ($ᵗ (inputs → HashOutput) : ProbComp _) >>= fun publicTable =>
          fixedWorld (fillAnswers inputs state privateTable publicTable) input >>= fun answer =>
            (fun last => ((⟨last.value, ⟨state, input, answer⟩ :: last.events, last.state⟩ : FirstHit.Recorded α),
                fillAnswers inputs state privateTable publicTable)) <$>
              fixedRecord (fillAnswers inputs state privateTable publicTable) (next answer)
                (FirstHit.advance state input answer)) := by
  unfold eagerSide
  simp only [fixedRecord_query_bind, map_bind, Functor.map_map]
theorem completion_coin (inputs : Finset HashInput) {α : Type} (n : Nat) (next : Fin (n + 1) → M α)
    (state : LazyPrivate.State) :
    𝒮[LazyPrivate.run (liftM (T3.Spec.query (.inl (.inl n)))) state >>= completedTail inputs _ next state] =
      𝒮[eagerSide inputs (liftM (T3.Spec.query (.inl (.inl n))) >>= next) state] := by
  rw [lazy_coin, bind_map_left, eagerSide_query_bind]
  unfold completedTail
  refine (evalSPMF_bind_bind_swap _ _ _).trans ?_
  apply evalSPMF_bind_congr'
  intro privateTable
  refine (evalSPMF_bind_bind_swap _ _ _).trans ?_
  apply evalSPMF_bind_congr'
  intro publicTable
  rfl
theorem completion_cached (inputs : Finset HashInput) {α : Type} (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) (state : LazyPrivate.State) (answer : T3.Spec.Range input)
    (hk : SourceReplay.known state input = some answer) :
    𝒮[LazyPrivate.run (liftM (T3.Spec.query input)) state >>= completedTail inputs input next state] =
      𝒮[eagerSide inputs (liftM (T3.Spec.query input) >>= next) state] := by
  have hi : SourceReplay.IsHash input := by
    rcases input with (n | x) | c
    · cases hk
    · trivial
    · trivial
  rw [SourceReplay.known_query_run state input answer hk, pure_bind, eagerSide_query_bind]
  unfold completedTail
  apply evalSPMF_bind_congr'
  intro privateTable
  apply evalSPMF_bind_congr'
  intro publicTable
  rw [fixedWorld_hash _ input hi, pure_bind, fillAnswers_known inputs state privateTable publicTable input answer hk,
    advance_cached state input answer hk]
theorem fillAnswers_public_fresh (inputs : Finset HashInput) (state : LazyPrivate.State)
    (privateTable : FullGame.FullTable) (publicTable : inputs → HashOutput) (x : HashInput) (hx : x ∈ inputs)
    (h : state.2 x = none) :
    fillAnswers inputs state privateTable publicTable (.inl (.inr x)) = publicTable ⟨x, hx⟩ := by
  change (state.2 x).getD (finiteHashAnswer ∅ inputs publicTable x) = _
  rw [h, Option.getD_none, SphincsSecurity.Concrete.finiteHashAnswer_none ∅ inputs _ x hx rfl]
theorem completion_public_fresh (inputs : Finset HashInput) {α : Type} (x : HashInput)
    (next : T3.Spec.Range (.inl (.inr x)) → M α) (state : LazyPrivate.State) (hx : x ∈ inputs)
    (hc : state.2 x = none) :
    𝒮[LazyPrivate.run (liftM (T3.Spec.query (.inl (.inr x)))) state >>= completedTail inputs _ next state] =
      𝒮[eagerSide inputs (liftM (T3.Spec.query (.inl (.inr x))) >>= next) state] := by
  rw [lazy_public_fresh state x hc, bind_map_left, eagerSide_query_bind]
  unfold completedTail
  simp only [fillAnswers_public_update inputs state _ _ x hx hc]
  refine (evalSPMF_bind_bind_swap _ _ _).trans ?_
  apply evalSPMF_bind_congr'
  intro privateTable
  let K : (inputs → HashOutput) → ProbComp (FirstHit.Recorded α × Answers) := fun table =>
    (fun last => ((⟨last.value, ⟨state, .inl (.inr x), table ⟨x, hx⟩⟩ :: last.events, last.state⟩ :
        FirstHit.Recorded α), fillAnswers inputs state privateTable table)) <$>
      fixedRecord (fillAnswers inputs state privateTable table) (next (table ⟨x, hx⟩))
        (state.1, state.2.cacheQuery x (table ⟨x, hx⟩))
  have hpoint : ∀ value table, ((fun last => ((⟨last.value, ⟨state, .inl (.inr x), value⟩ :: last.events,
      last.state⟩ : FirstHit.Recorded α),
        fillAnswers inputs state privateTable (Function.update table ⟨x, hx⟩ value))) <$>
      fixedRecord (fillAnswers inputs state privateTable (Function.update table ⟨x, hx⟩ value)) (next value)
        (state.1, state.2.cacheQuery x value)) = K (Function.update table ⟨x, hx⟩ value) := by
    intro value table
    simp only [K, Function.update_self]
  simp only [hpoint]
  refine Eq.trans (PrivateTable.refresh_table (⟨x, hx⟩ : inputs) K) ?_
  apply evalSPMF_bind_congr'
  intro publicTable
  rw [fixedWorld_public, pure_bind, fillAnswers_public_fresh inputs state privateTable publicTable x hx hc]
  rfl
theorem fillAnswers_private_fresh (inputs : Finset HashInput) (state : LazyPrivate.State)
    (privateTable : FullGame.FullTable) (publicTable : inputs → HashOutput) (c : Coordinate)
    (h : state.1 c = none) :
    fillAnswers inputs state privateTable publicTable (.inr c) = privateTable c := by
  change (state.1 c).getD (privateTable c) = _
  rw [h, Option.getD_none]
theorem completion_private_fresh (inputs : Finset HashInput) {α : Type} (c : Coordinate)
    (next : T3.Spec.Range (.inr c) → M α) (state : LazyPrivate.State) (hc : state.1 c = none) :
    𝒮[LazyPrivate.run (liftM (T3.Spec.query (.inr c))) state >>= completedTail inputs _ next state] =
      𝒮[eagerSide inputs (liftM (T3.Spec.query (.inr c)) >>= next) state] := by
  rw [lazy_private_fresh state c hc, bind_map_left, eagerSide_query_bind]
  unfold completedTail
  simp only [fillAnswers_private_update inputs state _ _ c hc]
  let K : FullGame.FullTable → ProbComp (FirstHit.Recorded α × Answers) := fun table =>
    ($ᵗ (inputs → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun last => ((⟨last.value, ⟨state, .inr c, table c⟩ :: last.events, last.state⟩ :
          FirstHit.Recorded α), fillAnswers inputs state table publicTable)) <$>
        fixedRecord (fillAnswers inputs state table publicTable) (next (table c))
          (state.1.cacheQuery c (table c), state.2)
  have hpoint : ∀ value table, (($ᵗ (inputs → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun last => ((⟨last.value, ⟨state, .inr c, value⟩ :: last.events, last.state⟩ : FirstHit.Recorded α),
        fillAnswers inputs state (Function.update table c value) publicTable)) <$>
      fixedRecord (fillAnswers inputs state (Function.update table c value) publicTable) (next value)
        (state.1.cacheQuery c value, state.2)) = K (Function.update table c value) := by
    intro value table
    simp only [K, Function.update_self]
  simp only [hpoint]
  refine Eq.trans (PrivateTable.refresh_table c K) ?_
  apply evalSPMF_bind_congr'
  intro privateTable
  simp only [K]
  apply evalSPMF_bind_congr'
  intro publicTable
  rw [fixedWorld_private, pure_bind, fillAnswers_private_fresh inputs state privateTable publicTable c hc]
  rfl
theorem record_completion (inputs : Finset HashInput) {α : Type} (program : M α) (state : LazyPrivate.State)
    (h : InputsIn inputs program state) :
    𝒮[FirstHit.record program state >>= fun result =>
        ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
          ($ᵗ (inputs → HashOutput) : ProbComp _) >>= fun publicTable =>
            pure (result, fillAnswers inputs result.state privateTable publicTable)] =
      𝒮[eagerSide inputs program state] := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [eagerSide, FirstHit.record_pure, fixedRecord_pure, pure_bind, map_pure]
  | query_bind input next ih =>
      have htail : ∀ middle ∈ support (LazyPrivate.run (liftM (T3.Spec.query input)) state),
          𝒮[(fun last => (⟨last.value, ⟨state, input, middle.1⟩ :: last.events, last.state⟩ :
              FirstHit.Recorded α)) <$> FirstHit.record (next middle.1) middle.2 >>= fun result =>
            ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
              ($ᵗ (inputs → HashOutput) : ProbComp _) >>= fun publicTable =>
                pure (result, fillAnswers inputs result.state privateTable publicTable)] =
          𝒮[completedTail inputs input next state middle] := by
        intro middle hm
        have hadv := FirstHit.query_advance state input middle hm
        have hin : InputsIn inputs (next middle.1) middle.2 := by
          rw [hadv]
          rcases input with (n | x) | c
          · exact h.coin middle.1
          · exact h.public.2 middle.1
          · apply h.priv middle.1
            intro v hv
            have hk := SourceReplay.known_query_run state (.inr c) v hv
            rw [hk, mem_support_pure_iff] at hm
            rw [hm]
        have hi := ih middle.1 middle.2 hin
        unfold eagerSide at hi
        rw [bind_map_left]
        have hmap := congrArg (fun law => (fun pair : FirstHit.Recorded α × Answers =>
          ((⟨pair.1.value, ⟨state, input, middle.1⟩ :: pair.1.events, pair.1.state⟩ : FirstHit.Recorded α),
            pair.2)) <$> law) hi
        simp only [← evalSPMF_map, map_bind, map_pure, Functor.map_map] at hmap
        unfold completedTail
        exact hmap
      rw [FirstHit.record_query_bind, bind_assoc, evalSPMF_bind_congr htail]
      rcases input with (n | x) | c
      · exact completion_coin inputs n next state
      · cases hc : state.2 x with
        | some v => exact completion_cached inputs _ next state v hc
        | none => exact completion_public_fresh inputs x next state h.public.1 hc
      · cases hc : state.1 c with
        | some v => exact completion_cached inputs _ next state v hc
        | none => exact completion_private_fresh inputs c next state hc
end SigGolfCandidate.T3.Security.Wots.Ref
end
-- ==== merged from T3_Secc_WotsTransportTable ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload
def GameSplit (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (generated : FirstHit.Recorded (Digest × T3.Cache))
    (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) (checked : FirstHit.Recorded Bool) : Prop :=
  generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
  interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
      (adversary generated.value.1 generated.value.2)) generated.state) ∧
  checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker generated.value.1 interaction.value)
      interaction.state) ∧
  result = ⟨checked.value, generated.events ++ (interaction.events ++ checked.events), checked.state⟩
namespace Ref
noncomputable def cut (state : LazyPrivate.State) (F : Answers) : Answers
  | .inl (.inl n) => F (.inl (.inl n))
  | .inl (.inr input) =>
      if input ∈ SeccLaw.publicUniverse ∨ (state.2 input).isSome then F (.inl (.inr input)) else (0 : HashOutput)
  | .inr coordinate => F (.inr coordinate)
theorem cut_shortAgree (state : LazyPrivate.State) (F : Answers) : ShortAgree (cut state F) F := by
  intro query hq
  rcases query with (n | x) | c
  · rfl
  · change (if x ∈ SeccLaw.publicUniverse ∨ (state.2 x).isSome then F (.inl (.inr x)) else (0 : HashOutput)) = _
    rw [if_pos (Or.inl (SeccLaw.mem_publicUniverse x hq))]
  · rfl
theorem cut_cached (state : LazyPrivate.State) (F : Answers) (query : T3.Spec.Domain)
    (h : ∀ x, query = .inl (.inr x) → (state.2 x).isSome) : cut state F query = F query := by
  rcases query with (n | x) | c
  · rfl
  · change (if x ∈ SeccLaw.publicUniverse ∨ (state.2 x).isSome then F (.inl (.inr x)) else (0 : HashOutput)) = _
    rw [if_pos (Or.inr (h x rfl))]
  · rfl
theorem eval_congr_queried {α : Type} (program : M α) (A T : Answers)
    (h : ∀ query ∈ SourceReplay.queried T program, A query = T query) :
    evalWithAnswerFn A program = evalWithAnswerFn T program ∧
      SourceReplay.queried A program = SourceReplay.queried T program := by
  induction program using OracleComp.inductionOn with
  | pure value => exact ⟨rfl, rfl⟩
  | query_bind input next ih =>
      rw [SourceReplay.queried_query_bind] at h
      have hi : A input = T input := h input List.mem_cons_self
      have hn := ih (T input) (fun query hq => h query (List.mem_cons_of_mem _ hq))
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, eval_query, eval_query, hi, hn.1,
        SourceReplay.queried_query_bind, SourceReplay.queried_query_bind, hi, hn.2]
      exact ⟨rfl, rfl⟩
theorem entriesOf_congr (A T : Answers) (queries : List T3.Spec.Domain)
    (h : ∀ query ∈ queries, A query = T query) : entriesOf A queries = entriesOf T queries := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
      have hr := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      rcases query with (n | x) | c
      · simpa [entriesOf] using hr
      · simp only [entriesOf, List.filterMap_cons] at hr ⊢
        rw [h _ List.mem_cons_self, hr]
      · simpa [entriesOf] using hr
theorem calls_append {ι : Type} (selected : ι → Prop) [DecidablePred selected] (left right : List ι) :
    SphincsSecurity.QueryCap.calls selected (left ++ right) =
      SphincsSecurity.QueryCap.calls selected left + SphincsSecurity.QueryCap.calls selected right := by
  simp [SphincsSecurity.QueryCap.calls, List.countP_append]
end Ref
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_PairGuessEager ====
section

section


namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers treeValue)
open SphincsSecurity (OracleWorld bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Table
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
theorem splitEquiv_snd (t : ChainGraph.HalfTable) (h : ChainGraph.HalfCoordinate)
    (hh : h ∉ Set.range CanonGraph.secretCoordinate) : (CanonGraph.splitEquiv t).2 ⟨h, hh⟩ = t h := by
  simp [CanonGraph.splitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.Set.sumCompl]
  rfl
theorem splitEquiv_symm_other (s : CanonGraph.Secrets) (o : CanonGraph.OtherHalves) (h : ChainGraph.HalfCoordinate)
    (hh : h ∉ Set.range CanonGraph.secretCoordinate) : CanonGraph.splitEquiv.symm (s, o) h = o ⟨h, hh⟩ := by
  have e := splitEquiv_snd (CanonGraph.splitEquiv.symm (s, o)) h hh
  rw [Equiv.apply_symm_apply] at e
  exact e.symm
theorem privateEquiv_symm_apply (s : CanonGraph.Secrets) (o : CanonGraph.OtherHalves) (c : Coordinate) :
    CanonGraph.privateEquiv.symm (s, o) c =
      ChainGraph.joinOutput (CanonGraph.splitEquiv.symm (s, o) (c, 0)) (CanonGraph.splitEquiv.symm (s, o) (c, 1)) :=
  rfl
end Table
def openedValues (fts : FtsCoord → Digest) (output : HashOutput) : List Digest := (openedPositions output).map fts
section Signer
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
noncomputable local instance instDecidableEqCache_pairGuessSigner : DecidableEq T3.Cache := Classical.decEq _
noncomputable def signerForest (output : HashOutput) : List Digest × List Digest × List Digest :=
  evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (Correctness.signForest (output.toNat % 2 ^ 31) (selections output))
noncomputable def signerLayers (request : Request) (output : HashOutput) : Option (List Pieces) :=
  evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (signLayers request.cache (output.toNat % 2 ^ 31) 4
    (evalWithAnswerFn (Omega.answers hU ω (fun _ => 0))
      (forestPk (output.toNat % 2 ^ 31) (signerForest hU ω output).2.2)))
end Signer
end SigGolfCandidate.T3.Security.BPair
end

section



section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Tracking
open SecretGuessObservation (runWith fixedRun fixedImpl afterTrial afterDisclosure)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
theorem disclosed_append_left (A : Answers) (l1 l2 : QueryLog Requests) (f : FtsCoord) (h : Disclosed A l1 f) :
    Disclosed A (l1 ++ l2) f := by
  obtain ⟨entry, he, rest⟩ := h
  exact ⟨entry, List.mem_append_left _ he, rest⟩
theorem disclosed_append_right (A : Answers) (l1 l2 : QueryLog Requests) (f : FtsCoord) (h : Disclosed A l2 f) :
    Disclosed A (l1 ++ l2) f := by
  obtain ⟨entry, he, rest⟩ := h
  exact ⟨entry, List.mem_append_right _ he, rest⟩
structure Tracks (fts : FtsCoord → Digest) (before after : WState) (log : QueryLog Requests)
    (entries : List Wots.Entry) : Prop where
  probes : after.probes ≤ before.probes + entries.length
  guesses : before.guesses ⊆ after.guesses
  retired : before.retired ⊆ after.retired
  origin : ∀ f ∈ after.retired, f ∈ before.retired ∨ f ∈ after.guesses ∨ Disclosed (Omega.answers hU ω fts) log f
  queried : ∀ f answer, (probeInput f (fts f), answer) ∈ entries → f ∈ after.retired
theorem Tracks.refl (fts : FtsCoord → Digest) (state : WState) : Tracks hU ω fts state state [] [] :=
  ⟨by simp, Finset.Subset.refl _, Finset.Subset.refl _, fun _ h => Or.inl h, fun _ _ h => by cases h⟩
theorem Tracks.trans {fts : FtsCoord → Digest} {s1 s2 s3 : WState} {l1 l2 : QueryLog Requests}
    {e1 e2 : List Wots.Entry} (first : Tracks hU ω fts s1 s2 l1 e1) (second : Tracks hU ω fts s2 s3 l2 e2) :
    Tracks hU ω fts s1 s3 (l1 ++ l2) (e1 ++ e2) := by
  refine ⟨?_, first.guesses.trans second.guesses, first.retired.trans second.retired, ?_, ?_⟩
  · have := first.probes
    have := second.probes
    simp only [List.length_append]
    omega
  · intro f hf
    rcases second.origin f hf with h | h | h
    · rcases first.origin f h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (second.guesses h))
      · exact Or.inr (Or.inr (disclosed_append_left _ _ _ _ h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (disclosed_append_right _ _ _ _ h))
  · intro f answer h
    rcases List.mem_append.mp h with h | h
    · exact second.retired (first.queried f answer h)
    · exact second.queried f answer h
end Tracking
end SigGolfCandidate.T3.Security.BPair
end
section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
end SigGolfCandidate.T3.Security.BPair
end
section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
open OracleComp.DeferredSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload GameWith.idealGame
theorem probEvent_bind_mono' {α β γ : Type} (mx : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
    (p : β → Prop) (r : γ → Prop) (h : ∀ x, Pr[p | f x] ≤ Pr[r | g x]) :
    Pr[p | mx >>= f] ≤ Pr[r | mx >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
def publicEntries (events : List FirstHit.QueryEvent) : List Wots.Entry :=
  events.filterMap fun e => match e with
    | ⟨_, .inl (.inr input), answer⟩ => some (input, answer)
    | _ => none
theorem publicEntries_pureRecord (T : Answers) {β : Type} (program : M β) (state : LazyPrivate.State) :
    publicEntries (Wots.Ref.pureRecord T program state).events = Wots.entriesOf T (SourceReplay.queried T program) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      rw [Wots.Ref.pureRecord_query_bind, SourceReplay.queried_query_bind]
      rcases input with (n | x) | c
      · exact ih _ _
      · change (x, T (.inl (.inr x))) :: publicEntries _ = (x, T (.inl (.inr x))) :: Wots.entriesOf T _
        rw [ih]
      · exact ih _ _
theorem entriesOf_length_le (T : Answers) (queries : List T3.Spec.Domain) :
    (Wots.entriesOf T queries).length ≤ queries.length := by
  unfold Wots.entriesOf
  exact List.length_filterMap_le _ _
section Law
noncomputable local instance instFintypeCoordinate_pairGuessEager : Fintype Coordinate := coordinateFintype
attribute [local instance] Wots.Ref.instSampleableTypeFullTable_wotsTransportCompletion
  FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
theorem pmf_probEvent_mono {α : Type} (p : PMF α) (A B : α → Prop) (h : ∀ x ∈ p.support, A x → B x) :
    Pr[A | p] ≤ Pr[B | p] := by
  simp only [probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ p.support
  · split_ifs with ha hb
    · exact le_rfl
    · exact absurd (h x hx ha) hb
    · exact zero_le
    · exact le_rfl
  · have hz : p x = 0 := by simpa [PMF.mem_support_iff] using hx
    split_ifs <;> simp [PMF.probOutput_eq_apply, hz]
end Law
end SigGolfCandidate.T3.Security.BPair
end
end
end
-- ==== merged from T3_Secc_PairGuessFinal ====
section

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
open OracleComp.DeferredSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem uniform_congr {X : Type} [Fintype X] (I J : SampleableType X) :
    𝒮[(@uniformSample X I : ProbComp X)] = 𝒮[(@uniformSample X J : ProbComp X)] := by
  apply evalSPMF_ext
  intro x
  rw [@probOutput_uniformSample X I _ x, @probOutput_uniformSample X J _ x]
theorem bind_uniform_congr {X β : Type} [Fintype X] (I J : SampleableType X) (f : X → ProbComp β) :
    𝒮[(@uniformSample X I : ProbComp X) >>= f] = 𝒮[(@uniformSample X J : ProbComp X) >>= f] := by
  rw [evalSPMF_bind, evalSPMF_bind, uniform_congr I J]
end SigGolfCandidate.T3.Security.BPair
end
-- ==== merged from T3_Secc_PairGuessLazyDefs ====
section

section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
open OracleComp.DeferredSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
end SigGolfCandidate.T3.Security.BPair
end
section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld bytesLE bytesLE_length)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
set_option warn.classDefReducibility false in
noncomputable def digestKeyFintype : Fintype (Digest × Message × BitVec 32) := inferInstance
attribute [irreducible] digestKeyFintype
theorem digestInputs_exists :
    ∃ S : Finset HashInput, ∀ x, x ∈ S ↔ ∃ rho m ctr, x = pad64 (digestInput rho m ctr) := by
  refine ⟨(@Finset.univ _ digestKeyFintype).image fun k => pad64 (digestInput k.1 k.2.1 k.2.2), fun x => ?_⟩
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, -, rfl⟩
    exact ⟨k.1, k.2.1, k.2.2, rfl⟩
  · rintro ⟨rho, m, ctr, rfl⟩
    exact ⟨(rho, m, ctr), @Finset.mem_univ _ digestKeyFintype _, rfl⟩
noncomputable def digestInputs : Finset HashInput := Classical.choose digestInputs_exists
attribute [irreducible] digestInputs
noncomputable instance (priority := high) digestInputs_decidable (x : HashInput) : Decidable (x ∈ digestInputs) :=
  Classical.propDecidable _
theorem mem_digestInputs {x : HashInput} : x ∈ digestInputs ↔ ∃ rho m ctr, x = pad64 (digestInput rho m ctr) := by
  rw [digestInputs]
  exact Classical.choose_spec digestInputs_exists x
theorem digestInput_mem (rho : Digest) (m : Message) (ctr : BitVec 32) : pad64 (digestInput rho m ctr) ∈ digestInputs :=
  mem_digestInputs.mpr ⟨rho, m, ctr, rfl⟩
theorem digestInput_length (rho : Digest) (m : Message) (ctr : BitVec 32) : (digestInput rho m ctr).length = 64 := by
  simp [digestInput, bytesLE_length]
theorem digestInputs_subset_publicUniverse : digestInputs ⊆ SeccLaw.publicUniverse := by
  intro x hx
  obtain ⟨rho, m, ctr, rfl⟩ := mem_digestInputs.mp hx
  apply SeccLaw.mem_publicUniverse
  rw [Cost.pad64_length, digestInput_length]
  unfold SeccLaw.maxInputLength
  omega
noncomputable def rowVal (D : digestInputs → HashOutput) (x : HashInput) : HashOutput :=
  if h : x ∈ digestInputs then D ⟨x, h⟩ else 0
inductive AuxL where
  | coin (n : Nat)
  | birth (x : HashInput)
  | trial (x : HashInput)
  | nonce (m : Message)
  | expose (o : Option HashOutput)
abbrev AuxSpecL : OracleSpec AuxL
  | .coin n => Fin (n + 1)
  | .birth _ => HashOutput
  | .trial _ => HashOutput
  | .nonce _ => Digest
  | .expose _ => Unit
abbrev WSpecL := SecretGuessObservation.World AuxSpecL FtsCoord Digest
structure LazyMem where
  rows : Sampling.RCache
  nonces : Message → Option Digest
  births : List HashOutput
  trials : List HashInput
  exposures : List HashOutput
def LazyMem.empty : LazyMem := ⟨∅, fun _ => none, [], [], []⟩
abbrev WStateL := SecretGuessObservation.State FtsCoord Digest LazyMem
def LazyMem.readRow (mem : LazyMem) (x : HashInput) (a : HashOutput) (isBirth : Bool) : LazyMem :=
  { mem with rows := mem.rows.cacheQuery x a,
             births := if isBirth then mem.births ++ [a] else mem.births,
             trials := if isBirth then mem.trials else mem.trials ++ [x] }
def LazyMem.replayRow (mem : LazyMem) (x : HashInput) (isBirth : Bool) : LazyMem :=
  if isBirth then mem else { mem with trials := mem.trials ++ [x] }
def LazyMem.drawNonce (mem : LazyMem) (m : Message) (v : Digest) : LazyMem :=
  { mem with nonces := Function.update mem.nonces m (some v) }
def LazyMem.expose (mem : LazyMem) (o : Option HashOutput) : LazyMem :=
  { mem with exposures := mem.exposures ++ o.toList }
noncomputable def rowStep (mem : LazyMem) (x : HashInput) (isBirth : Bool) (fresh : PMF HashOutput) :
    PMF (HashOutput × LazyMem) :=
  match mem.rows x with
  | some a => pure (a, mem.replayRow x isBirth)
  | none => if x ∈ digestInputs then (fun a => (a, mem.readRow x a isBirth)) <$> fresh
      else pure (0, mem.replayRow x isBirth)
noncomputable def nonceStep (mem : LazyMem) (m : Message) (fresh : PMF Digest) : PMF (Digest × LazyMem) :=
  match mem.nonces m with
  | some v => pure (v, mem)
  | none => (fun v => (v, mem.drawNonce m v)) <$> fresh
noncomputable def auxWith (rowSrc : HashInput → PMF HashOutput) (nonceSrc : Message → PMF Digest)
    (state : WStateL) : (input : AuxSpecL.Domain) → PMF (AuxSpecL.Range input × LazyMem)
  | .coin n => (fun c => (c, state.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))
  | .birth x => rowStep state.memory x true (rowSrc x)
  | .trial x => rowStep state.memory x false (rowSrc x)
  | .nonce m => nonceStep state.memory m (nonceSrc m)
  | .expose o => pure ((), state.memory.expose o)
noncomputable def envWith (rowSrc : HashInput → PMF HashOutput) (nonceSrc : Message → PMF Digest) :
    SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem where
  auxiliary := auxWith rowSrc nonceSrc
  trial mem _ _ _ := mem
  disclosure mem _ _ := mem
noncomputable def envL : SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem :=
  envWith (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)
noncomputable def envE (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem :=
  envWith (fun x => pure (rowVal D x)) (fun m => pure (Nn m))
def coinReqL (n : Nat) : OracleComp WSpecL (Fin (n + 1)) := liftM (WSpecL.query (.inl (.coin n)))
def birthReq (x : HashInput) : OracleComp WSpecL HashOutput := liftM (WSpecL.query (.inl (.birth x)))
def trialReq (x : HashInput) : OracleComp WSpecL HashOutput := liftM (WSpecL.query (.inl (.trial x)))
def nonceReq (m : Message) : OracleComp WSpecL Digest := liftM (WSpecL.query (.inl (.nonce m)))
def exposeReq (o : Option HashOutput) : OracleComp WSpecL Unit := liftM (WSpecL.query (.inl (.expose o)))
def guessReq (p : FtsCoord × Digest) : OracleComp WSpecL Bool := liftM (WSpecL.query (.inr (.inl p)))
def discloseReq (f : FtsCoord) : OracleComp WSpecL Digest := liftM (WSpecL.query (.inr (.inr f)))
noncomputable def searchL (rho : Digest) (m : Message) (counter : Nat) : Nat → OracleComp WSpecL (Option (BitVec 32 × HashOutput))
  | 0 => pure none
  | fuel + 1 => do
      let output ← trialReq (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))
      if digestAdmissible output = true then pure (some (BitVec.ofNat 32 counter, output))
      else searchL rho m (counter + 1) fuel
section World
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
noncomputable local instance instDecidableEqCache_pairGuessLazyDefs : DecidableEq T3.Cache := Classical.decEq _
noncomputable def hashL (ω : Omega U) (x : HashInput) : OracleComp WSpecL HashOutput :=
  match decodeProbe x with
  | some p => do
      let hit ← guessReq p
      pure (if hit then ω.labels (.ftsLeaf (toLeafPos p.1)) else finiteHashAnswer ∅ U ω.residual x)
  | none => if x ∈ digestInputs then birthReq x else pure (Omega.answers hU ω (fun _ => 0) (.inl (.inr x)))
noncomputable def finishL (ω : Omega U) (request : Request) (rho : Digest) :
    Option (BitVec 32 × HashOutput) → OracleComp WSpecL (Option Signature)
  | none => pure none
  | some (_, output) =>
      match signerLayers hU ω request output with
      | none => pure none
      | some pieces => do
          let values ← (openedPositions output).mapM discloseReq
          pure (some (Correctness.assembledSignature rho
            (openedValues (overwrite (openedPositions output) values) output,
              (signerForest hU ω output).2.1, (signerForest hU ω output).2.2) pieces))
noncomputable def programL (ω : Omega U) {β : Type} : M β → OracleComp WSpecL (β × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← coinReqL n
          next coin
      | .inl (.inr x) => do
          let answer ← hashL hU ω x
          let rest ← next answer
          pure (rest.1, (x, answer) :: rest.2)
      | .inr _ => next (0 : HashOutput))
end World
end SigGolfCandidate.T3.Security.BPair
end
end
-- ==== merged from T3_Secc_PairGuessLazyFree ====
section

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def NotDN : T3.Spec.Domain → Prop
  | .inl (.inl _) => True
  | .inl (.inr x) => x ∉ digestInputs
  | .inr (.inl _) => True
  | .inr (.inr (.inl _)) => False
  | .inr (.inr (.inr _)) => True
theorem not_digest_of_marker {x : HashInput} {h : Digest} (hx : Extract.hdrBlock x = bytesLE 16 h)
    (hm : tweakMarker h ≠ 0) : x ∉ digestInputs := by
  intro hmem
  obtain ⟨rho, m, ctr, rfl⟩ := mem_digestInputs.mp hmem
  rw [Extract.hdrBlock_pad64 _ (by rw [digestInput_length]; omega)] at hx
  unfold digestInput at hx
  have h2 : bytesLE 16 (digestHeader ctr) = bytesLE 16 h :=
    (Extract.hdrBlock_prefix rho (digestHeader ctr) (bytesLE 32 m)).symm.trans hx
  exact hm (by rw [← bytesLE_injective h2, digestHeader_marker])
/-- C4: the digest is the only query with low header word 0 (top fold labels may have byte0 = 0). -/
theorem not_digest_of_low {x : HashInput} {h : Digest} (hx : Extract.hdrBlock x = bytesLE 16 h)
    (hm : tweakLow h ≠ 0) : x ∉ digestInputs := by
  intro hmem
  obtain ⟨rho, m, ctr, rfl⟩ := mem_digestInputs.mp hmem
  rw [Extract.hdrBlock_pad64 _ (by rw [digestInput_length]; omega)] at hx
  unfold digestInput at hx
  have h2 : bytesLE 16 (digestHeader ctr) = bytesLE 16 h :=
    (Extract.hdrBlock_prefix rho (digestHeader ctr) (bytesLE 32 m)).symm.trans hx
  exact hm (by rw [← bytesLE_injective h2, digestHeader_lowNat])
section DN
open SourceQueries
theorem privatePair_dn (t l tr p ix : Nat) : AllQueriesSatisfy (privatePair t l tr p ix) NotDN := by
  unfold privatePair privateHash
  exact bind_allowed NotDN ((allQueriesSatisfy_query_iff _ _).mpr trivial) fun _ => pure_allowed _ _
theorem privateMac_dn (region : Region) : AllQueriesSatisfy (privateMac region) NotDN := by
  exact privateMac_allowed NotDN (fun _ => trivial) region
theorem chainStep_dn (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    AllQueriesSatisfy (shortHash (chainInput lay tree leaf i step value)) NotDN := by
  unfold shortHash publicHash
  apply bind_allowed NotDN
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    intro hm
    obtain ⟨rho, m, ctr, he⟩ := mem_digestInputs.mp hm
    have hh := congrArg Extract.hdrBlock he
    rw [chainInput_padded, Extract.hdrBlock_pad64 _ (by rw [digestInput_length]; omega)] at hh
    change ((chainInput lay tree leaf i step value).drop 16).take 16 = _ at hh
    rw [chainInput_header] at hh
    unfold digestInput at hh
    rw [Extract.hdrBlock_prefix] at hh
    exact chainHeader_ne_digestHeader _ _ _ _ _ _ (bytesLE_injective hh)
  · intro _; exact pure_allowed _ _
/-- Witness stack: the top chain step (G or F input) carries the chain header in bytes `16..32`. -/
theorem topChainStep_dn (leaf i step : Nat) (high : Bool) (value : Digest) :
    AllQueriesSatisfy (projHash high (topChainInput leaf i step value)) NotDN := by
  unfold projHash publicHash
  apply bind_allowed NotDN
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    intro hm
    obtain ⟨rho, m, ctr, he⟩ := mem_digestInputs.mp hm
    have hh := congrArg Extract.hdrBlock he
    have hpad : pad64 (topChainInput leaf i step value) = topChainInput leaf i step value := by
      unfold topChainInput; split
      · simp [pad64, SphincsSecurity.bytesLE_length, zero16]
      · exact chainInput_padded _ _ _ _ _ _
    have hhdr : ((topChainInput leaf i step value).drop 16).take 16 =
        SphincsSecurity.bytesLE 16 (chainHeader 0 0 leaf i step) := by
      unfold topChainInput; split
      · simp [zero16, List.append_assoc, SphincsSecurity.bytesLE_length]
      · exact chainInput_header _ _ _ _ _ _
    rw [hpad, Extract.hdrBlock_pad64 _ (by rw [digestInput_length]; omega)] at hh
    change ((topChainInput leaf i step value).drop 16).take 16 = _ at hh
    rw [hhdr] at hh
    unfold digestInput at hh
    rw [Extract.hdrBlock_prefix] at hh
    exact chainHeader_ne_digestHeader _ _ _ _ _ _ (bytesLE_injective hh)
  · intro _; exact pure_allowed _ _
theorem topChain_dn (leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (topChain leaf i start count value) NotDN := by
  unfold topChain
  exact foldlM_allowed NotDN _ _ (fun v step => topChainStep_dn leaf i step _ v) value
theorem chain_dn (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count value) NotDN := by
  unfold chain
  exact foldlM_allowed NotDN _ _ (fun v step => chainStep_dn lay tree leaf i step v) value
theorem leafHash_dn (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) NotDN := by
  unfold leafHash projHash publicHash
  exact bind_allowed NotDN ((allQueriesSatisfy_query_iff _ _).mpr
    (not_digest_of_marker (Extract.hdrBlock_leafInput lay tree leaf ends) (by rw [leafTweak_marker]; decide)))
    fun _ => pure_allowed _ _
theorem nodeHash_dn {tag : Nat} (lay tree heap : Nat) (left right : Digest) (_ht : tag % 256 ≠ 12) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) NotDN := by
  rw [nodeHash_eq_projHash]
  unfold projHash publicHash
  exact bind_allowed NotDN ((allQueriesSatisfy_query_iff _ _).mpr
    (not_digest_of_low (by rw [pad64_nodeInputP, nodeInputP]; exact Extract.hdrBlock_block4 _ _ _ _)
      (nodeTweak_low_ne_zero _ _ _ _)))
    fun _ => pure_allowed _ _
theorem mask_dn (level index : Nat) : AllQueriesSatisfy (mask level index) NotDN := by
  unfold mask pairedMask
  exact bind_allowed NotDN (privatePair_dn _ _ _ _ _) fun _ => pure_allowed _ _
theorem buildLeaf_dn (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeaf lay tree leaf digits signatureOnly) NotDN := by
  unfold buildLeaf
  apply bind_allowed NotDN
  · apply foldlM_allowed NotDN
    intro state pair
    apply bind_allowed NotDN (privatePair_dn _ _ _ _ _)
    intro seeds
    apply foldlM_allowed NotDN
    intro state half
    dsimp only
    split
    · exact pure_allowed _ _
    · apply bind_allowed NotDN (chain_dn _ _ _ _ _ _ _)
      intro value
      split
      · exact pure_allowed _ _
      · exact bind_allowed NotDN (chain_dn _ _ _ _ _ _ _) fun _ => pure_allowed _ _
  · intro state
    split
    · exact pure_allowed _ _
    · exact bind_allowed NotDN (leafHash_dn _ _ _ _) fun _ => pure_allowed _ _
theorem buildLevel_dn {tag : Nat} (lay tree h level : Nat) (nodes : List Digest) (ht : tag % 256 ≠ 12) :
    AllQueriesSatisfy (buildLevel tag lay tree h level nodes) NotDN := by
  unfold buildLevel
  exact mapM_allowed NotDN _ _ fun _ => nodeHash_dn _ _ _ _ _ ht
theorem buildLevels_dn {tag : Nat} (lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 12) :
    AllQueriesSatisfy (buildLevels tag lay tree h leaves) NotDN := by
  unfold buildLevels
  exact foldlM_allowed NotDN _ _ (fun levels level =>
    bind_allowed NotDN (buildLevel_dn _ _ _ _ _ ht) fun _ => pure_allowed _ _) _
theorem buildTree_dn (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (buildTree lay tree selected digits) NotDN := by
  unfold buildTree
  apply bind_allowed NotDN
  · exact foldlM_allowed NotDN _ _ (fun state leaf =>
      bind_allowed NotDN (buildLeaf_dn _ _ _ _ _) fun _ => pure_allowed _ _) _
  · intro state
    exact bind_allowed NotDN (buildLevels_dn _ _ _ _ (by decide)) fun _ => pure_allowed _ _
theorem maskedLevel_dn (nodes : List Digest) (level : Nat) :
    AllQueriesSatisfy (maskedLevel nodes level) NotDN := by
  unfold maskedLevel pairedMask
  apply bind_allowed NotDN
  · exact mapM_allowed NotDN _ _ (fun pair => bind_allowed NotDN (privatePair_dn _ _ _ _ _) (fun _ => pure_allowed _ _))
  · intro _; exact pure_allowed _ _
theorem topPairsFrom_dn (first start : Nat) (init : List Digest) :
    AllQueriesSatisfy (topPairsFrom first start init) NotDN := by
  unfold topPairsFrom topSeedPair
  exact foldlM_allowed NotDN _ _ (fun _ _ => bind_allowed NotDN (privatePair_dn _ _ _ _ _)
    fun _ => pure_allowed _ _) _
theorem buildLeafTopC_dn (leaf : Nat) (coefs : List Digest) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeafTopC leaf coefs digits signatureOnly) NotDN := by
  unfold buildLeafTopC
  apply bind_allowed NotDN
  · apply foldlM_allowed NotDN
    intro state i
    apply bind_allowed NotDN (topChain_dn _ _ _ _ _)
    intro value
    split
    · exact pure_allowed _ _
    · exact bind_allowed NotDN (topChain_dn _ _ _ _ _) fun _ => pure_allowed _ _
  · intro state
    split
    · exact pure_allowed _ _
    · exact bind_allowed NotDN (leafHash_dn _ _ _ _) fun _ => pure_allowed _ _
theorem buildLeafTop_dn (leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeafTop leaf digits signatureOnly) NotDN := by
  unfold buildLeafTop topCoefs
  exact bind_allowed NotDN (bind_allowed NotDN (topPairsFrom_dn _ _ _) fun _ => pure_allowed _ _)
    fun _ => buildLeafTopC_dn _ _ _ _
theorem topTreeStep_dn (st : List Digest × List Digest × Digest) (leaf : Nat) :
    AllQueriesSatisfy (topTreeStep st leaf) NotDN := by
  unfold topTreeStep topFamilyCoefs
  apply bind_allowed NotDN
  · split
    · unfold topCoefsK
      exact bind_allowed NotDN (topPairsFrom_dn _ _ _) fun _ => pure_allowed _ _
    · exact pure_allowed _ _
  · intro cc
    exact bind_allowed NotDN (buildLeafTopC_dn _ _ _ _) fun _ => pure_allowed _ _
/-- Top nonce trials: the node tweak sits in bytes `16..32` (nonce in `32..48`). -/
theorem topNodeHashN_dn (heap n : Nat) (left right : Digest) :
    AllQueriesSatisfy (topNodeHashN heap n left right) NotDN := by
  unfold topNodeHashN projHash publicHash
  refine bind_allowed NotDN ((allQueriesSatisfy_query_iff _ _).mpr
    (not_digest_of_low (h := nodeTweak 3 0 0 heap) ?_ (nodeTweak_low_ne_zero _ _ _ _))) fun _ => pure_allowed _ _
  rw [Extract.hdrBlock_pad64 _ (by simp [topNodeInput, nonceBytes, bytesLE_length])]
  unfold topNodeInput
  rw [List.append_assoc]
  exact Extract.hdrBlock_prefix _ _ _
theorem topNonceSearch_dn (h heap : Nat) (left right : Digest) :
    ∀ fuel n, AllQueriesSatisfy (topNonceSearch h heap left right fuel n) NotDN
  | 0, n => by
      unfold topNonceSearch
      exact bind_allowed NotDN (topNodeHashN_dn _ _ _ _) fun _ => pure_allowed _ _
  | fuel + 1, n => by
      unfold topNonceSearch
      refine bind_allowed NotDN (topNodeHashN_dn _ _ _ _) fun _ => ?_
      split
      · exact pure_allowed _ _
      · exact topNonceSearch_dn h heap left right fuel (n + 1)
theorem buildTopLevels_dn (leaves : List Digest) : AllQueriesSatisfy (buildTopLevels leaves) NotDN := by
  unfold buildTopLevels
  refine foldlM_allowed NotDN _ _ (fun levels level => bind_allowed NotDN ?_ fun _ => pure_allowed _ _) _
  unfold buildTopLevel
  refine mapM_allowed NotDN _ _ fun i => ?_
  split
  · exact nodeHash_dn _ _ _ _ _ (by decide)
  · unfold topNodeAt
    exact map_allowed NotDN _ (topNonceSearch_dn _ _ _ _ _ _)
theorem buildTopTree_dn : AllQueriesSatisfy buildTopTree NotDN := by
  unfold buildTopTree
  exact bind_allowed NotDN (foldlM_allowed NotDN _ _ topTreeStep_dn _) fun _ => buildTopLevels_dn _
theorem keygenPayload_dn : AllQueriesSatisfy keygenPayload NotDN := by
  unfold keygenPayload
  apply bind_allowed NotDN buildTopTree_dn
  intro built
  apply bind_allowed NotDN
  · exact mapM_allowed NotDN _ _ (fun level => maskedLevel_dn _ _)
  · intro _
    exact pure_allowed _ _
theorem keygen_dn : AllQueriesSatisfy keygen NotDN := by
  unfold keygen
  apply bind_allowed NotDN keygenPayload_dn
  intro generated
  exact bind_allowed NotDN (privateMac_dn _) fun _ => pure_allowed _ _
theorem topPath_dn (cache : T3.Cache) (leaf : Nat) : AllQueriesSatisfy (topPath cache leaf) NotDN := by
  unfold topPath
  exact mapM_allowed NotDN _ _ fun level =>
    bind_allowed NotDN (mask_dn _ _) fun _ => pure_allowed _ _
theorem signTop_dn (cache : T3.Cache) (leaf : Nat) (digits : List Nat) :
    AllQueriesSatisfy (signTop cache leaf digits) NotDN := by
  unfold signTop
  exact bind_allowed NotDN (buildLeafTop_dn _ _ _) fun _ =>
    bind_allowed NotDN (topPath_dn _ _) fun _ => pure_allowed _ _
end DN
def nonceHalf (m : Message) : ChainGraph.HalfCoordinate := (.inr (.inl m), 0)
theorem nonceHalf_not_secret (m : Message) : nonceHalf m ∉ Set.range CanonGraph.secretCoordinate := by
  rintro ⟨i, hi⟩
  have h1 := congrArg Prod.fst hi
  cases i with
  | inl a => cases h1
  | inr f => cases h1
def nonceOther (m : Message) : CanonGraph.OtherHalf := ⟨nonceHalf m, nonceHalf_not_secret m⟩
section Rest
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
noncomputable local instance instDecidableEqCache_pairGuessLazyFree : DecidableEq T3.Cache := Classical.decEq _
noncomputable def digestOf (ω : Omega U) : digestInputs → HashOutput := fun x => finiteHashAnswer ∅ U ω.residual x.val
def nonceOf (ω : Omega U) : Message → Digest := fun m => ω.other (nonceOther m)
end Rest
end SigGolfCandidate.T3.Security.BPair
end
-- ==== merged from ClaudeWCT_W9_New_Game_Signer ====
section

section


namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (PubGood allQ_pure allQ_bind allQ_foldlM allQ_mapM allQ_mono pubGood_shortHash
  pubGood_nodeHash)
open SphincsSecurity (bytesLE_length)
def LowerSeedQ (lay : Layer) (tree : Nat) : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inr (.inl tweak) => ∃ pair, tweak = lowerSeedHeader lay tree pair
  | _ => False
def LowerQuery (lay : Layer) (tree : Nat) (q : SigGolfCandidate.T3.Spec.Domain) : Prop :=
  PubGood q ∨ LowerSeedQ lay tree q
section
variable (lay : Layer) (tree : Nat)
theorem lowerQuery_chain (leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.chain lay tree leaf i start count value) (LowerQuery lay tree) :=
  allQ_mono (allQ_foldlM _ _ (fun _ _ => pubGood_shortHash _ (by simp [SigGolfCandidate.T3.chainInput, bytesLE_length, zero16])) _)
    (fun _ h => Or.inl h)
theorem lowerQuery_leafHash (leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.leafHash lay tree leaf ends) (LowerQuery lay tree) :=
  allQ_mono (SigGolfCandidate.T3M.pubGood_leafHash _ _ _ _) (fun _ h => Or.inl h)
theorem pubGood_halfHash (high : Bool) (input : HashInput) (h : 0 < input.length) :
    AllQueriesSatisfy (halfHash high input) PubGood := by
  rw [halfHash_eq]
  exact allQ_bind (SigGolfCandidate.T3M.pubGood_publicHash input h) fun _ => allQ_pure _
/-- C3: the chains of the current scheme (`chainW`). -/
theorem lowerQuery_chainW (leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chainW lay tree leaf i start count value) (LowerQuery lay tree) :=
  allQ_mono (allQ_foldlM _ _ (fun _ _ => pubGood_halfHash _ _
    (by rw [chainInputW_length]; omega)) _) (fun _ h => Or.inl h)
/-- C2: the leaf hash of the current scheme (`lowerLeafHash`). -/
theorem lowerQuery_lowerLeafHash (leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (lowerLeafHash lay tree leaf ends) (LowerQuery lay tree) := by
  rw [lowerLeafHash_eq]
  exact allQ_mono (pubGood_halfHash _ _ (by rw [SigGolfCandidate.T3.leafInput_length]; split_ifs <;> omega))
    (fun _ h => Or.inl h)
/-- C2: a level of a lower tree of the current scheme (`lowerLevel`). -/
theorem lowerQuery_lowerLevel (h level : Nat) (nodes : List Digest) :
    AllQueriesSatisfy (lowerLevel lay.val tree h level nodes) (LowerQuery lay tree) := by
  unfold lowerLevel
  refine allQ_mono (allQ_mapM _ _ fun _ => ?_) (fun _ h => Or.inl h)
  unfold lowerNodeHash lowerHash
  exact pubGood_halfHash _ _ (by simp [merkleNodeInput, bytesLE_length, zero16])
theorem lowerQuery_buildLevels (h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevels 3 lay.val tree h leaves) (LowerQuery lay tree) := by
  unfold buildLevels
  refine allQ_foldlM _ _ (fun levels level => allQ_bind ?_ fun _ => allQ_pure _) _
  unfold buildLevel
  exact allQ_mono (allQ_mapM _ _ fun _ => pubGood_nodeHash _ _ _ _ _ _) (fun _ h => Or.inl h)
theorem lowerQuery_buildLevelsBelow (h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevelsBelow 3 lay.val tree h leaves) (LowerQuery lay tree) := by
  unfold buildLevelsBelow
  exact allQ_foldlM _ _ (fun levels level =>
    allQ_bind (lowerQuery_lowerLevel lay tree _ _ _) fun _ => allQ_pure _) _
theorem lowerQuery_seedPair (pair : Nat) :
    AllQueriesSatisfy (lowerSeedPair lay tree pair) (LowerQuery lay tree) := by
  unfold lowerSeedPair privatePair privateHash
  refine allQ_bind ?_ fun _ => allQ_pure _
  exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨Or.inr ⟨pair, rfl⟩, fun _ => allQueriesSatisfy_pure _ _⟩
theorem lowerQuery_packedSecret (q : Nat) (carry : Digest) :
    AllQueriesSatisfy (packedSecret (lowerSeedPair lay tree) q carry) (LowerQuery lay tree) := by
  unfold packedSecret
  split
  · exact allQ_bind (lowerQuery_seedPair lay tree _) fun _ => allQ_pure _
  · exact allQ_pure _
theorem lowerQuery_buildLeafP (leaf : Nat) (digits : List Nat) (carry : Digest) :
    AllQueriesSatisfy (buildLeafP lay tree leaf digits carry) (LowerQuery lay tree) := by
  unfold buildLeafP
  refine allQ_bind (allQ_foldlM _ _ (fun state i => ?_) _) fun _ =>
    allQ_bind (lowerQuery_leafHash lay tree leaf _) fun _ => allQ_pure _
  refine allQ_bind (lowerQuery_packedSecret lay tree _ _) fun sc => ?_
  exact allQ_bind (lowerQuery_chain lay tree _ _ _ _ _) fun _ =>
    allQ_bind (lowerQuery_chain lay tree _ _ _ _ _) fun _ => allQ_pure _
theorem lowerQuery_lowerCoefs (leaf : Nat) (carry : List Digest) :
    AllQueriesSatisfy (lowerCoefs lay tree leaf carry) (LowerQuery lay tree) := by
  unfold lowerCoefs lowerFamCoefs
  split
  · exact allQ_bind (allQ_bind (allQ_foldlM _ _ (fun acc j =>
      allQ_bind (lowerQuery_seedPair lay tree _) fun _ => allQ_pure _) _) fun _ => allQ_pure _) fun _ => allQ_pure _
  · exact allQ_pure _
theorem lowerQuery_buildLeafPF (leaf : Nat) (digits : List Nat) (carry : List Digest) :
    AllQueriesSatisfy (buildLeafPF lay tree leaf digits carry) (LowerQuery lay tree) := by
  unfold buildLeafPF
  refine allQ_bind (lowerQuery_lowerCoefs lay tree leaf carry) fun cc => ?_
  refine allQ_bind (allQ_foldlM _ _ (fun state i => ?_) _) fun _ =>
    allQ_bind (lowerQuery_lowerLeafHash lay tree leaf _) fun _ => allQ_pure _
  exact allQ_bind (lowerQuery_chainW lay tree _ _ _ _ _) fun _ =>
    allQ_bind (lowerQuery_chainW lay tree _ _ _ _ _) fun _ => allQ_pure _
theorem lowerQuery_buildTreeP (selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (buildTreeP lay tree selected digits) (LowerQuery lay tree) := by
  unfold buildTreeP
  refine allQ_bind (allQ_foldlM _ _ (fun state leaf => ?_) _) fun _ =>
    allQ_bind (lowerQuery_buildLevelsBelow lay tree _ _) fun _ => allQ_pure _
  exact allQ_bind (lowerQuery_buildLeafPF lay tree _ _ _) fun _ => allQ_pure _
end
theorem lowerSeedQ_separated {lay : Layer} (hlay : lay ≠ 0) (tree : Nat) {tweak : BitVec 128}
    (h : LowerSeedQ lay tree (.inr (.inl tweak))) :
    (∀ coord index pair, tweak ≠ ftsSeedHeader coord index pair) ∧
      (∀ tree' position idx, tweak ≠ header 0 0 tree' position idx) ∧
      (∀ tag lay' tree' position idx, tag % 256 ≠ 0 → tweak ≠ header tag lay' tree' position idx) := by
  obtain ⟨pair, rfl⟩ := h
  exact ⟨fun coord index pair' he => ftsSeedHeader_ne_lowerSeedHeader coord index pair' lay tree pair he.symm,
    fun tree' position idx => lowerSeedHeader_ne_top lay hlay tree pair tree' position idx,
    fun tag lay' tree' position idx ht => lowerSeedHeader_ne_tag lay tree pair tag lay' tree' position idx ht⟩
end ClaudeWCT.WCT9
end

section




namespace ClaudeWCT.W9.T3.Security
open OracleComp OracleSpec SigGolfCandidate.T3
abbrev Signature : Type := ClaudeWCT.WCT9.Signature
abbrev signPayload : SigGolfCandidate.T3.Cache → Message → M (Option Signature) :=
  ClaudeWCT.WCT9.Rev3.signPayload
abbrev sign : SigGolfCandidate.T3.Cache → Message → M (Option Signature) :=
  ClaudeWCT.WCT9.Rev3.sign
theorem sign_eq (cache : SigGolfCandidate.T3.Cache) (message : Message) : sign cache message = (do
    let tag ← privateMac cache.region
    if tag ≠ cache.tag then return none
    signPayload cache message) := rfl
namespace Signer
open ClaudeWCT.WCT9 (Coord Child Rank child rank Opening)
open SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section allowed
variable (P : SigGolfCandidate.T3.Spec.Domain → Prop) (hpublic : ∀ input, P (.inl (.inr input)))
  (hseed : ∀ lay tree position index, P (.inr (.inl (header 8 lay tree position index))))
include hpublic in
theorem shortHash_allowed (input : HashInput) : AllQueriesSatisfy (shortHash input) P := by
  unfold shortHash publicHash
  exact SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr (hpublic _))
    fun _ => SourceQueries.pure_allowed P _
include hpublic in
theorem highHash_allowed (input : HashInput) : AllQueriesSatisfy (WCT9.highHash input) P := by
  unfold WCT9.highHash publicHash
  exact SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr (hpublic _))
    fun _ => SourceQueries.pure_allowed P _
include hpublic in
theorem projHash_allowed (high : Bool) (input : HashInput) :
    AllQueriesSatisfy (SigGolfCandidate.T3.projHash high input) P := by
  unfold SigGolfCandidate.T3.projHash publicHash
  exact SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr (hpublic _))
    fun _ => SourceQueries.pure_allowed P _
include hseed in
theorem seed_allowed (lay tree position index : Nat) :
    AllQueriesSatisfy (privatePair 8 lay tree position index) P := by
  unfold privatePair privateHash
  exact SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr (hseed _ _ _ _))
    fun _ => SourceQueries.pure_allowed P _
include hpublic in
theorem chain_allowed (index coord selected i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (WCT9.chain index coord selected i start count value) P := by
  unfold WCT9.chain
  exact SourceQueries.foldlM_allowed P _ _ (fun _ _ => projHash_allowed P hpublic _ _) _
include hpublic in
theorem leafHash_allowed (index coord selected : Nat) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHash index coord selected ends) P := by
  unfold WCT9.leafHash
  exact shortHash_allowed P hpublic _
include hseed in
theorem ftsCoefs_allowed (index coord : Nat) : AllQueriesSatisfy (WCT9.ftsCoefs index coord) P := by
  unfold WCT9.ftsCoefs
  apply SourceQueries.foldlM_allowed P
  intro acc j
  exact SourceQueries.bind_allowed P (by unfold WCT9.ftsSeedPair; exact seed_allowed P hseed _ _ _ _)
    fun _ => SourceQueries.pure_allowed P _
include hpublic in
theorem buildChildF_allowed (index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    AllQueriesSatisfy (WCT9.buildChildF index coord selected word coefs pad) P := by
  unfold WCT9.buildChildF
  apply SourceQueries.bind_allowed P
  · apply SourceQueries.foldlM_allowed P
    intro state i
    apply SourceQueries.bind_allowed P (chain_allowed P hpublic _ _ _ _ _ _ _)
    intro value
    apply SourceQueries.bind_allowed P (chain_allowed P hpublic _ _ _ _ _ _ _)
    intro _
    exact SourceQueries.pure_allowed P _
  · intro state
    exact SourceQueries.bind_allowed P (by unfold WCT9.leafHashP; exact shortHash_allowed P hpublic _)
      fun _ => SourceQueries.pure_allowed P _
include hpublic in
theorem nodeHash_allowed (tag lay tree heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) P := by
  unfold nodeHash
  exact shortHash_allowed P hpublic _
include hpublic in
/-- C1: an FTS hash (either half) makes one public query. -/
theorem ftsHash_allowed (heap : Nat) (input : HashInput) : AllQueriesSatisfy (WCT9.ftsHash heap input) P := by
  rw [WCT9.ftsHash_eq]
  split
  · exact highHash_allowed P hpublic _
  · exact shortHash_allowed P hpublic _
include hpublic in
theorem nodeHashH_allowed (coord index heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (WCT9.wctNodeHashH coord index heap left right) P := by
  unfold WCT9.wctNodeHashH
  exact ftsHash_allowed P hpublic _ _
include hpublic in
/-- C1: the paired child of heap `heap` makes only public queries. -/
theorem buildChildH_allowed (heap index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    AllQueriesSatisfy (WCT9.buildChildH heap index coord selected word coefs pad) P := by
  unfold WCT9.buildChildH
  apply SourceQueries.bind_allowed P
  · apply SourceQueries.foldlM_allowed P
    intro state i
    apply SourceQueries.bind_allowed P (chain_allowed P hpublic _ _ _ _ _ _ _)
    intro value
    apply SourceQueries.bind_allowed P (chain_allowed P hpublic _ _ _ _ _ _ _)
    intro _
    exact SourceQueries.pure_allowed P _
  · intro state
    exact SourceQueries.bind_allowed P (by unfold WCT9.leafHashH; exact ftsHash_allowed P hpublic _ _)
      fun _ => SourceQueries.pure_allowed P _
include hpublic in
/-- C1: every paired node (either half) makes one public query. -/
theorem sharedNode_allowed (first : Bool) (coord index heap : Nat)
    (pads : Nat → SigGolfCandidate.Research.SharedForest.PairRoot) (left right : Digest) :
    AllQueriesSatisfy (SigGolfCandidate.Research.SharedForest.sharedNode first coord index heap pads left right) P := by
  unfold SigGolfCandidate.Research.SharedForest.sharedNode SigGolfCandidate.Research.SharedForest.sharedOuterHash
  split
  · split
    · exact shortHash_allowed P hpublic _
    · exact highHash_allowed P hpublic _
  · split
    · split
      · exact highHash_allowed P hpublic _
      · exact shortHash_allowed P hpublic _
    · exact nodeHashH_allowed P hpublic _ _ _ _ _
include hpublic in
theorem heapBuild_allowed (index coord : Nat) (padR : Digest) (leaves : List Digest) :
    AllQueriesSatisfy (WCT9.heapBuild index coord padR leaves) P := by
  unfold WCT9.heapBuild
  apply SourceQueries.foldlM_allowed P
  intro nodes heap
  refine SourceQueries.bind_allowed P ?_ fun _ => SourceQueries.pure_allowed P _
  unfold WCT9.wctHeapNode
  split
  · unfold WCT9.wctTopHash; exact highHash_allowed P hpublic _
  · unfold WCT9.wctNodeHash; exact nodeHash_allowed P hpublic _ _ _ _ _ _
include hpublic hseed in
theorem buildCoordinateF_allowed (index : Nat) (coord : Coord) (selected : Child) (word : Rank)
    (prev : Digest × Digest) :
    AllQueriesSatisfy (WCT9.buildCoordinateF index coord selected word prev) P := by
  unfold WCT9.buildCoordinateF
  apply SourceQueries.bind_allowed P (ftsCoefs_allowed P hseed _ _)
  intro coefs
  apply SourceQueries.bind_allowed P
  · apply SourceQueries.foldlM_allowed P
    intro state j
    apply SourceQueries.bind_allowed P (buildChildF_allowed P hpublic _ _ _ _ _ _)
    rintro ⟨root, values⟩
    exact SourceQueries.pure_allowed P _
  · intro state
    exact SourceQueries.bind_allowed P (heapBuild_allowed P hpublic _ _ _ _)
      fun _ => SourceQueries.pure_allowed P _
include hpublic in
theorem forestPk_allowed (index : Nat) (pairs : List (Digest × Digest)) :
    AllQueriesSatisfy (WCT9.forestPk index pairs) P := by
  unfold WCT9.forestPk
  exact shortHash_allowed P hpublic _
omit hseed in
theorem layerCounterSearch_allowed'
    (henc : ∀ lay tree leaf msg counter, AllQueriesSatisfy (ClaudeWCT.WCT9.encodingHash lay (WCT9.layerEncodingInput lay tree leaf msg counter)) P)
    (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter fuel : Nat) :
    AllQueriesSatisfy (WCT9.layerCounterSearch lay tree leaf msg counter fuel) P := by
  induction fuel generalizing counter with
  | zero => exact SourceQueries.pure_allowed P _
  | succ fuel ih =>
      unfold WCT9.layerCounterSearch
      apply SourceQueries.bind_allowed P (henc _ _ _ _ _)
      intro answer
      split
      · exact ih _
      · exact SourceQueries.pure_allowed P _
include hpublic in
theorem layerCounterSearch_allowed (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter fuel : Nat) :
    AllQueriesSatisfy (WCT9.layerCounterSearch lay tree leaf msg counter fuel) P :=
  layerCounterSearch_allowed' P (fun _ _ _ _ _ => shortHash_allowed P hpublic _) lay tree leaf msg counter fuel
omit hseed in
theorem signLayersBC_allowed' (cache : SigGolfCandidate.T3.Cache)
    (henc : ∀ lay tree leaf msg counter, AllQueriesSatisfy (ClaudeWCT.WCT9.encodingHash lay (WCT9.layerEncodingInput lay tree leaf msg counter)) P)
    (hbuild : ∀ lay tree selected digits, AllQueriesSatisfy (WCT9.buildTreeP lay tree selected digits) P)
    (htop : ∀ leaf digits, AllQueriesSatisfy (signTop cache leaf digits) P) (index n : Nat) (msg : WCT9.LayerMsg) :
    AllQueriesSatisfy (WCT9.signLayersBC cache index n msg) P := by
  induction n generalizing msg with
  | zero => exact SourceQueries.pure_allowed P _
  | succ n ih =>
      unfold WCT9.signLayersBC
      apply SourceQueries.bind_allowed P (layerCounterSearch_allowed' P henc _ _ _ _ _ _)
      intro found
      split
      · exact SourceQueries.bind_allowed P (htop _ _) fun _ => SourceQueries.pure_allowed P _
      · split
        · apply SourceQueries.bind_allowed P (hbuild _ _ _ _)
          rintro ⟨levels, values⟩
          apply SourceQueries.bind_allowed P (ih _)
          intro previous
          split
          · exact SourceQueries.pure_allowed P _
          · exact SourceQueries.pure_allowed P _
        · exact SourceQueries.pure_allowed P _
include hpublic in
theorem signLayersBC_allowed (cache : SigGolfCandidate.T3.Cache)
    (hbuild : ∀ lay tree selected digits, AllQueriesSatisfy (WCT9.buildTreeP lay tree selected digits) P)
    (htop : ∀ leaf digits, AllQueriesSatisfy (signTop cache leaf digits) P) (index n : Nat) (msg : WCT9.LayerMsg) :
    AllQueriesSatisfy (WCT9.signLayersBC cache index n msg) P :=
  signLayersBC_allowed' P cache (fun _ _ _ _ _ => shortHash_allowed P hpublic _) hbuild htop index n msg
include hpublic in
theorem digestSearch_allowed (rho : Digest) (message : Message) (counter fuel : Nat) :
    AllQueriesSatisfy (WCT9.digestSearch rho message counter fuel) P := by
  induction fuel generalizing counter with
  | zero => exact SourceQueries.pure_allowed P _
  | succ fuel ih =>
      unfold WCT9.digestSearch digest publicHash
      apply SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr (hpublic _))
      intro output
      split
      · exact SourceQueries.pure_allowed P _
      · exact ih _
include hpublic hseed in
theorem signPayloadWith_allowed (limit : Nat) (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (hnonce : P (.inr (.inr (.inl message))))
    (hlayers : ∀ index n msg, AllQueriesSatisfy (WCT9.signLayersBC cache index n msg) P) :
    AllQueriesSatisfy (WCT9.signPayloadWith limit cache message) P := by
  unfold WCT9.signPayloadWith privateNonce privateHash
  apply SourceQueries.bind_allowed P
  · exact SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr hnonce)
      fun _ => SourceQueries.pure_allowed P _
  intro rho
  apply SourceQueries.bind_allowed P (digestSearch_allowed P hpublic _ _ _ _)
  intro found
  split
  · apply SourceQueries.bind_allowed P
    · apply SourceQueries.foldlM_allowed P
      intro state coord
      exact SourceQueries.bind_allowed P (buildCoordinateF_allowed P hpublic hseed _ _ _ _ _)
        fun _ => SourceQueries.pure_allowed P _
    · intro state
      apply SourceQueries.bind_allowed P (hlayers _ _ _)
      intro layers
      split
      · exact SourceQueries.pure_allowed P _
      · exact SourceQueries.pure_allowed P _
  · exact SourceQueries.pure_allowed P _
end allowed
/-! C2/C3 (FULL): the lower trees of the current scheme hash with `chainW`, `lowerLeafHash` and `lowerLevel`. Their
queries are those of `T3.chain` and `T3.leafHash` (same inputs, another half of the output); a lower node's query
needs its heap below `2 ^ height lay` (the packed node word's marker), which the honest tree shape guarantees. -/
theorem halfHash_allowed_of_short (P : SigGolfCandidate.T3.Spec.Domain → Prop) (high : Bool) {input : HashInput}
    (h : AllQueriesSatisfy (shortHash input) P) : AllQueriesSatisfy (WCT9.halfHash high input) P := by
  unfold shortHash publicHash at h
  have hq : P (.inl (.inr (pad64 input))) := ((allQueriesSatisfy_query_bind_iff _ _ _).mp h).1
  rw [WCT9.halfHash_eq]
  unfold publicHash
  exact SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr hq) fun _ => SourceQueries.pure_allowed P _
theorem chainW_allowed_of_chain (P : SigGolfCandidate.T3.Spec.Domain → Prop)
    (hstep : ∀ (lay : Layer) tree leaf i step value,
      AllQueriesSatisfy (shortHash (WCT9.chainInputW lay tree leaf i step value)) P)
    (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (WCT9.chainW lay tree leaf i start count value) P := by
  unfold WCT9.chainW
  exact SourceQueries.foldlM_allowed P _ _ (fun v step => halfHash_allowed_of_short P _ (hstep lay tree leaf i step v)) _
theorem lowerLeafHash_allowed_of_leafHash (P : SigGolfCandidate.T3.Spec.Domain → Prop)
    (hleaf : ∀ (lay : Layer) tree leaf ends, AllQueriesSatisfy (SigGolfCandidate.T3.leafHash lay tree leaf ends) P)
    (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.lowerLeafHash lay tree leaf ends) P := by
  rw [WCT9.lowerLeafHash_eq]
  exact halfHash_allowed_of_short P _ (hleaf lay tree leaf ends)
/-- A lower node hash only queries a public input. -/
theorem lowerNodeHash_allowed_of_public (P : SigGolfCandidate.T3.Spec.Domain → Prop)
    (hpublic : ∀ input, P (.inl (.inr input))) (lay tree heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (WCT9.lowerNodeHash lay tree heap left right) P := by
  unfold WCT9.lowerNodeHash WCT9.lowerHash
  exact halfHash_allowed_of_short P _ (shortHash_allowed P hpublic _)
theorem allQ_bind_supp {α β : Type} {P : SigGolfCandidate.T3.Spec.Domain → Prop} {p : M α} {f : α → M β}
    (hp : AllQueriesSatisfy p P) (hf : ∀ a ∈ support p, AllQueriesSatisfy (f a) P) :
    AllQueriesSatisfy (p >>= f) P := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    rw [pure_bind]
    exact hf a (by simp)
  | query_bind t mx ih =>
    rw [bind_assoc]
    rw [allQueriesSatisfy_query_bind_iff] at hp ⊢
    refine ⟨hp.1, fun u => ih u (hp.2 u) fun a ha => hf a ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, ha⟩
theorem mapM_allowed_mem {α β : Type} {P : SigGolfCandidate.T3.Spec.Domain → Prop} (f : α → M β) :
    ∀ (items : List α), (∀ a ∈ items, AllQueriesSatisfy (f a) P) → AllQueriesSatisfy (items.mapM f) P
  | [], _ => by simp
  | a :: items, h => by
    rw [List.mapM_cons]
    exact allQueriesSatisfy_bind (h a List.mem_cons_self) fun _ =>
      allQueriesSatisfy_bind (mapM_allowed_mem f items fun b hb => h b (List.mem_cons_of_mem _ hb)) fun _ =>
        allQueriesSatisfy_pure _ _
theorem mapM_support_length {α β : Type} (f : α → M β) :
    ∀ (xs : List α) (ys : List β), ys ∈ support (xs.mapM f) → ys.length = xs.length
  | [], ys, h => by simpa using h
  | x :: xs, ys, h => by
    rw [List.mapM_cons, mem_support_bind_iff] at h
    obtain ⟨y, -, h⟩ := h
    rw [mem_support_bind_iff] at h
    obtain ⟨zs, hzs, h⟩ := h
    simp only [support_pure, Set.mem_singleton_iff] at h
    subst h
    simp [mapM_support_length f xs zs hzs]
/-- A fold over `List.range' s n` with a step-indexed invariant on the reachable states. -/
theorem foldlM_range'_inv {α : Type} {P : SigGolfCandidate.T3.Spec.Domain → Prop} (I : Nat → α → Prop)
    (f : α → Nat → M α) :
    ∀ (n s : Nat) (init : α), I s init →
      (∀ k a, s ≤ k → k < s + n → I k a →
        AllQueriesSatisfy (f a k) P ∧ ∀ x ∈ support (f a k), I (k + 1) x) →
      AllQueriesSatisfy ((List.range' s n).foldlM f init) P ∧
        ∀ x ∈ support ((List.range' s n).foldlM f init), I (s + n) x
  | 0, s, init, h0, _ => ⟨by simp, by simpa using h0⟩
  | n + 1, s, init, h0, hs => by
    rw [List.range'_succ, List.foldlM_cons]
    obtain ⟨hq, hsup⟩ := hs s init (le_refl _) (by omega) h0
    have ih : ∀ a ∈ support (f init s), AllQueriesSatisfy ((List.range' (s + 1) n).foldlM f a) P ∧
        ∀ x ∈ support ((List.range' (s + 1) n).foldlM f a), I (s + 1 + n) x := fun a ha =>
      foldlM_range'_inv I f n (s + 1) a (hsup a ha) (fun k b h1 h2 h3 => hs k b (by omega) (by omega) h3)
    refine ⟨allQ_bind_supp hq fun a ha => (ih a ha).1, fun x hx => ?_⟩
    rw [mem_support_bind_iff] at hx
    obtain ⟨a, ha, hx⟩ := hx
    have := (ih a ha).2 x hx
    rwa [show s + 1 + n = s + (n + 1) by omega] at this
/-- A fold whose every step appends one element to the first component. -/
theorem foldlM_support_fst_length {α β γ : Type} (items : List β) (f : List γ × α → β → M (List γ × α))
    (hf : ∀ s b, ∀ x ∈ support (f s b), x.1.length = s.1.length + 1) :
    ∀ init, ∀ x ∈ support (items.foldlM f init), x.1.length = init.1.length + items.length := by
  induction items with
  | nil => intro init x hx; simp only [List.foldlM_nil, support_pure, Set.mem_singleton_iff] at hx; subst hx; simp
  | cons b items ih =>
    intro init x hx
    rw [List.foldlM_cons, mem_support_bind_iff] at hx
    obtain ⟨a, ha, hx⟩ := hx
    rw [ih a x hx, hf init b a ha, List.length_cons]
    omega
theorem height_le_seven {lay : Layer} (h0 : lay.val ≠ 0) : height lay ≤ 7 := by
  fin_cases lay <;> simp_all [height]
theorem lowerLevel_allowed (P : SigGolfCandidate.T3.Spec.Domain → Prop)
    (hnode : ∀ (lay : Layer) tree heap left right, heap < 2 ^ height lay →
      AllQueriesSatisfy (WCT9.lowerNodeHash lay.val tree heap left right) P)
    (lay : Layer) (tree level : Nat) (nodes : List Digest) (h1 : 1 ≤ level) (h2 : level < height lay)
    (hn : nodes.length = 2 ^ (height lay - (level - 1))) :
    AllQueriesSatisfy (WCT9.lowerLevel lay.val tree (height lay) level nodes) P := by
  unfold WCT9.lowerLevel
  refine mapM_allowed_mem _ _ fun i hi => hnode lay tree _ _ _ ?_
  rw [List.mem_range, hn, show height lay - (level - 1) = (height lay - level) + 1 by omega, pow_succ,
    Nat.mul_div_cancel _ (by decide)] at hi
  have hle : 2 ^ (height lay - level) * 2 ≤ 2 ^ height lay := by
    rw [← pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
  omega
theorem buildLevelsBelow_allowed (P : SigGolfCandidate.T3.Spec.Domain → Prop)
    (hnode : ∀ (lay : Layer) tree heap left right, heap < 2 ^ height lay →
      AllQueriesSatisfy (WCT9.lowerNodeHash lay.val tree heap left right) P)
    (lay : Layer) (tree : Nat) (leaves : List Digest) (hlen : leaves.length = 2 ^ height lay) :
    AllQueriesSatisfy (WCT9.buildLevelsBelow 3 lay.val tree (height lay) leaves) P := by
  unfold WCT9.buildLevelsBelow
  refine (foldlM_range'_inv (P := P)
    (fun k (levels : List (List Digest)) =>
      levels.length = k ∧ (levels.getD (k - 1) []).length = 2 ^ (height lay - (k - 1))) _
    (height lay - 1) 1 [leaves] ⟨rfl, by simpa using hlen⟩ ?_).1
  rintro k levels hk1 hk2 ⟨hl, hg⟩
  have hk : k < height lay := by omega
  refine ⟨SourceQueries.bind_allowed P (lowerLevel_allowed P hnode lay tree k _ hk1 hk hg) fun _ =>
    SourceQueries.pure_allowed P _, fun x hx => ?_⟩
  rw [mem_support_bind_iff] at hx
  obtain ⟨nodes, hnodes, hx⟩ := hx
  simp only [support_pure, Set.mem_singleton_iff] at hx
  subst hx
  have hnl := mapM_support_length _ _ _ hnodes
  rw [List.length_range, hg, show height lay - (k - 1) = (height lay - k) + 1 by omega, pow_succ,
    Nat.mul_div_cancel _ (by decide)] at hnl
  refine ⟨by simp [hl], ?_⟩
  rw [show k + 1 - 1 = k by omega, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [hl, hnl]
theorem buildTreeP_allowed' (P : SigGolfCandidate.T3.Spec.Domain → Prop)
    (hchain : ∀ (lay : Layer) tree leaf i step value,
      AllQueriesSatisfy (shortHash (WCT9.chainInputW lay tree leaf i step value)) P)
    (hleaf : ∀ (lay : Layer) tree leaf ends, AllQueriesSatisfy (SigGolfCandidate.T3.leafHash lay tree leaf ends) P)
    (hnode : ∀ (lay : Layer) tree heap left right, heap < 2 ^ height lay →
      AllQueriesSatisfy (WCT9.lowerNodeHash lay.val tree heap left right) P)
    (hseed : ∀ (lay : Layer) tree pair, AllQueriesSatisfy (WCT9.lowerSeedPair lay tree pair) P)
    (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (WCT9.buildTreeP lay tree selected digits) P := by
  have hpf : ∀ leaf digits carry, AllQueriesSatisfy (WCT9.buildLeafPF lay tree leaf digits carry) P := by
    intro leaf digits carry
    unfold WCT9.buildLeafPF
    refine SourceQueries.bind_allowed P ?_ fun cc => ?_
    · unfold WCT9.lowerCoefs WCT9.lowerFamCoefs
      split
      · refine SourceQueries.bind_allowed P ?_ fun _ => SourceQueries.pure_allowed P _
        refine SourceQueries.bind_allowed P ?_ fun _ => SourceQueries.pure_allowed P _
        exact SourceQueries.foldlM_allowed P _ _ (fun acc j =>
          SourceQueries.bind_allowed P (hseed _ _ _) fun _ => SourceQueries.pure_allowed P _) _
      · exact SourceQueries.pure_allowed P _
    refine SourceQueries.bind_allowed P (SourceQueries.foldlM_allowed P _ _ (fun state i => ?_) _) fun _ =>
      SourceQueries.bind_allowed P (lowerLeafHash_allowed_of_leafHash P hleaf _ _ _ _) fun _ =>
        SourceQueries.pure_allowed P _
    exact SourceQueries.bind_allowed P (chainW_allowed_of_chain P hchain _ _ _ _ _ _ _) fun _ =>
      SourceQueries.bind_allowed P (chainW_allowed_of_chain P hchain _ _ _ _ _ _ _) fun _ =>
        SourceQueries.pure_allowed P _
  unfold WCT9.buildTreeP
  refine allQ_bind_supp (SourceQueries.foldlM_allowed P _ _ (fun state leaf =>
    SourceQueries.bind_allowed P (hpf _ _ _) fun _ => SourceQueries.pure_allowed P _) _) fun state hstate => ?_
  have hlen : state.1.length = 2 ^ height lay := by
    have := foldlM_support_fst_length _ _ (fun s b x hx => by
      rw [mem_support_bind_iff] at hx
      obtain ⟨⟨⟨root, values⟩, carry⟩, -, hx⟩ := hx
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      simp) _ state hstate
    simpa using this
  exact SourceQueries.bind_allowed P (buildLevelsBelow_allowed P hnode lay tree _ hlen) fun _ =>
    SourceQueries.pure_allowed P _
theorem buildTreeP_allowed (P : SigGolfCandidate.T3.Spec.Domain → Prop) (hpublic : ∀ input, P (.inl (.inr input)))
    (hlower : ∀ (lay : Layer) tree pair, P (.inr (.inl (WCT9.lowerSeedHeader lay tree pair))))
    (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (WCT9.buildTreeP lay tree selected digits) P := by
  refine SigGolfCandidate.T3M.allQ_mono (WCT9.lowerQuery_buildTreeP lay tree selected digits) fun q hq => ?_
  rcases hq with ⟨hp, -⟩ | hs
  · rcases q with (n | input) | c
    · exact hp.elim
    · exact hpublic input
    · exact hp.elim
  · rcases q with (n | input) | (tweak | rest)
    · exact hs.elim
    · exact hs.elim
    · obtain ⟨pair, rfl⟩ := hs
      exact hlower lay tree pair
    · exact hs.elim
theorem signPayloadWith_nonMac (limit : Nat) (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    AllQueriesSatisfy (WCT9.signPayloadWith limit cache message) SiggolfT3Mac4.Source.NonMac :=
  signPayloadWith_allowed _ (fun _ => trivial)
    (fun lay tree position index => ⟨SiggolfT3Mac4.Source.non_mac_tweak 8 lay tree position index (by decide) 0,
      SiggolfT3Mac4.Source.non_mac_tweak 8 lay tree position index (by decide) 1⟩)
    limit cache message (SiggolfT3Mac4.Source.nonce_coordinate_other message)
    (fun index n msg => signLayersBC_allowed _ (fun _ => trivial) cache
      (buildTreeP_allowed _ (fun _ => trivial) (fun lay tree pair =>
        ⟨SiggolfT3Mac4.Source.non_mac_tweak 0 lay.val tree pair 0 (by decide) 0,
          SiggolfT3Mac4.Source.non_mac_tweak 0 lay.val tree pair 0 (by decide) 1⟩))
      (SiggolfT3Mac4.Source.Payload.signTop_allowed cache) index n msg)
theorem signPayload_nonMac (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    AllQueriesSatisfy (signPayload cache message) SiggolfT3Mac4.Source.NonMac :=
  signPayloadWith_nonMac _ cache message
theorem signPayloadWith_hashOnly (limit : Nat) (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    SigGolfCandidate.T3.Security.SourceReplay.HashOnly (WCT9.signPayloadWith limit cache message) :=
  signPayloadWith_allowed _ (fun _ => trivial) (fun _ _ _ _ => trivial) limit cache message trivial
    (fun index n msg => signLayersBC_allowed _ (fun _ => trivial) cache
      (buildTreeP_allowed _ (fun _ => trivial) (fun _ _ _ => trivial))
      (SourceQueries.signTop_allowed SigGolfCandidate.T3.Security.SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) cache)
      index n msg)
theorem signPayload_hashOnly (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    SigGolfCandidate.T3.Security.SourceReplay.HashOnly (signPayload cache message) :=
  signPayloadWith_hashOnly _ cache message
theorem signPayloadWith_avoids (protectedMessage : Message) (limit : Nat) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (hne : message ≠ protectedMessage) :
    NonceFreshness.Avoids protectedMessage (WCT9.signPayloadWith limit cache message) :=
  signPayloadWith_allowed _ (fun _ => by simp [NonceFreshness.nonceQuery])
    (fun _ _ _ _ => by simp [NonceFreshness.nonceQuery]) limit cache message
    (by simpa [NonceFreshness.nonceQuery] using hne)
    (fun index n msg => signLayersBC_allowed _ (fun _ => by simp [NonceFreshness.nonceQuery]) cache
      (buildTreeP_allowed _ (fun _ => by simp [NonceFreshness.nonceQuery])
        (fun _ _ _ => by simp [NonceFreshness.nonceQuery]))
      (NonceFreshness.avoids_signTop protectedMessage cache)
      index n msg)
theorem signPayload_avoids (protectedMessage : Message) (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (hne : message ≠ protectedMessage) : NonceFreshness.Avoids protectedMessage (signPayload cache message) :=
  signPayloadWith_avoids protectedMessage _ cache message hne
theorem sign_hashOnly (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    SigGolfCandidate.T3.Security.SourceReplay.HashOnly (sign cache message) := by
  rw [sign_eq]
  apply SourceQueries.bind_allowed SigGolfCandidate.T3.Security.SourceReplay.IsHash
    (SourceQueries.privateMac_allowed SigGolfCandidate.T3.Security.SourceReplay.IsHash (fun _ => trivial) _)
  intro tag
  split_ifs
  · exact SourceQueries.pure_allowed _ _
  · exact signPayload_hashOnly cache message
theorem sign_avoids (protectedMessage : Message) (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (hne : message ≠ protectedMessage) : NonceFreshness.Avoids protectedMessage (sign cache message) := by
  rw [sign_eq]
  apply NonceFreshness.avoids_bind protectedMessage (NonceFreshness.avoids_privateMac protectedMessage _)
  intro tag
  split_ifs
  · exact NonceFreshness.avoids_pure _ _
  · exact signPayload_avoids protectedMessage cache message hne
end Signer
end ClaudeWCT.W9.T3.Security
end

namespace ClaudeWCT.W9.T3.Security.SharedQueries
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Stage 2 (C2/C3, #866): the lower trees hash with `chainW`, `lowerLeafHash` (same inputs as `T3.chain` /
`T3.leafHash`, another half of the output; `Signer.halfHash_allowed_of_short`) and `lowerNodeHash`, whose query
needs the honest heap bound `heap < 2 ^ height lay` (the packed node word's marker). -/
structure TailAllowed (Q : SigGolfCandidate.T3.Spec.Domain → Prop) : Prop where
  chainStep : ∀ lay tree leaf i step value,
    AllQueriesSatisfy (shortHash (SigGolfCandidate.T3.chainInput lay tree leaf i step value)) Q
  /-- Pairing stage 1: the chain steps of the current scheme (G chains included). -/
  chainStepW : ∀ lay tree leaf i step value,
    AllQueriesSatisfy (shortHash (WCT9.chainInputW lay tree leaf i step value)) Q
  leaf : ∀ lay tree leaf ends, AllQueriesSatisfy (SigGolfCandidate.T3.leafHash lay tree leaf ends) Q
  node : ∀ (lay : Layer) tree heap left right, heap < 2 ^ height lay →
    AllQueriesSatisfy (lowerNodeHash lay.val tree heap left right) Q
  seed : ∀ lay tree pair, AllQueriesSatisfy (lowerSeedPair lay tree pair) Q
  encoding : ∀ lay tree leaf msg counter,
    AllQueriesSatisfy (encodingHash lay (layerEncodingInput lay tree leaf msg counter)) Q
  top : ∀ cache leaf digits, AllQueriesSatisfy (signTop cache leaf digits) Q

section
variable (Q : SigGolfCandidate.T3.Spec.Domain → Prop) (hQ : TailAllowed Q)
include hQ

theorem chain_allowed (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.chain lay tree leaf i start count value) Q := by
  unfold SigGolfCandidate.T3.chain
  exact SourceQueries.foldlM_allowed Q _ _ (fun _ _ => hQ.chainStep ..) _

theorem chainW_allowed (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chainW lay tree leaf i start count value) Q := by
  unfold chainW
  exact SourceQueries.foldlM_allowed Q _ _ (fun _ _ =>
    Signer.halfHash_allowed_of_short Q _ (hQ.chainStepW ..)) _

theorem lowerLeafHash_allowed (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (lowerLeafHash lay tree leaf ends) Q :=
  Signer.lowerLeafHash_allowed_of_leafHash Q hQ.leaf lay tree leaf ends

theorem lowerCoefs_allowed (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    AllQueriesSatisfy (lowerCoefs lay tree leaf carry) Q := by
  unfold lowerCoefs lowerFamCoefs
  split
  · refine SourceQueries.bind_allowed Q ?_ fun _ => SourceQueries.pure_allowed Q _
    refine SourceQueries.bind_allowed Q ?_ fun _ => SourceQueries.pure_allowed Q _
    exact SourceQueries.foldlM_allowed Q _ _ (fun acc j =>
      SourceQueries.bind_allowed Q (hQ.seed ..) fun _ => SourceQueries.pure_allowed Q _) _
  · exact SourceQueries.pure_allowed Q _

theorem buildLeafPF_allowed (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : List Digest) :
    AllQueriesSatisfy (buildLeafPF lay tree leaf digits carry) Q := by
  unfold buildLeafPF
  refine SourceQueries.bind_allowed Q (lowerCoefs_allowed Q hQ ..) fun _ => ?_
  refine SourceQueries.bind_allowed Q (SourceQueries.foldlM_allowed Q _ _ (fun state i => ?_) _) fun _ =>
    SourceQueries.bind_allowed Q (lowerLeafHash_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _
  exact SourceQueries.bind_allowed Q (chainW_allowed Q hQ ..) fun _ =>
    SourceQueries.bind_allowed Q (chainW_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _

theorem chainPrefixes_allowed (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chainPrefixes lay tree leaf i start count value) Q := by
  induction count generalizing start value with
  | zero => exact SourceQueries.pure_allowed Q _
  | succ count ih =>
    unfold chainPrefixes
    exact SourceQueries.bind_allowed Q (Signer.halfHash_allowed_of_short Q _ (hQ.chainStepW ..)) fun _ =>
      SourceQueries.bind_allowed Q (ih ..) fun _ => SourceQueries.pure_allowed Q _

theorem buildLeafPrefixes_allowed (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    AllQueriesSatisfy (buildLeafPrefixes lay tree leaf carry) Q := by
  unfold buildLeafPrefixes
  exact SourceQueries.bind_allowed Q (lowerCoefs_allowed Q hQ ..) fun _ =>
    SourceQueries.bind_allowed Q (SourceQueries.mapM_allowed Q _ _
      (fun _ => chainPrefixes_allowed Q hQ ..)) fun _ =>
      SourceQueries.bind_allowed Q (lowerLeafHash_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _

theorem buildTreePrefixes_allowed (lay : Layer) (tree selected : Nat) :
    AllQueriesSatisfy (buildTreePrefixes lay tree selected) Q := by
  unfold buildTreePrefixes
  refine Signer.allQ_bind_supp (SourceQueries.foldlM_allowed Q _ _ (fun state leaf => ?_) _)
    fun state hstate => ?_
  · dsimp only
    split
    · refine SourceQueries.bind_allowed Q (buildLeafPrefixes_allowed Q hQ ..) fun r => ?_
      rcases r with ⟨⟨root, prefixes⟩, carry⟩
      exact SourceQueries.pure_allowed Q _
    · refine SourceQueries.bind_allowed Q (buildLeafPF_allowed Q hQ ..) fun r => ?_
      rcases r with ⟨⟨root, prefixes⟩, carry⟩
      simp only [pure_bind]
      exact SourceQueries.pure_allowed Q _
  · -- C2: the lower levels need the honest leaf count (heap bound of `lowerNodeHash`), as in
    -- `Signer.buildTreeP_allowed'`.
    have hlen : state.1.length = 2 ^ height lay := by
      have := Signer.foldlM_support_fst_length _ _ (fun s b x hx => by
        dsimp only at hx
        split at hx
        all_goals
          try simp only [pure_bind] at hx
          rw [mem_support_bind_iff] at hx
          obtain ⟨⟨⟨root, values⟩, carry⟩, -, hx⟩ := hx
          simp only [support_pure, Set.mem_singleton_iff] at hx
          subst hx
          simp) _ state hstate
      simpa using this
    exact SourceQueries.bind_allowed Q (Signer.buildLevelsBelow_allowed Q hQ.node lay tree _ hlen) fun _ =>
      SourceQueries.pure_allowed Q _

theorem prepareRoots_allowed (index : Nat) : AllQueriesSatisfy (prepareRoots index) Q := by
  unfold prepareRoots
  exact SourceQueries.bind_allowed Q (buildTreePrefixes_allowed Q hQ ..) fun _ =>
    SourceQueries.bind_allowed Q (buildTreePrefixes_allowed Q hQ ..) fun _ =>
      SourceQueries.bind_allowed Q (buildTreePrefixes_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _

theorem layerCounterSearchAt_allowed (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) (counter fuel : Nat) :
    AllQueriesSatisfy (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) Q := by
  induction fuel generalizing counter with
  | zero => exact SourceQueries.pure_allowed Q _
  | succ fuel ih =>
    unfold CanonicalPolicy.layerCounterSearchAt
    -- the canonical search queries `publicHash` directly (the choice is applied by `producerDecodeOut`);
    -- its query set is the one of `encodingHash` (a pure map of the same query).
    have hpub : AllQueriesSatisfy (publicHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter))) Q := by
      have h := hQ.encoding lay tree leaf msg (BitVec.ofNat 32 counter)
      change AllQueriesSatisfy ((encodingAnswer lay) <$> publicHash _) Q at h
      simpa only [AllQueriesSatisfy, isQueryBound_map_iff] using h
    apply SourceQueries.bind_allowed Q hpub
    intro answer
    split
    · exact ih _
    · exact SourceQueries.pure_allowed Q _

theorem searchPreparedLayers_allowed (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) :
    AllQueriesSatisfy (searchPreparedLayers cache index prepared forest) Q := by
  unfold searchPreparedLayers
  apply SourceQueries.bind_allowed Q (layerCounterSearchAt_allowed Q hQ ..)
  intro found
  rcases found with _ | ⟨counter0,digits0,low0⟩
  · exact SourceQueries.pure_allowed Q _
  · dsimp only
    split
    · exact SourceQueries.pure_allowed Q _
    · apply SourceQueries.bind_allowed Q (layerCounterSearchAt_allowed Q hQ ..)
      intro found
      rcases found with _ | ⟨counter1,digits1,low1⟩
      · exact SourceQueries.pure_allowed Q _
      · dsimp only
        split
        · exact SourceQueries.pure_allowed Q _
        · apply SourceQueries.bind_allowed Q (layerCounterSearchAt_allowed Q hQ ..)
          intro found
          rcases found with _ | ⟨counter2,digits2,low2⟩
          · exact SourceQueries.pure_allowed Q _
          · dsimp only
            split
            · exact SourceQueries.pure_allowed Q _
            · apply SourceQueries.bind_allowed Q (layerCounterSearchAt_allowed Q hQ ..)
              intro found
              rcases found with _ | ⟨counter3,digits3,low3⟩
              · exact SourceQueries.pure_allowed Q _
              · exact SourceQueries.bind_allowed Q (hQ.top ..) fun _ => SourceQueries.pure_allowed Q _

theorem signFromOutput_allowed
    (hforest : ∀ index selected words, AllQueriesSatisfy (buildForest index selected words) Q)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    AllQueriesSatisfy (signFromOutput cache rho counter output) Q := by
  unfold signFromOutput
  apply SourceQueries.bind_allowed Q (hforest ..)
  intro forest
  apply SourceQueries.bind_allowed Q (prepareRoots_allowed Q hQ ..)
  intro prepared
  apply SourceQueries.bind_allowed Q (searchPreparedLayers_allowed Q hQ ..)
  intro layers
  cases layers <;> exact SourceQueries.pure_allowed Q _
end

end ClaudeWCT.W9.T3.Security.SharedQueries
end
-- ==== merged from ClaudeWCT_Bank_WCTRev3 ====
section

section
namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Completeness (searchLoop)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.WCT9 (Coord Child Rank child rank Opening wctHeader buildChildF buildCoordinateF)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem wct_digestSearch_public {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
    (hadm : S.producer = WCT9.producerAdmissible) (rho : Digest) (message : Message) :
    ∀ fuel counter, WCT9.digestSearch rho message counter fuel = S.search rho message counter fuel := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      rw [WCT9.digestSearch, FtsBankSpec.search, searchLoop]
      simp only [Sampling.publicProgram, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.Concrete.oracleHash, HasQuery.query, Sampling.publicHandler,
        digest, publicHash, Sampling.digestTrial, FtsBankSpec.decode, hadm]
      apply bind_congr
      intro answer
      split <;> simp only [simulateQ_pure, map_pure, ih, FtsBankSpec.search, Sampling.publicProgram]
def payAfterDigest (cache : T3.Cache) (rho : Digest) (output : HashOutput) : M (Option WCT9.Signature) := do
  let index := WCT9.digestIndex output
  let state ← (List.finRange 9).foldlM
    (fun (state : List Opening × List (Digest × Digest)) coord => do
      let selected := child output coord
      let (levels, values) ← buildCoordinateF index coord selected (rank output coord)
        (WCT9.prevPair WCT9.ftsStart state.2)
      let path := (List.range 7).map fun level =>
        (levels.getD level []).getD (selected.val / 2 ^ level ^^^ 1) 0
      let opening : Opening := ⟨fun i => values.getD i.val 0, fun i => path.getD i.val 0⟩
      pure (state.1 ++ [opening],
        state.2 ++ [((levels.getD 6 []).getD 0 0, (levels.getD 6 []).getD 1 0)])) ([], [])
  let top := WCT9.prevPair WCT9.ftsStart state.2
  let some layers ← WCT9.signLayersBC cache index 4 (.pair top.1 top.2) | pure none
  pure (some ⟨rho, fun coord => state.1.getD coord.val ⟨fun _ => 0, fun _ => 0⟩,
    fun lay => piecesSignature lay (layers.getD lay.val ([], []))⟩)
theorem signPayload_factor (cache : T3.Cache) (message : Message) :
    WCT9.signPayload cache message = (do
      let rho ← privateNonce message
      let found ← WCT9.digestSearch rho message 0 attemptLimit
      match found with
      | none => pure none
      | some (_, output) => payAfterDigest cache rho output) := by
  unfold WCT9.signPayload
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩ <;> rfl
theorem payloadRecord_erasure {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
    (hadm : S.producer = WCT9.producerAdmissible) (cache : T3.Cache) (message : Message) :
    Prod.fst <$> S.payloadRecord payAfterDigest cache message = WCT9.signPayload cache message := by
  rw [signPayload_factor]
  unfold FtsBankSpec.payloadRecord FtsBankSpec.recordForNonce
  simp only [map_bind]
  apply bind_congr
  intro rho
  rw [wct_digestSearch_public S hadm]
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩
  · simp
  · simp only [map_bind, map_pure]
    exact bind_pure _
section avoids
variable (m : Message)
theorem avoids_chain (index coord selected i start count : Nat) (value : Digest) :
    NonceFreshness.Avoids m (WCT9.chain index coord selected i start count value) := by
  unfold WCT9.chain
  exact NonceFreshness.avoids_foldlM m _ _ (fun _ _ => NonceFreshness.avoids_projHash m _ _) _
theorem avoids_leafHash (index coord selected : Nat) (ends : List Digest) :
    NonceFreshness.Avoids m (WCT9.leafHash index coord selected ends) := by
  unfold WCT9.leafHash
  exact NonceFreshness.avoids_shortHash m _
theorem avoids_forestPk (index : Nat) (roots : List (Digest × Digest)) :
    NonceFreshness.Avoids m (WCT9.forestPk index roots) := by
  unfold WCT9.forestPk
  exact NonceFreshness.avoids_shortHash m _
theorem avoids_buildChildF (index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    NonceFreshness.Avoids m (buildChildF index coord selected word coefs pad) :=
  W9.T3.Security.Signer.buildChildF_allowed _ (fun _ => by simp [NonceFreshness.nonceQuery])
    index coord selected word coefs pad
theorem avoids_ftsCoefs (index coord : Nat) : NonceFreshness.Avoids m (WCT9.ftsCoefs index coord) :=
  W9.T3.Security.Signer.ftsCoefs_allowed _ (fun _ _ _ _ => by simp [NonceFreshness.nonceQuery]) index coord
theorem avoids_buildCoordinateF (index : Nat) (coord : Coord) (selected : Child) (word : Rank)
    (prev : Digest × Digest) :
    NonceFreshness.Avoids m (buildCoordinateF index coord selected word prev) :=
  W9.T3.Security.Signer.buildCoordinateF_allowed _ (fun _ => by simp [NonceFreshness.nonceQuery])
    (fun _ _ _ _ => by simp [NonceFreshness.nonceQuery]) index coord selected word prev
theorem avoids_signLayersBC (cache : T3.Cache) (index n : Nat) (msg : WCT9.LayerMsg) :
    NonceFreshness.Avoids m (WCT9.signLayersBC cache index n msg) :=
  W9.T3.Security.Signer.signLayersBC_allowed _ (fun _ => by simp [NonceFreshness.nonceQuery]) cache
    (W9.T3.Security.Signer.buildTreeP_allowed _ (fun _ => by simp [NonceFreshness.nonceQuery])
      (fun _ _ _ => by simp [NonceFreshness.nonceQuery]))
    (NonceFreshness.avoids_signTop m cache) index n msg
end avoids
theorem wct_payAvoids : PayAvoids payAfterDigest := by
  intro m cache rho output
  unfold payAfterDigest
  apply NonceFreshness.avoids_bind m
  · apply NonceFreshness.avoids_foldlM m
    intro state coord
    exact NonceFreshness.avoids_bind m (avoids_buildCoordinateF m _ _ _ _ _) fun _ => NonceFreshness.avoids_pure m _
  · intro state
    apply NonceFreshness.avoids_bind m (avoids_signLayersBC m _ _ _ _)
    intro layers
    split
    · exact NonceFreshness.avoids_pure m _
    · exact NonceFreshness.avoids_pure m _
theorem wctHeader_value_lt (tag lay tree position index : Nat) :
    1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + (tree / 2 ^ 32 % 256) * 2 ^ 24 +
      position % 2 ^ 32 * 2 ^ 32 + tree % 2 ^ 32 * 2 ^ 64 + index % 2 ^ 32 * 2 ^ 96 < 2 ^ 128 := by
  have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
  have h2 := Nat.mod_lt lay (show 0 < 256 by decide)
  have h3 := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have h4 := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have h5 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h6 := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  norm_num only at h1 h2 h3 h4 h5 h6 ⊢
  omega
theorem wctHeader_toNat (tag lay tree position index : Nat) :
    (wctHeader tag lay tree position index).toNat =
      1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + (tree / 2 ^ 32 % 256) * 2 ^ 24 +
        position % 2 ^ 32 * 2 ^ 32 + tree % 2 ^ 32 * 2 ^ 64 + index % 2 ^ 32 * 2 ^ 96 := by
  unfold wctHeader
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (wctHeader_value_lt _ _ _ _ _)]
theorem wctHeader_byte1 (tag lay tree position index : Nat) :
    ((bytesLE 16 (wctHeader tag lay tree position index)).getD 1 0).toNat = tag % 256 := by
  have h : (bytesLE 16 (wctHeader tag lay tree position index)).getD 1 0 =
      ⟨(wctHeader tag lay tree position index).extractLsb' 8 8⟩ := rfl
  rw [h]
  show ((wctHeader tag lay tree position index).extractLsb' 8 8).toNat = tag % 256
  rw [BitVec.extractLsb'_toNat, wctHeader_toNat, Nat.shiftRight_eq_div_pow]
  have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
  have h2 := Nat.mod_lt lay (show 0 < 256 by decide)
  have h3 := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have h4 := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have h5 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h6 := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  generalize tag % 256 = a at *
  generalize lay % 256 = b at *
  generalize tree / 2 ^ 32 % 256 = c at *
  generalize position % 2 ^ 32 = d at *
  generalize tree % 2 ^ 32 = e at *
  generalize index % 2 ^ 32 = f at *
  norm_num at h4 h5 h6 ⊢
  omega
theorem wctHeader_byte0 (tag lay tree position index : Nat) :
    ((bytesLE 16 (wctHeader tag lay tree position index)).getD 0 0).toNat = 1 := by
  rw [bytesLE16_first_toNat, wctHeader_toNat]
  omega
theorem hdrBlock_pad64_prefix (a h rest : HashInput) (ha : a.length = 16) (hh : h.length = 16) :
    T3M.Extract.hdrBlock (pad64 (a ++ h ++ rest)) = h := by
  rw [T3M.Extract.hdrBlock_pad64 _ (by simp [ha, hh]; omega)]
  unfold T3M.Extract.hdrBlock
  rw [List.append_assoc, List.drop_left' ha, List.take_left' hh]
theorem shortHash_wct_ok (a rest : HashInput) (tag lay tree position index : Nat) (ha : a.length = 16)
    (_ht : tag % 256 ≠ 0) :
    AllQueriesSatisfy (shortHash (a ++ bytesLE 16 (wctHeader tag lay tree position index) ++ rest)) BPB.NotDigestQ := by
  unfold shortHash publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    show BPB.hdrMarker (pad64 (a ++ bytesLE 16 (wctHeader tag lay tree position index) ++ rest)) ≠ 0
    apply BPB.hdrMarker_ne_zero_of_byte0
    unfold BPB.hdrByte0
    rw [hdrBlock_pad64_prefix _ _ _ ha (bytesLE_length _ _), wctHeader_byte0]
    decide
  · intro _; exact SourceQueries.pure_allowed _ _
/-- Witness stack: FTS chain step in either format (G chains 1, 3: `value | header | 0 | 0`). -/
theorem chainInput_ok (index coord selected i step : Nat) (high : Bool) (value : Digest) :
    AllQueriesSatisfy (projHash high (WCT9.ftsChainInputW index coord selected i step value)) BPB.NotDigestQ := by
  unfold projHash publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    show BPB.hdrMarker (pad64 (WCT9.ftsChainInputW index coord selected i step value)) ≠ 0
    apply BPB.hdrMarker_ne_zero_of_byte0
    unfold BPB.hdrByte0 WCT9.ftsChainInputW
    split
    · rw [List.append_assoc (bytesLE 16 value ++ _), hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _)
        (bytesLE_length _ _), bytesLE16_first_toNat, WCT9.ftsChainHeader_toNat, WCT9.ftsChainLow_byte0]
      omega
    · unfold WCT9.chainInput
      rw [List.append_assoc (zero16 ++ _), hdrBlock_pad64_prefix _ _ _ (by simp [zero16]) (bytesLE_length _ _),
        bytesLE16_first_toNat, WCT9.ftsChainHeader_toNat, WCT9.ftsChainLow_byte0]
      omega
  · intro _; exact SourceQueries.pure_allowed _ _
theorem chain_ok (index coord selected i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (WCT9.chain index coord selected i start count value) BPB.NotDigestQ := by
  unfold WCT9.chain
  exact SourceQueries.foldlM_allowed BPB.NotDigestQ _ _ (fun v step => chainInput_ok _ _ _ _ _ _ _) _
theorem leafHash_ok (index coord selected : Nat) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHash index coord selected ends) BPB.NotDigestQ := by
  unfold WCT9.leafHash shortHash publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    show BPB.hdrMarker (pad64 (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (WCT9.ftsLeafHeader index coord selected) ++
      zero16 ++ (ends.drop 1).flatMap (bytesLE 16))) ≠ 0
    apply BPB.hdrMarker_ne_zero_of_byte0
    unfold BPB.hdrByte0
    rw [List.append_assoc (bytesLE 16 _ ++ bytesLE 16 _), hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _) (bytesLE_length _ _), bytesLE16_first_toNat,
      WCT9.ftsLeafHeader_firstByte]
    decide
  · intro _; exact SourceQueries.pure_allowed _ _
theorem leafHashP_ok (index coord selected : Nat) (pad : Digest) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHashP index coord selected pad ends) BPB.NotDigestQ := by
  unfold WCT9.leafHashP WCT9.leafInputP shortHash publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    show BPB.hdrMarker (pad64 (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (WCT9.ftsLeafHeader index coord selected) ++
      bytesLE 16 pad ++ (ends.drop 1).flatMap (bytesLE 16))) ≠ 0
    apply BPB.hdrMarker_ne_zero_of_byte0
    unfold BPB.hdrByte0
    rw [List.append_assoc (bytesLE 16 _ ++ bytesLE 16 _), hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _) (bytesLE_length _ _), bytesLE16_first_toNat,
      WCT9.ftsLeafHeader_firstByte]
    decide
  · intro _; exact SourceQueries.pure_allowed _ _
theorem topHash_ok (coord index heap : Nat) (left pad right : Digest) :
    AllQueriesSatisfy (WCT9.wctTopHash coord index heap left pad right) BPB.NotDigestQ :=
  WCT9.allQ_highHash_of_shortHash _ (BPB.shortHash_ok_marker
    (show T3M.Extract.hdrBlock (pad64 (WCT9.wctTopInput coord index heap left pad right)) =
        SphincsSecurity.bytesLE 16 (nodeTweak 3 (WCT9.nodeLayer coord) index heap) by
      change T3M.Extract.hdrBlock (pad64 (T3M.SecurityInputs.nodeInputP 3 (WCT9.nodeLayer coord) index heap
        left pad right)) = _
      rw [T3M.SecurityInputs.pad64_nodeInputP]; exact BSuf.hdrBlock_nodeInputP _ _ _ _ _ _ _)
    (nodeTweak_marker_ne_zero (by unfold WCT9.nodeLayer; omega) _ _))
theorem forest_header_plain (index : Nat) : header 15 0 index 0 0 = wctHeader 15 0 index 0 0 := by
  unfold wctHeader header
  rw [if_neg (by decide)]
  simp only [Nat.add_assoc]
theorem forestPk_ok (index : Nat) (roots : List (Digest × Digest)) :
    AllQueriesSatisfy (WCT9.forestPk index roots) BPB.NotDigestQ := by
  unfold WCT9.forestPk WCT9.forestInput
  rw [forest_header_plain]
  exact shortHash_wct_ok _ _ 15 _ _ _ _ (by simp [zero16]) (by decide)
theorem hdrBlock_pairEncodingInputP (lay : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (pad : BitVec 96) :
    T3M.Extract.hdrBlock (pad64 (WCT9.pairEncodingInputP lay tree leaf left right counter pad)) =
      SphincsSecurity.bytesLE 16 (rowTweak lay tree leaf) := by
  have hl : (WCT9.pairEncodingInputP lay tree leaf left right counter pad).length = 64 := by
    simp [WCT9.pairEncodingInputP, SphincsSecurity.bytesLE_length]
  rw [T3M.Extract.hdrBlock_pad64 _ (by omega)]
  unfold WCT9.pairEncodingInputP
  rw [List.append_assoc, List.append_assoc]
  exact T3M.Extract.hdrBlock_prefix _ _ _
theorem layerEncoding_ok (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter : BitVec 32) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.encodingHash lay (WCT9.layerEncodingInput lay tree leaf msg counter)) BPB.NotDigestQ := by
  cases msg with
  | forest root => exact BPB.encoding_ok lay tree leaf root counter
  | pair left right =>
      exact BPB.shortHash_ok_marker (hdrBlock_pairEncodingInputP lay tree leaf left right counter 0)
        (by rw [rowTweak_marker]; decide)
theorem buildChildF_ok (index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    AllQueriesSatisfy (buildChildF index coord selected word coefs pad) BPB.NotDigestQ := by
  unfold buildChildF
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state i
    apply SourceQueries.bind_allowed _ (chain_ok _ _ _ _ _ _ _)
    intro value
    apply SourceQueries.bind_allowed _ (chain_ok _ _ _ _ _ _ _)
    intro _
    exact SourceQueries.pure_allowed _ _
  · intro state
    exact SourceQueries.bind_allowed _ (leafHashP_ok _ _ _ _ _) fun _ => SourceQueries.pure_allowed _ _
/-- C1: the FTS leaf of heap `heap` (either hash half) makes the legacy padded leaf's single query. -/
theorem leafHashH_ok (heap index coord selected : Nat) (pad : Digest) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHashH heap index coord selected pad ends) BPB.NotDigestQ := by
  rw [WCT9.leafHashH_eq]
  exact WCT9.allQ_ftsHash_of_shortHash heap _ (leafHashP_ok index coord selected pad ends)
/-- C1: `buildChildF_ok` for the heap-indexed child `buildChildH`. -/
theorem buildChildH_ok (heap index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    AllQueriesSatisfy (WCT9.buildChildH heap index coord selected word coefs pad) BPB.NotDigestQ := by
  unfold WCT9.buildChildH
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state i
    apply SourceQueries.bind_allowed _ (chain_ok _ _ _ _ _ _ _)
    intro value
    apply SourceQueries.bind_allowed _ (chain_ok _ _ _ _ _ _ _)
    intro _
    exact SourceQueries.pure_allowed _ _
  · intro state
    exact SourceQueries.bind_allowed _ (leafHashH_ok _ _ _ _ _ _) fun _ => SourceQueries.pure_allowed _ _
theorem ftsCoefs_ok (index coord : Nat) : AllQueriesSatisfy (WCT9.ftsCoefs index coord) BPB.NotDigestQ := by
  unfold WCT9.ftsCoefs
  apply SourceQueries.foldlM_allowed
  intro acc j
  exact SourceQueries.bind_allowed _ (BPB.privatePair_ok _ _ _ _ _) fun _ => SourceQueries.pure_allowed _ _
theorem buildCoordinateF_ok (index : Nat) (coord : Coord) (selected : Child) (word : Rank) (prev : Digest × Digest) :
    AllQueriesSatisfy (buildCoordinateF index coord selected word prev) BPB.NotDigestQ := by
  unfold buildCoordinateF
  apply SourceQueries.bind_allowed _ (ftsCoefs_ok _ _)
  intro coefs
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state j
    exact SourceQueries.bind_allowed _ (buildChildF_ok _ _ _ _ _ _) fun _ => SourceQueries.pure_allowed _ _
  · intro state
    apply SourceQueries.bind_allowed
    · unfold WCT9.heapBuild
      apply SourceQueries.foldlM_allowed
      intro nodes heap
      refine SourceQueries.bind_allowed _ ?_ fun _ => SourceQueries.pure_allowed _ _
      unfold WCT9.wctHeapNode
      split
      · exact topHash_ok _ _ _ _ _ _
      · exact BPB.nodeHash_ok 3 _ _ _ _ _ (by decide)
    · intro _
      exact SourceQueries.pure_allowed _ _
/-- C2 (FULL): a lower node query of the honest tree shape (heap below `2 ^ height lay`) is no digest query: the
packed node word's marker is `128 + heap`. -/
theorem lowerNodeHash_notDigest (lay : Layer) (tree heap : Nat) (left right : Digest) (hh : heap < 2 ^ height lay) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.lowerNodeHash lay.val tree heap left right)
      SigGolfCandidate.T3.Security.BPB.NotDigestQ := by
  by_cases h0 : lay.val = 0
  · rw [h0, ClaudeWCT.WCT9.lowerNodeHash_top]
    exact SigGolfCandidate.T3.Security.BPB.nodeHash_ok _ _ _ _ _ _ (by decide)
  · have h7 : heap < 128 := lt_of_lt_of_le hh
      ((Nat.pow_le_pow_right (by decide) (ClaudeWCT.W9.T3.Security.Signer.height_le_seven h0)).trans (by norm_num))
    unfold ClaudeWCT.WCT9.lowerNodeHash ClaudeWCT.WCT9.lowerHash
    refine ClaudeWCT.W9.T3.Security.Signer.halfHash_allowed_of_short _ _
      (SigGolfCandidate.T3.Security.BPB.shortHash_ok_marker
        (hdr := ClaudeWCT.WCT9.merkleTweak lay.val tree heap) ?_ ?_)
    · unfold ClaudeWCT.WCT9.merkleNodeInput
      rw [List.append_assoc (SphincsSecurity.bytesLE 16 left ++
          SphincsSecurity.bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree heap)),
        SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp [SphincsSecurity.bytesLE_length, zero16]),
        SigGolfCandidate.T3M.Extract.hdrBlock_prefix]
    · rw [ClaudeWCT.WCT9.merkleTweak_lower h0]
      unfold ClaudeWCT.WCT9.lowerTweak ClaudeWCT.WCT9.lowerNodeWord ClaudeWCT.WCT9.lowerK
      rw [SigGolfCandidate.T3.append64_marker, BitVec.toNat_add, BitVec.toNat_ofNat,
        SigGolfCandidate.T3.hyperWord_toNat]
      omega
open SigGolfCandidate.T3.Security.BPB SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs in
/-- Pairing stage 1: a chain step of the current scheme (either format) is not a digest query. -/
theorem chainStepW_ok_rev3 (lay : SigGolfCandidate.T3.Layer) (tree leaf i step : Nat) (v : SigGolfCandidate.T3.Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.shortHash (ClaudeWCT.WCT9.chainInputW lay tree leaf i step v))
      SigGolfCandidate.T3.Security.BPB.NotDigestQ := by
  unfold SigGolfCandidate.T3.shortHash SigGolfCandidate.T3.publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    change hdrMarker (SigGolfCandidate.T3.pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i step v)) ≠ 0
    rw [ClaudeWCT.WCT9.chainInputW_padded]
    apply hdrMarker_ne_zero_of_byte0
    unfold hdrByte0 Extract.hdrBlock
    rw [ClaudeWCT.WCT9.chainInputW_header, bytesLE16_first_toNat]
    have := SigGolfCandidate.T3.chainHeader_firstByte lay tree leaf i step
    omega
  · intro _; exact SourceQueries.pure_allowed _ _
theorem wct_payNotDigest : PayNotDigest payAfterDigest := by
  intro cache rho output
  unfold payAfterDigest
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state coord
    exact SourceQueries.bind_allowed _ (buildCoordinateF_ok _ _ _ _ _) fun _ => SourceQueries.pure_allowed _ _
  · intro state
    apply SourceQueries.bind_allowed _ (W9.T3.Security.Signer.signLayersBC_allowed' _ _ layerEncoding_ok
      (W9.T3.Security.Signer.buildTreeP_allowed' _ chainStepW_ok_rev3 BPB.leafHash_ok
        (fun lay _ _ _ _ hh => lowerNodeHash_notDigest lay _ _ _ _ hh)
        (fun _ _ _ => BPB.privatePair_ok _ _ _ _ _)) (BPB.signTop_ok _) _ _ _)
    intro layers
    split
    · exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
end ClaudeWCT.Bank.WCT
end
section
namespace ClaudeWCT.Bank.BPORSRegression
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankRegression : DecidableEq T3.Cache := Classical.decEq _
theorem bpors_exists_admissible : ∃ x, digestAdmissible x = true := by
  obtain ⟨x, hx⟩ := CaseC.admissibleSet_nonempty
  exact ⟨x, (Finset.mem_filter.mp hx).2⟩
theorem bpors_acceptance_eq :
    Pr[fun x : HashOutput => digestAdmissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      expectedValue ($ᵗ HashOutput : ProbComp HashOutput) CaseC.admInd := by
  unfold CaseC.admInd
  rw [expectedValue_ite_one]
theorem bpors_one_le_score (X : List HashOutput) (N : HashOutput) (hadm : digestAdmissible N = true)
    (hcov : ∀ c, CaseC.CoordCovered X N c) : 1 ≤ CaseC.score X N := by
  unfold digestAdmissible at hadm
  rw [Bool.and_eq_true] at hadm
  exact CaseC.one_le_score X N (CaseC.outLeaves_injective N hadm.1) hadm.2 hcov
theorem bpors_finiteAverage (g : BPORS.History.Proposal → ENNReal) :
    BPORS.finiteAverage g = ∑ p, (Fintype.card BPORS.History.Proposal : ENNReal)⁻¹ * g p := by
  unfold BPORS.finiteAverage
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _
theorem bpors_law_sum : ∑ _p : BPORS.History.Proposal, (Fintype.card BPORS.History.Proposal : ENNReal)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]
noncomputable def bporsSpec : FtsBankSpec BPORS.History.Proposal where
  admissible := digestAdmissible
  producer := digestAdmissible
  exists_producer := bpors_exists_admissible
  acceptance_le := bpors_acceptance_eq ▸ CaseC.expected_admInd_tight
  proposal := CaseC.label
  law := fun _ => (Fintype.card BPORS.History.Proposal : ENNReal)⁻¹
  law_sum := bpors_law_sum
  accepted_proposal g := by
    rw [Sampling.digest_acceptanceProbability, ← bpors_finiteAverage]
    exact accepted_samplingData g
  score := CaseC.score
  covered X N := ∀ c, CaseC.CoordCovered X N c
  one_le_score := bpors_one_le_score
  score_append_mono := CaseC.score_append_mono
  price := BPORS.History.fullPrice
  average_score := CaseC.average_score
  horizon := BPORS.Numeric.proposalLength
  excessRate := 11324 / 100000000
  excess_le := (ClaudeWCT.Numerics.Law.lawAvg_uniform _ _).le.trans CaseC.excess_three_quarters
theorem bpors_decode : bporsSpec.decode = Sampling.digestDecode := rfl
theorem bpors_acceptance : bporsSpec.acceptance = acceptanceProbability := Sampling.digest_acceptanceProbability
theorem bpors_freshPrice (w : HashOutput → ENNReal) :
    bporsSpec.freshPrice w = Sampling.WeightedSelection.freshPrice w := by
  unfold FtsBankSpec.freshPrice Sampling.WeightedSelection.freshPrice
  rw [bpors_acceptance]
  rfl
theorem bpors_search (rho : Digest) (m : Message) (counter fuel : Nat) :
    bporsSpec.search rho m counter fuel = digestSearch rho m counter fuel :=
  (Sampling.digestSearch_public rho m fuel counter).symm
theorem bpors_admissibleSet : bporsSpec.admissibleSet = CaseC.admissibleSet := by
  ext x
  simp [FtsBankSpec.admissibleSet, CaseC.admissibleSet, bporsSpec]
theorem bpors_accepted : bporsSpec.accepted = CaseC.accepted := by
  unfold FtsBankSpec.accepted CaseC.accepted
  congr 1
theorem bpors_forecast : bporsSpec.forecast = CaseC.forecast := by
  funext R X N
  unfold FtsBankSpec.forecast CaseC.forecast
  rw [bpors_accepted]
  rfl
theorem bpors_excessForecast : bporsSpec.excessForecast = CaseC.excessForecast := by
  funext R X
  unfold FtsBankSpec.excessForecast CaseC.excessForecast
  exact ClaudeWCT.Numerics.Law.lawAvg_uniform _ _
theorem bpors_ledger : bporsSpec.ledger = CaseC.ledger := by
  funext R targets X slack
  unfold FtsBankSpec.ledger CaseC.ledger
  rw [bpors_forecast, bpors_excessForecast]
theorem bpors_corePotential : bporsSpec.corePotential = CaseC.corePotential := by
  funext b
  unfold FtsBankSpec.corePotential CaseC.corePotential
  rw [bpors_ledger]
  rfl
theorem bpors_Reuse : bporsSpec.Reuse = CaseC.Reuse := rfl
theorem bpors_admissibleEntry : bporsSpec.admissibleEntry = CaseC.admissibleEntry := by
  funext cache input
  unfold FtsBankSpec.admissibleEntry CaseC.admissibleEntry
  cases cache input <;> simp [bporsSpec]
theorem bpors_reuseMass : bporsSpec.reuseMass = CaseC.reuseMass := by
  funext cache m
  unfold FtsBankSpec.reuseMass CaseC.reuseMass
  rw [bpors_admissibleEntry]
theorem bpors_admInd : bporsSpec.admInd = CaseC.admInd := by
  funext a
  simp [FtsBankSpec.admInd, CaseC.admInd, bporsSpec]
theorem bpors_recordForNonce (cache : T3.Cache) (rho : Digest) (m : Message) :
    bporsSpec.recordForNonce payloadAfterDigest cache rho m = payloadRecordForNonce cache rho m := by
  unfold FtsBankSpec.recordForNonce payloadRecordForNonce
  rw [bpors_search]
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩ <;> rfl
theorem bpors_record (published : T3.Cache) (request : Request) :
    bporsSpec.authenticatedRecord payloadAfterDigest published request =
      FullGame.authenticatedRecord published request := by
  unfold FtsBankSpec.authenticatedRecord FullGame.authenticatedRecord
  apply bind_congr
  intro tag
  by_cases h : request.cache = published
  · simp only [h, if_true]
    unfold FtsBankSpec.payloadRecord payloadRecord
    apply bind_congr
    intro rho
    exact bpors_recordForNonce _ rho _
  · simp only [h, if_false]
theorem t3_core_sign (b : CaseC.BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + CaseC.reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat) (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if CaseC.Reuse cache rho m then CaseC.corePotential { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (digestSearch rho m 0 fuel) cache)
        (fun result => CaseC.corePotential (b.expose C' (result.1.map Prod.snd)))) ≤ CaseC.corePotential b := by
  have h := bporsSpec.core_sign b cache m C' (by rw [bpors_reuseMass]; exact hC) secret fuel hfuel
  simp only [bpors_corePotential, bpors_Reuse, bpors_search] at h
  exact h
theorem t3_core_birth (b : CaseC.BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + CaseC.admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => CaseC.corePotential { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      CaseC.corePotential b + (CaseC.theta + 1 / 64) / 2 ^ 128 := by
  have h := bporsSpec.core_birth b s hs C' (by rw [bpors_admInd]; exact hC)
  simp only [bpors_corePotential] at h
  exact h
theorem t3_core_initial (budget : Nat) :
    CaseC.corePotential ⟨[], [], false, 0, budget⟩ ≤ (budget : ENNReal) * (11324 / 100000000) / 2 ^ 128 := by
  have h := bporsSpec.core_initial budget
  rw [bpors_corePotential] at h
  exact h
theorem t3_core_win (b : CaseC.BankCore) (halive : ¬BPORS.Numeric.proposalLength < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, admissible (selections N) = true ∧ digestGate N = true ∧
      CaseC.CoveredBy b.exposures N) :
    1 ≤ CaseC.corePotential b := by
  rw [← bpors_corePotential]
  apply bporsSpec.core_win b halive
  rcases h with h | ⟨N, hN, hadm, hgate, hcov⟩
  · exact Or.inl h
  · refine Or.inr ⟨N, hN, ?_, ?_⟩
    · change digestAdmissible N = true
      unfold digestAdmissible
      rw [Bool.and_eq_true]
      exact ⟨hadm, hgate⟩
    · exact fun c => CaseC.coordCovered_of_opened b.exposures N c fun j => hcov _ (CaseC.opened_mem N c j)
theorem t3_fresh_signing_kernel (published : T3.Cache) (m : Message) (state : LazyPrivate.State)
    (hfresh : state.1 (.inr (.inl m)) = none)
    (F : (Option Signature × Option HashOutput) × LazyPrivate.State → ENNReal)
    (w : HashOutput → ENNReal) (P : ENNReal) (hP : Sampling.WeightedSelection.freshPrice w ≤ P)
    (hF : ∀ result ∈ support (LazyPrivate.run (FullGame.authenticatedRecord published ⟨m, published⟩) state),
      F result ≤ if CaseC.Reuse state.2 (CaseC.nonceOf result.2 m) m then 1 else result.1.2.elim P w) :
    expectedValue (LazyPrivate.run (FullGame.authenticatedRecord published ⟨m, published⟩) state) F ≤
      P + CaseC.reuseMass state.2 m := by
  have h := bporsSpec.fresh_signing_kernel payloadAfterDigest published m state hfresh F w P
    (by rw [bpors_freshPrice]; exact hP) (by rw [bpors_record]; exact hF)
  rw [bpors_record, bpors_reuseMass] at h
  exact h
theorem bpors_payNotDigest : PayNotDigest payloadAfterDigest := BPB.payloadAfterDigest_ok
theorem bpors_source (published : T3.Cache) :
    bporsSpec.source payloadAfterDigest published = MonitoredPrivate.interactionSource published := by
  funext input
  cases input with
  | inl input => rfl
  | inr request =>
      change Prod.fst <$> bporsSpec.authenticatedRecord payloadAfterDigest published request =
        FullGame.authenticatedSign published request
      rw [bpors_record, FullGame.authenticatedRecord_erasure]
end ClaudeWCT.Bank.BPORSRegression
namespace ClaudeWCT.Bank.BPORSRegression
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankRegression2 : DecidableEq T3.Cache := Classical.decEq _
theorem bpors_payAvoids : PayAvoids payloadAfterDigest := by
  intro m cache rho output
  unfold payloadAfterDigest
  aesop (config := { maxRuleApplications := 1000 })
    (add safe apply [(NonceFreshness.avoids_pure m), (NonceFreshness.avoids_bind m), (NonceFreshness.avoids_map m),
      (NonceFreshness.avoids_foldlM m), (NonceFreshness.avoids_mapM m), (NonceFreshness.avoids_buildFts m),
      (NonceFreshness.avoids_forestPk m), (NonceFreshness.avoids_signLayers m)])
theorem bpors_recordedExperiment (adversary : SigGolfCandidate.T3M.Final.AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    (fun r : PaddedGame.TraceResult => (r.1, r.2.2)) <$> PaddedGame.tracedExperiment adversary budget hbudget =
      bporsSpec.recordedExperiment payloadAfterDigest (CreationGame.rest adversary) := by
  rw [CreationGame.padded_trace_eq, FtsBankSpec.recordedExperiment, map_bind]
  apply bind_congr
  intro generated
  have ht := (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced_erasure
    (CreationGame.rest adversary generated.1.1 generated.1.2) ([], generated.2)
  rw [QueryRecorded.proposal_execution_erasure] at ht
  rw [bpors_source]
  exact ht
theorem bpors_birthWeight (budget : Nat) (input : LazyPrivate.Interaction.Domain)
    (state : MonitoredPrivate.History × QueryRecorded.State) :
    birthWeight (Sig := Signature) budget input state.2 =
      (CreationGame.classWeight CaseC.IsDigestInput budget input state : ENNReal) := by
  rcases input with (n | x) | request
  · simp [birthWeight, CreationGame.classWeight]
  · simp only [birthWeight, CreationGame.classWeight]
    by_cases h : CaseC.Birth budget x state.2
    · have h' : state.2.base.source.1 < budget ∧ CaseC.IsDigestInput x ∧ state.2.base.source.2.2 x = none :=
        ⟨h.2.2, h.1, h.2.1⟩
      rw [if_pos h, if_pos h', Nat.cast_one]
    · have h' : ¬(state.2.base.source.1 < budget ∧ CaseC.IsDigestInput x ∧ state.2.base.source.2.2 x = none) :=
        fun h' => h ⟨h'.2.1, h'.2.2, h'.1⟩
      rw [if_neg h, if_neg h', Nat.cast_zero]
  · simp [birthWeight, CreationGame.classWeight]
theorem bpors_expectedBirths (adversary : SigGolfCandidate.T3M.Final.AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    bporsSpec.expectedBirths payloadAfterDigest (CreationGame.rest adversary) budget =
      CreationGame.expectedBirths CaseC.IsDigestInput adversary budget hbudget := by
  unfold FtsBankSpec.expectedBirths CreationGame.expectedBirths
  congr 1
  funext generated
  have ht := BPORS.Adaptive.Creation.expectedCharges_project
    (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced
    (bporsSpec.recordedImpl payloadAfterDigest generated.1.2) Prod.snd
    (fun input st => by
      rw [(QueryRecorded.proposalModel generated.1.2 budget hbudget).traced_query_erasure,
        QueryRecorded.proposal_query_erasure, ← bpors_source]
      rfl)
    (birthWeight budget) (CreationGame.rest adversary generated.1.1 generated.1.2) ([], generated.2)
  rw [← ht]
  congr 1
  funext input state
  exact bpors_birthWeight budget input state
theorem t3_bank_potential_le (adversary : SigGolfCandidate.T3M.Final.AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    expectedValue (bporsSpec.bankExperiment payloadAfterDigest (CreationGame.rest adversary) budget)
        (fun r => bporsSpec.potential budget r.2) ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * CreationGame.expectedBirths CaseC.IsDigestInput adversary budget hbudget +
        (budget : ENNReal) * (11324 / 100000000) / 2 ^ 128 := by
  rw [← bpors_expectedBirths adversary budget hbudget]
  exact bporsSpec.bank_potential_le payloadAfterDigest bpors_payNotDigest bpors_payAvoids
    (CreationGame.rest adversary) budget
end ClaudeWCT.Bank.BPORSRegression
end
section
namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_wctBank : DecidableEq T3.Cache := Classical.decEq _
variable (horizon : Nat) (rate : ENNReal)
  (hexc : ExcessBound horizon rate)
noncomputable def authenticatedSign (published : T3.Cache) (request : Request) : M (Option WCT9.Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache = published then WCT9.signPayload request.cache request.message else pure none
theorem wct_record_erasure (published : T3.Cache) (request : Request) :
    Prod.fst <$> (wctSpec' horizon rate hexc).authenticatedRecord payAfterDigest published request =
      authenticatedSign published request := by
  unfold FtsBankSpec.authenticatedRecord authenticatedSign
  rw [map_bind]
  apply bind_congr
  intro tag
  split_ifs
  · exact payloadRecord_erasure _ rfl _ _
  · rfl
theorem wct_source_sign (published : T3.Cache) (request : Request) :
    (wctSpec' horizon rate hexc).source payAfterDigest published (.inr request) =
      authenticatedSign published request :=
  wct_record_erasure horizon rate hexc published request
noncomputable def interactionSource (published : T3.Cache) : QueryImpl (Interaction' WCT9.Signature) M
  | .inl input => forwardWorld input
  | .inr request => authenticatedSign published request
theorem wct_source (published : T3.Cache) :
    (wctSpec' horizon rate hexc).source payAfterDigest published = interactionSource published := by
  funext input
  cases input with
  | inl input => rfl
  | inr request => exact wct_source_sign horizon rate hexc published request
theorem wct_recordedExperiment (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool) :
    (wctSpec' horizon rate hexc).recordedExperiment payAfterDigest rest = (do
      let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
      (liftM (QueryRecorded.run (simulateQ (interactionSource generated.1.2) (rest generated.1.1 generated.1.2))
        generated.2) : PMF _)) := by
  unfold FtsBankSpec.recordedExperiment
  simp only [wct_source]
theorem wct_bank_potential_le (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool)
    (budget : Nat) :
    expectedValue ((wctSpec' horizon rate hexc).bankExperiment payAfterDigest rest budget)
        (fun r => (wctSpec' horizon rate hexc).potential budget r.2) ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * (wctSpec' horizon rate hexc).expectedBirths payAfterDigest rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpec' horizon rate hexc).bank_potential_le payAfterDigest wct_payNotDigest wct_payAvoids rest budget
theorem wct_potential_win (budget : Nat) (st : BankState WCT9.Signature) (halive : st.1.dead = false)
    (hcount : CaseC.countOf st.2 ≤ budget)
    (h : st.1.reused = true ∨ ∃ N ∈ st.1.targets, WCT9.admissible N = true ∧ Covered st.1.exposures N) :
    1 ≤ (wctSpec' horizon rate hexc).potential budget st :=
  (wctSpec' horizon rate hexc).potential_win budget st halive hcount h
theorem wct_event_le (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool) (budget : Nat)
    (weight : Bool × QueryRecorded.State → ENNReal) (hw : ∀ y, weight y ≤ 1)
    (hwin : ∀ b ∈ ((wctSpec' horizon rate hexc).bankExperiment payAfterDigest rest budget).support,
      weight (b.1, b.2.2) ≠ 0 → 1 ≤ (wctSpec' horizon rate hexc).potential budget b.2) :
    expectedValue ((wctSpec' horizon rate hexc).recordedExperiment payAfterDigest rest) weight ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * (wctSpec' horizon rate hexc).expectedBirths payAfterDigest rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpec' horizon rate hexc).bank_event_le payAfterDigest wct_payNotDigest wct_payAvoids rest budget
    weight hw hwin
end ClaudeWCT.Bank.WCT
end
section
namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.WCT9 (Coord Child Rank child rank Opening buildChildF buildCoordinateF)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section allowed
variable (Q : T3.Spec.Domain → Prop) (hpublic : ∀ input, Q (.inl (.inr input)))
  (hpair : ∀ tweak, Q (.inr (.inl tweak))) (hnonce : ∀ message, Q (.inr (.inr (.inl message))))
include hpublic in
theorem chain_allowed (index coord selected i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (WCT9.chain index coord selected i start count value) Q := by
  unfold WCT9.chain
  exact SourceQueries.foldlM_allowed Q _ _ (fun _ _ => SourceQueries.projHash_allowed Q hpublic _ _) _
include hpublic in
theorem buildChildF_allowed (index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    AllQueriesSatisfy (buildChildF index coord selected word coefs pad) Q :=
  W9.T3.Security.Signer.buildChildF_allowed Q hpublic index coord selected word coefs pad
include hpublic hpair in
theorem buildCoordinateF_allowed (index : Nat) (coord : Coord) (selected : Child) (word : Rank)
    (prev : Digest × Digest) :
    AllQueriesSatisfy (buildCoordinateF index coord selected word prev) Q :=
  W9.T3.Security.Signer.buildCoordinateF_allowed Q hpublic (fun _ _ _ _ => hpair _) index coord selected word prev
include hpublic hpair hnonce in
theorem payAfterDigest_allowed (cache : T3.Cache) (rho : Digest) (output : HashOutput) :
    AllQueriesSatisfy (payAfterDigest cache rho output) Q := by
  unfold payAfterDigest
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state coord
    exact SourceQueries.bind_allowed _ (buildCoordinateF_allowed Q hpublic hpair _ _ _ _ _)
      fun _ => SourceQueries.pure_allowed _ _
  · intro state
    apply SourceQueries.bind_allowed _ (W9.T3.Security.Signer.signLayersBC_allowed Q hpublic _
      (W9.T3.Security.Signer.buildTreeP_allowed Q hpublic (fun _ _ _ => hpair _))
      (SourceQueries.signTop_allowed Q hpublic hpair hnonce _) _ _ _)
    intro layers
    split
    · exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
end allowed
theorem wct_payHashOnly : PayHashOnly payAfterDigest :=
  payAfterDigest_allowed _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
theorem wct_payRho : PayRho payAfterDigest WCT9.Signature.rho := by
  intro A cache rho output σ h
  unfold payAfterDigest at h
  simp only [evalWithAnswerFn_bind] at h
  split at h
  all_goals (rw [evalWithAnswerFn_pure] at h; cases h)
  all_goals rfl
variable (horizon : Nat) (rate : ENNReal)
  (hexc : ExcessBound horizon rate)
theorem wct_bankInv_experiment (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool)
    (budget : Nat) (b : Bool × BankState WCT9.Signature)
    (hb : b ∈ ((wctSpec' horizon rate hexc).bankExperiment payAfterDigest rest budget).support) :
    ∃ generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial),
      (wctSpec' horizon rate hexc).BankInv payAfterDigest WCT9.Signature.rho generated.1.2 budget
        generated.2.events b.2 :=
  (wctSpec' horizon rate hexc).bankInv_experiment payAfterDigest WCT9.Signature.rho wct_payHashOnly
    wct_payRho wct_payAvoids rest budget b hb
end ClaudeWCT.Bank.WCT
namespace ClaudeWCT.Bank.BPORSRegression
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem bpors_payHashOnly : PayHashOnly payloadAfterDigest := by
  intro cache rho output
  unfold payloadAfterDigest
  aesop (config := { maxRuleApplications := 1000 })
    (add safe apply [(SourceQueries.pure_allowed Security.SourceReplay.IsHash),
      (SourceQueries.bind_allowed Security.SourceReplay.IsHash),
      (SourceQueries.foldlM_allowed Security.SourceReplay.IsHash),
      (SourceQueries.map_allowed Security.SourceReplay.IsHash),
      (SourceQueries.buildFts_allowed Security.SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial)),
      (SourceQueries.forestPk_allowed Security.SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial)),
      (SourceQueries.signLayers_allowed Security.SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial))])
theorem bpors_payRho : PayRho payloadAfterDigest Signature.rho :=
  CaseC.eval_payloadAfterDigest_rho
end ClaudeWCT.Bank.BPORSRegression
end
section
namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete (uniformWordAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_wctRev3 : DecidableEq T3.Cache := Classical.decEq _
theorem signPayloadWith_factor (limit : Nat) (cache : T3.Cache) (message : Message) :
    WCT9.signPayloadWith limit cache message = (do
      let rho ← privateNonce message
      let found ← WCT9.digestSearch rho message 0 limit
      match found with
      | none => pure none
      | some (_, output) => payAfterDigest cache rho output) := by
  unfold WCT9.signPayloadWith
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩ <;> rfl
theorem rev3_signPayload_factor (cache : T3.Cache) (message : Message) :
    WCT9.Rev3.signPayload cache message = (do
      let rho ← privateNonce message
      let found ← WCT9.digestSearch rho message 0 WCT9.digestAttemptLimit
      match found with
      | none => pure none
      | some (_, output) => payAfterDigest cache rho output) :=
  signPayloadWith_factor WCT9.digestAttemptLimit cache message
theorem payloadRecordL_erasure {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P)
    (hadm : S.producer = WCT9.producerAdmissible) (cache : T3.Cache) (message : Message) :
    Prod.fst <$> S.payloadRecord payAfterDigest cache message = WCT9.signPayloadWith S.limit cache message := by
  rw [signPayloadWith_factor]
  unfold FtsBankSpecL.payloadRecord FtsBankSpecL.recordForNonce
  simp only [map_bind]
  apply bind_congr
  intro rho
  rw [wct_digestSearch_public S.toFtsBankSpec hadm]
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩
  · simp
  · simp only [map_bind, map_pure]
    exact bind_pure _
noncomputable def wctSpecL (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate) :
    FtsBankSpecL WProposal :=
  (wctSpec' horizon rate hexc).atLimit WCT9.digestAttemptLimit WCT9.digestAttemptLimit_le
variable (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate)
@[simp] theorem wctSpecL_limit : (wctSpecL horizon rate hexc).limit = WCT9.digestAttemptLimit := rfl
theorem wctSpecL_admissible : (wctSpecL horizon rate hexc).admissible = WCT9.admissible := rfl
theorem wctSpecL_producer : (wctSpecL horizon rate hexc).producer = WCT9.producerAdmissible := rfl
theorem wctSpecL_law : (wctSpecL horizon rate hexc).law = honestLaw := rfl
@[simp] theorem wctSpecL_horizon : (wctSpecL horizon rate hexc).horizon = horizon := rfl
noncomputable def rev3AuthenticatedSign (published : T3.Cache) (request : Request) : M (Option WCT9.Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache = published then WCT9.Rev3.signPayload request.cache request.message else pure none
theorem wctL_record_erasure (published : T3.Cache) (request : Request) :
    Prod.fst <$> (wctSpecL horizon rate hexc).authenticatedRecord payAfterDigest published request =
      rev3AuthenticatedSign published request := by
  unfold FtsBankSpecL.authenticatedRecord rev3AuthenticatedSign
  rw [map_bind]
  apply bind_congr
  intro tag
  split_ifs
  · exact payloadRecordL_erasure _ rfl _ _
  · rfl
theorem excess_of_excessBound (h : ExcessBound horizon rate) :
    ClaudeWCT.Numerics.Law.lawAvg (wctSpecL horizon rate hexc).law (wctSpecL horizon rate hexc).horizon
      (fun W : List WProposal => (wctSpecL horizon rate hexc).price W - 1023 / 1024) ≤ rate := h
theorem wctL_bank_potential_le (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool)
    (budget : Nat) :
    expectedValue ((wctSpecL horizon rate hexc).bankExperiment payAfterDigest rest budget)
        (fun r => (wctSpecL horizon rate hexc).potential budget r.2) ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * (wctSpecL horizon rate hexc).expectedBirths payAfterDigest rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpecL horizon rate hexc).bank_potential_le payAfterDigest wct_payNotDigest wct_payAvoids rest budget
theorem wctL_potential_win (budget : Nat) (st : BankState WCT9.Signature) (halive : st.1.dead = false)
    (hcount : CaseC.countOf st.2 ≤ budget)
    (h : st.1.reused = true ∨ ∃ N ∈ st.1.targets, WCT9.admissible N = true ∧ Covered st.1.exposures N) :
    1 ≤ (wctSpecL horizon rate hexc).potential budget st :=
  (wctSpecL horizon rate hexc).potential_win budget st halive hcount h
theorem wctL_event_le (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool) (budget : Nat)
    (weight : Bool × QueryRecorded.State → ENNReal) (hw : ∀ y, weight y ≤ 1)
    (hwin : ∀ b ∈ ((wctSpecL horizon rate hexc).bankExperiment payAfterDigest rest budget).support,
      weight (b.1, b.2.2) ≠ 0 → 1 ≤ (wctSpecL horizon rate hexc).potential budget b.2) :
    expectedValue ((wctSpecL horizon rate hexc).recordedExperiment payAfterDigest rest) weight ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * (wctSpecL horizon rate hexc).expectedBirths payAfterDigest rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpecL horizon rate hexc).bank_event_le payAfterDigest wct_payNotDigest wct_payAvoids rest budget
    weight hw hwin
theorem wctL_bankInv_experiment (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool)
    (budget : Nat) (b : Bool × BankState WCT9.Signature)
    (hb : b ∈ ((wctSpecL horizon rate hexc).bankExperiment payAfterDigest rest budget).support) :
    ∃ generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial),
      (wctSpecL horizon rate hexc).BankInv payAfterDigest WCT9.Signature.rho generated.1.2 budget
        generated.2.events b.2 :=
  (wctSpecL horizon rate hexc).bankInv_experiment payAfterDigest WCT9.Signature.rho wct_payHashOnly
    wct_payRho wct_payAvoids rest budget b hb
theorem wctL_search (rho : Digest) (m : Message) :
    (wctSpecL horizon rate hexc).search rho m 0 (wctSpecL horizon rate hexc).limit =
      WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit :=
  (wct_digestSearch_public (wctSpecL horizon rate hexc).toFtsBankSpec rfl rho m _ 0).symm
end ClaudeWCT.Bank.WCT
end

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

noncomputable def bankSpec : FtsBankSpecL Proposal :=
  lawSpec.atLimit ClaudeWCT.WCT9.digestAttemptLimit (by decide +kernel)

theorem digestSearch_public (rho : Digest) (message : Message) :
    ∀ fuel counter, SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho message counter fuel =
      lawSpec.search rho message counter fuel := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      rw [SigGolfCandidate.Research.SharedForest.sharedDigestSearch, FtsBankSpec.search, searchLoop]
      simp only [Sampling.publicProgram, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.Concrete.oracleHash, HasQuery.query, Sampling.publicHandler,
        digest, publicHash, Sampling.digestTrial, FtsBankSpec.decode,
        show lawSpec.producer = producer from rfl, producer_source]
      apply bind_congr
      intro answer
      split <;> simp only [simulateQ_pure, map_pure, ih, FtsBankSpec.search, Sampling.publicProgram]

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def payAfterDigest (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (output : HashOutput) :
    M (Option SharedForest.Signature) :=
  Option.map SharedForest.Witness.signature <$> SharedForest.signFromOutput cache rho 0 output

theorem signature_counter (cache : SigGolfCandidate.T3.Cache) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) :
    Option.map SharedForest.Witness.signature <$> SharedForest.signFromOutput cache rho counter output =
      payAfterDigest cache rho output := by
  unfold payAfterDigest SharedForest.signFromOutput
  simp only [map_bind]
  apply bind_congr
  intro forest
  apply bind_congr
  intro prepared
  apply bind_congr
  intro layers
  cases layers <;> rfl

theorem signPayload_factor (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    SharedForest.signPayload cache message = (do
      let rho ← privateNonce message
      let found ← SharedForest.sharedDigestSearch rho message 0 ClaudeWCT.WCT9.digestAttemptLimit
      match found with
      | none => pure none
      | some (_,output) => payAfterDigest cache rho output) := by
  unfold SharedForest.signPayload
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  cases found with
  | none => rfl
  | some found =>
      rcases found with ⟨counter,output⟩
      dsimp only
      rw [← signature_counter cache rho counter output]
      simp only [map_eq_bind_pure_comp]
      apply bind_congr
      intro witness
      cases witness <;> rfl

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

structure ForestAllowed (Q : SigGolfCandidate.T3.Spec.Domain → Prop) : Prop where
  coefs : ∀ index coord, AllQueriesSatisfy (ftsCoefs index coord) Q
  child : ∀ heap index coord selected word coefs pad,
    AllQueriesSatisfy (ClaudeWCT.WCT9.buildChildH heap index coord selected word coefs pad) Q
  node : ∀ first coord index heap pads left right,
    AllQueriesSatisfy (sharedNode first coord index heap pads left right) Q

section
variable (Q : SigGolfCandidate.T3.Spec.Domain → Prop) (hQ : ForestAllowed Q)
include hQ

theorem sharedHeap_allowed (first : Bool) (index coord : Nat) (pads : Nat → PairRoot)
    (leaves : List Digest) : AllQueriesSatisfy (sharedHeap first index coord pads leaves) Q := by
  unfold sharedHeap
  exact SourceQueries.foldlM_allowed Q _ _ (fun _ _ =>
    SourceQueries.bind_allowed Q (hQ.node ..) fun _ => SourceQueries.pure_allowed Q _) _

theorem sharedCoordinate_allowed (first : Bool) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    AllQueriesSatisfy (buildSharedCoordinate first index coord selected word pads) Q := by
  unfold buildSharedCoordinate
  exact SourceQueries.bind_allowed Q (hQ.coefs ..) fun _ =>
    SourceQueries.bind_allowed Q (SourceQueries.foldlM_allowed Q _ _
      (fun _ _ => SourceQueries.bind_allowed Q (hQ.child ..) fun _ => SourceQueries.pure_allowed Q _) _) fun _ =>
      SourceQueries.bind_allowed Q (sharedHeap_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _

theorem pair_allowed (index pair : Nat) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (prev : PairRoot) : AllQueriesSatisfy (buildPair index pair s aWord bWord prev) Q := by
  unfold buildPair
  exact SourceQueries.bind_allowed Q (sharedCoordinate_allowed Q hQ ..) fun _ =>
    SourceQueries.bind_allowed Q (sharedCoordinate_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _

theorem singleton_allowed (index : Nat) (selected : Child) (word : Rank) (prev : PairRoot) :
    AllQueriesSatisfy (buildSingleton index selected word prev) Q := by
  unfold buildSingleton
  exact SourceQueries.bind_allowed Q (sharedCoordinate_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _

theorem forest_allowed (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    AllQueriesSatisfy (buildForest index selected words) Q := by
  unfold buildForest
  exact SourceQueries.bind_allowed Q (SourceQueries.foldlM_allowed Q _ _
    (fun _ _ => SourceQueries.bind_allowed Q (pair_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _) _) fun _ =>
    SourceQueries.bind_allowed Q (singleton_allowed Q hQ ..) fun _ => SourceQueries.pure_allowed Q _
end

section
variable (Q : SigGolfCandidate.T3.Spec.Domain → Prop)
  (hpublic : ∀ input, Q (.inl (.inr input)))
  (hpair : ∀ tweak, Q (.inr (.inl tweak)))
  (htop : ∀ cache leaf digits, AllQueriesSatisfy (signTop cache leaf digits) Q)

include hpublic hpair htop in
theorem tail_public : SharedQueries.TailAllowed Q where
  chainStep := fun _ _ _ _ _ _ => SourceQueries.shortHash_allowed Q hpublic _
  chainStepW := fun _ _ _ _ _ _ => SourceQueries.shortHash_allowed Q hpublic _
  leaf := fun _ _ _ _ => SourceQueries.shortHash_allowed Q hpublic _
  node := fun _ _ _ _ _ _ => W9.T3.Security.Signer.lowerNodeHash_allowed_of_public Q hpublic _ _ _ _ _
  seed := fun _ _ _ => SourceQueries.privatePair_allowed Q hpair _ _ _ _ _
  encoding := fun lay _ _ msg _ => by
    cases msg <;> exact SourceQueries.shortHash_allowed Q hpublic _
  top := htop

include hpublic hpair in
theorem forest_public : ForestAllowed Q where
  coefs := fun _ _ => W9.T3.Security.Signer.ftsCoefs_allowed Q (fun _ _ _ _ => hpair _) _ _
  child := W9.T3.Security.Signer.buildChildH_allowed Q hpublic
  node := W9.T3.Security.Signer.sharedNode_allowed Q hpublic
end

theorem pay_allowed (Q : SigGolfCandidate.T3.Spec.Domain → Prop)
    (htail : SharedQueries.TailAllowed Q) (hforest : ForestAllowed Q)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (output : HashOutput) :
    AllQueriesSatisfy (payAfterDigest cache rho output) Q :=
  SourceQueries.map_allowed Q _ (SharedQueries.signFromOutput_allowed Q htail
    (forest_allowed Q hforest) cache rho 0 output)

theorem payHashOnly : PayHashOnly payAfterDigest :=
  pay_allowed _ (tail_public _ (fun _ => trivial) (fun _ => trivial)
    (SourceQueries.signTop_allowed _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)))
    (forest_public _ (fun _ => trivial) (fun _ => trivial))

theorem payAvoids : PayAvoids payAfterDigest := by
  intro message
  apply pay_allowed
  · exact tail_public _ (fun _ => by simp [NonceFreshness.nonceQuery])
      (fun _ => by simp [NonceFreshness.nonceQuery]) (NonceFreshness.avoids_signTop message)
  · exact forest_public _ (fun _ => by simp [NonceFreshness.nonceQuery])
      (fun _ => by simp [NonceFreshness.nonceQuery])

theorem tail_notDigest : SharedQueries.TailAllowed BPB.NotDigestQ where
  chainStep := fun lay tree leaf i step value => by
    unfold shortHash publicHash
    apply SourceQueries.bind_allowed
    · apply (allQueriesSatisfy_query_iff _ _).mpr
      change BPB.hdrMarker (pad64 (SigGolfCandidate.T3.chainInput lay tree leaf i step value)) ≠ 0
      rw [chainInput_padded]
      apply BPB.hdrMarker_ne_zero_of_byte0
      unfold BPB.hdrByte0 SigGolfCandidate.T3M.Extract.hdrBlock
      rw [chainInput_header, bytesLE16_first_toNat]
      have := chainHeader_firstByte lay tree leaf i step
      omega
    · intro _; exact SourceQueries.pure_allowed _ _
  chainStepW := ClaudeWCT.Bank.WCT.chainStepW_ok_rev3
  leaf := BPB.leafHash_ok
  node := fun lay _ _ _ _ hh => ClaudeWCT.Bank.WCT.lowerNodeHash_notDigest lay _ _ _ _ hh
  seed := fun _ _ _ => BPB.privatePair_ok _ _ _ _ _
  encoding := WCT.layerEncoding_ok
  top := BPB.signTop_ok

theorem topInput_notDigest (coord index heap : Nat) (left pad right : Digest) :
    AllQueriesSatisfy (shortHash (wctTopInput coord index heap left pad right)) BPB.NotDigestQ :=
  BPB.shortHash_ok_marker
    (show SigGolfCandidate.T3M.Extract.hdrBlock (pad64 (wctTopInput coord index heap left pad right)) =
      SphincsSecurity.bytesLE 16 (nodeTweak 3 (nodeLayer coord) index heap) by
      change SigGolfCandidate.T3M.Extract.hdrBlock
        (pad64 (SigGolfCandidate.T3M.SecurityInputs.nodeInputP 3 (nodeLayer coord) index heap left pad right)) = _
      rw [SigGolfCandidate.T3M.SecurityInputs.pad64_nodeInputP]
      exact BSuf.hdrBlock_nodeInputP _ _ _ _ _ _ _)
    (nodeTweak_marker_ne_zero (by simp [nodeLayer]) _ _)

theorem forest_notDigest : ForestAllowed BPB.NotDigestQ where
  coefs := WCT.ftsCoefs_ok
  child := WCT.buildChildH_ok
  node := fun first coord index heap pads left right => by
    unfold sharedNode sharedOuterHash
    split
    · split
      · exact topInput_notDigest ..
      · exact allQ_highHash_of_shortHash _ (topInput_notDigest ..)
    · split
      · split
        · exact allQ_highHash_of_shortHash _ (topInput_notDigest ..)
        · exact topInput_notDigest ..
      · exact ClaudeWCT.WCT9.allQ_ftsHash_of_shortHash heap (ClaudeWCT.WCT9.nodeInput coord index heap left right)
          (BPB.nodeHash_ok 3 (ClaudeWCT.WCT9.nodeLayer coord) index heap left right (by decide))

theorem payNotDigest : PayNotDigest payAfterDigest :=
  pay_allowed _ tail_notDigest forest_notDigest

theorem payRho : PayRho payAfterDigest SigGolfCandidate.Research.SharedForest.Signature.rho := by
  intro A cache rho output sig h
  unfold payAfterDigest signFromOutput at h
  simp only [SigGolfCandidate.T3M.eval_map, evalWithAnswerFn_bind] at h
  split at h
  all_goals (rw [evalWithAnswerFn_pure] at h; cases h)
  all_goals rfl

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.FtsBankSpecL
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 200000
set_option maxRecDepth 10000

theorem payloadRecord_factor {P Sig : Type} [Fintype P] [SampleableType P]
    (S : FtsBankSpecL P) (pay : SigGolfCandidate.T3.Cache → Digest → HashOutput → M (Option Sig))
    (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    Prod.fst <$> S.payloadRecord pay cache message = (do
      let rho ← privateNonce message
      let found ← S.search rho message 0 S.limit
      match found with
      | none => pure none
      | some (_,output) => pay cache rho output) := by
  unfold FtsBankSpecL.payloadRecord FtsBankSpecL.recordForNonce
  simp only [map_bind]
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩
  · simp
  · simp only [map_bind,map_pure]
    exact bind_pure _

end ClaudeWCT.Bank.FtsBankSpecL

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem payloadRecord_erasure (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    Prod.fst <$> bankSpec.payloadRecord payAfterDigest cache message =
      SharedForest.signPayload cache message := by
  rw [FtsBankSpecL.payloadRecord_factor, signPayload_factor]
  apply bind_congr
  intro rho
  rw [digestSearch_public]
  rfl

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M.Final SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_pairedBank : DecidableEq T3.Cache := Classical.decEq _

noncomputable def authenticatedSign (published : T3.Cache) (request : Request) :
    M (Option SharedForest.Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache=published then SharedForest.signPayload request.cache request.message else pure none

theorem record_erasure (published : T3.Cache) (request : Request) :
    Prod.fst <$> bankSpec.authenticatedRecord payAfterDigest published request =
      authenticatedSign published request := by
  unfold FtsBankSpecL.authenticatedRecord authenticatedSign
  rw [map_bind]
  apply bind_congr
  intro tag
  split_ifs
  · exact payloadRecord_erasure _ _
  · rfl

noncomputable def recordedSource (published : T3.Cache) : QueryImpl (Interaction' SharedForest.Signature) M
  | .inl input => forwardWorld input
  | .inr request => authenticatedSign published request

theorem source_erasure (published : T3.Cache) :
    bankSpec.source payAfterDigest published = recordedSource published := by
  funext input
  cases input with
  | inl input => rfl
  | inr request => exact record_erasure published request

theorem recordedExperiment_erasure
    (rest : Digest → T3.Cache → OracleComp (Interaction' SharedForest.Signature) Bool) :
    bankSpec.recordedExperiment payAfterDigest rest = (do
      let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
      (liftM (QueryRecorded.run (simulateQ (recordedSource generated.1.2)
        (rest generated.1.1 generated.1.2)) generated.2) : PMF _)) := by
  unfold FtsBankSpecL.recordedExperiment
  simp_rw [source_erasure]

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def NotNonce : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inr (.inr (.inl _))=>False
  | _=>True

theorem notDN_of_marker_notNonce (q : SigGolfCandidate.T3.Spec.Domain)
    (hmark : BPB.NotDigestQ q) (hnonce : NotNonce q) : BPair.NotDN q := by
  rcases q with (n|x)|(tweak|(m|region))
  · trivial
  · intro hx
    obtain ⟨rho,m,c,rfl⟩:=BPair.mem_digestInputs.mp hx
    exact hmark (BPB.hdrMarker_digestInput rho m c)
  · trivial
  · exact hnonce.elim
  · trivial

theorem allQ_notDN {α : Type} (program : M α)
    (hmark : AllQueriesSatisfy program BPB.NotDigestQ)
    (hnonce : AllQueriesSatisfy program NotNonce) : AllQueriesSatisfy program BPair.NotDN := by
  induction program using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind q next ih =>
      obtain ⟨hm,hms⟩:=(allQueriesSatisfy_query_bind_iff _ _ _).mp hmark
      obtain ⟨hn,hns⟩:=(allQueriesSatisfy_query_bind_iff _ _ _).mp hnonce
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr
        ⟨notDN_of_marker_notNonce q hm hn,fun a=>ih a (hms a) (hns a)⟩

theorem forest_notNonce : ForestAllowed NotNonce :=
  forest_public NotNonce (fun _=>trivial) (fun _=>trivial)

theorem forest_notDN : ForestAllowed BPair.NotDN where
  coefs := fun index coord=>allQ_notDN _ (forest_notDigest.coefs index coord) (forest_notNonce.coefs index coord)
  child := fun heap index coord selected word coefs pad=>allQ_notDN _
    (forest_notDigest.child heap index coord selected word coefs pad)
    (forest_notNonce.child heap index coord selected word coefs pad)
  node := fun first coord index heap pads left right=>allQ_notDN _
    (forest_notDigest.node first coord index heap pads left right) (forest_notNonce.node first coord index heap pads left right)

theorem buildForest_notDN (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    AllQueriesSatisfy (buildForest index selected words) BPair.NotDN :=
  forest_allowed BPair.NotDN forest_notDN index selected words

end ClaudeWCT.Bank.Paired
end
-- ==== merged from SphincsSecurity_Proof_Forced_SecretGuessBy ====
section

/-!
# Predicate observations and sampler-generic secret-guess engines (campaign X1, stage A)

* `restrictBy` / `discloseBy` / `trialBy`: observing a function `view` (or a Boolean test) of one coordinate of a
  uniform table restricted to `allowed`; `bind_discloseBy` / `bind_trialBy` are the conditioning identities. The
  equality-trial engine of `SecretGuessObservation` is the special case `view = fun value => decide (value = c)`.
* `Sampler`, `withImpl`, `withRun`: the lazy engine of `SecretGuessObservation` with an arbitrary law for trial
  outcomes and disclosed values (same `State`, same `afterTrial` / `afterDisclosure` bookkeeping). Used for the FTS
  seed families, whose seeds are evaluations of a hidden coefficient vector rather than independent cells.
* Bounds for `withRun` under an abstract hazard: a pair potential (`withRun_pair_le`) and the first-guess forcing
  machinery (`withRun_event_le_forced_slot`). A monotone `Bad` flag switches the hazard off (FTS overflow).
These live in a new module (not in `SecretGuessObservation.lean`) to avoid rebuilding its 80 dependents.
-/

section
namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal UniformTableCompletion
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value Out : Type} [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]

/-- Restrict coordinate `coordinate` to the values whose `view` is `out`. -/
noncomputable def restrictBy (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out) (out : Out) :
    Coordinate → Finset Value :=
  Function.update allowed coordinate ((allowed coordinate).filter fun value => out = view value)
/-- Law of `view (labels coordinate)` for `labels` uniform on the table `allowed`. -/
noncomputable def discloseBy (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out) :
    SPMF Out :=
  complete allowed >>= fun labels => pure (view (labels coordinate))
/-- A Boolean test of one coordinate: `discloseBy` with `Out = Bool`. -/
noncomputable abbrev trialBy (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (test : Value → Bool) :
    SPMF Bool :=
  discloseBy allowed coordinate test
theorem restrictBy_subset (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out)
    (out : Out) (other : Coordinate) : restrictBy allowed coordinate view out other ⊆ allowed other := by
  by_cases heq : other = coordinate
  · subst other
    rw [restrictBy, Function.update_self]
    exact Finset.filter_subset _ _
  · simp only [restrictBy, Function.update_of_ne heq, Finset.Subset.refl]
theorem mem_restrictBy_self (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out)
    (out : Out) (value : Value) :
    value ∈ restrictBy allowed coordinate view out coordinate ↔ value ∈ allowed coordinate ∧ out = view value := by
  rw [restrictBy, Function.update_self, Finset.mem_filter]
theorem restrictBy_other (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out)
    (out : Out) {other : Coordinate} (h : other ≠ coordinate) :
    restrictBy allowed coordinate view out other = allowed other := by
  rw [restrictBy, Function.update_of_ne h]
theorem restrictBy_membership (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out)
    (out : Out) (labels : Coordinate → Value) :
    (∀ other, labels other ∈ restrictBy allowed coordinate view out other) ↔
      (∀ other, labels other ∈ allowed other) ∧ out = view (labels coordinate) := by
  constructor
  · intro h
    refine ⟨fun other => restrictBy_subset allowed coordinate view out other (h other), ?_⟩
    have hc := h coordinate
    rw [restrictBy, Function.update_self, Finset.mem_filter] at hc
    exact hc.2
  · rintro ⟨h, hh⟩ other
    by_cases heq : other = coordinate
    · subst other
      rw [restrictBy, Function.update_self]
      exact Finset.mem_filter.mpr ⟨h coordinate, hh⟩
    · simpa only [restrictBy, Function.update_of_ne heq] using h other
theorem restrictBy_mass (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out)
    (out : Out) (labels : Coordinate → Value) :
    (if out = view (labels coordinate) then complete allowed labels else 0) =
      restrictionWeight allowed (restrictBy allowed coordinate view out) *
        complete (restrictBy allowed coordinate view out) labels := by
  have h := restrict_guard allowed _ (restrictBy_subset allowed coordinate view out) _
    (restrictBy_membership allowed coordinate view out) labels
  by_cases hh : out = view (labels coordinate)
  · simpa only [if_pos hh] using h
  · simpa only [if_neg hh] using h
theorem discloseBy_apply (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out)
    (out : Out) :
    discloseBy allowed coordinate view out = restrictionWeight allowed (restrictBy allowed coordinate view out) := by
  rw [discloseBy, SPMF.bind_apply_eq_tsum]
  simp only [SPMF.pure_apply, mul_ite, mul_one, mul_zero, restrictBy_mass, ENNReal.tsum_mul_left,
    weight_tsum_complete]
theorem discloseBy_mass (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out)
    (out : Out) (labels : Coordinate → Value) :
    discloseBy allowed coordinate view out * complete (restrictBy allowed coordinate view out) labels =
      if out = view (labels coordinate) then complete allowed labels else 0 := by
  rw [discloseBy_apply, restrictBy_mass]
/-- Conditioning identity: observing `view` of one coordinate, then completing the restricted table, is the uniform
table. -/
theorem bind_discloseBy {Result : Type} (allowed : Coordinate → Finset Value) (coordinate : Coordinate)
    (view : Value → Out) (next : Out → (Coordinate → Value) → SPMF Result) :
    (complete allowed >>= fun labels => next (view (labels coordinate)) labels) =
      (discloseBy allowed coordinate view >>= fun out =>
        complete (restrictBy allowed coordinate view out) >>= next out) := by
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, ← ENNReal.tsum_mul_left, ← mul_assoc, discloseBy_mass, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro labels
  rw [tsum_eq_single (view (labels coordinate))]
  · simp only [if_true]
  · intro out hout
    rw [if_neg hout]
theorem bind_trialBy {Result : Type} (allowed : Coordinate → Finset Value) (coordinate : Coordinate)
    (test : Value → Bool) (next : Bool → (Coordinate → Value) → SPMF Result) :
    (complete allowed >>= fun labels => next (test (labels coordinate)) labels) =
      (trialBy allowed coordinate test >>= fun hit => complete (restrictBy allowed coordinate test hit) >>= next hit) :=
  bind_discloseBy allowed coordinate test next
theorem discloseBy_nonempty (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (view : Value → Out)
    (out : Out) (hout : discloseBy allowed coordinate view out ≠ 0) :
    ∀ other, (restrictBy allowed coordinate view out other).Nonempty := by
  by_contra hn
  rw [discloseBy_apply, weight_of_empty _ _ hn] at hout
  exact hout rfl
end SphincsSecurity.Concrete.SecretGuessObservation
end

section
namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- Laws of trial outcomes and disclosed values, as functions of the bookkeeping state. -/
structure Sampler (Coordinate Value Memory : Type) where
  trialLaw : State Coordinate Value Memory → Coordinate → Value → SPMF Bool
  discloseLaw : State Coordinate Value Memory → Coordinate → SPMF Value

variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]

/-- The lazy engine with sampler `sampler`: auxiliary queries as in `lazyImpl`, secret queries from the sampler. -/
noncomputable def withImpl (environment : Environment auxSpec Coordinate Value Memory)
    (sampler : Sampler Coordinate Value Memory) :
    QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF)
  | .inl input => lazyImpl environment (.inl input)
  | .inr (.inl (coordinate, candidate)) => StateT.mk fun state =>
      (fun hit => (hit, afterTrial environment state coordinate candidate hit)) <$>
        sampler.trialLaw state coordinate candidate
  | .inr (.inr coordinate) => StateT.mk fun state =>
      (fun value => (value, afterDisclosure environment state coordinate value)) <$>
        sampler.discloseLaw state coordinate
noncomputable def withRun {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (sampler : Sampler Coordinate Value Memory) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) :=
  runWith (withImpl environment sampler) computation state
variable (environment : Environment auxSpec Coordinate Value Memory) (sampler : Sampler Coordinate Value Memory)
/-- Every step of `withImpl` lands on an `afterTrial` / `afterDisclosure` / auxiliary-memory successor. -/
theorem withImpl_cases (state : State Coordinate Value Memory) (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (withImpl environment sampler input).run state result ≠ 0) :
    (∃ memory, result.2 = { state with memory := memory }) ∨
      (∃ coordinate candidate hit, input = .inr (.inl (coordinate, candidate)) ∧
        sampler.trialLaw state coordinate candidate hit ≠ 0 ∧
        result.2 = afterTrial environment state coordinate candidate hit) ∨
      (∃ coordinate value, input = .inr (.inr coordinate) ∧ sampler.discloseLaw state coordinate value ≠ 0 ∧
        result.2 = afterDisclosure environment state coordinate value) := by
  rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
  · simp only [withImpl, lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
      Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    exact Or.inl ⟨answer.2, rfl⟩
  · simp only [withImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
      Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨hit, hh, rfl⟩ := hr
    exact Or.inr (Or.inl ⟨coordinate, candidate, hit, rfl, hh, rfl⟩)
  · simp only [withImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
      Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨value, hv, rfl⟩ := hr
    exact Or.inr (Or.inr ⟨coordinate, value, rfl, hv, rfl⟩)
theorem withImpl_probes (state : State Coordinate Value Memory) (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (withImpl environment sampler input).run state result ≠ 0) :
    result.2.probes = state.probes + probeStep input := by
  rcases withImpl_cases environment sampler state input result hr with ⟨memory, h⟩ | ⟨c, v, hit, hi, -, h⟩ |
    ⟨c, value, hi, -, h⟩
  · rw [h]
    rcases input with input | (⟨c, v⟩ | c)
    · rfl
    · simp only [withImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
        Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      obtain ⟨hit, -, he⟩ := hr
      have := congrArg (fun s : State Coordinate Value Memory => s.probes) (he ▸ h)
      simp only [afterTrial] at this
      omega
    · rfl
  · subst hi; rw [h]; rfl
  · subst hi; rw [h]; rfl
theorem withRun_preserves {Result : Type} (invariant : State Coordinate Value Memory → Prop)
    (hstep : ∀ state, invariant state → ∀ input result,
      (withImpl environment sampler input).run state result ≠ 0 → invariant result.2)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hinvariant : invariant state) (result : Result × State Coordinate Value Memory)
    (hr : withRun environment sampler computation state result ≠ 0) : invariant result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [withRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact hinvariant
  | query_bind input next ih =>
      rw [withRun, runWith_query_bind, RetainedObservation.bind_nonzero] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      exact ih middle.1 middle.2 (hstep state hinvariant input middle hm) result hr
theorem withRun_probes_mono {Result : Type} (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (result : Result × State Coordinate Value Memory)
    (hr : withRun environment sampler computation state result ≠ 0) : state.probes ≤ result.2.probes := by
  apply withRun_preserves environment sampler (fun next => state.probes ≤ next.probes) _ computation state le_rfl
    result hr
  intro middle hm input next hn
  rw [withImpl_probes environment sampler middle input next hn]
  exact hm.trans (Nat.le_add_right _ _)
theorem afterTrial_guesses_sub (state : State Coordinate Value Memory) (hs : state.guesses ⊆ state.retired)
    (coordinate : Coordinate) (candidate : Value) (hit : Bool) :
    (afterTrial environment state coordinate candidate hit).guesses ⊆
      (afterTrial environment state coordinate candidate hit).retired := by
  simp only [afterTrial]
  split
  · rename_i hh
    rw [if_pos hh.1]
    exact Finset.insert_subset_insert coordinate hs
  · split
    · exact hs.trans (Finset.subset_insert _ _)
    · exact hs
/-- `guesses ⊆ retired` is preserved by every engine step. -/
theorem withImpl_guesses_sub (state : State Coordinate Value Memory) (hs : state.guesses ⊆ state.retired)
    (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (withImpl environment sampler input).run state result ≠ 0) : result.2.guesses ⊆ result.2.retired := by
  rcases withImpl_cases environment sampler state input result hr with ⟨memory, h⟩ | ⟨c, v, hit, -, -, h⟩ |
    ⟨c, value, -, -, h⟩
  · rw [h]; exact hs
  · rw [h]; exact afterTrial_guesses_sub environment state hs c v hit
  · rw [h]; exact hs.trans (Finset.subset_insert _ _)

/-! ### Abstract hazard and the pair bound -/

/-- Invariant `Inv` with a monotone failure flag `Bad`: steps preserve `Inv`, keep `Bad`, and keep `guesses ⊆ retired`;
while `¬Bad` and at most one guess was made, a trial at a non-retired coordinate hits with probability
`≤ (size - budget)⁻¹`. -/
structure Hazard (size budget : Nat) (Inv Bad : State Coordinate Value Memory → Prop) : Prop where
  step : ∀ state, Inv state → ∀ input result, (withImpl environment sampler input).run state result ≠ 0 →
    Inv result.2
  bad : ∀ state, Inv state → Bad state → ∀ input result, (withImpl environment sampler input).run state result ≠ 0 →
    Bad result.2
  guesses : ∀ state, Inv state → state.guesses ⊆ state.retired
  hazard : ∀ state, Inv state → ¬Bad state → state.guesses.card ≤ 1 → state.probes < budget →
    ∀ coordinate candidate, coordinate ∉ state.retired →
      sampler.trialLaw state coordinate candidate true ≤ ((size - budget : Nat) : ENNReal)⁻¹
variable {environment sampler}
private theorem expectation_const_le' {Result : Type} (law : SPMF Result) (value : ENNReal) :
    (∑' result, Pr[= result | law] * value) ≤ value := by
  rw [ENNReal.tsum_mul_right]
  exact mul_le_of_le_one_left' tsum_probOutput_le_one
/-- The pair potential, switched off under `Bad`. -/
noncomputable def pairPotentialB (Bad : State Coordinate Value Memory → Prop) (size budget : Nat)
    (state : State Coordinate Value Memory) : ENNReal :=
  if Bad state then 0 else pairPotential size budget state
theorem tsum_le_of_support {Result : Type} (law : SPMF Result) (f : Result → ENNReal) (c : ENNReal)
    (h : ∀ result, law result ≠ 0 → f result ≤ c) : (∑' result, Pr[= result | law] * f result) ≤ c := by
  refine le_trans (ENNReal.tsum_le_tsum fun result => ?_) (expectation_const_le' law c)
  by_cases hz : law result = 0
  · simp only [SPMF.probOutput_eq_apply, hz, zero_mul, le_refl]
  · exact mul_le_mul' le_rfl (h result hz)
theorem pairPotential_afterTrial_with (size budget : Nat) (state : State Coordinate Value Memory)
    (hs : state.guesses ⊆ state.retired) (coordinate : Coordinate) (candidate : Value) (law : SPMF Bool)
    (hrate : state.guesses.card ≤ 1 → state.probes < budget → coordinate ∉ state.retired →
      law true ≤ ((size - budget : Nat) : ENNReal)⁻¹) :
    (∑' hit, Pr[= hit | law] * pairPotential size budget (afterTrial environment state coordinate candidate hit)) ≤
      pairPotential size budget state := by
  classical
  by_cases hroom : state.probes < budget
  · have hwithin : state.probes ≤ budget := Nat.le_of_lt hroom
    have hafter : state.probes + 1 ≤ budget := hroom
    have hremaining : budget - state.probes = (budget - (state.probes + 1)) + 1 := by omega
    have hp (hit : Bool) : (afterTrial environment state coordinate candidate hit).probes = state.probes + 1 := rfl
    simp only [pairPotential, hp, afterTrial_guesses_card environment state hs, if_pos hafter, if_pos hwithin]
    by_cases hc : coordinate ∈ state.retired
    · simp only [hc, not_true_eq_false, and_false, if_false, Nat.add_zero]
      exact (expectation_const_le' _ _).trans (pairValue_mono _ _ (Nat.sub_le_sub_left (by omega) _))
    · by_cases hg : state.guesses.card ≤ 1
      · simp only [hc, not_false_eq_true, and_true]
        rw [hremaining]
        exact pairValue_trial _ _ (hrate hg hroom hc) _ _
      · obtain ⟨k, hk⟩ : ∃ k, state.guesses.card = k + 2 := ⟨state.guesses.card - 2, by omega⟩
        have h1 : ∀ hit : Bool, pairValue ((size - budget : Nat) : ENNReal)⁻¹ (budget - (state.probes + 1))
            (state.guesses.card + if hit = true ∧ coordinate ∉ state.retired then 1 else 0) = 1 := by
          intro hit
          rw [hk, show k + 2 + (if hit = true ∧ coordinate ∉ state.retired then 1 else 0) =
            (k + if hit = true ∧ coordinate ∉ state.retired then 1 else 0) + 2 by omega]
          rfl
        have h2 : pairValue ((size - budget : Nat) : ENNReal)⁻¹ (budget - state.probes) state.guesses.card = 1 := by
          rw [hk]; rfl
        simp only [h1, h2]
        exact expectation_const_le' law 1
  · have hafter : ¬state.probes + 1 ≤ budget := by omega
    simp only [pairPotential, afterTrial, if_neg hafter, mul_zero, tsum_zero]
    exact bot_le
theorem withImpl_pairPotentialB {size budget : Nat} {Inv Bad : State Coordinate Value Memory → Prop}
    (H : Hazard environment sampler size budget Inv Bad) (state : State Coordinate Value Memory) (hs : Inv state)
    (input : (World auxSpec Coordinate Value).Domain) :
    (∑' result, Pr[= result | (withImpl environment sampler input).run state] *
      pairPotentialB Bad size budget result.2) ≤ pairPotentialB Bad size budget state := by
  by_cases hbad : Bad state
  · refine tsum_le_of_support _ _ _ fun result hz => ?_
    simp only [pairPotentialB, if_pos (H.bad state hs hbad input result hz)]
    exact bot_le
  · have hle : (∑' result, Pr[= result | (withImpl environment sampler input).run state] *
        pairPotentialB Bad size budget result.2) ≤
        ∑' result, Pr[= result | (withImpl environment sampler input).run state] *
          pairPotential size budget result.2 := by
      refine ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl ?_
      unfold pairPotentialB
      split
      · exact bot_le
      · exact le_rfl
    refine hle.trans ?_
    rw [pairPotentialB, if_neg hbad]
    rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
    · refine tsum_le_of_support _ _ _ fun result hz => ?_
      rcases withImpl_cases environment sampler state _ result hz with ⟨memory, h⟩ | ⟨c, v, hit, hi, -, -⟩ |
        ⟨c, value, hi, -, -⟩
      · rw [h]; exact le_rfl
      · cases hi
      · cases hi
    · simp only [withImpl, StateT.run_mk, tsum_probOutput_map_mul]
      exact pairPotential_afterTrial_with size budget state (H.guesses state hs) coordinate candidate _
        (fun hg hp hc => H.hazard state hs hbad hg hp coordinate candidate hc)
    · refine tsum_le_of_support _ _ _ fun result hz => ?_
      rcases withImpl_cases environment sampler state _ result hz with ⟨memory, h⟩ | ⟨c, v, hit, hi, -, -⟩ |
        ⟨c, value, hi, -, h⟩
      · rw [h]; exact le_rfl
      · cases hi
      · rw [h]; exact le_rfl
theorem withRun_pairPotentialB {Result : Type} {size budget : Nat} {Inv Bad : State Coordinate Value Memory → Prop}
    (H : Hazard environment sampler size budget Inv Bad) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Inv state) :
    (∑' result, Pr[= result | withRun environment sampler computation state] *
      pairPotentialB Bad size budget result.2) ≤ pairPotentialB Bad size budget state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [withRun, runWith_pure, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      rw [withRun, runWith_query_bind, tsum_probOutput_bind_mul]
      apply le_trans _ (withImpl_pairPotentialB H state hs input)
      apply ENNReal.tsum_le_tsum
      intro middle
      by_cases hm : (withImpl environment sampler input).run state middle = 0
      · simp only [SPMF.probOutput_eq_apply, hm, zero_mul, le_refl]
      · exact mul_le_mul' le_rfl (ih middle.1 middle.2 (H.step state hs input middle hm))
/-- Pair bound for any sampler with a hazard: two new guesses within the budget, without `Bad`, have probability at
most `C(budget, 2) · (size - budget)⁻²`. -/
theorem withRun_pair_le {Result : Type} {size budget : Nat} {Inv Bad : State Coordinate Value Memory → Prop}
    (H : Hazard environment sampler size budget Inv Bad) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Inv state) (hprobes : state.probes = 0)
    (hguesses : state.guesses = ∅) :
    Pr[fun result => 2 ≤ result.2.guesses.card ∧ result.2.probes ≤ budget ∧ ¬Bad result.2 |
      withRun environment sampler computation state] ≤
      (budget.choose 2 : ENNReal) * ((size - budget : Nat) : ENNReal)⁻¹ ^ 2 := by
  apply (probEvent_le_tsum_probOutput_mul_cost_of_mem_support _ _
    (fun result => pairPotentialB Bad size budget result.2) ?_).trans
  · refine (withRun_pairPotentialB H computation state hs).trans ?_
    unfold pairPotentialB
    split
    · exact bot_le
    · simp [pairPotential, hprobes, hguesses, pairValue]
  · intro result _ h
    rw [pairPotentialB, if_neg h.2.2]
    exact pairPotential_two _ _ result.2 h.2.1 h.1
end SphincsSecurity.Concrete.SecretGuessObservation
end

section
namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
variable (environment : Environment auxSpec Coordinate Value Memory) (sampler : Sampler Coordinate Value Memory)

/-! ### First-guess forcing -/

/-- Forcing at `slot` applies to the first new guess only: fresh coordinate, no earlier guess, positive hit mass. -/
def EligibleWith (slot : Nat) (state : State Coordinate Value Memory) (coordinate : Coordinate) (candidate : Value) :
    Prop :=
  state.probes = slot ∧ coordinate ∉ state.retired ∧ state.guesses = ∅ ∧
    sampler.trialLaw state coordinate candidate true ≠ 0
noncomputable def forcedTrialWith (slot : Nat) (state : State Coordinate Value Memory) (coordinate : Coordinate)
    (candidate : Value) : SPMF Bool :=
  if EligibleWith sampler slot state coordinate candidate then pure true else sampler.trialLaw state coordinate candidate
noncomputable def forcedWithImpl (slot : Nat) :
    QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF)
  | .inl input => withImpl environment sampler (.inl input)
  | .inr (.inl (coordinate, candidate)) => StateT.mk fun state =>
      (fun hit => (hit, afterTrial environment state coordinate candidate hit)) <$>
        forcedTrialWith sampler slot state coordinate candidate
  | .inr (.inr coordinate) => withImpl environment sampler (.inr (.inr coordinate))
noncomputable def forcedWithRun {Result : Type} (slot : Nat) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) :=
  runWith (forcedWithImpl environment sampler slot) computation state
theorem forcedTrialWith_nonzero (slot : Nat) (state : State Coordinate Value Memory) (coordinate : Coordinate)
    (candidate : Value) (hit : Bool) (hhit : forcedTrialWith sampler slot state coordinate candidate hit ≠ 0) :
    sampler.trialLaw state coordinate candidate hit ≠ 0 := by
  by_cases he : EligibleWith sampler slot state coordinate candidate
  · simp only [forcedTrialWith, if_pos he, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hhit
    subst hit
    exact he.2.2.2
  · simpa only [forcedTrialWith, if_neg he] using hhit
theorem forcedWithImpl_nonzero (slot : Nat) (state : State Coordinate Value Memory)
    (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (forcedWithImpl environment sampler slot input).run state result ≠ 0) :
    (withImpl environment sampler input).run state result ≠ 0 := by
  rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
  · exact hr
  · simp only [forcedWithImpl, withImpl, StateT.run_mk, map_eq_bind_pure_comp,
      RetainedObservation.bind_nonzero] at hr ⊢
    obtain ⟨hit, hh, hr⟩ := hr
    exact ⟨hit, forcedTrialWith_nonzero sampler slot state coordinate candidate hit hh, hr⟩
  · exact hr
noncomputable def hitTrialWith (slot : Nat) (state : State Coordinate Value Memory) (coordinate : Coordinate)
    (candidate : Value) : SPMF Bool :=
  if state.probes = slot then
    sampler.trialLaw state coordinate candidate >>= fun hit =>
      if hit = true ∧ coordinate ∉ state.retired ∧ state.guesses = ∅ then pure hit else failure
  else sampler.trialLaw state coordinate candidate
noncomputable def trialFactorWith (slot : Nat) (state : State Coordinate Value Memory) (coordinate : Coordinate)
    (candidate : Value) : ENNReal :=
  if state.probes = slot then
    if coordinate ∉ state.retired ∧ state.guesses = ∅ then sampler.trialLaw state coordinate candidate true else 0
  else 1
theorem hitTrialWith_apply (slot : Nat) (state : State Coordinate Value Memory) (coordinate : Coordinate)
    (candidate : Value) (hit : Bool) :
    hitTrialWith sampler slot state coordinate candidate hit =
      trialFactorWith sampler slot state coordinate candidate * forcedTrialWith sampler slot state coordinate candidate hit := by
  by_cases hs : state.probes = slot
  · by_cases hc : coordinate ∉ state.retired ∧ state.guesses = ∅
    · have hmass : hitTrialWith sampler slot state coordinate candidate hit =
          if hit = true then sampler.trialLaw state coordinate candidate true else 0 := by
        rw [hitTrialWith, if_pos hs, SPMF.bind_apply_eq_tsum]
        simp only [tsum_fintype, Fintype.sum_bool, Bool.false_eq_true, false_and, if_false, true_and,
          hc, and_self, SPMF.failure_apply, mul_zero, add_zero]
        split <;> simp_all
      rw [hmass]
      by_cases hp : sampler.trialLaw state coordinate candidate true = 0
      · simp only [trialFactorWith, if_pos hs, if_pos hc, hp, zero_mul, ite_self]
      · have he : EligibleWith sampler slot state coordinate candidate := ⟨hs, hc.1, hc.2, hp⟩
        simp only [trialFactorWith, if_pos hs, if_pos hc, forcedTrialWith, if_pos he, SPMF.pure_apply,
          mul_ite, mul_one, mul_zero]
    · have hz : hitTrialWith sampler slot state coordinate candidate hit = 0 := by
        rw [hitTrialWith, if_pos hs, SPMF.bind_apply_eq_tsum]
        refine ENNReal.tsum_eq_zero.mpr fun h => ?_
        rw [if_neg (fun hh => hc ⟨hh.2.1, hh.2.2⟩), SPMF.failure_apply, mul_zero]
      simp only [hz, trialFactorWith, if_pos hs, if_neg hc, zero_mul]
  · have he : ¬EligibleWith sampler slot state coordinate candidate := fun h => hs h.1
    simp only [hitTrialWith, trialFactorWith, if_neg hs, forcedTrialWith, if_neg he, one_mul]
theorem hitTrialWith_bind_apply {Result : Type} (slot : Nat) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value) (next : Bool → SPMF Result) (result : Result) :
    (hitTrialWith sampler slot state coordinate candidate >>= next) result =
      trialFactorWith sampler slot state coordinate candidate *
        (forcedTrialWith sampler slot state coordinate candidate >>= next) result := by
  simp only [SPMF.bind_apply_eq_tsum, hitTrialWith_apply, mul_assoc, ENNReal.tsum_mul_left]
noncomputable def hitWithImpl (slot : Nat) :
    QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF)
  | .inl input => withImpl environment sampler (.inl input)
  | .inr (.inl (coordinate, candidate)) => StateT.mk fun state =>
      (fun hit => (hit, afterTrial environment state coordinate candidate hit)) <$>
        hitTrialWith sampler slot state coordinate candidate
  | .inr (.inr coordinate) => withImpl environment sampler (.inr (.inr coordinate))
noncomputable def forceFactorWith (slot : Nat) (state : State Coordinate Value Memory) :
    (World auxSpec Coordinate Value).Domain → ENNReal
  | .inr (.inl (coordinate, candidate)) => trialFactorWith sampler slot state coordinate candidate
  | _ => 1
theorem hitWithImpl_apply (slot : Nat) (state : State Coordinate Value Memory)
    (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory) :
    (hitWithImpl environment sampler slot input).run state result =
      forceFactorWith sampler slot state input * (forcedWithImpl environment sampler slot input).run state result := by
  rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
  · simp only [hitWithImpl, forcedWithImpl, forceFactorWith, one_mul]
  · simp only [hitWithImpl, forcedWithImpl, forceFactorWith, StateT.run_mk, map_eq_bind_pure_comp,
      Function.comp_def]
    exact hitTrialWith_bind_apply sampler slot state coordinate candidate
      (fun hit : Bool => pure (hit, afterTrial environment state coordinate candidate hit)) result
  · simp only [hitWithImpl, forcedWithImpl, forceFactorWith, one_mul]
noncomputable def hitWithRun {Result : Type} (slot : Nat) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) :=
  runWith (hitWithImpl environment sampler slot) computation state >>= fun result =>
    if slot < result.2.probes then pure result else (failure : SPMF _)
theorem hitWithRun_weighted_forced {Result : Type} (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (payoff : Result × State Coordinate Value Memory → ENNReal) :
    (∑' result, Pr[= result | hitWithRun environment sampler slot computation state] * payoff result) =
      ∑' result, Pr[= result | WeightedQuery.run (forcedWithImpl environment sampler slot) (forceFactorWith sampler slot)
        computation (state, 1)] * (forceWeight slot result.2 * payoff (result.1, result.2.1)) := by
  have h := WeightedQuery.run_payoff (hitWithImpl environment sampler slot) (forcedWithImpl environment sampler slot)
    (forceFactorWith sampler slot) (hitWithImpl_apply environment sampler slot) computation state 1
    (fun result => if slot < result.2.probes then payoff result else 0)
  simp only [one_mul] at h
  rw [hitWithRun, tsum_probOutput_bind_mul]
  convert h using 1
  · apply tsum_congr
    intro result
    congr 1
    by_cases hp : slot < result.2.probes
    · simp only [if_pos hp, tsum_probOutput_pure_mul]
    · simp only [if_neg hp, SPMF.probOutput_eq_apply, SPMF.failure_apply, zero_mul, tsum_zero]
  · apply tsum_congr
    intro result
    congr 1
    simp only [forceWeight, mul_ite, ite_mul, mul_zero, zero_mul]
theorem forceFactorWith_le_one (slot : Nat) (state : State Coordinate Value Memory)
    (input : (World auxSpec Coordinate Value).Domain) : forceFactorWith sampler slot state input ≤ 1 := by
  rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
  · exact le_rfl
  · simp only [forceFactorWith, trialFactorWith]
    split
    · split
      · simpa only [SPMF.probOutput_eq_apply] using
          (show Pr[= true | sampler.trialLaw state coordinate candidate] ≤ 1 from probOutput_le_one)
      · exact bot_le
    · exact le_rfl
  · exact le_rfl
variable {environment sampler}
theorem forceFactorWith_weight_bound {size budget : Nat} {Inv Bad : State Coordinate Value Memory → Prop}
    (H : Hazard environment sampler size budget Inv Bad) (slot : Nat) (hslot : slot < budget)
    (state : State Coordinate Value Memory) (weight : ENNReal) (hs : Inv state) (hw : weight ≤ 1)
    (hlate : slot < state.probes → weight ≤ ((size - budget : Nat) : ENNReal)⁻¹ ∨ Bad state)
    (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (forcedWithImpl environment sampler slot input).run state result ≠ 0) :
    weight * forceFactorWith sampler slot state input ≤ 1 ∧
      (slot < result.2.probes →
        weight * forceFactorWith sampler slot state input ≤ ((size - budget : Nat) : ENNReal)⁻¹ ∨ Bad result.2) := by
  have hm : weight * forceFactorWith sampler slot state input ≤ weight :=
    mul_le_of_le_one_right' (forceFactorWith_le_one sampler slot state input)
  have hwith := forcedWithImpl_nonzero environment sampler slot state input result hr
  refine ⟨hm.trans hw, fun hafter => ?_⟩
  by_cases hb : slot < state.probes
  · rcases hlate hb with h | h
    · exact Or.inl (hm.trans h)
    · exact Or.inr (H.bad state hs h input result hwith)
  by_cases hbad : Bad state
  · exact Or.inr (H.bad state hs hbad input result hwith)
  left
  have hp := withImpl_probes environment sampler state input result hwith
  rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
  · simp only [probeStep, Nat.add_zero] at hp; omega
  · change result.2.probes = state.probes + 1 at hp
    have he : state.probes = slot := by omega
    simp only [forceFactorWith, trialFactorWith, if_pos he]
    split
    next hc =>
      have hg : state.guesses.card ≤ 1 := by rw [hc.2]; simp
      exact (mul_le_of_le_one_left' hw).trans
        (H.hazard state hs hbad hg (he ▸ hslot) coordinate candidate hc.1)
    next hc => simp only [mul_zero]; exact bot_le
  · simp only [probeStep, Nat.add_zero] at hp; omega
theorem weightedForcedWith_weight_bound {Result : Type} {size budget : Nat}
    {Inv Bad : State Coordinate Value Memory → Prop} (H : Hazard environment sampler size budget Inv Bad)
    (slot : Nat) (hslot : slot < budget) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Inv state) (hp : state.probes ≤ slot)
    (result : Result × State Coordinate Value Memory × ENNReal)
    (hr : WeightedQuery.run (forcedWithImpl environment sampler slot) (forceFactorWith sampler slot) computation
      (state, 1) result ≠ 0) :
    forceWeight slot result.2 ≤ ((size - budget : Nat) : ENNReal)⁻¹ ∨ Bad result.2.1 := by
  let valid (st : State Coordinate Value Memory × ENNReal) : Prop :=
    Inv st.1 ∧ st.2 ≤ 1 ∧ (slot < st.1.probes → st.2 ≤ ((size - budget : Nat) : ENNReal)⁻¹ ∨ Bad st.1)
  have hstep (st : State Coordinate Value Memory × ENNReal) (hv : valid st)
      (input : (World auxSpec Coordinate Value).Domain)
      (middle : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
      (hm : (forcedWithImpl environment sampler slot input).run st.1 middle ≠ 0) :
      valid (middle.2, st.2 * forceFactorWith sampler slot st.1 input) :=
    ⟨H.step st.1 hv.1 input middle (forcedWithImpl_nonzero environment sampler slot st.1 input middle hm),
      forceFactorWith_weight_bound H slot hslot st.1 st.2 hv.1 hv.2.1 hv.2.2 input middle hm⟩
  have hinitial : valid (state, 1) := ⟨hs, le_rfl, fun h => absurd (show slot < state.probes from h) (by omega)⟩
  have h := WeightedQuery.run_preserves (forcedWithImpl environment sampler slot) (forceFactorWith sampler slot)
    valid hstep computation (state, 1) hinitial result hr
  rw [forceWeight]
  split
  · exact h.2.2 ‹_›
  · exact Or.inl bot_le
theorem hitWithRun_payoff_le_forced {Result : Type} {size budget : Nat}
    {Inv Bad : State Coordinate Value Memory → Prop} (H : Hazard environment sampler size budget Inv Bad)
    (slot : Nat) (hslot : slot < budget) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Inv state) (hp : state.probes ≤ slot)
    (payoff : Result × State Coordinate Value Memory → ENNReal) :
    (∑' result, Pr[= result | hitWithRun environment sampler slot computation state] *
      (if Bad result.2 then 0 else payoff result)) ≤
      ((size - budget : Nat) : ENNReal)⁻¹ *
        (∑' result, Pr[= result | forcedWithRun environment sampler slot computation state] * payoff result) := by
  rw [hitWithRun_weighted_forced]
  have hforget := congrArg (fun law : SPMF (Result × State Coordinate Value Memory) =>
    ∑' result, Pr[= result | law] * payoff result)
    (WeightedQuery.run_forget (forcedWithImpl environment sampler slot) (forceFactorWith sampler slot) computation
      (state, 1))
  rw [tsum_probOutput_map_mul] at hforget
  rw [forcedWithRun, runWith, ← show (∑' result, Pr[= result | WeightedQuery.run (forcedWithImpl environment sampler slot)
      (forceFactorWith sampler slot) computation (state, 1)] * payoff (result.1, result.2.1)) =
      (∑' result, Pr[= result | (simulateQ (forcedWithImpl environment sampler slot) computation).run state] *
        payoff result) from hforget, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hz : WeightedQuery.run (forcedWithImpl environment sampler slot) (forceFactorWith sampler slot) computation
    (state, 1) result = 0
  · simp only [SPMF.probOutput_eq_apply, hz, zero_mul, mul_zero, le_refl]
  · rw [mul_left_comm (((size - budget : Nat) : ENNReal)⁻¹)]
    apply mul_le_mul' le_rfl
    dsimp only
    rcases weightedForcedWith_weight_bound H slot hslot computation state hs hp result hz with h | h
    · split
      · simp only [mul_zero]; exact bot_le
      · exact mul_le_mul' h le_rfl
    · rw [if_pos h, mul_zero]; exact bot_le
end SphincsSecurity.Concrete.SecretGuessObservation
end

section
namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
variable (environment : Environment auxSpec Coordinate Value Memory) (sampler : Sampler Coordinate Value Memory)

/-! ### First-guess decomposition -/

theorem hitWithImpl_eq_with (slot : Nat) (state : State Coordinate Value Memory) (hne : state.probes ≠ slot)
    (input : (World auxSpec Coordinate Value).Domain) :
    (hitWithImpl environment sampler slot input).run state = (withImpl environment sampler input).run state := by
  rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
  · rfl
  · simp only [hitWithImpl, withImpl, StateT.run_mk, hitTrialWith, if_neg hne]
  · rfl
theorem hitWithImplRun_after {Result : Type} (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hslot : slot < state.probes) :
    runWith (hitWithImpl environment sampler slot) computation state = withRun environment sampler computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [withRun, runWith_pure]
  | query_bind input next ih =>
      rw [runWith_query_bind, withRun, runWith_query_bind,
        hitWithImpl_eq_with environment sampler slot state (Nat.ne_of_gt hslot)]
      apply RetainedObservation.bind_congr
      intro middle hm
      have hp := withImpl_probes environment sampler state input middle hm
      apply ih middle.1 middle.2
      rw [hp]
      exact hslot.trans_le (Nat.le_add_right _ _)
theorem hitWithRun_apply {Result : Type} (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (result : Result × State Coordinate Value Memory) : hitWithRun environment sampler slot computation state result =
      if slot < result.2.probes then runWith (hitWithImpl environment sampler slot) computation state result else 0 := by
  rw [hitWithRun, SPMF.bind_apply_eq_tsum, tsum_eq_single result]
  · split <;> simp only [SPMF.pure_apply_self, SPMF.failure_apply, mul_one, mul_zero]
  · intro other hother
    split <;> simp only [SPMF.pure_apply, if_neg (Ne.symm hother), SPMF.failure_apply, mul_zero]
theorem hitWithRun_after {Result : Type} (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hslot : slot < state.probes) :
    hitWithRun environment sampler slot computation state = withRun environment sampler computation state := by
  apply SPMF.ext
  intro result
  rw [hitWithRun_apply, hitWithImplRun_after environment sampler slot computation state hslot]
  by_cases hp : slot < result.2.probes
  · exact if_pos hp
  · rw [if_neg hp]
    symm
    by_contra hr
    exact hp (hslot.trans_le (withRun_probes_mono environment sampler computation state result hr))
theorem hitWithRun_query_bind {Result : Type} (slot : Nat) (input : (World auxSpec Coordinate Value).Domain)
    (next : (World auxSpec Coordinate Value).Range input → OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) :
    hitWithRun environment sampler slot (liftM ((World auxSpec Coordinate Value).query input) >>= next) state =
      ((hitWithImpl environment sampler slot input).run state >>= fun middle =>
        hitWithRun environment sampler slot (next middle.1) middle.2) := by
  simp only [hitWithRun, runWith_query_bind, bind_assoc]
theorem hitWithRun_probe_at {Result : Type} (coordinate : Coordinate) (candidate : Value)
    (next : Bool → OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory) :
    hitWithRun environment sampler state.probes
      (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state =
      (sampler.trialLaw state coordinate candidate >>= fun hit =>
        if hit = true ∧ coordinate ∉ state.retired ∧ state.guesses = ∅ then
          withRun environment sampler (next hit) (afterTrial environment state coordinate candidate hit)
        else failure) := by
  rw [hitWithRun_query_bind]
  simp only [hitWithImpl, StateT.run_mk, bind_map_left, hitTrialWith, ite_true, bind_assoc]
  apply congrArg (sampler.trialLaw state coordinate candidate >>= ·)
  funext hit
  by_cases hh : hit = true ∧ coordinate ∉ state.retired ∧ state.guesses = ∅
  · rw [if_pos hh, pure_bind, hitWithRun_after environment sampler state.probes _ _ (Nat.lt_succ_self _)]
    rw [if_pos hh]
  · simp only [if_neg hh, failure_bind]
theorem hitWithRun_probe_other {Result : Type} (slot : Nat) (coordinate : Coordinate) (candidate : Value)
    (next : Bool → OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hne : state.probes ≠ slot) :
    hitWithRun environment sampler slot
      (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state =
      (sampler.trialLaw state coordinate candidate >>= fun hit =>
        hitWithRun environment sampler slot (next hit) (afterTrial environment state coordinate candidate hit)) := by
  rw [hitWithRun_query_bind, hitWithImpl_eq_with environment sampler slot state hne]
  simp only [withImpl, StateT.run_mk, bind_map_left]
  rfl
private theorem sum_bind_apply' {Index First Result : Type} (indices : Finset Index) (law : SPMF First)
    (next : Index → First → SPMF Result) (result : Result) :
    (∑ index ∈ indices, (law >>= next index) result) =
      ∑' first, law first * ∑ index ∈ indices, next index first result := by
  simp only [SPMF.bind_apply_eq_tsum]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp only [Finset.mul_sum]
theorem hitWithImpl_no_probe (slot : Nat) (input : (World auxSpec Coordinate Value).Domain) (hn : probeStep input = 0) :
    hitWithImpl environment sampler slot input = withImpl environment sampler input := by
  rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
  · rfl
  · cases hn
  · rfl
theorem withImpl_no_probe_guesses (input : (World auxSpec Coordinate Value).Domain) (hn : probeStep input = 0)
    (state : State Coordinate Value Memory)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (withImpl environment sampler input).run state result ≠ 0) : result.2.guesses = state.guesses := by
  rcases withImpl_cases environment sampler state input result hr with ⟨memory, h⟩ | ⟨c, v, hit, hi, -, -⟩ |
    ⟨c, value, -, -, h⟩
  · rw [h]
  · subst hi; cases hn
  · rw [h]; rfl
theorem hitWithRun_sum_no_probe {Result : Type} (slots : Finset Nat) (input : (World auxSpec Coordinate Value).Domain)
    (hn : probeStep input = 0)
    (next : (World auxSpec Coordinate Value).Range input → OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (result : Result × State Coordinate Value Memory) :
    (∑ slot ∈ slots, hitWithRun environment sampler slot
        (liftM ((World auxSpec Coordinate Value).query input) >>= next) state result) =
      ∑' middle, (withImpl environment sampler input).run state middle *
        ∑ slot ∈ slots, hitWithRun environment sampler slot (next middle.1) middle.2 result := by
  simp_rw [hitWithRun_query_bind, hitWithImpl_no_probe environment sampler _ input hn]
  exact sum_bind_apply' slots _ _ result
theorem hitWithRun_sum_probe {Result : Type} (budget : Nat) (coordinate : Coordinate) (candidate : Value)
    (next : Bool → OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (result : Result × State Coordinate Value Memory) (hbudget : state.probes < budget) :
    (∑ slot ∈ Finset.Ico state.probes budget, hitWithRun environment sampler slot
      (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state result) =
      ∑' hit, sampler.trialLaw state coordinate candidate hit *
        ((if hit = true ∧ coordinate ∉ state.retired ∧ state.guesses = ∅ then
            withRun environment sampler (next hit) (afterTrial environment state coordinate candidate hit) result
          else 0) +
          ∑ slot ∈ Finset.Ico (state.probes + 1) budget,
            hitWithRun environment sampler slot (next hit) (afterTrial environment state coordinate candidate hit)
              result) := by
  rw [Finset.sum_eq_sum_Ico_succ_bot hbudget, hitWithRun_probe_at, SPMF.bind_apply_eq_tsum]
  have htail :
      (∑ slot ∈ Finset.Ico (state.probes + 1) budget, hitWithRun environment sampler slot
        (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state result) =
      ∑' hit, sampler.trialLaw state coordinate candidate hit *
        ∑ slot ∈ Finset.Ico (state.probes + 1) budget,
          hitWithRun environment sampler slot (next hit) (afterTrial environment state coordinate candidate hit)
            result := by
    calc
      _ = ∑ slot ∈ Finset.Ico (state.probes + 1) budget,
          (sampler.trialLaw state coordinate candidate >>= fun hit =>
            hitWithRun environment sampler slot (next hit) (afterTrial environment state coordinate candidate hit))
              result := by
        apply Finset.sum_congr rfl
        intro slot hslot
        rw [hitWithRun_probe_other environment sampler slot coordinate candidate next state (by
          have h := (Finset.mem_Ico.mp hslot).1
          omega)]
      _ = _ := sum_bind_apply' _ _ _ result
  rw [htail, ← ENNReal.tsum_add]
  apply tsum_congr
  intro hit
  by_cases hh : hit = true ∧ coordinate ∉ state.retired ∧ state.guesses = ∅
  · simp only [if_pos hh, mul_add]
  · simp only [if_neg hh, SPMF.failure_apply, mul_zero, zero_add]
/-- A run that makes its first guess within the budget splits along the probe slot of that first guess. -/
theorem withRun_first_guess_le_sum {Result : Type} (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (result : Result × State Coordinate Value Memory) (budget : Nat)
    (hbudget : result.2.probes ≤ budget) (h0 : state.guesses = ∅) (hnew : result.2.guesses ≠ ∅) :
    withRun environment sampler computation state result ≤
      ∑ slot ∈ Finset.Ico state.probes budget, hitWithRun environment sampler slot computation state result := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      by_cases he : result = (value, state)
      · subst result
        exact False.elim (hnew h0)
      · simp only [withRun, runWith_pure, SPMF.pure_apply, if_neg he]
        exact bot_le
  | query_bind input next ih =>
      by_cases hn : probeStep input = 0
      · rw [hitWithRun_sum_no_probe environment sampler _ input hn, withRun, runWith_query_bind,
          SPMF.bind_apply_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro middle
        by_cases hm : (withImpl environment sampler input).run state middle = 0
        · simp only [hm, zero_mul, le_refl]
        · have hp := withImpl_probes environment sampler state input middle hm
          rw [hn, Nat.add_zero] at hp
          have hg := withImpl_no_probe_guesses environment sampler input hn state middle hm
          have h := ih middle.1 middle.2 (hg.trans h0)
          rw [hp] at h
          exact mul_le_mul' le_rfl h
      · rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
        · exact False.elim (hn rfl)
        · by_cases hz : withRun environment sampler
              (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state
              result = 0
          · rw [hz]
            exact bot_le
          have hpositive := hz
          rw [withRun, runWith_query_bind] at hpositive
          simp only [withImpl, StateT.run_mk, bind_map_left, RetainedObservation.bind_nonzero] at hpositive
          obtain ⟨hit, _, htail⟩ := hpositive
          have hp := withRun_probes_mono environment sampler (next hit)
            (afterTrial environment state coordinate candidate hit) result htail
          have hroom : state.probes < budget := by
            change state.probes + 1 ≤ result.2.probes at hp
            omega
          rw [hitWithRun_sum_probe environment sampler budget coordinate candidate next state result hroom]
          simp only [withRun, runWith_query_bind, withImpl, StateT.run_mk, bind_map_left, SPMF.bind_apply_eq_tsum]
          apply ENNReal.tsum_le_tsum
          intro hit
          apply mul_le_mul' le_rfl
          by_cases hh : hit = true ∧ coordinate ∉ state.retired ∧ state.guesses = ∅
          · rw [if_pos hh]
            exact le_add_right le_rfl
          · rw [if_neg hh, zero_add]
            have hh' : ¬(hit = true ∧ coordinate ∉ state.retired) := fun h => hh ⟨h.1, h.2, h0⟩
            apply ih hit (afterTrial environment state coordinate candidate hit)
            simpa only [afterTrial, if_neg hh'] using h0
        · exact False.elim (hn rfl)
variable {environment sampler}
/-- First-guess forcing bound: an event that forces a guess within the budget, without `Bad`, is bounded by the
hazard rate times the forced runs' payoffs, summed over the slot of the first guess. -/
theorem withRun_event_le_forced_slot {Result : Type} {size budget : Nat}
    {Inv Bad : State Coordinate Value Memory → Prop} (H : Hazard environment sampler size budget Inv Bad)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hs : Inv state) (hp0 : state.probes = 0) (hg0 : state.guesses = ∅)
    (event : Result × State Coordinate Value Memory → Prop)
    (payoff : Nat → Result × State Coordinate Value Memory → ENNReal)
    (hevent : ∀ result, withRun environment sampler computation state result ≠ 0 → event result →
      result.2.guesses.Nonempty ∧ result.2.probes ≤ budget ∧ ¬Bad result.2 ∧
        ∀ slot < result.2.probes, 1 ≤ payoff slot result) :
    Pr[event | withRun environment sampler computation state] ≤
      ((size - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget, ∑' result,
          Pr[= result | forcedWithRun environment sampler slot computation state] * payoff slot result := by
  let cond : Result × State Coordinate Value Memory → Prop := fun result =>
    result.2.guesses.Nonempty ∧ result.2.probes ≤ budget ∧ ¬Bad result.2 ∧
      ∀ slot < result.2.probes, 1 ≤ payoff slot result
  have hstep : (∑' result, Pr[= result | withRun environment sampler computation state] *
      (if cond result then (1 : ENNReal) else 0)) ≤
      ∑ slot ∈ Finset.range budget, ∑' result,
        Pr[= result | hitWithRun environment sampler slot computation state] *
          (if Bad result.2 then 0 else payoff slot result) := by
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    apply ENNReal.tsum_le_tsum
    intro result
    by_cases hg : cond result
    · rw [if_pos hg, mul_one, SPMF.probOutput_eq_apply]
      have h := withRun_first_guess_le_sum environment sampler computation state result budget hg.2.1 hg0
        hg.1.ne_empty
      rw [hp0, ← Finset.range_eq_Ico] at h
      refine h.trans (Finset.sum_le_sum fun slot hslot => ?_)
      rw [SPMF.probOutput_eq_apply, if_neg hg.2.2.1, hitWithRun_apply]
      split
      · next hlt => exact le_mul_of_one_le_right' (hg.2.2.2 slot hlt)
      · simp only [zero_mul, le_refl]
    · simp only [if_neg hg, mul_zero]
      exact bot_le
  apply (probEvent_le_tsum_probOutput_mul_cost_of_mem_support _ _
    (fun result => if cond result then (1 : ENNReal) else 0) ?_).trans
  · apply hstep.trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro slot hslot
    exact hitWithRun_payoff_le_forced H slot (Finset.mem_range.mp hslot) computation state hs (by omega)
      (payoff slot)
  · intro result hr he
    have h := hevent result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr) he
    rw [if_pos h]
end SphincsSecurity.Concrete.SecretGuessObservation
end
end
-- ==== merged from ClaudeWCT_GuessV2_WCTCoords ====
section

section
namespace ClaudeWCT.Guess
section Slots
variable {κ τ : Type}
def Covered (Exp : κ → (τ → ℕ) → Prop) (u : κ → τ → ℕ) (k : κ) (t : τ) : Prop :=
  ∃ d, Exp k d ∧ u k t ≤ d t
theorem no_exposure_of_uncovered_zero {Exp : κ → (τ → ℕ) → Prop} {u : κ → τ → ℕ} {k : κ} {t : τ}
    (h : ¬Covered Exp u k t) (hu : u k t = 0) : ∀ d, ¬Exp k d := by
  intro d hd
  exact h ⟨d, hd, by rw [hu]; exact Nat.zero_le _⟩
theorem uncovered_of_no_exposure {Exp : κ → (τ → ℕ) → Prop} {u : κ → τ → ℕ} {k : κ}
    (h : ∀ d, ¬Exp k d) (t : τ) : ¬Covered Exp u k t := by
  rintro ⟨d, hd, -⟩
  exact h d hd
theorem two_probed [Fintype τ] [DecidableEq τ] (v : τ → ℕ) {s w : ℕ} (hsum : ∑ t, v t = s) (hle : ∀ t, v t ≤ w)
    (hws : w < s) : ∃ t t', t ≠ t' ∧ 1 ≤ v t ∧ 1 ≤ v t' := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t, ht⟩ : ∃ t, 1 ≤ v t := by
    by_contra h0
    push Not at h0
    have : ∑ t, v t = 0 := Finset.sum_eq_zero fun t _ => by have := h0 t; omega
    omega
  have hz : ∀ t' ∈ (Finset.univ : Finset τ), t' ≠ t → v t' = 0 := by
    intro t' _ hne
    have := hcon t t' (Ne.symm hne) ht
    omega
  have hs := Finset.sum_eq_single_of_mem t (Finset.mem_univ t) hz
  have := hle t
  omega
theorem three_way [Fintype τ] [DecidableEq κ] [DecidableEq τ] (Exp : κ → (τ → ℕ) → Prop) (u : κ → τ → ℕ) {s w : ℕ}
    (hsum : ∀ k, ∑ t, u k t = s) (hle : ∀ k t, u k t ≤ w) (hws : w < s) :
    (∀ k t, Covered Exp u k t) ∨
      (∃ k t, ¬Covered Exp u k t ∧ 1 ≤ u k t ∧ ∀ k' t', (k', t') ≠ (k, t) → Covered Exp u k' t') ∨
      (∃ k t k' t', (k, t) ≠ (k', t') ∧ ¬Covered Exp u k t ∧ 1 ≤ u k t ∧
        ¬Covered Exp u k' t' ∧ 1 ≤ u k' t') := by
  have hpair_of_unexposed : ∀ k, (∀ d, ¬Exp k d) →
      ∃ k t k' t', (k, t) ≠ (k', t') ∧ ¬Covered Exp u k t ∧ 1 ≤ u k t ∧
        ¬Covered Exp u k' t' ∧ 1 ≤ u k' t' := by
    intro k hk
    obtain ⟨t, t', hne, h1, h2⟩ := two_probed (u k) (hsum k) (hle k) hws
    refine ⟨k, t, k, t', fun h => hne (Prod.ext_iff.mp h).2, uncovered_of_no_exposure hk t, h1,
      uncovered_of_no_exposure hk t', h2⟩
  by_cases hall : ∀ k t, Covered Exp u k t
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨k0, t0, h0⟩ := hall
  rcases Nat.eq_zero_or_pos (u k0 t0) with hz0 | hp0
  · exact Or.inr (hpair_of_unexposed k0 (no_exposure_of_uncovered_zero h0 hz0))
  by_cases hrest : ∀ k' t', (k', t') ≠ (k0, t0) → Covered Exp u k' t'
  · exact Or.inl ⟨k0, t0, h0, hp0, hrest⟩
  right
  push Not at hrest
  obtain ⟨k1, t1, hne, h1⟩ := hrest
  rcases Nat.eq_zero_or_pos (u k1 t1) with hz1 | hp1
  · exact hpair_of_unexposed k1 (no_exposure_of_uncovered_zero h1 hz1)
  · exact ⟨k0, t0, k1, t1, Ne.symm hne, h0, hp0, h1, hp1⟩
theorem near_exposed {Exp : κ → (τ → ℕ) → Prop} {u : κ → τ → ℕ} {s w : ℕ} [Fintype τ] [DecidableEq τ]
    (hsum : ∀ k, ∑ t, u k t = s) (hle : ∀ k t, u k t ≤ w) (hws : w < s) {k : κ} {t : τ}
    (hrest : ∀ k' t', (k', t') ≠ (k, t) → Covered Exp u k' t') : ∃ d, Exp k d := by
  obtain ⟨t1, t2, hne, -, -⟩ := two_probed (u k) (hsum k) (hle k) hws
  by_cases h1 : t1 = t
  · subst h1
    obtain ⟨d, hd, -⟩ := hrest k t2 (fun h => hne (Prod.ext_iff.mp h).2.symm)
    exact ⟨d, hd⟩
  · obtain ⟨d, hd, -⟩ := hrest k t1 (fun h => h1 (Prod.ext_iff.mp h).2)
    exact ⟨d, hd⟩
end Slots
end ClaudeWCT.Guess
end
section
namespace ClaudeWCT.Guess
open OracleComp OracleSpec
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
abbrev ChainAddr := Fin (2 ^ 31) × Fin 9 × Fin 128 × Fin 6
abbrev GCoord := ChainAddr × Fin 4
def chainOf (N : HashOutput) (k : Fin 9) (t : Fin 6) : ChainAddr :=
  (⟨WCT9.digestIndex N, WCT9.digestIndex_lt _⟩, k, child N k, t)
theorem chainOf_injective (N : HashOutput) {k k' : Fin 9} {t t' : Fin 6}
    (h : chainOf N k t = chainOf N k' t') : k = k' ∧ t = t' := by
  simp only [chainOf, Prod.mk.injEq] at h
  exact ⟨h.2.1, h.2.2.2⟩
def deficit (N : HashOutput) (k : Fin 9) (t : Fin 6) : Nat := wordDigit (rank N k) t
theorem deficit_le (N : HashOutput) (k : Fin 9) (t : Fin 6) : deficit N k t ≤ 4 := wordDigit_le_four _ _
theorem deficit_sum (N : HashOutput) (k : Fin 9) : ∑ t, deficit N k t = 7 := wordStep_count _
/-- Witness stack: the probe is the FTS step input in either format (G chains 1, 3: `value | header | 0 | 0`). -/
def probeInput (a : ChainAddr) (p : Fin 4) (c : Digest) : HashInput :=
  WCT9.ftsChainInputW a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val p.val c
theorem probeInput_length (a : ChainAddr) (p : Fin 4) (c : Digest) : (probeInput a p c).length = 64 :=
  WCT9.ftsChainInputW_length _ _ _ _ _ _
theorem pad64_wctChainInput (index coord selected i step : Nat) (value : Digest) :
    pad64 (WCT9.chainInput index coord selected i step value) = WCT9.chainInput index coord selected i step value := by
  simp [pad64, WCT9.chainInput, zero16, bytesLE_length]
theorem pad64_probeInput (a : ChainAddr) (p : Fin 4) (c : Digest) : pad64 (probeInput a p c) = probeInput a p c :=
  WCT9.ftsChainInputW_padded _ _ _ _ _ _
def hdrBlock (input : HashInput) : HashInput := (input.drop 16).take 16
theorem chainInput_split (index coord selected i step : Nat) (value : Digest) :
    WCT9.chainInput index coord selected i step value =
      zero16 ++ (bytesLE 16 (ftsChainHeader index coord selected i step) ++
        (zero16 ++ bytesLE 16 value)) := by
  simp [WCT9.chainInput, List.append_assoc]
theorem hdrBlock_wctChainInput (index coord selected i step : Nat) (value : Digest) :
    hdrBlock (WCT9.chainInput index coord selected i step value) =
      bytesLE 16 (ftsChainHeader index coord selected i step) := by
  rw [chainInput_split, hdrBlock, List.drop_left' (by simp [zero16])]
  exact List.take_left' (bytesLE_length _ _)
theorem hdrBlock_ftsChainInputW (index coord selected i step : Nat) (value : Digest) :
    hdrBlock (WCT9.ftsChainInputW index coord selected i step value) =
      bytesLE 16 (ftsChainHeader index coord selected i step) := by
  cases hG : ftsIsG i
  · rw [WCT9.ftsChainInputW_F hG]; exact hdrBlock_wctChainInput _ _ _ _ _ _
  · rw [WCT9.ftsChainInputW_G hG, hdrBlock, List.append_assoc, List.append_assoc,
      List.drop_left' (bytesLE_length _ _)]
    exact List.take_left' (bytesLE_length _ _)
theorem hdrBlock_probeInput (a : ChainAddr) (p : Fin 4) (c : Digest) :
    hdrBlock (probeInput a p c) = bytesLE 16 (ftsChainHeader a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val p.val) :=
  hdrBlock_ftsChainInputW _ _ _ _ _ _
theorem wctHeader_toNat' (tag lay tree position index : Nat) :
    (wctHeader tag lay tree position index).toNat =
      1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + (tree / 2 ^ 32 % 256) * 2 ^ 24 +
        position % 2 ^ 32 * 2 ^ 32 + tree % 2 ^ 32 * 2 ^ 64 + index % 2 ^ 32 * 2 ^ 96 := by
  unfold wctHeader
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
  have h2 := Nat.mod_lt lay (show 0 < 256 by decide)
  have h3 := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have h4 := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have h5 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h6 := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  norm_num only at h1 h2 h3 h4 h5 h6 ⊢
  omega
def tagByte (h : BitVec 128) : Nat := h.toNat / 2 ^ 8 % 256
theorem tagByte_wctHeader (tag lay tree position index : Nat) :
    tagByte (wctHeader tag lay tree position index) = tag % 256 := by
  unfold tagByte
  rw [wctHeader_toNat']
  have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
  have h2 := Nat.mod_lt lay (show 0 < 256 by decide)
  have h3 := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have h4 := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have h5 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h6 := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  norm_num only at h1 h2 h3 h4 h5 h6 ⊢
  omega
theorem tagByte_header (tag lay tree position index : Nat) :
    tagByte (header tag lay tree position index) = tag % 256 := by
  unfold tagByte header
  rw [BitVec.toNat_ofNat]
  have key : ∀ R : Nat, (1 + tag % 256 * 2 ^ 8 + R * 2 ^ 16) % 2 ^ 128 / 2 ^ 8 % 256 = tag % 256 := by
    intro R
    have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
    omega
  have e : ∀ x : Nat, x % 2 ^ 16 = 0 →
      1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + (tree / 2 ^ 32 % 256) * 2 ^ 24 + x =
        1 + tag % 256 * 2 ^ 8 + (lay % 256 + (tree / 2 ^ 32 % 256) * 2 ^ 8 + x / 2 ^ 16) * 2 ^ 16 := by
    intro x hx
    omega
  split_ifs
  · rw [e _ (by omega)]
    exact key _
  · rw [e _ (by omega)]
    exact key _
theorem chainHeader_inj' {a a' : ChainAddr} {p p' : Fin 4}
    (h : ftsChainHeader a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val p.val =
      ftsChainHeader a'.1.val a'.2.1.val a'.2.2.1.val a'.2.2.2.val p'.val) : a = a' ∧ p = p' := by
  obtain ⟨⟨i, hi⟩, ⟨k, hk⟩, ⟨j, hj⟩, ⟨t, ht⟩⟩ := a
  obtain ⟨⟨i', hi'⟩, ⟨k', hk'⟩, ⟨j', hj'⟩, ⟨t', ht'⟩⟩ := a'
  obtain ⟨p, hp⟩ := p
  obtain ⟨p', hp'⟩ := p'
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := ftsChainHeaderP_injective hi (by omega) hj (by omega) (by omega)
    hi' (by omega) hj' (by omega) (by omega) h
  exact ⟨rfl, rfl⟩
theorem probeInput_injective {a a' : ChainAddr} {p p' : Fin 4} {c c' : Digest}
    (h : probeInput a p c = probeInput a' p' c') : a = a' ∧ p = p' ∧ c = c' := by
  have hh := congrArg hdrBlock h
  rw [hdrBlock_probeInput, hdrBlock_probeInput] at hh
  obtain ⟨rfl, rfl⟩ := chainHeader_inj' (bytesLE_injective hh)
  refine ⟨rfl, rfl, ?_⟩
  unfold probeInput at h
  cases hG : ftsIsG a.2.2.2.val
  · rw [WCT9.ftsChainInputW_F hG, WCT9.ftsChainInputW_F hG, chainInput_split, chainInput_split] at h
    have h1 := List.append_cancel_left h
    have h2 := List.append_cancel_left h1
    exact bytesLE_injective (List.append_cancel_left h2)
  · rw [WCT9.ftsChainInputW_G hG, WCT9.ftsChainInputW_G hG] at h
    simp only [List.append_assoc] at h
    exact bytesLE_injective (List.append_inj h (by simp only [bytesLE_length])).1
noncomputable def decodeProbe (x : HashInput) : Option (GCoord × Digest) :=
  haveI := Classical.propDecidable (∃ q : GCoord × Digest, x = probeInput q.1.1 q.1.2 q.2)
  if h : ∃ q : GCoord × Digest, x = probeInput q.1.1 q.1.2 q.2 then some (Classical.choose h) else none
theorem decodeProbe_probeInput (a : ChainAddr) (p : Fin 4) (c : Digest) :
    decodeProbe (probeInput a p c) = some ((a, p), c) := by
  have h : ∃ q : GCoord × Digest, probeInput a p c = probeInput q.1.1 q.1.2 q.2 := ⟨((a, p), c), rfl⟩
  rw [decodeProbe, dif_pos h]
  obtain ⟨h1, h2, h3⟩ := probeInput_injective (Classical.choose_spec h).symm
  exact congrArg some (Prod.ext (Prod.ext h1 h2) h3)
theorem eq_of_decodeProbe {x : HashInput} {q : GCoord × Digest} (h : decodeProbe x = some q) :
    x = probeInput q.1.1 q.1.2 q.2 := by
  unfold decodeProbe at h
  split at h
  · rename_i hx
    cases h
    exact Classical.choose_spec hx
  · cases h
theorem decodeProbe_eq_none {x : HashInput} :
    decodeProbe x = none ↔ ∀ a p c, x ≠ probeInput a p c := by
  constructor
  · intro h a p c hx
    rw [hx, decodeProbe_probeInput] at h
    cases h
  · intro h
    rw [decodeProbe, dif_neg]
    rintro ⟨q, hq⟩
    exact h q.1.1 q.1.2 q.2 hq
theorem ftsChainHeader_byte0 (index coord selected i step : Nat) :
    128 ≤ (ftsChainHeader index coord selected i step).toNat % 256 := by
  rw [ftsChainHeader_toNat, ftsChainLow_byte0]
  omega
theorem decodeProbe_of_hdrBlock {x : HashInput} {h : BitVec 128} (hx : hdrBlock x = bytesLE 16 h)
    (ht : h.toNat % 256 < 128) : decodeProbe x = none := by
  rw [decodeProbe_eq_none]
  intro a p c he
  rw [he, hdrBlock_probeInput] at hx
  have := bytesLE_injective hx
  have hb := ftsChainHeader_byte0 a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val p.val
  rw [this] at hb
  omega
theorem ftsChainHeader_byte1 (index coord selected i step : Nat) :
    (ftsChainHeader index coord selected i step).toNat / 256 % 256 < 4 := by
  rw [ftsChainHeader_toNat]
  unfold ftsChainLow
  have := Nat.mod_lt i (show 0 < 8 by decide)
  have := Nat.mod_lt step (show 0 < 4 by decide)
  have := Nat.mod_lt coord (show 0 < 16 by decide)
  have := Nat.mod_lt selected (show 0 < 128 by decide)
  omega
/-- Headers whose tag byte is at least 4 are never chain probes (FTS chain headers carry the step `< 4` there). -/
theorem decodeProbe_of_hdrBlock_tag {x : HashInput} {h : BitVec 128} (hx : hdrBlock x = bytesLE 16 h)
    (ht : 4 ≤ h.toNat / 256 % 256) : decodeProbe x = none := by
  rw [decodeProbe_eq_none]
  intro a p c he
  rw [he, hdrBlock_probeInput] at hx
  have := bytesLE_injective hx
  have hb := ftsChainHeader_byte1 a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val p.val
  rw [this] at hb
  omega
/-- FTS seed of chain `a` (stage-A family seed; agrees with `WCT9.seed` by `rfl`). -/
def seedOf (A : Correctness.Answers) (a : ChainAddr) : Digest :=
  ClaudeWCT.Arith.familyEval (List.ofFn (WCT9.ftsCoef A a.1.val a.2.1.val)) (WCT9.ftsPoint a.2.2.1.val a.2.2.2.val)
def chainValue (A : Correctness.Answers) (a : ChainAddr) (p : Nat) : Digest :=
  evalWithAnswerFn A (WCT9.chain a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val 0 p (seedOf A a))
def honestProbe (A : Correctness.Answers) (c : GCoord) : HashInput := probeInput c.1 c.2 (chainValue A c.1 c.2.val)
def ChainCovered (X : List HashOutput) (a : ChainAddr) (p : Nat) : Prop :=
  ∃ out ∈ X, WCT9.digestIndex out = a.1.val ∧ child out a.2.1 = a.2.2.1 ∧ 4 - wordDigit (rank out a.2.1) a.2.2.2 ≤ p
def SlotCovered (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 6) : Prop :=
  ∃ out ∈ X, WCT9.digestIndex out = WCT9.digestIndex N ∧ child out k = child N k ∧
    deficit N k t ≤ wordDigit (rank out k) t
theorem ChainCovered.mono_pos {X : List HashOutput} {a : ChainAddr} {p p' : Nat} (h : p ≤ p')
    (hc : ChainCovered X a p) : ChainCovered X a p' := by
  obtain ⟨out, hout, h1, h2, h3⟩ := hc
  exact ⟨out, hout, h1, h2, h3.trans h⟩
theorem ChainCovered.mono_log {X Y : List HashOutput} {a : ChainAddr} {p : Nat} (h : ∀ x ∈ X, x ∈ Y)
    (hc : ChainCovered X a p) : ChainCovered Y a p := by
  obtain ⟨out, hout, h1, h2, h3⟩ := hc
  exact ⟨out, h out hout, h1, h2, h3⟩
theorem slotCovered_iff_chainCovered (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 6) :
    SlotCovered X N k t ↔ ChainCovered X (chainOf N k t) (4 - deficit N k t) := by
  have hu := deficit_le N k t
  constructor
  · rintro ⟨out, hout, h1, h2, h3⟩
    exact ⟨out, hout, h1, h2, by simp only [chainOf]; omega⟩
  · rintro ⟨out, hout, h1, h2, h3⟩
    have hd := wordDigit_le_four (rank out k) t
    exact ⟨out, hout, h1, h2, by simp only [chainOf] at h3; omega⟩
theorem slotCovered_iff_covered (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 6) :
    SlotCovered X N k t ↔
      Covered (fun k d => ∃ out ∈ X, WCT9.digestIndex out = WCT9.digestIndex N ∧ child out k = child N k ∧
        d = fun t => wordDigit (rank out k) t) (deficit N) k t := by
  constructor
  · rintro ⟨out, hout, h1, h2, h3⟩
    exact ⟨_, ⟨out, hout, h1, h2, rfl⟩, h3⟩
  · rintro ⟨d, ⟨out, hout, h1, h2, rfl⟩, h3⟩
    exact ⟨out, hout, h1, h2, h3⟩
theorem caseC_slots (X : List HashOutput) (N : HashOutput) :
    (∀ k t, SlotCovered X N k t) ∨
      (∃ k t, 1 ≤ deficit N k t ∧ ¬ChainCovered X (chainOf N k t) (4 - deficit N k t) ∧
        ∀ k' t', (k', t') ≠ (k, t) → SlotCovered X N k' t') ∨
      (∃ k t k' t', (k, t) ≠ (k', t') ∧
        1 ≤ deficit N k t ∧ ¬ChainCovered X (chainOf N k t) (4 - deficit N k t) ∧
        1 ≤ deficit N k' t' ∧ ¬ChainCovered X (chainOf N k' t') (4 - deficit N k' t')) := by
  have h := three_way (fun k d => ∃ out ∈ X, WCT9.digestIndex out = WCT9.digestIndex N ∧
      child out k = child N k ∧ d = fun t => wordDigit (rank out k) t) (deficit N) (s := 7) (w := 4)
    (deficit_sum N) (deficit_le N) (by decide)
  simp only [← slotCovered_iff_covered, slotCovered_iff_chainCovered] at h
  rcases h with h | ⟨k, t, h1, h2, h3⟩ | ⟨k, t, k', t', hne, h1, h2, h3, h4⟩
  · exact Or.inl fun k t => (slotCovered_iff_chainCovered X N k t).mpr (h k t)
  · exact Or.inr (Or.inl ⟨k, t, h2, h1, fun k' t' hne => (slotCovered_iff_chainCovered X N k' t').mpr (h3 k' t' hne)⟩)
  · exact Or.inr (Or.inr ⟨k, t, k', t', hne, h2, h1, h4, h3⟩)
theorem chainOf_ne {N : HashOutput} {k k' : Fin 9} {t t' : Fin 6} (h : (k, t) ≠ (k', t')) :
    chainOf N k t ≠ chainOf N k' t' := by
  intro he
  obtain ⟨rfl, rfl⟩ := chainOf_injective N he
  exact h rfl
theorem queried_shortHash (A : Correctness.Answers) (input : HashInput) :
    Security.SourceReplay.queried A (shortHash input) = [.inl (.inr (pad64 input))] := by
  unfold shortHash publicHash
  rw [Security.SourceReplay.queried_bind]
  have h : Security.SourceReplay.queried A (Spec.query (.inl (.inr (pad64 input))) : M HashOutput) =
      [.inl (.inr (pad64 input))] := by
    rw [show (Spec.query (.inl (.inr (pad64 input))) : M HashOutput) =
      (liftM (Spec.query (.inl (.inr (pad64 input)))) >>= pure) from (bind_pure _).symm,
      Security.SourceReplay.queried_query_bind]
    rfl
  rw [h]
  rfl
theorem queried_projHash (A : Correctness.Answers) (high : Bool) (input : HashInput) :
    Security.SourceReplay.queried A (projHash high input) = [.inl (.inr (pad64 input))] := by
  unfold projHash publicHash
  rw [Security.SourceReplay.queried_bind]
  have h : Security.SourceReplay.queried A (Spec.query (.inl (.inr (pad64 input))) : M HashOutput) =
      [.inl (.inr (pad64 input))] := by
    rw [show (Spec.query (.inl (.inr (pad64 input))) : M HashOutput) =
      (liftM (Spec.query (.inl (.inr (pad64 input)))) >>= pure) from (bind_pure _).symm,
      Security.SourceReplay.queried_query_bind]
    rfl
  rw [h]
  rfl
theorem queried_chain_first (A : Correctness.Answers) (index coord selected i start count : Nat) (value : Digest)
    (hc : 1 ≤ count) :
    (.inl (.inr (WCT9.ftsChainInputW index coord selected i start value)) : Spec.Domain) ∈
      Security.SourceReplay.queried A (WCT9.chain index coord selected i start count value) := by
  obtain ⟨n, rfl⟩ : ∃ n, count = n + 1 := ⟨count - 1, by omega⟩
  unfold WCT9.chain
  rw [List.range'_succ, List.foldlM_cons, Security.SourceReplay.queried_bind, queried_projHash, WCT9.ftsChainInputW_padded]
  exact List.mem_append_left _ (List.mem_singleton_self _)
theorem queried_mapM_mem {α β : Type} (A : Correctness.Answers) (f : α → M β) (l : List α) (x : α) (hx : x ∈ l)
    (q : Spec.Domain) (hq : q ∈ Security.SourceReplay.queried A (f x)) : q ∈ Security.SourceReplay.queried A (l.mapM f) := by
  induction l with
  | nil => cases hx
  | cons y rest ih =>
      rw [List.mapM_cons, Security.SourceReplay.queried_bind]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_append_left _ hq
      · apply List.mem_append_right
        rw [Security.SourceReplay.queried_bind]
        exact List.mem_append_left _ (ih hx)
theorem recoverCoordinate_probe (A : Correctness.Answers) (sig : WCT9.Signature) (index : Nat) (output : HashOutput)
    (coord : WCT9.Coord) (prev : Digest × Digest) (t : Fin 6) (hu : 1 ≤ wordDigit (rank output coord) t) :
    (.inl (.inr (WCT9.ftsChainInputW index coord.val (child output coord).val t.val (4 - wordDigit (rank output coord) t)
        ((sig.openings coord).values t))) : Spec.Domain) ∈
      Security.SourceReplay.queried A (WCT9.recoverCoordinate sig index output coord prev) := by
  unfold WCT9.recoverCoordinate
  rw [Security.SourceReplay.queried_bind]
  apply List.mem_append_left
  exact queried_mapM_mem A _ (List.finRange 6) t (List.mem_finRange t) _
    (queried_chain_first A _ _ _ _ _ _ _ hu)
end ClaudeWCT.Guess
end
end
-- ==== merged from ClaudeWCT_GuessV2_FamilyEngine ====
section

/-!
# The FTS seed-family world (campaign X1, stage A)

Hidden values of the case-C world: one coefficient vector `K f : Fin 54 → Digest` per FTS family
`f = (index, coord)` and the step-1..3 labels `g12`. The world's table `GCoord → Digest` is `phi K g12`: the seed
`(a, 0)` is `familyEval (K (famOf a)) (ptOf a)`, the steps are `g12`. The lazy engine keeps today's `State` (its
`allowed` sets record every trial and disclosure); the posterior of family `f` is `famPostA allowed f`, the vectors
whose seeds lie in the allowed sets, and the step labels stay a product table (`labelAllowed`).

* `sampler`: trial and disclosure laws (`trialBy` / `discloseBy` on the two tables).
* `fam_posterior`, `fam_erasure`: the eager world (`hiddenLaw`, then `fixedRun` on `phi K g12`) is the lazy run.
* `Inv`, `Bad`, `hazard`: per-family posteriors are `famPost` with at most 53 known points while at most 51
  seeds per family are retired without a guess (`¬Bad`) and at most one guess was made; then a trial at a fresh seed
  hits with probability at most `(2^128 - budget)⁻¹` (A1's `fam_hazard_prob`), labels as today.
-/

namespace ClaudeWCT.Guess.Fam
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 (Digest)
open SphincsSecurity.Concrete SphincsSecurity.Concrete.SecretGuessObservation SphincsSecurity.Concrete.UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

abbrev FamIdx := Fin (2 ^ 31) × Fin 9
abbrev Coefs := Fin 54 → Digest
abbrev LabelIdx := ChainAddr × Fin 3
/-- The family of chain `a`. -/
def famOf (a : ChainAddr) : FamIdx := (a.1, a.2.1)
/-- The evaluation point of chain `a` in its family. -/
def ptOf (a : ChainAddr) : Nat := WCT9.ftsPoint a.2.2.1.val a.2.2.2.val
/-- Member `(j, t)` of family `f`. -/
def member (f : FamIdx) (j : Fin 128) (t : Fin 6) : ChainAddr := (f.1, f.2, j, t)
/-- The seed of chain `a` under coefficient vector `K`. -/
def seedK (K : Coefs) (a : ChainAddr) : Digest := ClaudeWCT.Arith.familyEval (List.ofFn K) (ptOf a)
theorem famOf_member (f : FamIdx) (j : Fin 128) (t : Fin 6) : famOf (member f j t) = f := rfl
theorem member_famOf (a : ChainAddr) : member (famOf a) a.2.2.1 a.2.2.2 = a := rfl
theorem ptOf_member (f : FamIdx) (j : Fin 128) (t : Fin 6) : ptOf (member f j t) = WCT9.ftsPoint j.val t.val := rfl
theorem ftsPoint_lt (j : Fin 128) (t : Fin 6) : WCT9.ftsPoint j.val t.val < 1024 := by
  unfold WCT9.ftsPoint WCT9.ftsOrdinal; omega
theorem ftsPoint_inj {j j' : Fin 128} {t t' : Fin 6} (h : WCT9.ftsPoint j.val t.val = WCT9.ftsPoint j'.val t'.val) :
    j = j' ∧ t = t' := by
  unfold WCT9.ftsPoint WCT9.ftsOrdinal at h
  have := t.isLt; have := t'.isLt
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
/-- Posterior of family `f`: coefficient vectors whose seeds all lie in the allowed sets. -/
noncomputable def famPostA (allowed : GCoord → Finset Digest) (f : FamIdx) : Finset Coefs :=
  Finset.univ.filter fun K => ∀ j t, seedK K (member f j t) ∈ allowed (member f j t, 0)
theorem mem_famPostA (allowed : GCoord → Finset Digest) (f : FamIdx) (K : Coefs) :
    K ∈ famPostA allowed f ↔ ∀ j t, seedK K (member f j t) ∈ allowed (member f j t, 0) := by
  simp only [famPostA, Finset.mem_filter, Finset.mem_univ, true_and]
/-- The step-label table (`(a, q)` is the label at step `q + 1`). -/
def labelAllowed (allowed : GCoord → Finset Digest) (l : LabelIdx) : Finset Digest := allowed (l.1, l.2.succ)
/-- The world's table from the hidden coefficients and labels. -/
def phi (K : FamIdx → Coefs) (g12 : LabelIdx → Digest) (c : GCoord) : Digest :=
  if h : c.2 = 0 then seedK (K (famOf c.1)) c.1 else g12 (c.1, c.2.pred h)
theorem phi_seed (K : FamIdx → Coefs) (g12 : LabelIdx → Digest) (a : ChainAddr) :
    phi K g12 (a, 0) = seedK (K (famOf a)) a := rfl
theorem phi_label (K : FamIdx → Coefs) (g12 : LabelIdx → Digest) (l : LabelIdx) :
    phi K g12 (l.1, l.2.succ) = g12 l := by
  unfold phi
  rw [dif_neg (Fin.succ_ne_zero _)]
  simp
/-- The eager hidden law given the allowed sets. -/
noncomputable def hiddenLaw (allowed : GCoord → Finset Digest) : SPMF (GCoord → Digest) :=
  complete (famPostA allowed) >>= fun K => complete (labelAllowed allowed) >>= fun g12 => pure (phi K g12)
/-- Trial and disclosure laws of the family world. -/
noncomputable def sampler (Memory : Type) : Sampler GCoord Digest Memory where
  trialLaw state c v :=
    if h : c.2 = 0 then trialBy (famPostA state.allowed) (famOf c.1) (fun K => decide (seedK K c.1 = v))
    else trialBy (labelAllowed state.allowed) (c.1, c.2.pred h) (fun x => decide (x = v))
  discloseLaw state c :=
    if h : c.2 = 0 then discloseBy (famPostA state.allowed) (famOf c.1) (fun K => seedK K c.1)
    else discloseBy (labelAllowed state.allowed) (c.1, c.2.pred h) id

/-! ### Restriction lemmas -/

theorem member_ne_of_famOf {f : FamIdx} {a : ChainAddr} (h : famOf a ≠ f) (j : Fin 128) (t : Fin 6) :
    member f j t ≠ a := fun he => h (he ▸ famOf_member f j t)
theorem label_ne_seed (l : LabelIdx) (a : ChainAddr) : ((l.1, l.2.succ) : GCoord) ≠ (a, 0) :=
  fun he => Fin.succ_ne_zero _ (Prod.mk.inj he).2
theorem labelIdx_eq_of_ne {c : GCoord} (hc : c.2 ≠ 0) {l : LabelIdx} (hl : l ≠ (c.1, c.2.pred hc)) :
    ((l.1, l.2.succ) : GCoord) ≠ c := by
  intro he
  apply hl
  have h1 : l.1 = c.1 := congrArg Prod.fst he
  have h2 : l.2.succ = c.2 := congrArg Prod.snd he
  refine Prod.ext h1 ?_
  rw [← Fin.succ_inj, Fin.succ_pred]
  exact h2
theorem label_succ_pred {c : GCoord} (hc : c.2 ≠ 0) : ((c.1, (c.2.pred hc).succ) : GCoord) = c := by
  rw [Fin.succ_pred]
theorem seed_ne_of_famOf {f : FamIdx} {a : ChainAddr} (h : f ≠ famOf a) (j : Fin 128) (t : Fin 6) :
    ((member f j t, 0) : GCoord) ≠ (a, 0) := fun he =>
  member_ne_of_famOf (Ne.symm h) j t (Prod.mk.inj he).1
theorem seed_ne_label (f : FamIdx) (j : Fin 128) (t : Fin 6) {c : GCoord} (hc : c.2 ≠ 0) :
    ((member f j t, 0) : GCoord) ≠ c := fun he => hc ((congrArg Prod.snd he).symm)
theorem famPostA_restrict_seed (allowed : GCoord → Finset Digest) (a : ChainAddr) (v : Digest) (hit : Bool) :
    famPostA (restrict allowed (a, 0) v hit) =
      restrictBy (famPostA allowed) (famOf a) (fun K => decide (seedK K a = v)) hit := by
  funext f
  by_cases hf : f = famOf a
  · subst hf
    ext K
    rw [mem_restrictBy_self]
    simp only [famPostA, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨fun j t => ?_, ?_⟩
      · have hj := h j t
        by_cases he : ((member (famOf a) j t, 0) : GCoord) = (a, 0)
        · rw [he, restrict, Function.update_self, Finset.mem_filter] at hj
          rw [he]; exact hj.1
        · rwa [restrict, Function.update_of_ne he] at hj
      · have hj := h a.2.2.1 a.2.2.2
        rw [member_famOf, restrict, Function.update_self, Finset.mem_filter] at hj
        exact hj.2
    · rintro ⟨h, hh⟩ j t
      by_cases he : ((member (famOf a) j t, 0) : GCoord) = (a, 0)
      · have hm : member (famOf a) j t = a := (Prod.mk.inj he).1
        rw [he, restrict, Function.update_self, Finset.mem_filter]
        have h1 := h j t
        rw [hm] at h1 ⊢
        exact ⟨h1, hh⟩
      · rw [restrict, Function.update_of_ne he]; exact h j t
  · rw [restrictBy_other _ _ _ _ hf]
    ext K
    simp only [famPostA, Finset.mem_filter, Finset.mem_univ, true_and]
    refine forall_congr' fun j => forall_congr' fun t => ?_
    rw [restrict, Function.update_of_ne (seed_ne_of_famOf hf j t)]
theorem labelAllowed_restrict_seed (allowed : GCoord → Finset Digest) (a : ChainAddr) (v : Digest) (hit : Bool) :
    labelAllowed (restrict allowed (a, 0) v hit) = labelAllowed allowed := by
  funext l
  simp only [labelAllowed, restrict, Function.update_of_ne (label_ne_seed l a)]
theorem famPostA_restrict_label (allowed : GCoord → Finset Digest) (c : GCoord) (hc : c.2 ≠ 0) (v : Digest)
    (hit : Bool) : famPostA (restrict allowed c v hit) = famPostA allowed := by
  funext f
  ext K
  simp only [famPostA, Finset.mem_filter, Finset.mem_univ, true_and]
  refine forall_congr' fun j => forall_congr' fun t => ?_
  rw [restrict, Function.update_of_ne (seed_ne_label f j t hc)]
theorem labelAllowed_restrict_label (allowed : GCoord → Finset Digest) (c : GCoord) (hc : c.2 ≠ 0) (v : Digest)
    (hit : Bool) : labelAllowed (restrict allowed c v hit) =
      restrictBy (labelAllowed allowed) (c.1, c.2.pred hc) (fun x => decide (x = v)) hit := by
  funext l
  by_cases hl : l = (c.1, c.2.pred hc)
  · subst hl
    ext x
    rw [mem_restrictBy_self]
    simp only [labelAllowed, label_succ_pred hc, restrict, Function.update_self, Finset.mem_filter]
  · rw [restrictBy_other _ _ _ _ hl]
    simp only [labelAllowed, restrict, Function.update_of_ne (labelIdx_eq_of_ne hc hl)]
theorem famPostA_disclose_seed (allowed : GCoord → Finset Digest) (a : ChainAddr) (value : Digest)
    (hv : value ∈ allowed (a, 0)) :
    famPostA (discloseTableValue allowed (a, 0) value) =
      restrictBy (famPostA allowed) (famOf a) (fun K => seedK K a) value := by
  funext f
  by_cases hf : f = famOf a
  · subst hf
    ext K
    rw [mem_restrictBy_self]
    simp only [famPostA, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have ha := h a.2.2.1 a.2.2.2
      rw [member_famOf, discloseTableValue, Function.update_self, Finset.mem_singleton] at ha
      refine ⟨fun j t => ?_, ha.symm⟩
      have hj := h j t
      by_cases he : ((member (famOf a) j t, 0) : GCoord) = (a, 0)
      · have hm : member (famOf a) j t = a := (Prod.mk.inj he).1
        rw [hm, ha]; exact hv
      · rwa [discloseTableValue, Function.update_of_ne he] at hj
    · rintro ⟨h, hh⟩ j t
      by_cases he : ((member (famOf a) j t, 0) : GCoord) = (a, 0)
      · have hm : member (famOf a) j t = a := (Prod.mk.inj he).1
        rw [he, discloseTableValue, Function.update_self, Finset.mem_singleton, hm, hh]
      · rw [discloseTableValue, Function.update_of_ne he]; exact h j t
  · rw [restrictBy_other _ _ _ _ hf]
    ext K
    simp only [famPostA, Finset.mem_filter, Finset.mem_univ, true_and]
    refine forall_congr' fun j => forall_congr' fun t => ?_
    rw [discloseTableValue, Function.update_of_ne (seed_ne_of_famOf hf j t)]
theorem labelAllowed_disclose_seed (allowed : GCoord → Finset Digest) (a : ChainAddr) (value : Digest) :
    labelAllowed (discloseTableValue allowed (a, 0) value) = labelAllowed allowed := by
  funext l
  simp only [labelAllowed, discloseTableValue, Function.update_of_ne (label_ne_seed l a)]
theorem famPostA_disclose_label (allowed : GCoord → Finset Digest) (c : GCoord) (hc : c.2 ≠ 0) (value : Digest) :
    famPostA (discloseTableValue allowed c value) = famPostA allowed := by
  funext f
  ext K
  simp only [famPostA, Finset.mem_filter, Finset.mem_univ, true_and]
  refine forall_congr' fun j => forall_congr' fun t => ?_
  rw [discloseTableValue, Function.update_of_ne (seed_ne_label f j t hc)]
theorem labelAllowed_disclose_label (allowed : GCoord → Finset Digest) (c : GCoord) (hc : c.2 ≠ 0) (value : Digest)
    (hv : value ∈ allowed c) :
    labelAllowed (discloseTableValue allowed c value) =
      restrictBy (labelAllowed allowed) (c.1, c.2.pred hc) id value := by
  funext l
  by_cases hl : l = (c.1, c.2.pred hc)
  · subst hl
    ext x
    rw [mem_restrictBy_self]
    simp only [labelAllowed, label_succ_pred hc, discloseTableValue, Function.update_self, Finset.mem_singleton, id]
    constructor
    · rintro rfl; exact ⟨hv, rfl⟩
    · rintro ⟨-, rfl⟩; rfl
  · rw [restrictBy_other _ _ _ _ hl]
    simp only [labelAllowed, discloseTableValue, Function.update_of_ne (labelIdx_eq_of_ne hc hl)]
/-- A disclosed seed with positive mass lies in the allowed set. -/
theorem mem_of_discloseBy_seed (allowed : GCoord → Finset Digest) (a : ChainAddr) (value : Digest)
    (h : discloseBy (famPostA allowed) (famOf a) (fun K => seedK K a) value ≠ 0) : value ∈ allowed (a, 0) := by
  obtain ⟨K, hK⟩ := discloseBy_nonempty _ _ _ _ h (famOf a)
  simp only [mem_restrictBy_self, mem_famPostA] at hK
  obtain ⟨hK1, hK2⟩ := hK
  have hm := hK1 a.2.2.1 a.2.2.2
  rw [hK2]
  exact hm
theorem mem_of_discloseBy_label (allowed : GCoord → Finset Digest) (c : GCoord) (hc : c.2 ≠ 0) (value : Digest)
    (h : discloseBy (labelAllowed allowed) (c.1, c.2.pred hc) id value ≠ 0) : value ∈ allowed c := by
  obtain ⟨x, hx⟩ := discloseBy_nonempty _ _ _ _ h (c.1, c.2.pred hc)
  rw [mem_restrictBy_self] at hx
  have hm := hx.1
  simp only [labelAllowed, label_succ_pred hc] at hm
  rw [hx.2]
  exact hm

/-! ### Conditioning the hidden law -/

theorem hiddenLaw_bind_seed {Result : Type} (allowed : GCoord → Finset Digest) (a : ChainAddr) (v : Digest)
    (next : Bool → (GCoord → Digest) → SPMF Result) :
    (hiddenLaw allowed >>= fun g => next (decide (g (a, 0) = v)) g) =
      (trialBy (famPostA allowed) (famOf a) (fun K => decide (seedK K a = v)) >>= fun hit =>
        hiddenLaw (restrict allowed (a, 0) v hit) >>= next hit) := by
  unfold hiddenLaw
  simp only [bind_assoc, pure_bind]
  simp only [famPostA_restrict_seed, labelAllowed_restrict_seed]
  exact bind_trialBy (famPostA allowed) (famOf a) (fun K => decide (seedK K a = v))
    (fun hit K => complete (labelAllowed allowed) >>= fun g12 => next hit (phi K g12))
theorem phi_label' (K : FamIdx → Coefs) (g12 : LabelIdx → Digest) (c : GCoord) (hc : c.2 ≠ 0) :
    phi K g12 c = g12 (c.1, c.2.pred hc) := by
  unfold phi
  rw [dif_neg hc]
theorem hiddenLaw_bind_label {Result : Type} (allowed : GCoord → Finset Digest) (c : GCoord) (hc : c.2 ≠ 0)
    (v : Digest) (next : Bool → (GCoord → Digest) → SPMF Result) :
    (hiddenLaw allowed >>= fun g => next (decide (g c = v)) g) =
      (trialBy (labelAllowed allowed) (c.1, c.2.pred hc) (fun x => decide (x = v)) >>= fun hit =>
        hiddenLaw (restrict allowed c v hit) >>= next hit) := by
  unfold hiddenLaw
  simp only [bind_assoc, pure_bind]
  simp only [famPostA_restrict_label allowed c hc, labelAllowed_restrict_label allowed c hc]
  calc (complete (famPostA allowed) >>= fun K => complete (labelAllowed allowed) >>= fun g12 =>
          next (decide (phi K g12 c = v)) (phi K g12))
      = (complete (famPostA allowed) >>= fun K =>
          trialBy (labelAllowed allowed) (c.1, c.2.pred hc) (fun x => decide (x = v)) >>= fun hit =>
            complete (restrictBy (labelAllowed allowed) (c.1, c.2.pred hc) (fun x => decide (x = v)) hit) >>=
              fun g12 => next hit (phi K g12)) := by
        refine bind_congr fun K => ?_
        simp only [phi_label' _ _ c hc]
        exact bind_trialBy (labelAllowed allowed) (c.1, c.2.pred hc) (fun x => decide (x = v))
          (fun hit g12 => next hit (phi K g12))
    _ = _ := RetainedObservation.bind_comm _ _ _
theorem hiddenLaw_bind_disclose_seed {Result : Type} (allowed : GCoord → Finset Digest) (a : ChainAddr)
    (next : Digest → (GCoord → Digest) → SPMF Result) :
    (hiddenLaw allowed >>= fun g => next (g (a, 0)) g) =
      (discloseBy (famPostA allowed) (famOf a) (fun K => seedK K a) >>= fun value =>
        hiddenLaw (discloseTableValue allowed (a, 0) value) >>= next value) := by
  unfold hiddenLaw
  simp only [bind_assoc, pure_bind, phi_seed]
  refine (bind_discloseBy (famPostA allowed) (famOf a) (fun K => seedK K a)
    (fun value K => complete (labelAllowed allowed) >>= fun g12 => next value (phi K g12))).trans ?_
  refine RetainedObservation.bind_congr _ _ _ fun value hv => ?_
  rw [famPostA_disclose_seed allowed a value (mem_of_discloseBy_seed allowed a value hv),
    labelAllowed_disclose_seed]
theorem hiddenLaw_bind_disclose_label {Result : Type} (allowed : GCoord → Finset Digest) (c : GCoord) (hc : c.2 ≠ 0)
    (next : Digest → (GCoord → Digest) → SPMF Result) :
    (hiddenLaw allowed >>= fun g => next (g c) g) =
      (discloseBy (labelAllowed allowed) (c.1, c.2.pred hc) id >>= fun value =>
        hiddenLaw (discloseTableValue allowed c value) >>= next value) := by
  unfold hiddenLaw
  simp only [bind_assoc, pure_bind]
  calc (complete (famPostA allowed) >>= fun K => complete (labelAllowed allowed) >>= fun g12 =>
          next (phi K g12 c) (phi K g12))
      = (complete (famPostA allowed) >>= fun K =>
          discloseBy (labelAllowed allowed) (c.1, c.2.pred hc) id >>= fun value =>
            complete (restrictBy (labelAllowed allowed) (c.1, c.2.pred hc) id value) >>=
              fun g12 => next value (phi K g12)) := by
        refine bind_congr fun K => ?_
        simp only [phi_label' _ _ c hc]
        exact bind_discloseBy (labelAllowed allowed) (c.1, c.2.pred hc) id (fun value g12 => next value (phi K g12))
    _ = (discloseBy (labelAllowed allowed) (c.1, c.2.pred hc) id >>= fun value =>
          complete (famPostA allowed) >>= fun K =>
            complete (restrictBy (labelAllowed allowed) (c.1, c.2.pred hc) id value) >>=
              fun g12 => next value (phi K g12)) := RetainedObservation.bind_comm _ _ _
    _ = _ := by
        refine RetainedObservation.bind_congr _ _ _ fun value hv => ?_
        rw [famPostA_disclose_label allowed c hc,
          labelAllowed_disclose_label allowed c hc value (mem_of_discloseBy_label allowed c hc value hv)]

/-! ### The family world is the lazy run -/

section Erasure
variable {Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
theorem fam_posterior {Result : Type} (environment : Environment auxSpec GCoord Digest Memory)
    (computation : OracleComp (World auxSpec GCoord Digest) Result) (state : State GCoord Digest Memory) :
    (hiddenLaw state.allowed >>= fun g => (fun result => (g, result)) <$> fixedRun environment g computation state) =
      (withRun environment (sampler Memory) computation state >>= fun result =>
        (fun g => (g, result)) <$> hiddenLaw result.2.allowed) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result => simp only [fixedRun, withRun, runWith_pure, pure_bind, ← bind_pure_comp]
  | query_bind input next ih =>
      rcases input with input | (⟨c, v⟩ | c)
      · simp only [fixedRun, withRun, runWith_query_bind, fixedImpl, withImpl, lazyImpl,
          StateT.run_mk, bind_map_left, map_bind, bind_assoc]
        rw [RetainedObservation.bind_comm]
        exact congrArg ((liftM (environment.auxiliary state input) : SPMF _) >>= ·)
          (funext fun answer => ih answer.1 { state with memory := answer.2 })
      · simp only [fixedRun, withRun, runWith_query_bind, fixedImpl, withImpl, StateT.run_mk, pure_bind,
          bind_map_left, bind_assoc]
        obtain ⟨a, q⟩ := c
        by_cases hq : q = 0
        · subst hq
          rw [hiddenLaw_bind_seed state.allowed a v (fun hit g =>
            (fun result => (g, result)) <$> runWith (fixedImpl environment g) (next hit)
              (afterTrial environment state (a, 0) v hit))]
          simp only [sampler, dif_pos rfl]
          exact congrArg (trialBy (famPostA state.allowed) (famOf a) (fun K => decide (seedK K a = v)) >>= ·)
            (funext fun hit => ih hit (afterTrial environment state (a, 0) v hit))
        · rw [hiddenLaw_bind_label state.allowed (a, q) hq v (fun hit g =>
            (fun result => (g, result)) <$> runWith (fixedImpl environment g) (next hit)
              (afterTrial environment state (a, q) v hit))]
          simp only [sampler, dif_neg hq]
          exact congrArg (trialBy (labelAllowed state.allowed) (a, q.pred hq) (fun x => decide (x = v)) >>= ·)
            (funext fun hit => ih hit (afterTrial environment state (a, q) v hit))
      · simp only [fixedRun, withRun, runWith_query_bind, fixedImpl, withImpl, StateT.run_mk, pure_bind,
          bind_map_left, bind_assoc]
        obtain ⟨a, q⟩ := c
        by_cases hq : q = 0
        · subst hq
          rw [hiddenLaw_bind_disclose_seed state.allowed a (fun value g =>
            (fun result => (g, result)) <$> runWith (fixedImpl environment g) (next value)
              (afterDisclosure environment state (a, 0) value))]
          simp only [sampler, dif_pos rfl]
          exact congrArg (discloseBy (famPostA state.allowed) (famOf a) (fun K => seedK K a) >>= ·)
            (funext fun value => ih value (afterDisclosure environment state (a, 0) value))
        · rw [hiddenLaw_bind_disclose_label state.allowed (a, q) hq (fun value g =>
            (fun result => (g, result)) <$> runWith (fixedImpl environment g) (next value)
              (afterDisclosure environment state (a, q) value))]
          simp only [sampler, dif_neg hq]
          exact congrArg (discloseBy (labelAllowed state.allowed) (a, q.pred hq) id >>= ·)
            (funext fun value => ih value (afterDisclosure environment state (a, q) value))
end Erasure

/-! ### Marginal laws -/

theorem restrictionWeight_update {C V : Type} [Fintype C] [DecidableEq C] [DecidableEq V]
    (allowed : C → Finset V) (c : C) (S : Finset V) (ha : ∀ c', (allowed c').Nonempty) :
    restrictionWeight allowed (Function.update allowed c S) = (S.card : ℝ≥0∞) / (allowed c).card := by
  unfold restrictionWeight
  have h1 : (∏ x, (Function.update allowed c S x).card) = S.card * ∏ x ∈ Finset.univ.erase c, (allowed x).card := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  have h2 : (∏ x, (allowed x).card) = (allowed c).card * ∏ x ∈ Finset.univ.erase c, (allowed x).card :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ c)).symm
  have hP : (∏ x ∈ Finset.univ.erase c, (allowed x).card) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun x _ => (Finset.card_pos.mpr (ha x)).ne'
  rw [h1, h2, Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_right _ _ (by exact_mod_cast hP) (ENNReal.natCast_ne_top _)
theorem trialBy_true_eq {C V : Type} [Fintype C] [DecidableEq C] [DecidableEq V] (allowed : C → Finset V) (c : C)
    (test : V → Bool) (ha : ∀ c', (allowed c').Nonempty) :
    trialBy allowed c test true = (((allowed c).filter fun x => true = test x).card : ℝ≥0∞) / (allowed c).card := by
  rw [discloseBy_apply, restrictBy, restrictionWeight_update _ _ _ ha]
  congr

/-! ### Invariant, overflow flag, hazard -/

section Hazard
variable {Memory : Type}
/-- Seeds of family `f` that are retired (disclosed or hit). -/
noncomputable def retiredSeeds (state : State GCoord Digest Memory) (f : FamIdx) : Finset (Fin 128 × Fin 6) :=
  Finset.univ.filter fun p => ((member f p.1 p.2, 0) : GCoord) ∈ state.retired
/-- Seeds of family `f` retired without a guess (disclosed by honest signing). -/
noncomputable def freeRetired (state : State GCoord Digest Memory) (f : FamIdx) : Finset (Fin 128 × Fin 6) :=
  (retiredSeeds state f).filter fun p => ((member f p.1 p.2, 0) : GCoord) ∉ state.guesses
theorem mem_retiredSeeds (state : State GCoord Digest Memory) (f : FamIdx) (p : Fin 128 × Fin 6) :
    p ∈ retiredSeeds state f ↔ ((member f p.1 p.2, 0) : GCoord) ∈ state.retired := by
  simp [retiredSeeds]
theorem mem_freeRetired (state : State GCoord Digest Memory) (f : FamIdx) (p : Fin 128 × Fin 6) :
    p ∈ freeRetired state f ↔
      ((member f p.1 p.2, 0) : GCoord) ∈ state.retired ∧ ((member f p.1 p.2, 0) : GCoord) ∉ state.guesses := by
  simp [freeRetired, retiredSeeds]
/-- FTS overflow in the engine: some family has more than 51 seeds retired without a guess. -/
def Bad (state : State GCoord Digest Memory) : Prop := ∃ f, 51 < (freeRetired state f).card
/-- Values excluded from the fresh seeds of family `f` (one per failed guess). -/
noncomputable def missCount (state : State GCoord Digest Memory) (f : FamIdx) : Nat :=
  ∑ p : Fin 128 × Fin 6, if ((member f p.1 p.2, 0) : GCoord) ∈ state.retired then 0
    else 2 ^ 128 - (state.allowed (member f p.1 p.2, 0)).card
/-- Invariant of the family engine. -/
structure Inv (state : State GCoord Digest Memory) : Prop where
  guesses : state.guesses ⊆ state.retired
  fam : ∀ f, (famPostA state.allowed f).Nonempty
  label : ∀ l, (labelAllowed state.allowed l).Nonempty
  labelSize : ∀ l : LabelIdx, ((l.1, l.2.succ) : GCoord) ∉ state.retired →
    2 ^ 128 ≤ (labelAllowed state.allowed l).card + state.probes
  retiredSeed : ∀ a : ChainAddr, ((a, 0) : GCoord) ∈ state.retired → (state.allowed (a, 0)).card ≤ 1
  misses : ∀ f, missCount state f ≤ state.probes
theorem card_digest : Fintype.card Digest = 2 ^ 128 := by simp
theorem famPostA_univ (f : FamIdx) : famPostA (fun _ => Finset.univ) f = Finset.univ := by
  ext K
  simp [famPostA]
theorem inv_initial (memory : Memory) : Inv (initialState memory : State GCoord Digest Memory) := by
  refine ⟨by simp [initialState], fun f => ?_, fun l => ⟨0, by simp [labelAllowed, initialState]⟩, ?_, ?_, ?_⟩
  · rw [show (initialState memory : State GCoord Digest Memory).allowed = fun _ => Finset.univ from rfl,
      famPostA_univ]
    exact Finset.univ_nonempty
  · intro l _
    simp [labelAllowed, initialState, card_digest]
  · intro a ha
    simp [initialState] at ha
  · intro f
    simp [missCount, initialState, card_digest]
/-- Known pairs `(point, seed)` of family `f`: the retired seeds with their (at most one) allowed value. -/
noncomputable def knownOf (state : State GCoord Digest Memory) (f : FamIdx) : Finset (Nat × Digest) :=
  (retiredSeeds state f).biUnion fun p =>
    (state.allowed (member f p.1 p.2, 0)).image fun v => (WCT9.ftsPoint p.1.val p.2.val, v)
/-- Excluded pairs of family `f`: fresh seeds and the values they can no longer take. -/
noncomputable def missesOf (state : State GCoord Digest Memory) (f : FamIdx) : Finset (Nat × Digest) :=
  (Finset.univ.filter fun p : Fin 128 × Fin 6 => ((member f p.1 p.2, 0) : GCoord) ∉ state.retired).biUnion fun p =>
    (Finset.univ \ state.allowed (member f p.1 p.2, 0)).image fun v => (WCT9.ftsPoint p.1.val p.2.val, v)
theorem seedK_member (K : Coefs) (f : FamIdx) (j : Fin 128) (t : Fin 6) :
    seedK K (member f j t) = ClaudeWCT.Arith.familyEval (List.ofFn K) (WCT9.ftsPoint j.val t.val) := rfl
set_option linter.constructorNameAsVariable false in
theorem famPostA_eq (state : State GCoord Digest Memory) (hs : Inv state) (f : FamIdx) :
    famPostA state.allowed f = ClaudeWCT.Arith.famPost (m := 53) (knownOf state f) (missesOf state f) := by
  ext K
  rw [mem_famPostA]
  simp only [ClaudeWCT.Arith.famPost, ClaudeWCT.Arith.famAffine, Finset.mem_filter, Finset.mem_univ, true_and,
    knownOf, missesOf, retiredSeeds, Finset.mem_biUnion, Finset.mem_image, Finset.mem_sdiff,
    forall_exists_index, and_imp]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro _ ⟨j, t⟩ hp v hv rfl
      have hk := h j t
      exact Finset.card_le_one.mp (hs.retiredSeed _ hp) _ hk _ hv
    · rintro _ ⟨j, t⟩ hp v hv rfl heq
      have heq' : seedK K (member f j t) = v := heq
      exact hv (heq' ▸ h j t)
  · rintro ⟨hknown, hmiss⟩ j t
    by_cases hr : ((member f j t, 0) : GCoord) ∈ state.retired
    · obtain ⟨K0, hK0⟩ := hs.fam f
      simp only [mem_famPostA] at hK0
      have hv := hK0 j t
      have he := hknown (WCT9.ftsPoint j.val t.val, seedK K0 (member f j t)) (j, t) hr _ hv rfl
      rw [← seedK_member] at he
      rw [he]
      exact hv
    · by_contra hn
      exact hmiss (WCT9.ftsPoint j.val t.val, seedK K (member f j t)) (j, t) hr (seedK K (member f j t)) hn rfl
        (seedK_member K f j t).symm
theorem knownOf_card_le (state : State GCoord Digest Memory) (hs : Inv state) (f : FamIdx) :
    (knownOf state f).card ≤ (retiredSeeds state f).card := by
  unfold knownOf
  refine Finset.card_biUnion_le.trans ?_
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro p hp
  refine Finset.card_image_le.trans ?_
  exact hs.retiredSeed _ (Finset.mem_filter.mp hp).2
theorem retiredSeeds_card_le (state : State GCoord Digest Memory) (f : FamIdx) :
    (retiredSeeds state f).card ≤ (freeRetired state f).card + state.guesses.card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := retiredSeeds state f)
    (fun p => ((member f p.1 p.2, 0) : GCoord) ∉ state.guesses)
  have hg : ((retiredSeeds state f).filter fun p => ¬((member f p.1 p.2, 0) : GCoord) ∉ state.guesses).card ≤
      state.guesses.card := by
    refine Finset.card_le_card_of_injOn (fun p => ((member f p.1 p.2, 0) : GCoord)) ?_ ?_
    · intro p hp
      simpa using (Finset.mem_filter.mp hp).2
    · rintro ⟨j, t⟩ _ ⟨j', t'⟩ _ he
      simp only [member, Prod.mk.injEq] at he
      obtain ⟨⟨-, -, rfl, rfl⟩, -⟩ := he
      rfl
  have hf : freeRetired state f = (retiredSeeds state f).filter fun p =>
      ((member f p.1 p.2, 0) : GCoord) ∉ state.guesses := rfl
  rw [hf]
  omega
theorem missesOf_card_le (state : State GCoord Digest Memory) (hs : Inv state) (f : FamIdx) :
    (missesOf state f).card ≤ state.probes := by
  have h : (missesOf state f).card ≤ missCount state f := by
    unfold missesOf missCount
    refine Finset.card_biUnion_le.trans ?_
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro p _
    by_cases hr : ((member f p.1 p.2, 0) : GCoord) ∈ state.retired
    · simp only [hr, not_true_eq_false, if_false, if_true, le_refl]
    · simp only [hr, not_false_eq_true, if_true, if_false]
      refine Finset.card_image_le.trans (le_of_eq ?_)
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, card_digest]
  exact h.trans (hs.misses f)
theorem notMem_known (state : State GCoord Digest Memory) (a : ChainAddr) (ha : ((a, 0) : GCoord) ∉ state.retired) :
    ptOf a ∉ (knownOf state (famOf a)).image Prod.fst := by
  intro hmem
  obtain ⟨⟨pt, w⟩, hpw, hfst⟩ := Finset.mem_image.mp hmem
  simp only [knownOf, Finset.mem_biUnion, Finset.mem_image] at hpw
  obtain ⟨⟨j, t⟩, hr, w', -, he⟩ := hpw
  simp only [Prod.mk.injEq] at he
  have hp : WCT9.ftsPoint j.val t.val = WCT9.ftsPoint a.2.2.1.val a.2.2.2.val := by
    rw [he.1]; exact hfst
  obtain ⟨rfl, rfl⟩ := ftsPoint_inj hp
  exact ha ((mem_retiredSeeds _ _ _).mp hr)
/-- Hazard of a fresh seed: at most `(2^128 - budget)⁻¹` while `¬Bad`, with at most one guess. -/
theorem hazard_seed (state : State GCoord Digest Memory) (hs : Inv state) (hbad : ¬Bad state)
    (hg : state.guesses.card ≤ 1) (budget : Nat) (hp : state.probes < budget) (a : ChainAddr)
    (ha : ((a, 0) : GCoord) ∉ state.retired) (v : Digest) :
    trialBy (famPostA state.allowed) (famOf a) (fun K => decide (seedK K a = v)) true ≤
      ((2 ^ 128 - budget : Nat) : ℝ≥0∞)⁻¹ := by
  rw [trialBy_true_eq _ _ _ hs.fam]
  have hfree : (freeRetired state (famOf a)).card ≤ 51 := by
    by_contra h
    exact hbad ⟨famOf a, by omega⟩
  have hknown : (knownOf state (famOf a)).card ≤ 53 :=
    (knownOf_card_le state hs _).trans ((retiredSeeds_card_le state _).trans (by omega))
  have hpts : ∀ p ∈ knownOf state (famOf a), p.1 < 1024 := by
    intro p hp
    simp only [knownOf, Finset.mem_biUnion, Finset.mem_image] at hp
    obtain ⟨⟨j, t⟩, -, v, -, rfl⟩ := hp
    exact ftsPoint_lt j t
  have hmpts : ∀ p ∈ missesOf state (famOf a), p.1 < 1024 := by
    intro p hp
    simp only [missesOf, Finset.mem_biUnion, Finset.mem_image] at hp
    obtain ⟨⟨j, t⟩, -, v, -, rfl⟩ := hp
    exact ftsPoint_lt j t
  have hb : ptOf a < 1024 := ftsPoint_lt a.2.2.1 a.2.2.2
  have h := ClaudeWCT.Arith.fam_hazard_prob (m := 53) hknown hpts hmpts hb (notMem_known state a ha) v
    ((missesOf_card_le state hs _).trans hp.le)
  rw [← famPostA_eq state hs] at h
  have hf : ((famPostA state.allowed (famOf a)).filter fun K => true = decide (seedK K a = v)) =
      (famPostA state.allowed (famOf a)).filter fun K => ClaudeWCT.Arith.familyEval (List.ofFn K) (ptOf a) = v := by
    apply Finset.filter_congr
    intro K _
    simp [seedK]
  rw [hf]
  exact h
theorem hazard_label (state : State GCoord Digest Memory) (hs : Inv state) (budget : Nat) (hp : state.probes < budget)
    (c : GCoord) (hc : c.2 ≠ 0) (hr : c ∉ state.retired) (v : Digest) :
    trialBy (labelAllowed state.allowed) (c.1, c.2.pred hc) (fun x => decide (x = v)) true ≤
      ((2 ^ 128 - budget : Nat) : ℝ≥0∞)⁻¹ := by
  rw [trialBy_true_eq _ _ _ hs.label]
  have hsize := hs.labelSize (c.1, c.2.pred hc) (by rwa [label_succ_pred hc])
  have hcard : ((labelAllowed state.allowed (c.1, c.2.pred hc)).filter fun x => true = decide (x = v)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    simp only [Finset.mem_filter, eq_comm (a := true), decide_eq_true_eq] at hx hy
    rw [hx.2, hy.2]
  calc (((labelAllowed state.allowed (c.1, c.2.pred hc)).filter fun x => true = decide (x = v)).card : ℝ≥0∞) /
        (labelAllowed state.allowed (c.1, c.2.pred hc)).card
      ≤ 1 / ((labelAllowed state.allowed (c.1, c.2.pred hc)).card : ℝ≥0∞) :=
        ENNReal.div_le_div_right (by exact_mod_cast hcard) _
    _ ≤ ((2 ^ 128 - budget : Nat) : ℝ≥0∞)⁻¹ := by
        rw [one_div]
        apply ENNReal.inv_le_inv.mpr
        exact_mod_cast (show 2 ^ 128 - budget ≤ (labelAllowed state.allowed (c.1, c.2.pred hc)).card by omega)
end Hazard

/-! ### Preservation -/

section Preservation
variable {Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
variable (environment : Environment auxSpec GCoord Digest Memory)
theorem card_restrict_ge (allowed : GCoord → Finset Digest) (c : GCoord) (v : Digest) (hit : Bool) (x : GCoord)
    (h : hit = true → x ≠ c) : (allowed x).card ≤ (restrict allowed c v hit x).card + 1 := by
  cases hit with
  | false => exact restrict_false_card allowed c v x
  | true => rw [restrict, Function.update_of_ne (h rfl)]; omega
theorem trial_seed_mass {state : State GCoord Digest Memory} {a : ChainAddr} {v : Digest} {hit : Bool}
    (h : (sampler Memory).trialLaw state (a, 0) v hit ≠ 0) :
    trialBy (famPostA state.allowed) (famOf a) (fun K => decide (seedK K a = v)) hit ≠ 0 := by
  simpa only [sampler, dite_true] using h
theorem trial_label_mass {state : State GCoord Digest Memory} {c : GCoord} (hc : c.2 ≠ 0) {v : Digest} {hit : Bool}
    (h : (sampler Memory).trialLaw state c v hit ≠ 0) :
    trialBy (labelAllowed state.allowed) (c.1, c.2.pred hc) (fun x => decide (x = v)) hit ≠ 0 := by
  simpa only [sampler, dif_neg hc] using h
theorem disclose_seed_mass {state : State GCoord Digest Memory} {a : ChainAddr} {value : Digest}
    (h : (sampler Memory).discloseLaw state (a, 0) value ≠ 0) :
    discloseBy (famPostA state.allowed) (famOf a) (fun K => seedK K a) value ≠ 0 := by
  simpa only [sampler, dite_true] using h
theorem disclose_label_mass {state : State GCoord Digest Memory} {c : GCoord} (hc : c.2 ≠ 0) {value : Digest}
    (h : (sampler Memory).discloseLaw state c value ≠ 0) :
    discloseBy (labelAllowed state.allowed) (c.1, c.2.pred hc) id value ≠ 0 := by
  simpa only [sampler, dif_neg hc] using h
theorem indicator_sum_le_one (f : FamIdx) (c : GCoord) :
    (∑ p : Fin 128 × Fin 6, if ((member f p.1 p.2, 0) : GCoord) = c then 1 else 0) ≤ 1 := by
  rw [← Finset.card_filter]
  apply Finset.card_le_one.mpr
  rintro ⟨j, t⟩ hp ⟨j', t'⟩ hp'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
  rw [← hp'] at hp
  simp only [member, Prod.mk.injEq] at hp
  obtain ⟨⟨-, -, rfl, rfl⟩, -⟩ := hp
  rfl
theorem inv_afterTrial (state : State GCoord Digest Memory) (hs : Inv state) (c : GCoord) (v : Digest) (hit : Bool)
    (hmass : (sampler Memory).trialLaw state c v hit ≠ 0) : Inv (afterTrial environment state c v hit) := by
  obtain ⟨a, q⟩ := c
  have hret : state.retired ⊆ (afterTrial environment state (a, q) v hit).retired := by
    simp only [afterTrial]; split
    · exact Finset.subset_insert _ _
    · exact le_rfl
  have hhitret : hit = true → ((a, q) : GCoord) ∈ (afterTrial environment state (a, q) v hit).retired := by
    rintro rfl; simp [afterTrial]
  refine ⟨afterTrial_guesses_sub environment state hs.guesses _ v hit, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    change (famPostA (restrict state.allowed (a, q) v hit) f).Nonempty
    by_cases hq : q = 0
    · subst hq
      rw [famPostA_restrict_seed]
      exact discloseBy_nonempty _ _ _ _ (trial_seed_mass hmass) f
    · rw [famPostA_restrict_label _ (a, q) hq]
      exact hs.fam f
  · intro l
    change (labelAllowed (restrict state.allowed (a, q) v hit) l).Nonempty
    by_cases hq : q = 0
    · subst hq
      rw [labelAllowed_restrict_seed]
      exact hs.label l
    · rw [labelAllowed_restrict_label _ (a, q) hq]
      exact discloseBy_nonempty _ _ _ _ (trial_label_mass hq hmass) l
  · intro l hl
    have hold := hs.labelSize l (fun h => hl (hret h))
    have hge := card_restrict_ge state.allowed (a, q) v hit (l.1, l.2.succ)
      (fun hh he => hl (he ▸ hhitret hh))
    change 2 ^ 128 ≤ (restrict state.allowed (a, q) v hit (l.1, l.2.succ)).card + (state.probes + 1)
    simp only [labelAllowed] at hold
    omega
  · intro a' ha'
    change (restrict state.allowed (a, q) v hit (a', 0)).card ≤ 1
    by_cases hold : ((a', 0) : GCoord) ∈ state.retired
    · exact (Finset.card_le_card (restrict_subset state.allowed (a, q) v hit (a', 0))).trans (hs.retiredSeed a' hold)
    · have hhit : hit = true ∧ ((a', 0) : GCoord) = (a, q) := by
        simp only [afterTrial] at ha'
        split at ha'
        · rename_i hh
          rcases Finset.mem_insert.mp ha' with h | h
          · exact ⟨hh, h⟩
          · exact absurd h hold
        · exact absurd ha' hold
      obtain ⟨rfl, he⟩ := hhit
      rw [he, restrict, Function.update_self]
      apply Finset.card_le_one.mpr
      intro x hx y hy
      simp only [Finset.mem_filter, eq_comm (a := true), decide_eq_true_eq] at hx hy
      rw [hx.2, hy.2]
  · intro f
    change missCount (afterTrial environment state (a, q) v hit) f ≤ state.probes + 1
    have hstep : ∀ p : Fin 128 × Fin 6,
        (if ((member f p.1 p.2, 0) : GCoord) ∈ (afterTrial environment state (a, q) v hit).retired then 0
          else 2 ^ 128 - ((afterTrial environment state (a, q) v hit).allowed (member f p.1 p.2, 0)).card) ≤
        (if ((member f p.1 p.2, 0) : GCoord) ∈ state.retired then 0
          else 2 ^ 128 - (state.allowed (member f p.1 p.2, 0)).card) +
          (if ((member f p.1 p.2, 0) : GCoord) = (a, q) then 1 else 0) := by
      intro p
      split
      · exact Nat.zero_le _
      · rename_i hn
        have hn' : ((member f p.1 p.2, 0) : GCoord) ∉ state.retired := fun h => hn (hret h)
        rw [if_neg hn']
        change 2 ^ 128 - (restrict state.allowed (a, q) v hit (member f p.1 p.2, 0)).card ≤ _
        by_cases he : ((member f p.1 p.2, 0) : GCoord) = (a, q)
        · rw [if_pos he]
          have hge := card_restrict_ge state.allowed (a, q) v hit (member f p.1 p.2, 0)
            (fun hh he' => hn (he' ▸ hhitret hh))
          omega
        · rw [if_neg he, restrict, Function.update_of_ne he]
          omega
    unfold missCount
    refine (Finset.sum_le_sum fun p _ => hstep p).trans ?_
    rw [Finset.sum_add_distrib]
    have := hs.misses f
    have := indicator_sum_le_one f (a, q)
    unfold missCount at *
    omega
theorem inv_afterDisclosure (state : State GCoord Digest Memory) (hs : Inv state) (c : GCoord) (value : Digest)
    (hmass : (sampler Memory).discloseLaw state c value ≠ 0) : Inv (afterDisclosure environment state c value) := by
  obtain ⟨a, q⟩ := c
  have hvmem : value ∈ state.allowed (a, q) := by
    by_cases hq : q = 0
    · subst hq; exact mem_of_discloseBy_seed _ _ _ (disclose_seed_mass hmass)
    · exact mem_of_discloseBy_label _ (a, q) hq _ (disclose_label_mass hq hmass)
  refine ⟨hs.guesses.trans (Finset.subset_insert _ _), ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    change (famPostA (discloseTableValue state.allowed (a, q) value) f).Nonempty
    by_cases hq : q = 0
    · subst hq
      rw [famPostA_disclose_seed _ _ _ hvmem]
      exact discloseBy_nonempty _ _ _ _ (disclose_seed_mass hmass) f
    · rw [famPostA_disclose_label _ (a, q) hq]
      exact hs.fam f
  · intro l
    change (labelAllowed (discloseTableValue state.allowed (a, q) value) l).Nonempty
    by_cases hq : q = 0
    · subst hq
      rw [labelAllowed_disclose_seed]
      exact hs.label l
    · rw [labelAllowed_disclose_label _ (a, q) hq _ hvmem]
      exact discloseBy_nonempty _ _ _ _ (disclose_label_mass hq hmass) l
  · intro l hl
    have hne : ((l.1, l.2.succ) : GCoord) ≠ (a, q) := fun he => hl (by rw [he]; simp [afterDisclosure])
    have hold := hs.labelSize l (fun h => hl (Finset.mem_insert_of_mem h))
    change 2 ^ 128 ≤ (discloseTableValue state.allowed (a, q) value (l.1, l.2.succ)).card + state.probes
    rw [discloseTableValue, Function.update_of_ne hne]
    exact hold
  · intro a' ha'
    change (discloseTableValue state.allowed (a, q) value (a', 0)).card ≤ 1
    by_cases he : ((a', 0) : GCoord) = (a, q)
    · rw [he, discloseTableValue, Function.update_self, Finset.card_singleton]
    · rw [discloseTableValue, Function.update_of_ne he]
      exact hs.retiredSeed a' ((Finset.mem_insert.mp ha').resolve_left he)
  · intro f
    change missCount (afterDisclosure environment state (a, q) value) f ≤ state.probes
    refine le_trans (Finset.sum_le_sum fun p _ => ?_) (hs.misses f)
    split
    · exact Nat.zero_le _
    · rename_i hn
      have hne : ((member f p.1 p.2, 0) : GCoord) ≠ (a, q) := fun he => hn (by rw [he]; simp [afterDisclosure])
      have hn' : ((member f p.1 p.2, 0) : GCoord) ∉ state.retired := fun h => hn (Finset.mem_insert_of_mem h)
      rw [if_neg hn']
      change 2 ^ 128 - (discloseTableValue state.allowed (a, q) value (member f p.1 p.2, 0)).card ≤ _
      rw [discloseTableValue, Function.update_of_ne hne]
theorem inv_step (state : State GCoord Digest Memory) (hs : Inv state)
    (input : (World auxSpec GCoord Digest).Domain)
    (result : (World auxSpec GCoord Digest).Range input × State GCoord Digest Memory)
    (hr : (withImpl environment (sampler Memory) input).run state result ≠ 0) : Inv result.2 := by
  rcases withImpl_cases environment (sampler Memory) state input result hr with ⟨memory, h⟩ |
    ⟨c, v, hit, -, hm, h⟩ | ⟨c, value, -, hm, h⟩
  · rw [h]; exact ⟨hs.guesses, hs.fam, hs.label, hs.labelSize, hs.retiredSeed, hs.misses⟩
  · rw [h]; exact inv_afterTrial environment state hs c v hit hm
  · rw [h]; exact inv_afterDisclosure environment state hs c value hm
theorem freeRetired_mono {state state' : State GCoord Digest Memory} (f : FamIdx)
    (hr : state.retired ⊆ state'.retired)
    (hg : ∀ x, x ∈ state'.guesses → x ∈ state.retired → x ∈ state.guesses) :
    freeRetired state f ⊆ freeRetired state' f := by
  intro p hp
  rw [mem_freeRetired] at hp ⊢
  exact ⟨hr hp.1, fun h => hp.2 (hg _ h hp.1)⟩
theorem bad_step (state : State GCoord Digest Memory) (hbad : Bad state)
    (input : (World auxSpec GCoord Digest).Domain)
    (result : (World auxSpec GCoord Digest).Range input × State GCoord Digest Memory)
    (hr : (withImpl environment (sampler Memory) input).run state result ≠ 0) : Bad result.2 := by
  obtain ⟨f, hf⟩ := hbad
  refine ⟨f, lt_of_lt_of_le hf (Finset.card_le_card ?_)⟩
  rcases withImpl_cases environment (sampler Memory) state input result hr with ⟨memory, h⟩ |
    ⟨c, v, hit, -, -, h⟩ | ⟨c, value, -, -, h⟩
  · rw [h]; exact freeRetired_mono f le_rfl fun _ h _ => h
  · rw [h]
    refine freeRetired_mono f ?_ ?_
    · simp only [afterTrial]; split
      · exact Finset.subset_insert _ _
      · exact le_rfl
    · intro x hx hxr
      simp only [afterTrial] at hx
      split at hx
      · rename_i hh
        rcases Finset.mem_insert.mp hx with h | h
        · exact absurd (h ▸ hxr) hh.2
        · exact h
      · exact hx
  · rw [h]
    exact freeRetired_mono f (Finset.subset_insert _ _) fun _ h _ => h
/-- The family world satisfies the abstract hazard with size `2^128`. -/
theorem hazardFam (budget : Nat) :
    Hazard environment (sampler Memory) (2 ^ 128) budget Inv Bad where
  step := inv_step environment
  bad state _ hbad := bad_step environment state hbad
  guesses state hs := hs.guesses
  hazard state hs hbad hg hp c v hc := by
    obtain ⟨a, q⟩ := c
    by_cases hq : q = 0
    · subst hq
      simp only [sampler, dif_pos rfl]
      exact hazard_seed state hs hbad hg budget hp a hc v
    · simp only [sampler, dif_neg hq]
      exact hazard_label state hs budget hp (a, q) hq hc v
end Preservation

/-! ### Erasure and the bounds of the family world -/

section Main
variable {Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
variable (environment : Environment auxSpec GCoord Digest Memory)
theorem hiddenLaw_bind_const {Result : Type} (allowed : GCoord → Finset Digest)
    (hF : ∀ f, (famPostA allowed f).Nonempty) (hL : ∀ l, (labelAllowed allowed l).Nonempty) (X : SPMF Result) :
    (hiddenLaw allowed >>= fun _ => X) = X := by
  unfold hiddenLaw
  rw [complete_of_nonempty _ hF, complete_of_nonempty _ hL]
  simp only [bind_assoc, pure_bind]
  rw [show (fun _ : FamIdx → Coefs => (liftM (uniformTable (labelAllowed allowed) hL) : SPMF _) >>= fun _ => X) =
      fun _ => X from funext fun _ => RetainedObservation.lift_bind_const _ _]
  exact RetainedObservation.lift_bind_const _ _
/-- The eager family world (hidden coefficients and labels, then the fixed run) is the lazy family engine. -/
theorem fam_erasure {Result : Type} (computation : OracleComp (World auxSpec GCoord Digest) Result)
    (state : State GCoord Digest Memory) (hs : Inv state) :
    (hiddenLaw state.allowed >>= fun g => fixedRun environment g computation state) =
      withRun environment (sampler Memory) computation state := by
  have h := congrArg (Functor.map Prod.snd) (fam_posterior environment computation state)
  simp only [map_bind, Functor.map_map, id_map'] at h
  calc _ = (withRun environment (sampler Memory) computation state >>= fun result =>
          (fun _ => result) <$> hiddenLaw result.2.allowed) := h
    _ = (withRun environment (sampler Memory) computation state >>= pure) := by
      apply RetainedObservation.bind_congr
      intro result hr
      have hinv := withRun_preserves environment (sampler Memory) Inv
        (fun st hst input r hr' => inv_step environment st hst input r hr') computation state hs result hr
      rw [map_eq_bind_pure_comp]
      exact hiddenLaw_bind_const _ hinv.fam hinv.label _
    _ = _ := bind_pure _
/-- Pair bound of the family world (`trial_true_le'` is `hazard_seed` / `hazard_label`). -/
theorem fam_pair_le {Result : Type} (computation : OracleComp (World auxSpec GCoord Digest) Result)
    (memory : Memory) (budget : Nat) :
    Pr[fun result => 2 ≤ result.2.guesses.card ∧ result.2.probes ≤ budget ∧ ¬Bad result.2 |
      withRun environment (sampler Memory) computation (initialState memory)] ≤
      (budget.choose 2 : ℝ≥0∞) * ((2 ^ 128 - budget : Nat) : ℝ≥0∞)⁻¹ ^ 2 :=
  withRun_pair_le (hazardFam environment budget) computation _ (inv_initial memory) rfl rfl
/-- First-guess forcing bound of the family world. -/
theorem fam_event_le_forced_slot {Result : Type} (computation : OracleComp (World auxSpec GCoord Digest) Result)
    (memory : Memory) (budget : Nat) (event : Result × State GCoord Digest Memory → Prop)
    (payoff : Nat → Result × State GCoord Digest Memory → ℝ≥0∞)
    (hevent : ∀ result, withRun environment (sampler Memory) computation (initialState memory) result ≠ 0 →
      event result → result.2.guesses.Nonempty ∧ result.2.probes ≤ budget ∧ ¬Bad result.2 ∧
        ∀ slot < result.2.probes, 1 ≤ payoff slot result) :
    Pr[event | withRun environment (sampler Memory) computation (initialState memory)] ≤
      ((2 ^ 128 - budget : Nat) : ℝ≥0∞)⁻¹ *
        ∑ slot ∈ Finset.range budget, ∑' result,
          Pr[= result | forcedWithRun environment (sampler Memory) slot computation (initialState memory)] *
            payoff slot result :=
  withRun_event_le_forced_slot (hazardFam environment budget) computation _ (inv_initial memory) rfl rfl event
    payoff hevent
end Main
end ClaudeWCT.Guess.Fam

/-! A first-guess potential retaining unused probe credit.  Unlike a union bound
    by the maximum number of probes, the terminal credit can be transported to
    the actual expected number of queries in the FTS class. -/
namespace SphincsSecurity.Concrete.SecretGuessObservation.CountedFirst
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]

noncomputable def indicator (Bad : State Coordinate Value Memory → Prop) (budget : Nat)
    (state : State Coordinate Value Memory) : ENNReal :=
  if Bad state then 0 else if state.probes ≤ budget then
    if state.guesses.Nonempty then 1 else 0 else 0
noncomputable def potential (Bad : State Coordinate Value Memory → Prop) (size budget : Nat)
    (state : State Coordinate Value Memory) : ENNReal :=
  indicator Bad budget state + ((size - budget : Nat) : ENNReal)⁻¹ * (budget - state.probes : Nat)

theorem indicator_le_one (Bad : State Coordinate Value Memory → Prop) (budget : Nat)
    (state : State Coordinate Value Memory) : indicator Bad budget state ≤ 1 := by
  unfold indicator
  split_ifs <;> simp

theorem indicator_frame (Bad : State Coordinate Value Memory → Prop) (budget : Nat)
    (s t : State Coordinate Value Memory) (hp : t.probes = s.probes)
    (hg : t.guesses = s.guesses) (hb : Bad s → Bad t) :
    indicator Bad budget t ≤ indicator Bad budget s := by
  unfold indicator
  by_cases hs : Bad s
  · rw [if_pos hs, if_pos (hb hs)]
  · rw [if_neg hs]
    by_cases ht : Bad t
    · rw [if_pos ht]; exact bot_le
    · rw [if_neg ht, hp, hg]

theorem step_potential {environment : Environment auxSpec Coordinate Value Memory}
    {sampler : Sampler Coordinate Value Memory} {size budget : Nat}
    {Inv Bad : State Coordinate Value Memory → Prop}
    (H : Hazard environment sampler size budget Inv Bad) (state : State Coordinate Value Memory)
    (hs : Inv state) (input : (World auxSpec Coordinate Value).Domain) :
    (∑' result, Pr[= result | (withImpl environment sampler input).run state] *
      potential Bad size budget result.2) ≤ potential Bad size budget state := by
  rcases input with input | (⟨coordinate, candidate⟩ | coordinate)
  · refine tsum_le_of_support _ _ _ fun result hr => ?_
    rcases withImpl_cases environment sampler state (.inl input) result hr with
      ⟨memory, he⟩ | ⟨c, v, hit, hi, -, -⟩ | ⟨c, v, hi, -, -⟩
    · have hb := H.bad state hs
      rw [potential, potential]
      refine add_le_add (indicator_frame Bad budget state result.2 ?_ ?_ ?_) ?_
      · rw [he]
      · rw [he]
      · exact fun h => hb h _ result hr
      · rw [he]
    · cases hi
    · cases hi
  · simp only [withImpl, StateT.run_mk, tsum_probOutput_map_mul]
    have hp (hit : Bool) : (afterTrial environment state coordinate candidate hit).probes = state.probes + 1 := rfl
    have hcredit : ((size - budget : Nat) : ENNReal)⁻¹ * (budget - (state.probes + 1) : Nat) ≤
        ((size - budget : Nat) : ENNReal)⁻¹ * (budget - state.probes : Nat) := by
      exact mul_le_mul' le_rfl (Nat.cast_le.mpr (Nat.sub_le_sub_left (Nat.le_succ state.probes) budget))
    have hbad_step (hit : Bool) (hh : sampler.trialLaw state coordinate candidate hit ≠ 0)
        (hb : Bad state) : Bad (afterTrial environment state coordinate candidate hit) := by
      apply H.bad state hs hb (.inr (.inl (coordinate, candidate)))
        (hit, afterTrial environment state coordinate candidate hit)
      simp only [withImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero]
      exact ⟨hit, hh, by simp⟩
    by_cases hb : Bad state
    · refine tsum_le_of_support _ _ _ fun hit hh => ?_
      simp only [potential, indicator, if_pos hb, if_pos (hbad_step hit hh hb), hp, zero_add]
      exact hcredit
    by_cases hroom : state.probes < budget
    swap
    · refine tsum_le_of_support _ _ _ fun hit _ => ?_
      have hpast : ¬state.probes + 1 ≤ budget := by omega
      have hz : budget - (state.probes + 1) = 0 := by omega
      simp only [potential, indicator, hp, if_neg hpast, hz, Nat.cast_zero, mul_zero, add_zero]
      split_ifs <;> exact bot_le
    by_cases hg : state.guesses.Nonempty
    · refine tsum_le_of_support _ _ _ fun hit _ => ?_
      have hind : indicator Bad budget state = 1 := by simp [indicator, hb, hg, Nat.le_of_lt hroom]
      rw [potential, potential, hind, hp]
      exact add_le_add (indicator_le_one _ _ _) hcredit
    have hempty : state.guesses = ∅ := Finset.not_nonempty_iff_eq_empty.mp hg
    have hind : indicator Bad budget state = 0 := by simp [indicator, hb, hg]
    by_cases hc : coordinate ∈ state.retired
    · refine tsum_le_of_support _ _ _ fun hit _ => ?_
      have hzero : indicator Bad budget (afterTrial environment state coordinate candidate hit) = 0 := by
        simp [indicator, afterTrial, hc, hempty]
      rw [potential, potential, hzero, hind, hp, zero_add, zero_add]
      exact hcredit
    have hr : sampler.trialLaw state coordinate candidate true ≤ ((size - budget : Nat) : ENNReal)⁻¹ :=
      H.hazard state hs hb (by simp [hempty]) hroom coordinate candidate hc
    let credit : ENNReal := ((size - budget : Nat) : ENNReal)⁻¹ * (budget - (state.probes + 1) : Nat)
    have hpoint (hit : Bool) : potential Bad size budget (afterTrial environment state coordinate candidate hit) ≤
        credit + if hit = true then 1 else 0 := by
      rw [potential, hp]
      dsimp only [credit]
      rw [add_comm]
      apply add_le_add le_rfl
      cases hit
      · simp [indicator, afterTrial, hempty]
      · simpa only [if_true] using indicator_le_one Bad budget (afterTrial environment state coordinate candidate true)
    calc
      _ ≤ ∑' hit, Pr[= hit | sampler.trialLaw state coordinate candidate] * (credit + if hit = true then 1 else 0) :=
        ENNReal.tsum_le_tsum fun hit => mul_le_mul' le_rfl (hpoint hit)
      _ = (∑' hit, Pr[= hit | sampler.trialLaw state coordinate candidate] * credit) +
          sampler.trialLaw state coordinate candidate true := by
        simp only [mul_add, ENNReal.tsum_add]
        congr 1
        simp [tsum_fintype, SPMF.probOutput_eq_apply]
      _ ≤ credit + ((size - budget : Nat) : ENNReal)⁻¹ :=
        add_le_add (tsum_le_of_support _ _ _ fun _ _ => le_rfl) hr
      _ = potential Bad size budget state := by
        rw [potential, hind, zero_add]
        have hremaining : budget - state.probes = (budget - (state.probes + 1)) + 1 := by omega
        rw [hremaining, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
  · refine tsum_le_of_support _ _ _ fun result hr => ?_
    rcases withImpl_cases environment sampler state (.inr (.inr coordinate)) result hr with
      ⟨memory, he⟩ | ⟨c, v, hit, hi, -, -⟩ | ⟨c, v, hi, -, he⟩
    · rw [potential, potential]
      refine add_le_add (indicator_frame Bad budget state result.2 ?_ ?_ ?_) ?_
      · rw [he]
      · rw [he]
      · exact fun h => H.bad state hs h _ result hr
      · rw [he]
    · cases hi
    · rw [potential, potential]
      refine add_le_add (indicator_frame Bad budget state result.2 ?_ ?_ ?_) ?_
      · rw [he]; rfl
      · rw [he]; rfl
      · exact fun h => H.bad state hs h _ result hr
      · rw [he]; rfl

theorem run_potential {environment : Environment auxSpec Coordinate Value Memory}
    {sampler : Sampler Coordinate Value Memory} {size budget : Nat}
    {Inv Bad : State Coordinate Value Memory → Prop}
    (H : Hazard environment sampler size budget Inv Bad) {Result : Type}
    (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Inv state) :
    (∑' result, Pr[= result | withRun environment sampler computation state] *
      potential Bad size budget result.2) ≤ potential Bad size budget state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [withRun, runWith_pure, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      rw [withRun, runWith_query_bind, tsum_probOutput_bind_mul]
      apply le_trans _ (step_potential H state hs input)
      apply ENNReal.tsum_le_tsum
      intro middle
      by_cases hm : (withImpl environment sampler input).run state middle = 0
      · simp only [SPMF.probOutput_eq_apply, hm, zero_mul, le_refl]
      · exact mul_le_mul' le_rfl (ih middle.1 middle.2 (H.step state hs input middle hm))


/-- Total runs retain the unused credit exactly, so the first-hit bound pays
    only for the expected number of probes actually made. -/
theorem expected_indicator_le_count {environment : Environment auxSpec Coordinate Value Memory}
    {sampler : Sampler Coordinate Value Memory} {size budget : Nat}
    {Inv Bad : State Coordinate Value Memory → Prop}
    (H : Hazard environment sampler size budget Inv Bad) {Result : Type}
    (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Inv state) (hp : state.probes = 0)
    (hg : state.guesses = ∅) (hsize : budget < size)
    (hcomplete : (∑' result, Pr[= result | withRun environment sampler computation state]) = 1) :
    (∑' result, Pr[= result | withRun environment sampler computation state] * indicator Bad budget result.2) ≤
      ((size - budget : Nat) : ENNReal)⁻¹ *
        ∑' result, Pr[= result | withRun environment sampler computation state] * (min result.2.probes budget : Nat) := by
  let law := withRun environment sampler computation state
  let rate : ENNReal := ((size - budget : Nat) : ENNReal)⁻¹
  let unused : ENNReal := ∑' result, Pr[= result | law] * (rate * (budget - result.2.probes : Nat))
  have hrate : rate ≠ ⊤ := by
    dsimp [rate]
    apply ENNReal.inv_ne_top.mpr
    exact_mod_cast (show size - budget ≠ 0 by omega)
  have hu : unused ≤ rate * budget :=
    tsum_le_of_support _ _ _ fun result _ => mul_le_mul' le_rfl (Nat.cast_le.mpr (Nat.sub_le _ _))
  have hufin : unused ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top hrate (by simp)) hu
  have hpartition : rate * (∑' result, Pr[= result | law] * (min result.2.probes budget : Nat)) + unused =
      rate * budget := by
    dsimp only [unused]
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    calc
      _ = ∑' result, Pr[= result | law] * (rate * budget) := by
        apply tsum_congr
        intro result
        have hn : min result.2.probes budget + (budget - result.2.probes) = budget := by omega
        have hn' : ((min result.2.probes budget : Nat) : ENNReal) + (budget - result.2.probes : Nat) = budget := by
          exact_mod_cast hn
        rw [← hn']
        ring
      _ = (∑' result, Pr[= result | law]) * (rate * budget) := ENNReal.tsum_mul_right
      _ = rate * budget := by rw [hcomplete, one_mul]
  have h := run_potential H computation state hs
  have hi : indicator Bad budget state = 0 := by simp [indicator, hg]
  rw [potential, hi, hp, Nat.sub_zero, zero_add] at h
  simp only [potential, mul_add, ENNReal.tsum_add] at h
  apply (ENNReal.add_le_add_iff_right hufin).mp
  exact h.trans_eq hpartition.symm

theorem event_le_count {environment : Environment auxSpec Coordinate Value Memory}
    {sampler : Sampler Coordinate Value Memory} {size budget : Nat}
    {Inv Bad : State Coordinate Value Memory → Prop}
    (H : Hazard environment sampler size budget Inv Bad) {Result : Type}
    (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Inv state) (hp : state.probes = 0)
    (hg : state.guesses = ∅) (hsize : budget < size)
    (hcomplete : (∑' result, Pr[= result | withRun environment sampler computation state]) = 1)
    (event : Result × State Coordinate Value Memory → Prop)
    (hevent : ∀ result, withRun environment sampler computation state result ≠ 0 → event result →
      ¬Bad result.2 ∧ result.2.probes ≤ budget ∧ result.2.guesses.Nonempty) :
    Pr[event | withRun environment sampler computation state] ≤
      ((size - budget : Nat) : ENNReal)⁻¹ *
        ∑' result, Pr[= result | withRun environment sampler computation state] * (min result.2.probes budget : Nat) := by
  refine le_trans ?_ (expected_indicator_le_count H computation state hs hp hg hsize hcomplete)
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : withRun environment sampler computation state result = 0
  · simp only [SPMF.probOutput_eq_apply, hr, mul_zero, zero_mul]
    split_ifs <;> exact le_rfl
  · by_cases he : event result
    · obtain ⟨hb, hp, hg⟩ := hevent result hr he
      simp only [if_pos he, indicator, if_neg hb, if_pos hp, if_pos hg, mul_one, le_refl]
    · simp only [if_neg he, zero_le]

theorem event_le_class_cost {environment : Environment auxSpec Coordinate Value Memory}
    {sampler : Sampler Coordinate Value Memory} {size budget : Nat}
    {Inv Bad : State Coordinate Value Memory → Prop}
    (H : Hazard environment sampler size budget Inv Bad) {Result : Type}
    (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Inv state) (hp : state.probes = 0)
    (hg : state.guesses = ∅) (hsize : budget < size)
    (hcomplete : (∑' result, Pr[= result | withRun environment sampler computation state]) = 1)
    (event : Result × State Coordinate Value Memory → Prop)
    (hevent : ∀ result, withRun environment sampler computation state result ≠ 0 → event result →
      ¬Bad result.2 ∧ result.2.probes ≤ budget ∧ result.2.guesses.Nonempty)
    (cost : Result × State Coordinate Value Memory → Nat)
    (hcost : ∀ result, withRun environment sampler computation state result ≠ 0 →
      min result.2.probes budget ≤ cost result) :
    Pr[event | withRun environment sampler computation state] ≤
      ((size - budget : Nat) : ENNReal)⁻¹ *
        ∑' result, Pr[= result | withRun environment sampler computation state] * (cost result : ENNReal) := by
  refine (event_le_count H computation state hs hp hg hsize hcomplete event hevent).trans ?_
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : withRun environment sampler computation state result = 0
  · simp only [SPMF.probOutput_eq_apply, hr, zero_mul, le_refl]
  · exact mul_le_mul' le_rfl (Nat.cast_le.mpr (hcost result hr))

end SphincsSecurity.Concrete.SecretGuessObservation.CountedFirst
end
-- ==== merged from ClaudeWCT_GuessV2_NearScore ====
section

namespace ClaudeWCT.Guess
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open scoped ENNReal
def NearCoveredAt (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 6) : Prop :=
  ∀ k' t', (k', t') ≠ (k, t) → SlotCovered X N k' t'
def NearCoveredBy (X : List HashOutput) (N : HashOutput) : Prop := ∃ k t, NearCoveredAt X N k t
theorem SlotCovered.mono_log {X Y : List HashOutput} {N : HashOutput} {k : Fin 9} {t : Fin 6}
    (h : ∀ x ∈ X, x ∈ Y) (hc : SlotCovered X N k t) : SlotCovered Y N k t := by
  obtain ⟨out, hout, h1, h2, h3⟩ := hc
  exact ⟨out, h out hout, h1, h2, h3⟩
theorem NearCoveredAt.mono_log {X Y : List HashOutput} {N : HashOutput} {k : Fin 9} {t : Fin 6}
    (h : ∀ x ∈ X, x ∈ Y) (hc : NearCoveredAt X N k t) : NearCoveredAt Y N k t :=
  fun k' t' hne => (hc k' t' hne).mono_log h
open Classical in
noncomputable def nearScore (X : List HashOutput) (N : HashOutput) : ENNReal :=
  if admissible N = true then ∑ k : Fin 9, ∑ t : Fin 6, (if NearCoveredAt X N k t then 1 else 0) else 0
theorem one_le_nearScore {X : List HashOutput} {N : HashOutput} (hadm : admissible N = true)
    (h : NearCoveredBy X N) : 1 ≤ nearScore X N := by
  classical
  obtain ⟨k, t, hkt⟩ := h
  unfold nearScore
  rw [if_pos hadm]
  calc (1 : ENNReal) = if NearCoveredAt X N k t then 1 else 0 := by rw [if_pos hkt]
    _ ≤ ∑ t' : Fin 6, (if NearCoveredAt X N k t' then 1 else 0) :=
        Finset.single_le_sum (f := fun t' => if NearCoveredAt X N k t' then (1 : ENNReal) else 0)
          (fun _ _ => zero_le) (Finset.mem_univ t)
    _ ≤ _ := Finset.single_le_sum (f := fun k' => ∑ t' : Fin 6, if NearCoveredAt X N k' t' then (1 : ENNReal) else 0)
          (fun _ _ => zero_le) (Finset.mem_univ k)
theorem nearScore_append_mono (X Y : List HashOutput) (N : HashOutput) : nearScore X N ≤ nearScore (X ++ Y) N := by
  classical
  unfold nearScore
  split_ifs with hadm
  · apply Finset.sum_le_sum
    intro k _
    apply Finset.sum_le_sum
    intro t _
    by_cases h : NearCoveredAt X N k t
    · rw [if_pos h, if_pos (h.mono_log fun x hx => List.mem_append_left _ hx)]
    · rw [if_neg h]
      exact zero_le
  · exact le_rfl
theorem nearScore_le (X : List HashOutput) (N : HashOutput) : nearScore X N ≤ 54 := by
  classical
  unfold nearScore
  split_ifs
  · calc _ ≤ ∑ _k : Fin 9, ∑ _t : Fin 6, (1 : ENNReal) := by
          apply Finset.sum_le_sum; intro k _
          apply Finset.sum_le_sum; intro t _
          split_ifs <;> simp
      _ = 54 := by simp; norm_num
  · exact zero_le
noncomputable def nearPrice (X : List HashOutput) : ENNReal :=
  2 ^ 128 * SigGolfCandidate.T3.BPORS.finiteAverage (fun N : HashOutput => nearScore X N)
theorem average_nearScore (X : List HashOutput) :
    SigGolfCandidate.T3.BPORS.finiteAverage (fun N : HashOutput => nearScore X N) = nearPrice X / 2 ^ 128 := by
  unfold nearPrice
  rw [mul_comm, ENNReal.mul_div_cancel_right (by positivity) (by finiteness)]
theorem nearCoveredBy_of_caseC {X : List HashOutput} {N : HashOutput} {k : Fin 9} {t : Fin 6}
    (h : ∀ k' t', (k', t') ≠ (k, t) → SlotCovered X N k' t') : NearCoveredBy X N :=
  ⟨k, t, h⟩
end ClaudeWCT.Guess
end
-- ==== merged from ClaudeWCT_GuessV2_WorldHash ====
section

section
namespace ClaudeWCT.Guess
open SphincsSecurity.Concrete.SecretGuessObservation
section Prefix
variable {Chain : Type} {w : ℕ}
def PrefixIn (S : Finset (Chain × Fin w)) (a : Chain) (p : ℕ) : Prop :=
  ∃ q : Fin w, q.val ≤ p ∧ (a, q) ∈ S
theorem PrefixIn.mono_set {S S' : Finset (Chain × Fin w)} {a : Chain} {p : ℕ} (h : S ⊆ S')
    (hp : PrefixIn S a p) : PrefixIn S' a p := by
  obtain ⟨q, hq, hm⟩ := hp
  exact ⟨q, hq, h hm⟩
theorem PrefixIn.mono_pos {S : Finset (Chain × Fin w)} {a : Chain} {p p' : ℕ} (h : p ≤ p')
    (hp : PrefixIn S a p) : PrefixIn S a p' := by
  obtain ⟨q, hq, hm⟩ := hp
  exact ⟨q, hq.trans h, hm⟩
theorem not_prefixIn_empty (a : Chain) (p : ℕ) : ¬PrefixIn (∅ : Finset (Chain × Fin w)) a p := by
  rintro ⟨q, -, hm⟩
  exact Finset.notMem_empty _ hm
theorem prefixIn_of_mem {S : Finset (Chain × Fin w)} {a : Chain} {q : Fin w} (h : (a, q) ∈ S) :
    PrefixIn S a q.val :=
  ⟨q, le_rfl, h⟩
theorem prefixIn_insert [DecidableEq Chain] {S : Finset (Chain × Fin w)} {x : Chain × Fin w} {a : Chain} {p : ℕ} :
    PrefixIn (insert x S) a p ↔ (x.1 = a ∧ x.2.val ≤ p) ∨ PrefixIn S a p := by
  constructor
  · rintro ⟨q, hq, hm⟩
    rcases Finset.mem_insert.mp hm with h | h
    · left
      subst h
      exact ⟨rfl, hq⟩
    · exact Or.inr ⟨q, hq, h⟩
  · rintro (⟨h1, h2⟩ | h)
    · refine ⟨x.2, h2, ?_⟩
      rw [← h1]
      exact Finset.mem_insert_self _ _
    · exact h.mono_set (Finset.subset_insert _ _)
theorem nonempty_of_prefixIn {S : Finset (Chain × Fin w)} {a : Chain} {p : ℕ} (h : PrefixIn S a p) :
    S.Nonempty := by
  obtain ⟨q, -, hm⟩ := h
  exact ⟨_, hm⟩
theorem two_le_card_of_prefixIn [DecidableEq Chain] {S : Finset (Chain × Fin w)} {a b : Chain} {p p' : ℕ}
    (hab : a ≠ b) (ha : PrefixIn S a p) (hb : PrefixIn S b p') : 2 ≤ S.card := by
  obtain ⟨q, -, hq⟩ := ha
  obtain ⟨q', -, hq'⟩ := hb
  have hne : ((a, q) : Chain × Fin w) ≠ (b, q') := fun h => hab (Prod.ext_iff.mp h).1
  have hsub : ({(a, q), (b, q')} : Finset (Chain × Fin w)) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hq
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact hq'
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair hne] at this
end Prefix
section Tracks
variable {Chain Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {w : ℕ}
structure PrefixTracks (Cov : Chain → ℕ → Prop) (before after : State (Chain × Fin w) Value Memory) : Prop where
  guesses : before.guesses ⊆ after.guesses
  retired : before.retired ⊆ after.retired
  origin : ∀ a p, PrefixIn after.retired a p →
    PrefixIn before.retired a p ∨ PrefixIn after.guesses a p ∨ Cov a p
theorem PrefixTracks.refl (Cov : Chain → ℕ → Prop) (state : State (Chain × Fin w) Value Memory) :
    PrefixTracks Cov state state :=
  ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ _ h => Or.inl h⟩
theorem PrefixTracks.mono {Cov Cov' : Chain → ℕ → Prop} {s s' : State (Chain × Fin w) Value Memory}
    (hc : ∀ a p, Cov a p → Cov' a p) (h : PrefixTracks Cov s s') : PrefixTracks Cov' s s' := by
  refine ⟨h.guesses, h.retired, fun a p hp => ?_⟩
  rcases h.origin a p hp with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (hc a p h1))
theorem PrefixTracks.trans {C1 C2 : Chain → ℕ → Prop} {s1 s2 s3 : State (Chain × Fin w) Value Memory}
    (first : PrefixTracks C1 s1 s2) (second : PrefixTracks C2 s2 s3) :
    PrefixTracks (fun a p => C1 a p ∨ C2 a p) s1 s3 := by
  refine ⟨first.guesses.trans second.guesses, first.retired.trans second.retired, fun a p hp => ?_⟩
  rcases second.origin a p hp with h | h | h
  · rcases first.origin a p h with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (h'.mono_set second.guesses))
    · exact Or.inr (Or.inr (Or.inl h'))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))
theorem PrefixTracks.trans_false {C : Chain → ℕ → Prop} {s1 s2 s3 : State (Chain × Fin w) Value Memory}
    (first : PrefixTracks C s1 s2) (second : PrefixTracks (fun _ _ => False) s2 s3) : PrefixTracks C s1 s3 :=
  (first.trans second).mono fun _ _ h => h.elim id False.elim
theorem prefixIn_guesses_of_tracks {Cov : Chain → ℕ → Prop} {init final : State (Chain × Fin w) Value Memory}
    (h : PrefixTracks Cov init final) (hinit : init.retired = ∅) {a : Chain} {p : ℕ}
    (hr : PrefixIn final.retired a p) (hc : ¬Cov a p) : PrefixIn final.guesses a p := by
  rcases h.origin a p hr with h1 | h1 | h1
  · rw [hinit] at h1
    exact absurd h1 (not_prefixIn_empty a p)
  · exact h1
  · exact absurd h1 hc
variable [DecidableEq Chain] [Fintype Chain] [DecidableEq Value]
omit [Fintype Chain] in
theorem afterTrial_tracks (environment : Environment auxSpec (Chain × Fin w) Value Memory)
    (state : State (Chain × Fin w) Value Memory) (coordinate : Chain × Fin w) (candidate : Value) (hit : Bool) :
    PrefixTracks (fun _ _ => False) state (afterTrial environment state coordinate candidate hit) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [afterTrial]
    split <;> simp only [Finset.subset_insert, Finset.Subset.refl]
  · simp only [afterTrial]
    split <;> simp only [Finset.subset_insert, Finset.Subset.refl]
  · intro a p hp
    simp only [afterTrial] at hp ⊢
    by_cases hh : hit = true
    · rw [if_pos hh, prefixIn_insert] at hp
      rcases hp with ⟨h1, h2⟩ | hp
      · by_cases hret : coordinate ∈ state.retired
        · left
          refine ⟨coordinate.2, h2, ?_⟩
          rw [← h1]
          exact hret
        · right; left
          rw [if_pos ⟨hh, hret⟩]
          refine ⟨coordinate.2, h2, ?_⟩
          rw [← h1]
          exact Finset.mem_insert_self _ _
      · exact Or.inl hp
    · rw [if_neg hh] at hp
      exact Or.inl hp
omit [Fintype Chain] [DecidableEq Value] in
theorem afterDisclosure_tracks_next (environment : Environment auxSpec (Chain × Fin w) Value Memory)
    (state : State (Chain × Fin w) Value Memory) (coordinate : Chain × Fin w) (value : Value)
    (hprev : PrefixIn state.retired coordinate.1 coordinate.2.val) :
    PrefixTracks (fun _ _ => False) state (afterDisclosure environment state coordinate value) := by
  refine ⟨Finset.Subset.refl _, Finset.subset_insert _ _, ?_⟩
  intro a p hp
  simp only [afterDisclosure] at hp ⊢
  rw [prefixIn_insert] at hp
  rcases hp with ⟨h1, h2⟩ | hp
  · left
    rw [← h1]
    exact hprev.mono_pos h2
  · exact Or.inl hp
omit [Fintype Chain] [DecidableEq Value] in
theorem afterDisclosure_tracks_cov (environment : Environment auxSpec (Chain × Fin w) Value Memory)
    (state : State (Chain × Fin w) Value Memory) (coordinate : Chain × Fin w) (value : Value) :
    PrefixTracks (fun a p => coordinate.1 = a ∧ coordinate.2.val ≤ p) state
      (afterDisclosure environment state coordinate value) := by
  refine ⟨Finset.Subset.refl _, Finset.subset_insert _ _, ?_⟩
  intro a p hp
  simp only [afterDisclosure] at hp ⊢
  rw [prefixIn_insert] at hp
  rcases hp with h | hp
  · exact Or.inr (Or.inr h)
  · exact Or.inl hp
omit [Fintype Chain] in
theorem mem_retired_afterTrial_hit (environment : Environment auxSpec (Chain × Fin w) Value Memory)
    (state : State (Chain × Fin w) Value Memory) (coordinate : Chain × Fin w) (candidate : Value) :
    coordinate ∈ (afterTrial environment state coordinate candidate true).retired := by
  simp only [afterTrial, if_true]
  exact Finset.mem_insert_self _ _
end Tracks
end ClaudeWCT.Guess
end
section
namespace ClaudeWCT.Guess
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Concrete
open SphincsSecurity.Concrete.SecretGuessObservation
set_option backward.isDefEq.respectTransparency false
section ChainWorld
variable {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {Chain V R : Type} {w : ℕ}
def trialQ (c : Chain × Fin w) (v : V) : OracleComp (World auxSpec (Chain × Fin w) V) Bool :=
  liftM ((World auxSpec (Chain × Fin w) V).query (.inr (.inl (c, v))))
def discloseQ (c : Chain × Fin w) : OracleComp (World auxSpec (Chain × Fin w) V) V :=
  liftM ((World auxSpec (Chain × Fin w) V).query (.inr (.inr c)))
def succPos (p : Fin w) : Option (Fin w) := if h : p.val + 1 < w then some ⟨p.val + 1, h⟩ else none
theorem succPos_val {p p' : Fin w} (h : succPos p = some p') : p'.val = p.val + 1 := by
  unfold succPos at h
  split at h
  · cases h; rfl
  · cases h
def probeW (step : Chain → Fin w → V → R) (top : Chain → R) (miss : R) (a : Chain) (p : Fin w) (v : V) :
    OracleComp (World auxSpec (Chain × Fin w) V) R := do
  let hit ← trialQ (auxSpec := auxSpec) (a, p) v
  if hit then
    match succPos p with
    | some p' => do
        let next ← discloseQ (auxSpec := auxSpec) (a, p')
        pure (step a p next)
    | none => pure (top a)
  else pure miss
def probeAnswer [DecidableEq V] (step : Chain → Fin w → V → R) (top : Chain → R) (miss : R)
    (g : Chain × Fin w → V) (a : Chain) (p : Fin w) (v : V) : R :=
  if g (a, p) = v then
    (match succPos p with
      | some p' => step a p (g (a, p'))
      | none => top a)
  else miss
def discloseAll (cs : List (Chain × Fin w)) : OracleComp (World auxSpec (Chain × Fin w) V) (List V) :=
  cs.mapM fun c => discloseQ (auxSpec := auxSpec) c
variable [DecidableEq Chain] [DecidableEq V]
omit [DecidableEq Chain] in
theorem fixed_probeW (auxiliary : QueryImpl auxSpec ProbComp) (g : Chain × Fin w → V)
    (step : Chain → Fin w → V → R) (top : Chain → R) (miss : R) (a : Chain) (p : Fin w) (v : V) :
    simulateQ (fixedAnswers auxiliary g) (probeW (auxSpec := auxSpec) step top miss a p v) =
      pure (probeAnswer step top miss g a p v) := by
  unfold probeW probeAnswer trialQ
  rw [simulateQ_bind, simulateQ_spec_query]
  change (pure (decide (g (a, p) = v)) >>= _) = _
  rw [pure_bind]
  by_cases hv : g (a, p) = v
  · simp only [hv, decide_true, if_true]
    cases succPos p with
    | none => simp only [simulateQ_pure]
    | some p' =>
        simp only
        unfold discloseQ
        rw [simulateQ_bind, simulateQ_spec_query]
        change (pure (g (a, p')) >>= _) = _
        rw [pure_bind, simulateQ_pure]
  · simp only [hv, decide_false, Bool.false_eq_true, if_false, simulateQ_pure]
omit [DecidableEq Chain] in
theorem fixed_discloseQ (auxiliary : QueryImpl auxSpec ProbComp) (g : Chain × Fin w → V) (c : Chain × Fin w) :
    simulateQ (fixedAnswers auxiliary g) (discloseQ (auxSpec := auxSpec) c) = pure (g c) := by
  unfold discloseQ
  rw [simulateQ_spec_query]
  rfl
omit [DecidableEq Chain] in
theorem fixed_discloseAll (auxiliary : QueryImpl auxSpec ProbComp) (g : Chain × Fin w → V)
    (cs : List (Chain × Fin w)) :
    simulateQ (fixedAnswers auxiliary g) (discloseAll (auxSpec := auxSpec) cs) = pure (cs.map g) := by
  induction cs with
  | nil => simp [discloseAll]
  | cons c rest ih =>
      unfold discloseAll at ih ⊢
      rw [List.mapM_cons, simulateQ_bind, fixed_discloseQ, pure_bind, simulateQ_bind, ih, pure_bind,
        simulateQ_pure]
      simp
variable {Memory : Type}
theorem fixedRun_bind_nonzero' {First Result : Type} (environment : Environment auxSpec (Chain × Fin w) V Memory)
    (g : Chain × Fin w → V) (first : OracleComp (World auxSpec (Chain × Fin w) V) First)
    (next : First → OracleComp (World auxSpec (Chain × Fin w) V) Result) (state : State (Chain × Fin w) V Memory)
    (result : Result × State (Chain × Fin w) V Memory) (hr : fixedRun environment g (first >>= next) state result ≠ 0) :
    ∃ middle, fixedRun environment g first state middle ≠ 0 ∧ fixedRun environment g (next middle.1) middle.2 result ≠ 0 := by
  unfold fixedRun runWith at hr ⊢
  rw [simulateQ_bind, StateT.run_bind, RetainedObservation.bind_nonzero] at hr
  exact hr
theorem fixedRun_pure_nonzero' {Result : Type} (environment : Environment auxSpec (Chain × Fin w) V Memory)
    (g : Chain × Fin w → V) (value : Result) (state : State (Chain × Fin w) V Memory)
    (result : Result × State (Chain × Fin w) V Memory) (hr : fixedRun environment g (pure value) state result ≠ 0) :
    result = (value, state) := by
  unfold fixedRun at hr
  rw [runWith_pure] at hr
  simpa only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr
theorem fixedRun_trialQ (environment : Environment auxSpec (Chain × Fin w) V Memory) (g : Chain × Fin w → V)
    (c : Chain × Fin w) (v : V) (state : State (Chain × Fin w) V Memory) (result : Bool × State (Chain × Fin w) V Memory)
    (hr : fixedRun environment g (trialQ (auxSpec := auxSpec) c v) state result ≠ 0) :
    result = (decide (g c = v), afterTrial environment state c v (decide (g c = v))) := by
  unfold fixedRun runWith trialQ at hr
  rw [simulateQ_spec_query] at hr
  simpa only [fixedImpl, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr
theorem fixedRun_discloseQ (environment : Environment auxSpec (Chain × Fin w) V Memory) (g : Chain × Fin w → V)
    (c : Chain × Fin w) (state : State (Chain × Fin w) V Memory) (result : V × State (Chain × Fin w) V Memory)
    (hr : fixedRun environment g (discloseQ (auxSpec := auxSpec) c) state result ≠ 0) :
    result = (g c, afterDisclosure environment state c (g c)) := by
  unfold fixedRun runWith discloseQ at hr
  rw [simulateQ_spec_query] at hr
  simpa only [fixedImpl, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr
theorem fixedRun_probeW (environment : Environment auxSpec (Chain × Fin w) V Memory) (g : Chain × Fin w → V)
    (step : Chain → Fin w → V → R) (top : Chain → R) (miss : R) (a : Chain) (p : Fin w) (v : V)
    (state : State (Chain × Fin w) V Memory) (result : R × State (Chain × Fin w) V Memory)
    (hr : fixedRun environment g (probeW (auxSpec := auxSpec) step top miss a p v) state result ≠ 0) :
    result.1 = probeAnswer step top miss g a p v ∧
      PrefixTracks (fun _ _ => False) state result.2 ∧
      result.2.probes = state.probes + 1 ∧
      result.2.guesses ⊆ insert (a, p) state.guesses ∧
      (g (a, p) = v → (a, p) ∈ result.2.retired) := by
  unfold probeW at hr
  obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero' environment g _ _ state result hr
  have hmid := fixedRun_trialQ environment g (a, p) v state middle hm
  subst hmid
  have htrial := afterTrial_tracks environment state (a, p) v (decide (g (a, p) = v))
  have hguess1 : (afterTrial environment state (a, p) v (decide (g (a, p) = v))).guesses ⊆
      insert (a, p) state.guesses := by
    simp only [afterTrial]
    split <;> simp only [Finset.Subset.refl, Finset.subset_insert]
  by_cases hv : g (a, p) = v
  · have hhit : decide (g (a, p) = v) = true := decide_eq_true hv
    simp only [hhit, if_true] at hr
    have hret : (a, p) ∈ (afterTrial environment state (a, p) v true).retired :=
      mem_retired_afterTrial_hit environment state (a, p) v
    rw [hhit] at htrial hguess1
    cases hs : succPos p with
    | none =>
        rw [hs] at hr
        have h := fixedRun_pure_nonzero' environment g _ _ result hr
        subst h
        refine ⟨by simp [probeAnswer, hv, hs], htrial, by simp [afterTrial], hguess1, fun _ => hret⟩
    | some p' =>
        rw [hs] at hr
        obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero' environment g _ _ _ result hr
        have htl := fixedRun_discloseQ environment g (a, p') _ tail ht
        subst htl
        have h := fixedRun_pure_nonzero' environment g _ _ result hr
        subst h
        have hnext := afterDisclosure_tracks_next environment (afterTrial environment state (a, p) v true) (a, p')
          (g (a, p')) ⟨p, by rw [succPos_val hs]; omega, hret⟩
        refine ⟨by simp [probeAnswer, hv, hs], htrial.trans_false hnext, by simp [afterDisclosure, afterTrial],
          by simpa [afterDisclosure] using hguess1, fun _ => Finset.mem_insert_of_mem hret⟩
  · have hmiss : decide (g (a, p) = v) = false := decide_eq_false hv
    simp only [hmiss, Bool.false_eq_true, if_false] at hr
    have h := fixedRun_pure_nonzero' environment g _ _ result hr
    subst h
    rw [hmiss] at htrial hguess1
    exact ⟨by simp [probeAnswer, hv], htrial, by simp [afterTrial], hguess1, fun h => absurd h hv⟩
theorem fixedRun_discloseAll (environment : Environment auxSpec (Chain × Fin w) V Memory) (g : Chain × Fin w → V)
    (cs : List (Chain × Fin w)) (state : State (Chain × Fin w) V Memory)
    (result : List V × State (Chain × Fin w) V Memory)
    (hr : fixedRun environment g (discloseAll (auxSpec := auxSpec) cs) state result ≠ 0) :
    result.1 = cs.map g ∧ result.2.probes = state.probes ∧ result.2.guesses = state.guesses ∧
      PrefixTracks (fun a p => ∃ c ∈ cs, c.1 = a ∧ c.2.val ≤ p) state result.2 := by
  induction cs generalizing state result with
  | nil =>
      have h := fixedRun_pure_nonzero' environment g _ state result hr
      subst h
      exact ⟨rfl, rfl, rfl, PrefixTracks.refl _ _⟩
  | cons c rest ih =>
      unfold discloseAll at hr
      rw [List.mapM_cons] at hr
      obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero' environment g _ _ state result hr
      have hmid := fixedRun_discloseQ environment g c state middle hm
      subst hmid
      obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero' environment g _ _ _ result hr
      have h := fixedRun_pure_nonzero' environment g _ _ result hr
      subst h
      obtain ⟨h1, h2, h3, h4⟩ := ih _ tail ht
      refine ⟨by simp [h1], by rw [h2]; rfl, by rw [h3]; rfl, ?_⟩
      refine ((afterDisclosure_tracks_cov environment state c (g c)).trans h4).mono ?_
      rintro a p (⟨h1, h2⟩ | ⟨c', hc', h1, h2⟩)
      · exact ⟨c, List.mem_cons_self, h1, h2⟩
      · exact ⟨c', List.mem_cons_of_mem _ hc', h1, h2⟩
end ChainWorld
end ClaudeWCT.Guess
end
section
namespace ClaudeWCT.Guess
open OracleComp OracleSpec
open SigGolfCandidate.T3 ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem eval_shortHash (A : Correctness.Answers) (input : HashInput) :
    evalWithAnswerFn A (shortHash input) = (A (.inl (.inr (pad64 input)))).extractLsb' 0 128 := rfl
/-- Witness stack: an FTS step keeps the half `ftsChainHigh i step` (HIGH for G chains 1, 3 on steps < 3). -/
theorem eval_projHash (A : Correctness.Answers) (high : Bool) (input : HashInput) :
    evalWithAnswerFn A (projHash high input) = projHalf high (A (.inl (.inr (pad64 input)))) := rfl
theorem eval_chain_walk (A : Correctness.Answers) (index coord selected i : Nat) (val : Nat → Digest) (s n : Nat)
    (hstep : ∀ p, s ≤ p → p < s + n →
      projHalf (ftsChainHigh i p) (A (.inl (.inr (WCT9.ftsChainInputW index coord selected i p (val p))))) =
        val (p + 1)) :
    evalWithAnswerFn A (WCT9.chain index coord selected i s n (val s)) = val (s + n) := by
  induction n generalizing s with
  | zero => simp [WCT9.chain, evalWithAnswerFn_pure]
  | succ n ih =>
      unfold WCT9.chain
      rw [List.range'_succ, List.foldlM_cons, evalWithAnswerFn_bind, eval_projHash, WCT9.ftsChainInputW_padded,
        hstep s le_rfl (by omega)]
      have := ih (s + 1) (fun p h1 h2 => hstep p (by omega) (by omega))
      unfold WCT9.chain at this
      rw [this]
      congr 1
      omega
theorem queried_chain_walk (A : Correctness.Answers) (index coord selected i : Nat) (val : Nat → Digest) (s n : Nat)
    (hstep : ∀ p, s ≤ p → p < s + n →
      projHalf (ftsChainHigh i p) (A (.inl (.inr (WCT9.ftsChainInputW index coord selected i p (val p))))) =
        val (p + 1))
    (p : Nat) (h1 : s ≤ p) (h2 : p < s + n) :
    (.inl (.inr (WCT9.ftsChainInputW index coord selected i p (val p))) : Spec.Domain) ∈
      Security.SourceReplay.queried A (WCT9.chain index coord selected i s n (val s)) := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
      unfold WCT9.chain
      rw [List.range'_succ, List.foldlM_cons, Security.SourceReplay.queried_bind, queried_projHash,
        WCT9.ftsChainInputW_padded]
      by_cases hp : p = s
      · subst hp
        exact List.mem_append_left _ (List.mem_singleton_self _)
      · apply List.mem_append_right
        rw [eval_projHash, WCT9.ftsChainInputW_padded, hstep s le_rfl (by omega)]
        have := ih (s + 1) (fun p h1 h2 => hstep p (by omega) (by omega)) (by omega) (by omega)
        unfold WCT9.chain at this
        exact this
theorem chainValue_walk (A : Correctness.Answers) (a : ChainAddr) (s n : Nat) :
    evalWithAnswerFn A (WCT9.chain a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val s n (chainValue A a s)) =
      chainValue A a (s + n) := by
  unfold chainValue WCT9.chain
  have hr : List.range' 0 (s + n) = List.range' 0 s ++ List.range' s n := by
    have := List.range'_append (s := 0) (m := s) (n := n) (step := 1)
    simpa [Nat.add_comm] using this.symm
  rw [hr, List.foldlM_append, evalWithAnswerFn_bind]
theorem chainValue_succ (A : Correctness.Answers) (a : ChainAddr) (p : Nat) :
    projHalf (ftsChainHigh a.2.2.2.val p)
      (A (.inl (.inr (WCT9.ftsChainInputW a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val p (chainValue A a p))))) =
      chainValue A a (p + 1) := by
  have h := chainValue_walk A a p 1
  unfold WCT9.chain at h
  simp only [List.range'_one, List.foldlM_cons, List.foldlM_nil, evalWithAnswerFn_bind, eval_projHash,
    evalWithAnswerFn_pure] at h
  rw [WCT9.ftsChainInputW_padded] at h
  exact h
end ClaudeWCT.Guess
end
section
namespace ClaudeWCT.Guess
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open SphincsSecurity.Concrete
open SphincsSecurity.Concrete.SecretGuessObservation
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-- A chain-probe world with hidden parameter `h : H`: answers, the table `view h` it exposes on chain probes, and
the public step/top/miss answers (campaign X1: `H` carries the FTS seed-family coefficients and the step labels). -/
structure ChainTable (H : Type) where
  answers : H → Correctness.Answers
  view : H → GCoord → Digest
  base : H
  step : ChainAddr → Fin 4 → Digest → HashOutput
  top : ChainAddr → HashOutput
  miss : HashInput → HashOutput
  answers_probe : ∀ h a p c, answers h (.inl (.inr (probeInput a p c))) =
    probeAnswer step top (miss (probeInput a p c)) (view h) a p c
  answers_public : ∀ h h' x, decodeProbe x = none → answers h (.inl (.inr x)) = answers h' (.inl (.inr x))
  step_low : ∀ a p v, projHalf (ftsChainHigh a.2.2.2.val p.val) (step a p v) = v
  seed : ∀ h a, seedOf (answers h) a = view h (a, 0)
namespace ChainTable
variable {H : Type} (T : ChainTable H)
noncomputable def walkVal (h : H) (a : ChainAddr) (p : Nat) : Digest :=
  if hp : p < 4 then T.view h (a, ⟨p, hp⟩) else (T.top a).extractLsb' 0 128
theorem walk_step (h : H) (a : ChainAddr) (p : Nat) (hp : p < 4) :
    projHalf (ftsChainHigh a.2.2.2.val p) (T.answers h (.inl (.inr (WCT9.ftsChainInputW a.1.val a.2.1.val
      a.2.2.1.val a.2.2.2.val p (T.walkVal h a p))))) = T.walkVal h a (p + 1) := by
  have hq := T.answers_probe h a ⟨p, hp⟩ (T.walkVal h a p)
  unfold probeInput at hq
  simp only at hq
  rw [hq]
  have hv : T.view h (a, ⟨p, hp⟩) = T.walkVal h a p := by simp [walkVal, hp]
  unfold probeAnswer
  rw [if_pos hv]
  unfold succPos
  by_cases h1 : p + 1 < 4
  · rw [dif_pos h1]
    simp only
    have hs := T.step_low a ⟨p, hp⟩
    simp only at hs
    rw [hs]
    simp [walkVal, h1]
  · rw [dif_neg h1]
    simp only
    have hp3 : p = 3 := by omega
    subst hp3
    rw [WCT9.ftsChainHigh_three, projHalf_false]
    simp [walkVal, h1]
theorem chainValue_answers (h : H) (a : ChainAddr) (p : Nat) (hp : p ≤ 4) :
    chainValue (T.answers h) a p = T.walkVal h a p := by
  have h0 : seedOf (T.answers h) a = T.walkVal h a 0 := by rw [T.seed]; simp [walkVal]
  unfold chainValue
  rw [h0]
  have := eval_chain_walk (T.answers h) a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val (T.walkVal h a) 0 p
    (fun q _ hq => T.walk_step h a q (by omega))
  simpa using this
theorem chainValue_answers_fin (h : H) (c : GCoord) :
    chainValue (T.answers h) c.1 c.2.val = T.view h c := by
  rw [T.chainValue_answers h c.1 c.2.val (by omega)]
  simp [walkVal, c.2.isLt]
theorem honestProbe_answers (h : H) (c : GCoord) :
    honestProbe (T.answers h) c = probeInput c.1 c.2 (T.view h c) := by
  unfold honestProbe
  rw [T.chainValue_answers_fin]
variable {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
noncomputable def hashW (x : HashInput) : OracleComp (World auxSpec GCoord Digest) HashOutput :=
  match decodeProbe x with
  | none => pure (T.answers T.base (.inl (.inr x)))
  | some q => probeW (auxSpec := auxSpec) T.step T.top (T.miss x) q.1.1 q.1.2 q.2
theorem fixed_hashW (auxiliary : QueryImpl auxSpec ProbComp) (h : H) (x : HashInput) :
    simulateQ (fixedAnswers auxiliary (T.view h)) (T.hashW (auxSpec := auxSpec) x) =
      pure (T.answers h (.inl (.inr x))) := by
  unfold hashW
  cases hd : decodeProbe x with
  | none =>
      simp only [simulateQ_pure]
      rw [T.answers_public h T.base x hd]
  | some q =>
      simp only
      rw [fixed_probeW, eq_of_decodeProbe hd, T.answers_probe]
theorem fixedRun_hashW {Memory : Type} (environment : Environment auxSpec GCoord Digest Memory)
    (h : H) (x : HashInput) (state : State GCoord Digest Memory)
    (result : HashOutput × State GCoord Digest Memory)
    (hr : fixedRun environment (T.view h) (T.hashW (auxSpec := auxSpec) x) state result ≠ 0) :
    result.1 = T.answers h (.inl (.inr x)) ∧
      PrefixTracks (fun _ _ => False) state result.2 ∧
      result.2.probes ≤ state.probes + 1 ∧
      (∀ c : GCoord, x = honestProbe (T.answers h) c → c ∈ result.2.retired) := by
  unfold hashW at hr
  cases hd : decodeProbe x with
  | none =>
      rw [hd] at hr
      have hh := fixedRun_pure_nonzero' environment (T.view h) _ state result hr
      subst hh
      refine ⟨T.answers_public _ h x hd, PrefixTracks.refl _ _, Nat.le_succ _, ?_⟩
      intro c hc
      rw [hc, honestProbe, decodeProbe_probeInput] at hd
      cases hd
  | some q =>
      rw [hd] at hr
      obtain ⟨h1, h2, h3, -, h5⟩ := fixedRun_probeW environment (T.view h) T.step T.top (T.miss x) q.1.1 q.1.2 q.2
        state result hr
      have hx := eq_of_decodeProbe hd
      refine ⟨?_, h2, h3.le, ?_⟩
      · rw [h1, hx, T.answers_probe]
      · intro c hc
        rw [T.honestProbe_answers, hx] at hc
        obtain ⟨ha, hp, hv⟩ := probeInput_injective hc
        have hcq : c = q.1 := Prod.ext ha.symm hp.symm
        subst hcq
        exact h5 hv.symm
end ChainTable
end ClaudeWCT.Guess
end
end
