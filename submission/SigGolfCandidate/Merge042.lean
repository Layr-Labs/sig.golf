import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import SigGolfCandidate.Merge003
import SigGolfCandidate.Merge015
import SigGolfCandidate.Merge017
import SigGolfCandidate.Merge028
import SigGolfCandidate.Merge030
import SigGolfCandidate.Merge032
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge039
import SigGolfCandidate.Merge040
import SigGolfCandidate.Merge041

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
-- ==== merged from ClaudeWCT_Numerics_TopZeroChecks ====
section

/-! # Top layer (campaign T51): the canonical top histograms and the T51 signing-moment packet
The canonical top producer accepts a word only if at most 7 of its 51 digits (the checksum included) are zero
(`ClaudeWCT.WCT9.producerZeroCap 0 = 7`), at the top floor 14 with the d6b LOW bonus 2. This module provides
* the canonical statistics of the T51 model word (`SigGolfResearch.T51Top`): the zero-fibered packed generating
  polynomial (`stat = 32712·zeros + 141·weight + score`, radix `2^128`, zero counts `< 8`), whose windows are the
  exact top credit histograms `topCountsT51` / `topFreeCountsT51` (kernel checks), and the bridge from the T51 top
  digests to the model (`wordCredit`, `savedCopies`, `topDispatchPenalty`, zero digits, `TopChoice.blocked`);
* the canonical top API at the T51 floor (`ClaudeWCT.W9.T3.ProducerV5.Canonical`: `topWordCount`, `topFreeCount_eq`,
  `topHighWeight`, `selected_top_path_card`, `producerDecodeAt_top_credit_lt`);
* the T51 signing-moment packet (`ClaudeWCT.Numerics.TopZero`): top counts (credit ≥ 12), the d6b split histogram,
  the initial bound (floor 14, pool 69), the fixed power (fixed sign work 112326) and the full moment
  (1.999750417 < 1.99976; RC: gate 791, cap 777). -/

namespace SigGolfResearch.T51Top
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

/-- The canonical statistic `32712 * zeros + 141 * weight + score`. -/
def canonS : GStat := ⟨fun g r => tstat 6 (decide (g.val = 0)) false r, fun j r => tstat 5 false (pen j) r, pstat⟩
theorem canonS_eval (w : «Word») : canonS.eval w = SigGolfResearch.T51Top.stat w := rfl

/-- Zero counts below 8. -/
def cutExp : Nat := 32712 * 8
def packedT (free : Bool) : Nat := packedG cutExp canonS free
attribute [irreducible] packedT

def Sk (free : Bool) (k : Nat) (w : «Word») : Prop := (free = true → isFree w) ∧ SigGolfResearch.T51Top.stat w = k
instance (free : Bool) (k : Nat) : DecidablePred (Sk free k) := fun w => by unfold Sk; infer_instance
def cnt (free : Bool) (k : Nat) : Nat := (univ.filter (Sk free k)).card
attribute [irreducible] cnt

theorem packedT_cnt (free : Bool) (k : Nat) (hk : k < cutExp) : packedT free / B ^ k % B = cnt free k := by
  rw [packedT, packedG_digit _ _ _ _ hk, cnt]
  rfl

/-! ### Histogram windows
A credit `c` (no path bonus) of an accepted top word is `score + [checksum = 4] - 3`; the checksum digit is
`d = 152 - weight ∈ [0, 5]`, and the zero filter is `zeros + [d = 0] ≤ 7`. For each admissible `(d, z)` the
coefficients of the credits `12 ..< 138` form one window of 126 radix-`B` digits. -/
def pairsL : List (Nat × Nat) :=
  ((List.range 6).flatMap fun d => (List.range 8).map fun z => (d, z)).filter
    fun pr => decide (pr.2 + ind (pr.1 = 0) ≤ 7)
def pos (pr : Nat × Nat) (c : Nat) : Nat := 32712 * pr.2 + 141 * (152 - pr.1) + (c + 3 - ind (pr.1 = 4))
def winLen : Nat := 126
def window (p : Nat) (pr : Nat × Nat) : Nat := (p >>> (128 * pos pr 12)) % B ^ winLen
def windows (free : Bool) : List Nat := pairsL.map (window (packedT free))
attribute [irreducible] windows
def digitAt (i W : Nat) : Nat := (W >>> (128 * i)) % B
def histAt (ws : List Nat) (i : Nat) : Nat := (ws.map (digitAt i)).sum
def histW (h : List (Nat × Nat)) (c : Nat) : Nat := (h.map fun e => if e.1 = c then e.2 else 0).sum
def histCheck (counts : List (Nat × Nat)) (free : Bool) : Bool :=
  (List.range winLen).all fun i => histW counts (12 + i) == histAt (windows free) i

theorem pairsL_nodup : pairsL.Nodup := by decide
theorem mem_pairsL (d z : Nat) : (d, z) ∈ pairsL ↔ d < 6 ∧ z < 8 ∧ z + ind (d = 0) ≤ 7 := by
  simp only [pairsL, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a, ha, b, hb, rfl, rfl⟩, h⟩; exact ⟨ha, hb, h⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨d, h1, z, h2, rfl, rfl⟩, h3⟩

attribute [irreducible] pairsL

theorem shiftRight_B (p n : Nat) : p >>> (128 * n) = p / B ^ n := by
  rw [Nat.shiftRight_eq_div_pow, B, ← pow_mul]

theorem window_digit (p : Nat) (pr : Nat × Nat) (i : Nat) (hi : i < winLen) :
    (window p pr >>> (128 * i)) % B = p / B ^ (pos pr 12 + i) % B := by
  rw [window, shiftRight_B, shiftRight_B, digit_mod_pow _ _ _ _ hi, Nat.div_div_eq_div_mul, ← pow_add]

theorem pos_add (pr : Nat × Nat) (i : Nat) : pos pr (12 + i) = pos pr 12 + i := by
  unfold pos ind; split_ifs <;> omega

theorem pos_lt (d z : Nat) (hpr : (d, z) ∈ pairsL) (c : Nat) (hc : c < 138) : pos (d, z) c < cutExp := by
  obtain ⟨h1, h2, h3⟩ := (mem_pairsL d z).mp hpr
  have hi := ind_le (d = 4)
  show 32712 * z + 141 * (152 - d) + (c + 3 - ind (d = 4)) < 32712 * 8
  omega

theorem sum_map_map_congr {α β : Type} (l : List α) (f : α → β) (g : β → Nat) (h : α → Nat)
    (H : ∀ a ∈ l, g (f a) = h a) : ((l.map f).map g).sum = (l.map h).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [H a (by simp), ih (fun b hb => H b (by simp [hb]))]

theorem histAt_eq (free : Bool) (i : Nat) (hi : i < winLen) :
    histAt (windows free) i = (pairsL.map fun pr => cnt free (pos pr (12 + i))).sum := by
  have hmap : ∀ pr ∈ pairsL, digitAt i (window (packedT free) pr) = cnt free (pos pr (12 + i)) := by
    intro pr hpr
    obtain ⟨d, z⟩ := pr
    rw [digitAt, window_digit _ _ _ hi, ← pos_add]
    exact packedT_cnt free _ (pos_lt d z hpr _ (by unfold winLen at hi; omega))
  unfold histAt
  rw [windows]
  exact sum_map_map_congr pairsL (window (packedT free)) (digitAt i) _ hmap

/-- The model predicate of an accepted top word of credit `c` (no path bonus). -/
def accepts (c : Nat) (w : «Word») : Prop :=
  147 ≤ SigGolfResearch.T51Top.weight w ∧ SigGolfResearch.T51Top.weight w ≤ 152 ∧ SigGolfResearch.T51Top.zeros w + ind (SigGolfResearch.T51Top.weight w = 152) ≤ 7 ∧ SigGolfResearch.T51Top.score w + ind (SigGolfResearch.T51Top.weight w = 148) = c + 3
def Qc (free : Bool) (c : Nat) (w : «Word») : Prop := (free = true → isFree w) ∧ accepts c w
instance (free : Bool) (c : Nat) : DecidablePred (Qc free c) := fun w => by unfold Qc accepts; infer_instance

theorem accepts_le {c : Nat} {w : «Word»} (h : accepts c w) : c ≤ 137 := by
  have := score_le w
  have := ind_le (SigGolfResearch.T51Top.weight w = 148)
  unfold accepts at h
  omega

theorem key_mem (c : Nat) (w : «Word») (h : accepts c w) : (152 - SigGolfResearch.T51Top.weight w, SigGolfResearch.T51Top.zeros w) ∈ pairsL := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine (mem_pairsL _ _).mpr ⟨by omega, ?_, ?_⟩
  · have := ind_le (SigGolfResearch.T51Top.weight w = 152); omega
  · by_cases w3 : SigGolfResearch.T51Top.weight w = 152
    · rw [ind_pos w3] at h3; rw [ind_pos (by omega)]; omega
    · rw [ind_neg w3] at h3; rw [ind_neg (by omega)]; omega

theorem fiber_eq (free : Bool) (c : Nat) (hc2 : c < 138) (d z : Nat) (hd : d < 6) (hz8 : z < 8)
    (hz7 : z + ind (d = 0) ≤ 7) (w : «Word») :
    (Qc free c w ∧ (152 - SigGolfResearch.T51Top.weight w, SigGolfResearch.T51Top.zeros w) = (d, z)) ↔ Sk free (pos (d, z) c) w := by
  have hs := stat_eq w
  have hsc := score_le w
  have hw := weight_le w
  unfold Qc accepts Sk
  rw [Prod.mk.injEq]
  show _ ↔ _ ∧ SigGolfResearch.T51Top.stat w = 32712 * z + 141 * (152 - d) + (c + 3 - ind (d = 4))
  rcases ind_cases (d = 4) with ⟨i4, e4⟩ | ⟨i4, e4⟩ <;> rw [e4] <;>
  rcases ind_cases (d = 0) with ⟨i0, e0⟩ | ⟨i0, e0⟩ <;> rw [e0] at hz7 <;>
  rcases ind_cases (SigGolfResearch.T51Top.weight w = 152) with ⟨i3, e3⟩ | ⟨i3, e3⟩ <;> rw [e3] <;>
  rcases ind_cases (SigGolfResearch.T51Top.weight w = 148) with ⟨i7, e7⟩ | ⟨i7, e7⟩ <;> rw [e7] <;>
  · constructor
    · intro h
      have g1 := h.1.2.1
      have g2 := h.1.2.2.1
      have g3 := h.1.2.2.2.1
      have g4 := h.1.2.2.2.2
      have g5 := h.2.1
      have g6 := h.2.2
      exact ⟨h.1.1, by omega⟩
    · intro h
      have g := h.2
      have k1 : 147 ≤ SigGolfResearch.T51Top.weight w := by omega
      have k2 : SigGolfResearch.T51Top.weight w ≤ 152 := by omega
      have k3 : SigGolfResearch.T51Top.zeros w = z := by omega
      have k4 : 152 - SigGolfResearch.T51Top.weight w = d := by omega
      exact ⟨⟨h.1, k1, k2, by omega, by omega⟩, k4, k3⟩

theorem model_count (free : Bool) (c : Nat) (hc1 : 12 ≤ c) (hc2 : c < 138) :
    (univ.filter (Qc free c)).card = histAt (windows free) (c - 12) := by
  rw [histAt_eq free _ (by unfold winLen; omega), show 12 + (c - 12) = c by omega,
    ← List.sum_toFinset _ pairsL_nodup]
  rw [fiber_card_filter (Qc free c) (fun w => (152 - SigGolfResearch.T51Top.weight w, SigGolfResearch.T51Top.zeros w)) pairsL.toFinset
    (fun w hq => List.mem_toFinset.mpr (key_mem c w hq.2))]
  apply Finset.sum_congr rfl
  intro pr hpr
  obtain ⟨d, z⟩ := pr
  obtain ⟨hd, hz8, hz7⟩ := (mem_pairsL d z).mp (List.mem_toFinset.mp hpr)
  rw [cnt, Finset.filter_filter]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  exact fiber_eq free c hc2 d z hd hz8 hz7 w

theorem model_count_of_check (counts : List (Nat × Nat)) (free : Bool) (h : histCheck counts free = true)
    (c : Nat) (hc1 : 12 ≤ c) (hc2 : c < 138) :
    (univ.filter (Qc free c)).card = histW counts c := by
  rw [model_count free c hc1 hc2]
  unfold histCheck at h
  rw [List.all_eq_true] at h
  have := h (c - 12) (List.mem_range.mpr (by unfold winLen; omega))
  rw [beq_iff_eq, show 12 + (c - 12) = c by omega] at this
  exact this.symm

end SigGolfResearch.T51Top

namespace SigGolfResearch.T51Top
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Accepted top words (digit sum 152, zeros `≤ 7`, the checksum included) by credit `c ≥ 12` (reward - penalty, no
path bonus). -/
def topCountsT51 : List (Nat × Nat) := [(12,315267888952829519964878148817408),(13,502581346701182045522268145774137),(14,752511626605814064391474231634097),(15,1065558889020304945675904928167367),(16,1435173543730904921684088400733665),(17,1847358414495983032061822829906264),(18,2281059026126517901177221012090047),(19,2710088137917419774744565183673440),(20,3106381285222563864679340438895972),(21,3443101210383762587339493452981998),(22,3697164833100889464932241878451900),(23,3851950020861338549606416396512391),(24,3899466402443270255183300791298816),(25,3840497083895266749755782060534290),(26,3683438290245130298421569470678936),(27,3443246811490046271672743583069683),(28,3139756159292829995297839335681433),(29,2794787539114124815693836628274285),(30,2429665578785143309544744767521438),(31,2063911680114308962796572867575890),(32,1713979195232822763579746142893595),(33,1392034529852189954508107526852456),(34,1105873428300327158397997185708580),(35,859565447621140307361943490363595),(36,653882477690401234607090421926351),(37,486856173817396099173657622031378),(38,354782414252248455204523845017178),(39,253070632192734928840467446199840),(40,176719187273282712210967289445601),(41,120779088503944530431991335270023),(42,80776907135688649363243261396168),(43,52870350636583016492232039516898),(44,33860738089922211619787018377115),(45,21208781064250528632644276779374),(46,12989906571273476445322356097518),(47,7780272589154649898193776372287),(48,4554308446783618596549660812911),(49,2603689645505090258870517889338),(50,1453957434519794999076766650058),(51,792910168967510598376785179942),(52,421760455281535110174513103031),(53,218725672809233917248828043613),(54,110652438871872713032333839247),(55,54543565521105730781452342433),(56,26150796855825835062166991600),(57,12205435648988997694899471032),(58,5547018465369871787926613938),(59,2446663600613089231928625868),(60,1046684360751594765503422443),(61,435598336819529787498090077),(62,175805023853601196223333167),(63,68449619613514022562097299),(64,25841717283341691968204252),(65,9478773374051756905910165),(66,3336656681249301760085315),(67,1128696760071200189970841),(68,372452471932842146413249),(69,117949362025534644968846),(70,35221179476225672079433),(71,10260006775364160419227),(72,2913115076880581317101),(73,758493754933562958424),(74,188769225925145507859),(75,47894625739629217091),(76,10845676719716212822),(77,2151833132882470252),(78,474642317931986090),(79,97255931088472544),(80,14591562005458974),(81,2630076595352220),(82,492925440180390),(83,40324945858980),(84,4360291116622),(85,1324310968456),(86,121038590736),(87,875923776),(88,287165088)]
/-- The same restricted to words whose LOW half is not forced (r6 group 8 rank `≥ 64`). -/
def topFreeCountsT51 : List (Nat × Nat) := [(12,282559939817465342628440835330478),(13,449531826473941812198654424498336),(14,671679536679118155878398264670365),(15,949057367256986544053436168665683),(16,1275426698651883430286602707781017),(17,1637974563793195715116183500128883),(18,2017746308622482177055320174126433),(19,2391428081759058874794028308265531),(20,2734273530578908023550395197329282),(21,3022865586093975226088057177011379),(22,3237339642185944724382107443046154),(23,3363715886763297140030052612232182),(24,3395714150629552737366614323529813),(25,3334783194955924198019678398722140),(26,3188999364365112193419670485694138),(27,2972052559251269626688486169073355),(28,2701696952482902936298571014698086),(29,2397206605668107613542592052829741),(30,2077218548921436478696536057990486),(31,1758604203314945787643422806975417),(32,1455405459748317766481802777336458),(33,1177845305972739623289320776378780),(34,932311767924861340017826228798971),(35,721951883754901994367106738366398),(36,547085919166208939675385961604751),(37,405727266483366872683046760520036),(38,294458183401020090678486524487479),(39,209160020741517175284617157422083),(40,145425112359276469462165621902767),(41,98948296698660984995805535996470),(42,65872682151013422232937140888836),(43,42910875740502999387981667569020),(44,27347650257872154980318498794920),(45,17042716743870458778912047755059),(46,10383797773248711267716064175854),(47,6185739861010776354509842024312),(48,3600666351570151960274832520261),(49,2046588482550212720390308249196),(50,1136010319426713325811546594119),(51,615661961726518426056776402538),(52,325366048026888809860727947349),(53,167606751600724338628670539398),(54,84200995815721530265899996678),(55,41203774548537734283675193327),(56,19606321244714397760341317705),(57,9079157552056602903276001467),(58,4092313872661107374797735123),(59,1789563098014996372126636777),(60,758757584155293036256466929),(61,312816715263099117499892103),(62,125007309410924000394275131),(63,48172731806094265959772715),(64,17991480177433442045135942),(65,6523968894065580486182764),(66,2268997670619973617082938),(67,758003385439166096761128),(68,246821159731968159030052),(69,77053382146070805879863),(70,22671091355759130442382),(71,6503108629079711373764),(72,1815242636058569509472),(73,464174467719285920610),(74,113491077189466389625),(75,28237502074863276668),(76,6248281254779921656),(77,1212323783156267194),(78,261840165059759183),(79,52179972917130331),(80,7618366411112909),(81,1345792409546788),(82,242026514474962),(83,18571403401158),(84,2050132798658),(85,599959642891),(86,50925893655),(87,329325360),(88,110625732)]

theorem histCheck_all : histCheck topCountsT51 false = true := by decide +kernel
theorem histCheck_free : histCheck topFreeCountsT51 true = true := by decide +kernel


/-- `|C_L∖B|`: canonical top words that are LOW-good (credit ≥ 12, i.e. floor 14 with the LOW bonus 2) and whose LOW
half is not forced. -/
def freeCountT51 : Nat := 50025990371737199867992306903047594
theorem freeCountT51_hist : ((List.range' 12 126).map (histW topFreeCountsT51)).sum = freeCountT51 := by
  decide +kernel
theorem topCountsT51_lt : ∀ e ∈ topCountsT51, e.1 < 138 := by decide
theorem histW_eq_zero (h : List (Nat × Nat)) (c : Nat) (hc : ∀ e ∈ h, e.1 ≠ c) : histW h c = 0 := by
  unfold histW
  induction h with
  | nil => rfl
  | cons e t ih =>
    rw [List.map_cons, List.sum_cons, if_neg (hc e (by simp)), Nat.zero_add]
    exact ih (fun e' he' => hc e' (by simp [he']))

end SigGolfResearch.T51Top

namespace SigGolfResearch.T51Top
open Finset SigGolfCandidate.T3 SigGolfCandidate.T3.Nonbinary ClaudeWCT.WCT9
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

theorem wordCredit_encode (w : «Word») (chk : Nat) :
    wordCredit 0 (dataDigits 0 (encode w) ++ [chk]) = credits w + ind (chk + 1 = 5) := by
  unfold wordCredit
  rw [show chainCount 0 = 51 from rfl, filter_range_length, sum_51, getD48, getD49, getD50,
    show maxDigit 0 48 = 6 from rfl, show maxDigit 0 49 = 6 from rfl, show maxDigit 0 50 = 5 from rfl]
  unfold credits pcredit
  congr 2
  congr 1
  · apply Finset.sum_congr rfl; intro g _
    obtain ⟨a0, a1, a2, m0, m1, m2⟩ := blk6 w chk g
    rw [a0, a1, a2, m0, m1, m2]; rfl
  · apply Finset.sum_congr rfl; intro j _
    obtain ⟨a0, a1, a2, m0, m1, m2⟩ := blk5 w chk j
    rw [a0, a1, a2, m0, m1, m2]; rfl

set_option maxHeartbeats 4000000 in
theorem savedCopies_encode (w : «Word») (chk : Nat) :
    savedCopies 0 (dataDigits 0 (encode w) ++ [chk]) = copies w := by
  unfold savedCopies
  rw [show chainCount 0 = 51 from rfl, filter_range_length, sum_51]
  have h50 : ind (safeZeroCopy 0 (dataDigits 0 (encode w) ++ [chk]) 50) = 0 := by
    apply ind_neg; unfold safeZeroCopy; simp
  have h48 : ind (safeZeroCopy 0 (dataDigits 0 (encode w) ++ [chk]) 48) = 0 := by
    apply ind_neg; unfold safeZeroCopy; simp
  have h49 : ind (safeZeroCopy 0 (dataDigits 0 (encode w) ++ [chk]) 49) = pcopies w.2.2.val := by
    unfold pcopies
    apply ind_congr; unfold safeZeroCopy
    rw [getD49, show 49 - 1 = 48 from rfl, getD48, show maxDigit 0 49 = 6 from rfl,
      show maxDigit 0 48 = 6 from rfl]
    constructor
    · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, _, _, h3⟩⟩
      · omega
      · exact absurd rfl h2
      · exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, by omega, h2⟩)⟩
  rw [h50, h48, h49, Nat.add_zero, Nat.zero_add]
  unfold copies
  congr 1
  congr 1
  · apply Finset.sum_congr rfl; intro g _
    obtain ⟨a0, a1, a2, m0, m1, m2⟩ := blk6 w chk g
    have hg := g.isLt
    unfold tcopies
    congr 1; congr 1
    · apply ind_congr; unfold safeZeroCopy; rw [a0, m0]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, h2, _⟩⟩
        · exact ⟨by simp; omega, h1⟩
        · exact absurd rfl h2
        · omega
      · rintro ⟨h1, h2⟩; exact ⟨h2, Or.inl (by simp at h1; omega)⟩
    · apply ind_congr; unfold safeZeroCopy
      rw [a1, m1, show 3 * g.val + 1 - 1 = 3 * g.val by omega, a0, m0]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, _, _, h3⟩⟩
        · omega
        · exact absurd rfl h2
        · exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, by omega, h2⟩)⟩
    · apply ind_congr; unfold safeZeroCopy
      rw [a2, m2, show 3 * g.val + 2 - 1 = 3 * g.val + 1 by omega, a1, m1]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, _, _, h3⟩⟩
        · omega
        · exact absurd rfl h2
        · exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, by omega, h2⟩)⟩
  · apply Finset.sum_congr rfl; intro j _
    obtain ⟨a0, a1, a2, m0, m1, m2⟩ := blk5 w chk j
    have hj := j.isLt
    unfold tcopies
    congr 1; congr 1
    · apply ind_congr; unfold safeZeroCopy; rw [a0, m0]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, h2, _⟩⟩
        · omega
        · exact absurd rfl h2
        · omega
      · rintro ⟨h1, _⟩; exact absurd h1 (by simp)
    · apply ind_congr; unfold safeZeroCopy
      rw [a1, m1, show 3 * (9 + j.val) + 1 - 1 = 3 * (9 + j.val) by omega, a0, m0]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, _, _, h3⟩⟩
        · omega
        · exact absurd rfl h2
        · exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, by omega, h2⟩)⟩
    · apply ind_congr; unfold safeZeroCopy
      rw [a2, m2, show 3 * (9 + j.val) + 2 - 1 = 3 * (9 + j.val) + 1 by omega, a1, m1]
      constructor
      · rintro ⟨h1, h2 | ⟨h2, _⟩ | ⟨_, _, _, h3⟩⟩
        · omega
        · exact absurd rfl h2
        · exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr (Or.inr ⟨by omega, by omega, by omega, h2⟩)⟩

theorem penalty_encode (w : «Word») (chk : Nat) :
    topDispatchPenalty (dataDigits 0 (encode w) ++ [chk]) = penalty w := by
  unfold topDispatchPenalty
  rw [filter_range_length, show 17 = 9 + (7 + 1) by rfl, Finset.sum_range_add, Finset.sum_range_add,
    Finset.sum_range, Finset.sum_range, Finset.sum_range_one]
  have h0 : (∑ g : Fin 9, ind ((g.val = 10 ∨ g.val = 11 ∨ g.val = 12) ∧
      (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val) 0 + (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val + 1) 0 +
        (dataDigits 0 (encode w) ++ [chk]).getD (3 * g.val + 2) 0 < 3)) = 0 := by
    apply Finset.sum_eq_zero; intro g _; apply ind_neg; have := g.isLt; omega
  have h16 : ind ((9 + (7 + 0) = 10 ∨ 9 + (7 + 0) = 11 ∨ 9 + (7 + 0) = 12) ∧
      (dataDigits 0 (encode w) ++ [chk]).getD (3 * (9 + (7 + 0))) 0 +
        (dataDigits 0 (encode w) ++ [chk]).getD (3 * (9 + (7 + 0)) + 1) 0 +
        (dataDigits 0 (encode w) ++ [chk]).getD (3 * (9 + (7 + 0)) + 2) 0 < 3) = 0 := by
    apply ind_neg; omega
  rw [h0, h16, Nat.zero_add, Nat.add_zero]
  unfold penalty
  apply Finset.sum_congr rfl; intro j _
  obtain ⟨a0, a1, a2, -, -, -⟩ := blk5 w chk j
  rw [a0, a1, a2]
  apply ind_congr
  unfold pen tsum
  have := j.isLt
  simp only [decide_eq_true_eq]
  omega

theorem zeros_encode (w : «Word») (chk : Nat) :
    ((dataDigits 0 (encode w) ++ [chk]).filter (· = 0)).length = SigGolfResearch.T51Top.zeros w + ind (chk = 0) := by
  rw [List.filter_append, List.length_append]
  congr 1
  · unfold dataDigits
    rw [show dataCount 0 = 50 from rfl, List.filter_map, List.length_map]
    rw [show ((List.range 50).filter ((fun x => decide (x = 0)) ∘ coreDigit 0 (encode w))) =
      (List.range 50).filter (fun i => decide (coreDigit 0 (encode w) i = 0)) from rfl, filter_range_length, sum_50]
    unfold zeros pzeros
    congr 1
    congr 1
    · apply Finset.sum_congr rfl; intro g _
      rw [show 3 * g.val = 3 * g.val + 0 by rfl, core_encode6 w g 0 (by decide), core_encode6 w g 1 (by decide),
        core_encode6 w g 2 (by decide)]; rfl
    · apply Finset.sum_congr rfl; intro j _
      rw [show 3 * (9 + j.val) = 3 * (9 + j.val) + 0 by rfl, core_encode5 w j 0 (by decide),
        core_encode5 w j 1 (by decide), core_encode5 w j 2 (by decide)]; rfl
    · have e0 := core_encode7 w 0 (by decide)
      have e1 := core_encode7 w 1 (by decide)
      simp only [Nat.add_zero, Nat.reduceAdd] at e0 e1
      rw [e0, e1]
  · unfold ind; by_cases h : chk = 0 <;> simp [h]

theorem score_penalty (w : «Word») : SigGolfResearch.T51Top.score w + penalty w = credits w + 4 * copies w + 3 := by
  have hb (j : Fin 7) : (if pen j = true then ind (3 ≤ tsum 5 (w.2.1 j).val) else 0) +
      ind (pen j = true ∧ tsum 5 (w.2.1 j).val < 3) = ind (pen j = true) := by
    unfold ind; by_cases hp : pen j = true <;> by_cases ht : 3 ≤ tsum 5 (w.2.1 j).val <;> simp [hp, ht] <;> omega
  have h3 : (∑ j : Fin 7, ind (pen j = true)) = 3 := by decide
  have hs := Finset.sum_congr rfl (fun j (_ : j ∈ (univ : Finset (Fin 7))) => hb j)
  rw [Finset.sum_add_distrib, h3] at hs
  unfold score credits copies penalty tscore pscore
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    Finset.sum_const_zero] at hs ⊢
  omega

/-! ### The canonical top producer (no path bonus) on model words -/
/-- The canonical top producer accepts `v` at floor 0 without the path bonus, with credit `c`. -/
def acc (c : Nat) (v : Digest) : Prop :=
  match CanonicalPolicy.producerDecodeAt 0 0 false v with
  | none => False
  | some ds => CanonicalPolicy.credit 0 false ds = c
instance (c : Nat) : DecidablePred (acc c) := fun v => by
  unfold acc; split <;> infer_instance

theorem acc_iff (c : Nat) (v : Digest) :
    acc c v ↔ ∃ ds, CanonicalPolicy.producerDecodeAt 0 0 false v = some ds ∧ CanonicalPolicy.credit 0 false ds = c := by
  unfold acc; cases CanonicalPolicy.producerDecodeAt 0 0 false v <;> simp

theorem decode_canonical_top (v : Digest) : CanonicalPolicy.decode 0 v = decode 0 v := by
  simp [CanonicalPolicy.decode, CanonicalPolicy.normalLayer]

theorem acc_valid (c : Nat) (v : Digest) (h : acc c v) : topRanksValid v = true := by
  obtain ⟨ds, hd, -⟩ := (acc_iff c v).mp h
  have hs := (CanonicalPolicy.producerDecodeAt_spec hd).1
  rw [decode_canonical_top] at hs
  exact (decode_top_some hs).2.1

theorem acc_encode_iff (c : Nat) (w : «Word») : acc c (encode w) ↔ accepts c w := by
  rw [acc_iff]
  have hd0 := decode_top_encode w
  unfold accepts
  by_cases hdec : 147 ≤ SigGolfResearch.T51Top.weight w ∧ SigGolfResearch.T51Top.weight w ≤ 152
  · rw [if_pos hdec] at hd0
    unfold CanonicalPolicy.producerDecodeAt
    rw [decode_canonical_top, hd0]
    simp only
    set chk := 152 - SigGolfResearch.T51Top.weight w with hchk
    have hz := zeros_encode w chk
    have hc := wordCredit_encode w chk
    have hp := penalty_encode w chk
    have hcp := savedCopies_encode w chk
    have hsp := score_penalty w
    have e1 : ind (chk + 1 = 5) = ind (SigGolfResearch.T51Top.weight w = 148) := ind_congr (by omega)
    have e2 : ind (chk = 0) = ind (SigGolfResearch.T51Top.weight w = 152) := ind_congr (by omega)
    have i1 := ind_le (SigGolfResearch.T51Top.weight w = 148)
    simp only [CanonicalPolicy.pathReward, CanonicalPolicy.reward, CanonicalPolicy.pathBonus_false, Nat.add_zero,
      CanonicalPolicy.credit, dispatchPenalty, if_true, canonicalZeroBound, producerZeroCap, producerRankBound,
      true_or, and_true]
    rw [hz, hc, hp, hcp, e1, e2]
    constructor
    · rintro ⟨ds, hds, hcr⟩
      split_ifs at hds with hcond
      · cases hds
        refine ⟨hdec.1, hdec.2, hcond.2, by omega⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨_, if_pos ⟨by omega, h3⟩, by omega⟩
  · rw [if_neg hdec] at hd0
    unfold CanonicalPolicy.producerDecodeAt
    rw [decode_canonical_top, hd0]
    simp only [reduceCtorEq, false_and, exists_false, false_iff, not_and]
    intro h1 h2
    exact absurd ⟨h1, h2⟩ hdec

theorem high_bits (X r : Nat) (h8 : X / 2 ^ 120 % 256 = r) (hlt : X < 2 ^ 128) :
    X < 2 ^ 126 ↔ r < 64 := by
  simp only [Nat.reducePow] at *
  omega

theorem blocked_encode (w : «Word») : TopChoice.blocked (encode w) ↔ ¬ isFree w := by
  have h8 : r6Raw (encode w) 8 = (w.1 8).val := by
    have := r6Raw_encode w 8
    rw [if_neg (by decide)] at this
    exact this
  unfold r6Raw r6Shift at h8
  rw [if_neg (by decide)] at h8
  have hlt : topCode (encode w) < 2 ^ 128 := by rw [topCode_encode]; exact code_lt w
  have key := high_bits _ _ h8 hlt
  unfold TopChoice.blocked isFree
  rw [← topCode_lt_iff _ 126 (by decide), key]
  omega

/-- Exact count of the top words of credit `c` accepted by the canonical producer (no path bonus). -/
theorem card_acc (c : Nat) (hc1 : 12 ≤ c) (hc2 : c < 138) :
    (univ.filter (acc c)).card = histW topCountsT51 c := by
  rw [card_encode (acc c) (acc_valid c), ← model_count_of_check topCountsT51 false histCheck_all c hc1 hc2]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  rw [acc_encode_iff]
  unfold Qc
  simp

/-- Exact count of those whose LOW half is not forced. -/
theorem card_acc_free (c : Nat) (hc1 : 12 ≤ c) (hc2 : c < 138) :
    (univ.filter fun v => acc c v ∧ ¬ TopChoice.blocked v).card = histW topFreeCountsT51 c := by
  rw [card_encode (fun v => acc c v ∧ ¬ TopChoice.blocked v) (fun v h => acc_valid c v h.1),
    ← model_count_of_check topFreeCountsT51 true histCheck_free c hc1 hc2]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  rw [acc_encode_iff, blocked_encode]
  unfold Qc
  simp only [not_not, forall_const]
  exact And.comm

/-- Every accepted top word has credit at most 137 (no path bonus). -/
theorem acc_le (c : Nat) (v : Digest) (h : acc c v) : c ≤ 137 := by
  have hv := acc_valid c v h
  rw [← encode_wordOf v hv, acc_encode_iff] at h
  exact accepts_le h

end SigGolfResearch.T51Top

/-! ### The canonical top API at the T51 floor (restated from #938's NF17 bridge) -/
namespace ClaudeWCT.W9.T3.ProducerV5.Canonical
open OracleComp OracleSpec ENNReal Finset
open SigGolfCandidate.T3 ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem pda_zero_of {floor : Nat} {v : Digest} {ds : List Nat}
    (h : CanonicalPolicy.producerDecodeAt 0 floor false v = some ds) :
    CanonicalPolicy.producerDecodeAt 0 0 false v = some ds :=
  producerDecodeAt_floor_zero (fun _ h => absurd h (by simp)) h

/-- Campaign T51: accepted top words of credit `c` (canonical producer at floor 0, no path bonus). -/
noncomputable def topWordCount (c : Nat) : Nat :=
  (univ.filter (accepted 0 0 (fun ds => CanonicalPolicy.credit 0 false ds = c))).card

theorem card_filter_congr' {α : Type} [Fintype α] (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ a, p a ↔ q a) : (univ.filter p).card = (univ.filter q).card :=
  congrArg Finset.card (Finset.filter_congr fun a _ => h a)

theorem accepted_credit_acc (c : Nat) (v : Digest) :
    accepted 0 0 (fun ds => CanonicalPolicy.credit 0 false ds = c) v ↔ SigGolfResearch.T51Top.acc c v := by
  rw [accepted_iff, SigGolfResearch.T51Top.acc_iff]

theorem accepted_credit_floor_iff (floor c : Nat) (hf : floor ≤ c) (v : Digest) :
    accepted 0 floor (fun ds => CanonicalPolicy.credit 0 false ds = c) v ↔
      accepted 0 0 (fun ds => CanonicalPolicy.credit 0 false ds = c) v := by
  rw [accepted_iff, accepted_iff]
  apply exists_congr; intro ds
  constructor
  · rintro ⟨hd, hc⟩; exact ⟨pda_zero_of hd, hc⟩
  · rintro ⟨hd, hc⟩
    refine ⟨?_, hc⟩
    have hs := (producerDecodeAt_eq_some_iff _ _ _ _ _).mp hd
    apply (producerDecodeAt_eq_some_iff _ _ _ _ _).mpr
    refine ⟨hs.1, ?_, hs.2.2⟩
    have h1 := hs.2.1
    simp only [CanonicalPolicy.credit] at hc
    omega

theorem accepted_top_credit_card (floor credit : Nat) (hf : floor ≤ credit) :
    (univ.filter (accepted 0 floor (fun ds => CanonicalPolicy.credit 0 false ds = credit))).card =
      topWordCount credit :=
  card_filter_congr' _ _ (accepted_credit_floor_iff floor credit hf)

/-- Campaign T51: the exact top credit law (credits `≥ 12`), from the T51 generating polynomial. -/
theorem topWordCount_eq (c : Nat) (hc : 12 ≤ c) :
    topWordCount c = SigGolfResearch.T51Top.histW SigGolfResearch.T51Top.topCountsT51 c := by
  by_cases h138 : c < 138
  · unfold topWordCount
    rw [card_filter_congr' _ (SigGolfResearch.T51Top.acc c) (accepted_credit_acc c),
      SigGolfResearch.T51Top.card_acc c hc h138]
  · have h0 : topWordCount c = 0 := by
      unfold topWordCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v _ hv
      have := SigGolfResearch.T51Top.acc_le c v ((accepted_credit_acc c v).mp hv)
      omega
    rw [h0, SigGolfResearch.T51Top.histW_eq_zero _ _
      (fun e he => by have := SigGolfResearch.T51Top.topCountsT51_lt e he; omega)]

/-- Campaign T51 (top floor 14, LOW bonus 2): the LOW-good predicate is acceptance at 12 without the bonus. -/
theorem topGood_iff (v : Digest) : topGood v ↔ accepted 0 12 (fun _ => True) v := by
  unfold topGood
  rw [show CanonicalPolicy.topFloor = 14 from rfl, producerDecodeAt_top_true 14 (by decide), accepted_iff]
  simp only [and_true]
  exact Option.isSome_iff_exists

/-- The credit of a top word (0 when the producer rejects it at floor 0). -/
def creditOf (v : Digest) : Nat :=
  match CanonicalPolicy.producerDecodeAt 0 0 false v with
  | none => 0
  | some ds => CanonicalPolicy.credit 0 false ds

theorem creditOf_of_acc {c : Nat} {v : Digest} (h : SigGolfResearch.T51Top.acc c v) : creditOf v = c := by
  obtain ⟨ds, hd, hc⟩ := (SigGolfResearch.T51Top.acc_iff c v).mp h
  unfold creditOf; rw [hd]; exact hc

theorem accepted12_iff (v : Digest) :
    accepted 0 12 (fun _ => True) v ↔ ∃ c, 12 ≤ c ∧ SigGolfResearch.T51Top.acc c v := by
  rw [accepted_iff]
  constructor
  · rintro ⟨ds, hd, -⟩
    have hc := CanonicalPolicy.producerDecodeAt_credit hd
    exact ⟨_, hc, (SigGolfResearch.T51Top.acc_iff _ v).mpr ⟨ds, pda_zero_of hd, rfl⟩⟩
  · rintro ⟨c, hc, ha⟩
    have h := (accepted_credit_floor_iff 12 c hc v).mpr ((accepted_credit_acc c v).mpr ha)
    obtain ⟨ds, hd, -⟩ := (accepted_iff _ _ _ v).mp h
    exact ⟨ds, hd, trivial⟩

theorem fiber_free (c : Nat) (hc : 12 ≤ c) (v : Digest) :
    ((accepted 0 12 (fun _ => True) v ∧ ¬ TopChoice.blocked v) ∧ creditOf v = c) ↔
      (SigGolfResearch.T51Top.acc c v ∧ ¬ TopChoice.blocked v) := by
  constructor
  · rintro ⟨⟨ha, hb⟩, he⟩
    obtain ⟨c', -, hc'⟩ := (accepted12_iff v).mp ha
    have := creditOf_of_acc hc'
    subst he
    rw [this]; exact ⟨hc', hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨⟨(accepted12_iff v).mpr ⟨c, hc, ha⟩, hb⟩, creditOf_of_acc ha⟩

/-- Campaign T51: the exact number of LOW-good top words whose LOW is not forced. -/
theorem topFreeCount_eq : topFreeCount = SigGolfResearch.T51Top.freeCountT51 := by
  unfold topFreeCount
  rw [card_filter_congr' _ (fun v => accepted 0 12 (fun _ => True) v ∧ ¬ TopChoice.blocked v)
    (fun v => and_congr_left' (topGood_iff v))]
  rw [SigGolfResearch.T51Top.fiber_card_filter (fun v => accepted 0 12 (fun _ => True) v ∧ ¬ TopChoice.blocked v)
    creditOf (List.range' 12 126).toFinset (fun v hv => by
      obtain ⟨c, hc, ha⟩ := (accepted12_iff v).mp hv.1
      rw [creditOf_of_acc ha, List.mem_toFinset, List.mem_range'_1]
      have := SigGolfResearch.T51Top.acc_le c v ha
      omega)]
  rw [← SigGolfResearch.T51Top.freeCountT51_hist, ← List.sum_toFinset _ List.nodup_range']
  apply Finset.sum_congr rfl
  intro c hc
  have hc' := List.mem_range'_1.mp (List.mem_toFinset.mp hc)
  rw [Finset.filter_filter, card_filter_congr' _ (fun v => SigGolfResearch.T51Top.acc c v ∧ ¬ TopChoice.blocked v)
    (fun v => fiber_free c hc'.1 v)]
  exact SigGolfResearch.T51Top.card_acc_free c hc'.1 (by omega)

/-- Campaign T51: the HIGH half is selected with weight `3*2^126 - freeCount` per accepted HIGH word. -/
def topHighWeight : Nat := 3*2^126 - SigGolfResearch.T51Top.freeCountT51

theorem topFreeCount_eq_filter :
    (univ.filter fun v : Digest => topGood v ∧ ¬ TopChoice.blocked v).card = SigGolfResearch.T51Top.freeCountT51 :=
  topFreeCount_eq

theorem freeCount_add_top :
    TopChoice.freeCount topGood + SigGolfResearch.T51Top.freeCountT51 = 3 * 2 ^ 126 := by
  have h := TopChoice.freeCount_add topGood
  rw [topFreeCount_eq_filter] at h
  exact h

/-- Pure arithmetic (keeps `TopChoice.freeCount topGood` abstract for the kernel). -/
theorem highWeight_arith (F : Nat) (h : F + SigGolfResearch.T51Top.freeCountT51 = 3 * 2 ^ 126) :
    F = topHighWeight := by
  unfold topHighWeight
  omega

theorem freeCount_eq_compl : TopChoice.freeCount topGood = topHighWeight :=
  highWeight_arith _ freeCount_add_top

/-- The d6b top selection count at credit `c ≥ floor ≥ 14`: weight `2^128` through LOW (credit `c - 2`),
`topHighWeight` through HIGH (credit `c`). -/
theorem selected_top_path_card (floor c : Nat) (hf : 14 ≤ floor) (hc : floor ≤ c) :
    (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 floor answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c).card =
      topWordCount (c - 2) * 2^128 + topHighWeight * topWordCount c := by
  have he : (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 floor answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c) =
      (univ.filter fun a : HashOutput => if topGood (a.extractLsb' 0 128) ∨ TopChoice.blocked (a.extractLsb' 0 128)
        then accepted 0 (floor - 2) (fun ds => CanonicalPolicy.credit 0 false ds + 2 = c) (a.extractLsb' 0 128)
        else accepted 0 floor (fun ds => CanonicalPolicy.credit 0 false ds = c) (a.extractLsb' 128 128)) :=
    Finset.filter_congr fun a _ => top_decoder_event floor c (by omega) a
  have hlo : (univ.filter (accepted 0 (floor - 2) (fun ds => CanonicalPolicy.credit 0 false ds + 2 = c))).card =
      topWordCount (c - 2) := by
    have hq : (univ.filter (accepted 0 (floor - 2) (fun ds => CanonicalPolicy.credit 0 false ds + 2 = c))) =
        univ.filter (accepted 0 (floor - 2) (fun ds => CanonicalPolicy.credit 0 false ds = c - 2)) := by
      apply Finset.filter_congr
      intro v _
      unfold accepted
      cases CanonicalPolicy.producerDecodeAt 0 (floor - 2) false v with
      | none => rfl
      | some ds => simp only; omega
    rw [hq, accepted_top_credit_card (floor - 2) (c - 2) (by omega)]
  have hhi : (univ.filter (accepted 0 floor (fun ds => CanonicalPolicy.credit 0 false ds = c))).card =
      topWordCount c := accepted_top_credit_card floor c hc
  have hfree : TopChoice.freeCount topGood = topHighWeight := freeCount_eq_compl
  rw [he, card_choose_path_generic topGood _ _ (fun d h => accepted_topGood (by omega) h), hlo, hhi, hfree]

theorem accepted_top_credit_le {floor credit : Nat} {v : Digest}
    (h : accepted 0 floor (fun ds => CanonicalPolicy.credit 0 false ds = credit) v) : credit ≤ 137 := by
  obtain ⟨ds, hd, hc⟩ := (accepted_iff 0 floor _ v).mp h
  exact SigGolfResearch.T51Top.acc_le credit v
    ((SigGolfResearch.T51Top.acc_iff credit v).mpr ⟨ds, pda_zero_of hd, hc⟩)

theorem producerDecodeAt_top_credit_lt {floor : Nat} (hf : 3 ≤ floor) {low : Bool} {value : Digest}
    {ds : List Nat} (h : CanonicalPolicy.producerDecodeAt 0 floor low value = some ds) :
    CanonicalPolicy.credit 0 low ds < 220 := by
  have ha : accepted 0 0 (fun digits => CanonicalPolicy.credit 0 false digits =
      CanonicalPolicy.credit 0 false ds) value :=
    (accepted_iff 0 0 _ value).mpr ⟨ds, producerDecodeAt_floor_zero (fun _ _ => hf) h, rfl⟩
  have hb := accepted_top_credit_le ha
  rw [CanonicalPolicy.credit_top] at hb ⊢
  cases low <;> simp at hb ⊢ <;> omega

end ClaudeWCT.W9.T3.ProducerV5.Canonical

namespace ClaudeWCT.Numerics.TopZero
open CanonicalCompression hiding topChoiceFree topHighW topCounts topAcceptedHistogram
open CanonicalHistogram hiding topHistogramCheck top_histogram_checked
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 10000000
set_option Elab.async false

/-- Campaign T51: zero-capped top word counts at target 152 by credit (no path bonus), credit ≥ 12, ≤ 7 zero digits
(the checksum included). -/
def topCounts : List (Nat × Nat) := SigGolfResearch.T51Top.topCountsT51

/-- Zero-capped canonical free top words (`|C_L∖B|`, top floor 14). -/
def topChoiceFree : Nat := SigGolfResearch.T51Top.freeCountT51
/-- Weight (over `2^256`) of an accepted HIGH top word: the LOW halves that are neither good nor forced. -/
def topHighW : Nat := 3 * 2 ^ 126 - topChoiceFree

/-- d6b split with the zero cap: LOW (credit `c + 2`, weight `2^128`) or HIGH (credit `c`, weight `topHighW`).
Entries below the top floor 14 never matter. -/
def topAcceptedHistogram : List (Nat × Nat) :=
  topCounts.flatMap fun e => [(e.1 + 2, e.2 * 2 ^ 128), (e.1, e.2 * topHighW)]

def initialBound : Nat := 366648481088737248065818665243608968537

/-- T51 fixed sign cost (PINNED P12, measured): 4 + 112142 + 16 top family pairs + 152 + 12 = 112326 compressions. -/
def fixedSignCost : Nat := 112326

/-- Fixed power for the T51 fixed sign cost 112326. -/
def fixedBound : Nat := 616334705435489293055497825014826663607

theorem initial_checked :
    recurrenceCheck topDen topAcceptedHistogram 14 69 rowOne initialBound = true := by
  decide +kernel

theorem fixed_power_checked :
    powerUp (ceilDiv (zNum * scale) zDen) fixedSignCost ≤ fixedBound := by
  decide +kernel

/-- The T51 signing moment 1.999750417 < 1.99976 (claim 199976, the least integer claim that passes). -/
theorem full_moment_checked :
    mulUp (mulUp fixedBound ftsBound) initialBound * 100000 < 199976 * scale := by
  decide +kernel

/-- Top tail at the 2^20 top counter window (block 256 = 2^20 / 4096), floor 14. -/
theorem top_tail_checked : tailCheck (acceptedMass topAcceptedHistogram 14) topDen 256 = true := by
  decide +kernel

theorem initialBound_ge_scale : scale ≤ initialBound := by norm_num [scale, initialBound]

end ClaudeWCT.Numerics.TopZero

namespace ClaudeWCT.Numerics.TopZero
open CanonicalCompression hiding topChoiceFree topHighW topCounts topAcceptedHistogram
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem fixed_ratio_bound : ((zNum:ℝ)/zDen)^fixedSignCost≤(fixedBound:ℝ)/scale := by
  have hs : (0:ℝ)<scale := by norm_num [scale]
  have hceil := ceilDiv_ratio_le (zNum*scale) zDen (by norm_num [zDen])
  have hc : ((zNum:ℝ)/zDen)≤(ceilDiv (zNum*scale) zDen:ℝ)/scale := by
    apply (le_div_iff₀ hs).mpr
    simpa only [Nat.cast_mul,mul_div_assoc,div_mul_eq_mul_div] using hceil
  have hp := powerUp_ratio_ge (ceilDiv (zNum*scale) zDen) fixedSignCost
  calc
    _ ≤ ((ceilDiv (zNum*scale) zDen:ℝ)/scale)^fixedSignCost := by gcongr
    _ ≤ _ := hp.trans (div_le_div_of_nonneg_right (by exact_mod_cast fixed_power_checked) hs.le)

theorem envelope_ratio_le_two_of (F X : Nat) (hX : X ≤ 200000)
    (hn : mulUp (mulUp F ftsBound) initialBound * 100000 < X * scale) :
    ((F:ℝ)/scale)*(((ftsBound:ℝ)/scale)*((initialBound:ℝ)/scale))≤2 := by
  have hs : (0:ℝ)<scale := by norm_num [scale]
  have hmul2 := mulUp_ratio_ge (mulUp F ftsBound) initialBound
  have hnum : (mulUp (mulUp F ftsBound) initialBound:ℝ)/scale<X/100000 := by
    have hreal : (mulUp (mulUp F ftsBound) initialBound:ℝ)*100000<X*(scale:ℝ) := by exact_mod_cast hn
    apply (div_lt_iff₀ hs).mpr
    nlinarith
  have hX' : (X:ℝ)/100000 ≤ 2 := by
    have : (X:ℝ) ≤ 200000 := by exact_mod_cast hX
    rw [div_le_iff₀ (by norm_num)]
    linarith
  calc
    _ = (((F:ℝ)/scale)*((ftsBound:ℝ)/scale))*((initialBound:ℝ)/scale) := by ring
    _ ≤ ((mulUp F ftsBound:ℝ)/scale)*((initialBound:ℝ)/scale) := by
        gcongr
        exact mulUp_ratio_ge F ftsBound
    _ ≤ _ := hmul2
    _ ≤ 2 := hnum.le.trans hX'

/-- Full moment ≤ 2 (1.99976) for the T51 fixed sign cost 112326 (cap 777, pool 69, floor 14, d6b). -/
theorem envelope_ratio_le_two : ((fixedBound:ℝ)/scale)*
    (((ftsBound:ℝ)/scale)*((initialBound:ℝ)/scale))≤2 :=
  envelope_ratio_le_two_of fixedBound 199976 (by norm_num) full_moment_checked

end ClaudeWCT.Numerics.TopZero
end
-- ==== merged from ClaudeWCT_Numerics_N600PriceCanonical ====
section

/-! ### Configuration (1)+(2), e7b: exact selected-credit laws for the restricted top choice and the
path-aware lower credit, from the packed generating polynomials. -/
namespace ClaudeWCT.Numerics.CanonicalHistogram
open OracleComp OracleSpec ENNReal Finset CanonicalCompression
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.ProducerV5.Canonical
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option quotPrecheck false

theorem histogramWeight_append (a b : List (Nat × Nat)) (x : Nat) :
    histogramWeight (a ++ b) x = histogramWeight a x + histogramWeight b x := by
  rw [histogramWeight_sum, histogramWeight_sum, histogramWeight_sum, List.map_append, List.sum_append]

theorem histogramWeight_split (h : List (Nat × Nat)) (k a b x : Nat) :
    histogramWeight (h.flatMap fun e => [(e.1 + k, e.2 * a), (e.1, e.2 * b)]) x =
      (if k ≤ x then histogramWeight h (x - k) * a else 0) + histogramWeight h x * b := by
  induction h with
  | nil => simp [histogramWeight]
  | cons e t ih =>
      rw [List.flatMap_cons, histogramWeight_append, ih]
      have h1 : histogramWeight (e :: t) (x - k) = (if e.1 = x - k then e.2 else 0) + histogramWeight t (x - k) := by
        rw [histogramWeight_sum, histogramWeight_sum]; simp
      have h2 : histogramWeight (e :: t) x = (if e.1 = x then e.2 else 0) + histogramWeight t x := by
        rw [histogramWeight_sum, histogramWeight_sum]; simp
      have h3 : histogramWeight [(e.1 + k, e.2 * a), (e.1, e.2 * b)] x =
          (if e.1 + k = x then e.2 * a else 0) + (if e.1 = x then e.2 * b else 0) := by
        rw [histogramWeight_sum]; simp
      rw [h1, h2, h3]
      have key : (if e.1 + k = x then e.2 * a else 0) =
          (if k ≤ x then (if e.1 = x - k then e.2 else 0) * a else 0) := by
        by_cases hk : k ≤ x
        · rw [if_pos hk]
          by_cases he : e.1 + k = x
          · rw [if_pos he, if_pos (by omega)]
          · rw [if_neg he, if_neg (by omega), Nat.zero_mul]
        · rw [if_neg hk, if_neg (by omega)]
      rw [key]
      by_cases hk : k ≤ x
      · simp only [if_pos hk]
        split_ifs <;> ring
      · simp only [if_neg hk]
        split_ifs <;> ring

/-- Campaign T51: the model histogram weight is the packet's `histogramWeight`. -/
theorem histW_eq_histogramWeight (h : List (Nat × Nat)) (c : Nat) :
    SigGolfResearch.T51Top.histW h c = histogramWeight h c := by
  rw [histogramWeight_sum]; rfl

theorem topWordCount_eq_hist (r : Nat) (h12 : 12 ≤ r) : topWordCount r = histogramWeight TopZero.topCounts r := by
  rw [topWordCount_eq r h12, histW_eq_histogramWeight]; rfl

theorem topHighWeight_eq : topHighWeight = TopZero.topHighW := rfl

/-- The d6b top selection law at the canonical floor 14 (T51), with the top producer zero cap 7. -/
theorem selected_top_histogram_card (c : Nat) (hc : 14 ≤ c) :
    (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 14 answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c).card =
      histogramWeight TopZero.topAcceptedHistogram c := by
  rw [selected_top_path_card 14 c le_rfl hc, TopZero.topAcceptedHistogram, histogramWeight_split,
    if_pos (by omega : 2 ≤ c), topWordCount_eq_hist (c - 2) (by omega), topWordCount_eq_hist c (by omega),
    topHighWeight_eq]
  ring

theorem selected_top_histogram_probability (c : Nat) (hc : 14 ≤ c) :
    Pr[fun answer => ∃ dl, CanonicalPolicy.producerDecodeOut 0 14 answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (histogramWeight TopZero.topAcceptedHistogram c : ENNReal) / topDen := by
  classical
  rw [probEvent_uniformSample]
  rw [show (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut 0 14 answer = some dl ∧
        CanonicalPolicy.credit 0 dl.2 dl.1 = c) = _ from rfl, selected_top_histogram_card c hc]
  simp only [Fintype.card_bitVec, topDen, Nat.cast_pow, Nat.cast_ofNat]

local notation "lowerCountN" credit:arg =>
  (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
    SigGolfResearch.LowerEffectiveCounting.zeros w ≤ 5 ∧
    SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
    SigGolfResearch.LowerEffectiveCounting.score w = credit).card

local notation "lowerFiberN" z:arg credit:arg =>
  (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
    SigGolfResearch.LowerEffectiveCounting.zeros w = z ∧
    SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
    SigGolfResearch.LowerEffectiveCounting.score w = credit).card

theorem lower_counts_from_digits (p encoded : Nat)
    (hd : ∀ (z : Fin 6) (i : Nat), i<128 →
      SharedDigitBlock.digit (2^132) p (65536*z.val+128*201+i) = lowerFiberN z.val i)
    (he : encoded = (List.range 6).foldl (fun s zeros =>
      s + ((p >>> (132*(65536*zeros+128*201))) % 2^(132*128))) 0)
    (i : Nat) (hi : i<128) : coefficient 132 encoded i = lowerCountN i := by
  have hsum (j : Nat) (hj : j<128) :
      (∑ z : Fin 6, 1*SharedDigitBlock.digit (2^132) p (65536*z.val+128*201+j)) = lowerCountN j := by
    simp only [Nat.one_mul]
    rw [← lower_fibers j]
    apply Finset.sum_congr rfl
    intro z _
    exact hd z j hj
  have he' : encoded = ∑ z : Fin 6, 1*(p / (2^132)^(65536*z.val+128*201) % (2^132)^128) := by
    rw [he, lower_windows_fold]
    simp only [Nat.one_mul]
  rw [coefficient, bits_digit_eq, he']
  exact (SharedDigitBlock.digit_window_sum (2^132) 128 (fun _ : Fin 6 => p)
    (fun z => 65536*z.val+128*201) (fun _ => 1) (by positivity)
    (fun j hj => by
      rw [hsum j hj]
      have := lower_counts_bound j
      omega) i hi).trans (hsum i hi)

theorem lower_counts_of_check
    (hd : ∀ (z : Fin 6) (i : Nat), i<128 →
      SharedDigitBlock.digit (2^132) SigGolfResearch.LowerEffectiveCounting.packed
        (65536*z.val+128*201+i) = lowerFiberN z.val i)
    (hcheck : lowerHistogramCheck = true) (c : Fin 128) :
    lowerWordCount c.val = histogramWeight lowerCounts c.val := by
  have he : packHistogram 132 0 128 lowerCounts =
      (List.range 6).foldl (fun s zeros => s +
        ((SigGolfResearch.LowerEffectiveCounting.packed >>> (132*(65536*zeros+128*201))) % 2^(132*128))) 0 :=
    by simpa only [lowerHistogramCheck, decide_eq_true_eq] using hcheck
  exact (lower_counts_from_digits _ _ hd he c.val c.isLt).symm.trans (lower_histogram_digits c)

/-- The path-aware lower selection law. -/
theorem selected_lower_histogram_card
    (hd : ∀ (z : Fin 6) (i : Nat), i<128 →
      SharedDigitBlock.digit (2^132) SigGolfResearch.LowerEffectiveCounting.packed
        (65536*z.val+128*201+i) = lowerFiberN z.val i)
    (hcheck : lowerHistogramCheck = true)
    (lay : Layer) (hl : lay ≠ 0) (floor c : Nat) (hf : floor ≤ c) (hc : c < 128) :
    (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut lay floor answer = some dl ∧
        CanonicalPolicy.credit lay dl.2 dl.1 = c).card = histogramWeight lowerHistogram c * 2^126 := by
  rw [selected_lower_path_card lay hl floor c hf, lowerHistogram, pathSplit, histogramWeight_split,
    lower_counts_of_check hd hcheck ⟨c, hc⟩]
  by_cases h4 : 4 ≤ c
  · rw [if_pos h4, if_pos h4, lower_counts_of_check hd hcheck ⟨c - 4, by omega⟩]
    ring
  · rw [if_neg h4, if_neg h4]
    ring

theorem selected_lower_histogram_probability
    (hd : ∀ (z : Fin 6) (i : Nat), i<128 →
      SharedDigitBlock.digit (2^132) SigGolfResearch.LowerEffectiveCounting.packed
        (65536*z.val+128*201+i) = lowerFiberN z.val i)
    (hcheck : lowerHistogramCheck = true)
    (lay : Layer) (hl : lay ≠ 0) (floor c : Nat) (hf : floor ≤ c) (hc : c < 128) :
    Pr[fun answer => ∃ dl, CanonicalPolicy.producerDecodeOut lay floor answer = some dl ∧
        CanonicalPolicy.credit lay dl.2 dl.1 = c | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (histogramWeight lowerHistogram c : ENNReal) / lowerDen := by
  classical
  rw [probEvent_uniformSample]
  rw [show (univ.filter fun answer : HashOutput => ∃ dl, CanonicalPolicy.producerDecodeOut lay floor answer = some dl ∧
        CanonicalPolicy.credit lay dl.2 dl.1 = c) = _ from rfl,
    selected_lower_histogram_card hd hcheck lay hl floor c hf hc]
  simp only [Fintype.card_bitVec, lowerDen, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (2 : ENNReal)^256 = (4*2^128)*2^126 by norm_num]
  exact ENNReal.mul_div_mul_right _ _ (by simp) (by simp)

end ClaudeWCT.Numerics.CanonicalHistogram
end
-- ==== merged from ClaudeWCT_Numerics_RouteCFees ====
section

/-! Route C for the marked-index bank excess (R6 campaign, stream RC).

`E (X - θ)⁺` for `X = ∑ⱼ pb Lⱼ` is split pointwise into a clipped background `Y = ∑ min (pb Lⱼ) c₀`
(Chernoff), one large bucket on a short row (paid through the exact one-index conditional law and the
Scarf bound), two or more large buckets (negative correlation), and buckets on long rows (first
moment). All numeric premises are per-bucket moments of the coordinate law; they are discharged from
binned fee certificates elsewhere. -/

namespace ClaudeWCT.Numerics.RouteC
open ENNReal Finset ClaudeWCT.Numerics.Law
open SphincsSecurity.Concrete (binomialAverage binomialAverage_succ binomialAverage_mono
  binomialAverage_sum binomialAverage_mul_left)
open SigGolfCandidate.T3.BPORS.History (atIndex atIndex_cons)

/-! ### The one-index conditional law (RC_SPEC I5 / L2) -/
section Split
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] (v : β → ENNReal)

/-- The draws of a marked word at the indices other than `j`, re-indexed by the subtype. -/
def eraseIdx (j : α) : List (α × β) → List ({i // i ≠ j} × β)
  | [] => []
  | p :: W => if h : p.1 = j then eraseIdx j W else (⟨p.1, h⟩, p.2) :: eraseIdx j W

omit [Fintype α] [Fintype β] in
theorem eraseIdx_cons_self (j : α) (b : β) (W : List (α × β)) :
    eraseIdx j ((j, b) :: W) = eraseIdx j W := by
  simp [eraseIdx]

omit [Fintype α] [Fintype β] in
theorem eraseIdx_cons_ne {j a : α} (h : a ≠ j) (b : β) (W : List (α × β)) :
    eraseIdx j ((a, b) :: W) = (⟨a, h⟩, b) :: eraseIdx j W := by
  simp [eraseIdx, h]

omit [Fintype α] [Fintype β] in
theorem atIndex_eraseIdx (j : α) (i : {i // i ≠ j}) (W : List (α × β)) :
    atIndex i (eraseIdx j W) = atIndex i.1 W := by
  induction W with
  | nil => rfl
  | cons p W ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : a = j
    · subst h
      rw [eraseIdx_cons_self, ih, atIndex_cons_ne (Ne.symm i.2)]
    · rw [eraseIdx_cons_ne h, atIndex_cons, atIndex_cons, ih]
      simp only [Subtype.ext_iff]

theorem binomialAverage_congr (rate : ENNReal) (T : ℕ) {f g : ℕ → ENNReal}
    (h : ∀ r, r ≤ T → f r = g r) : binomialAverage rate T f = binomialAverage rate T g := by
  induction T generalizing f g with
  | zero => exact h 0 le_rfl
  | succ T ih =>
    rw [binomialAverage_succ, binomialAverage_succ, ih (fun r hr => h r (by omega)),
      ih (fun r hr => h (r + 1) (by omega))]

theorem card_ne_subtype (j : α) : Fintype.card {i // i ≠ j} = Fintype.card α - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- Splitting a marked word at one index: the bucket at `j` is a binomial number of coordinate
draws, and given that bucket the other draws form the marked law on the remaining indices. -/
theorem law_marked_split (hv : ∑ b, v b = 1) (j : α) (hcard : 1 < Fintype.card α) (T : ℕ)
    (F : List β → List ({i // i ≠ j} × β) → ENNReal) :
    lawAvg (marked (α := α) v) T (fun W => F (atIndex j W) (eraseIdx j W)) =
      binomialAverage (Fintype.card α : ENNReal)⁻¹ T
        (fun r => lawAvg v r (fun L => lawAvg (marked (α := {i // i ≠ j}) v) (T - r) (F L))) := by
  set p : ENNReal := (Fintype.card α : ENNReal)⁻¹ with hp
  have hc0 : (Fintype.card α : ENNReal) ≠ 0 := by exact_mod_cast (by omega : Fintype.card α ≠ 0)
  have hct : (Fintype.card α : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  set n' : ℕ := Fintype.card {i // i ≠ j} with hn'
  have hn'v : n' = Fintype.card α - 1 := card_ne_subtype j
  have hn'0 : (n' : ENNReal) ≠ 0 := by exact_mod_cast (by omega : n' ≠ 0)
  have hn't : (n' : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hk : (n' : ENNReal) * p = 1 - p := by
    have h1 : (n' : ENNReal) + 1 = Fintype.card α := by
      rw [hn'v]; norm_cast; omega
    have h2 : (n' : ENNReal) * p + p = 1 := by
      rw [← add_one_mul, h1, hp, ENNReal.mul_inv_cancel hc0 hct]
    rw [← h2, ENNReal.add_sub_cancel_right (by simp [hp, hc0])]
  induction T generalizing F with
  | zero =>
    simp [lawAvg_zero, atIndex, eraseIdx, binomialAverage]
  | succ T ih =>
    rw [lawAvg_succ, sum_marked]
    -- the summand for one first draw `(a, b)`
    let A : ENNReal := binomialAverage p T
      (fun r => lawAvg v (r + 1) (fun L => lawAvg (marked (α := {i // i ≠ j}) v) (T - r) (F L)))
    let B : {i // i ≠ j} → ENNReal := fun a' => binomialAverage p T (fun r => lawAvg v r
      (fun L => ∑ b, v b * lawAvg (marked (α := {i // i ≠ j}) v) (T - r) (fun R => F L ((a', b) :: R))))
    have hrow : ∀ a : α, ∑ b, v b * lawAvg (marked (α := α) v) T
        (fun W => F (atIndex j ((a, b) :: W)) (eraseIdx j ((a, b) :: W))) =
        if h : a = j then A else B ⟨a, h⟩ := by
      intro a
      by_cases h : a = j
      · rw [dif_pos h]
        subst h
        simp_rw [atIndex_cons_self, eraseIdx_cons_self]
        have hb : ∀ b, lawAvg (marked (α := α) v) T (fun W => F (b :: atIndex a W) (eraseIdx a W)) =
            binomialAverage p T (fun r => lawAvg v r
              (fun L => lawAvg (marked (α := {i // i ≠ a}) v) (T - r) (F (b :: L)))) :=
          fun b => ih (fun L R => F (b :: L) R)
        simp_rw [hb]
        rw [binomialAverage_lawSum]
        rfl
      · rw [dif_neg h]
        simp_rw [atIndex_cons_ne h, eraseIdx_cons_ne h]
        have hb : ∀ b, lawAvg (marked (α := α) v) T
            (fun W => F (atIndex j W) ((⟨a, h⟩, b) :: eraseIdx j W)) =
            binomialAverage p T (fun r => lawAvg v r (fun L => lawAvg (marked (α := {i // i ≠ j}) v)
              (T - r) (fun R => F L ((⟨a, h⟩, b) :: R)))) :=
          fun b => ih (fun L R => F L ((⟨a, h⟩, b) :: R))
        simp_rw [hb]
        rw [binomialAverage_lawSum]
        congr 1
        funext r
        rw [lawAvg_sum]
        simp_rw [lawAvg_mul_left]
    simp_rw [hrow]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), dif_pos rfl]
    have hrest : ∑ a ∈ univ.erase j, (Fintype.card α : ENNReal)⁻¹ * (if h : a = j then A else B ⟨a, h⟩) =
        ∑ a' : {i // i ≠ j}, p * B a' := by
      rw [Finset.sum_subtype (univ.erase j) (p := fun a => a ≠ j) (fun x => by simp)]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [dif_neg a'.2]
    rw [hrest, ← Finset.mul_sum, binomialAverage_succ]
    -- the `j`-draw term
    have hA : A = binomialAverage p T (fun r => lawAvg v (r + 1)
        (fun L => lawAvg (marked (α := {i // i ≠ j}) v) (T + 1 - (r + 1)) (F L))) := by
      refine binomialAverage_congr p T fun r _ => ?_
      rw [Nat.add_sub_add_right]
    -- the other draws
    have hB : ∑ a', B a' = (n' : ENNReal) * binomialAverage p T (fun r => lawAvg v r
        (fun L => lawAvg (marked (α := {i // i ≠ j}) v) (T + 1 - r) (F L))) := by
      have hsum : ∑ a', B a' = binomialAverage p T (fun r => lawAvg v r (fun L =>
          ∑ a' : {i // i ≠ j}, ∑ b, v b *
            lawAvg (marked (α := {i // i ≠ j}) v) (T - r) (fun R => F L ((a', b) :: R)))) := by
        simp only [B]
        rw [← binomialAverage_sum]
        congr 1
        funext r
        rw [← lawAvg_sum]
      rw [hsum, ← binomialAverage_mul_left]
      refine binomialAverage_congr p T fun r hr => ?_
      rw [← lawAvg_mul_left]
      congr 1
      funext L
      have hs := sum_marked v (α' := {i // i ≠ j})
        (fun x => lawAvg (marked (α := {i // i ≠ j}) v) (T - r) (fun R => F L (x :: R)))
      rw [show T + 1 - r = (T - r) + 1 by omega, lawAvg_succ, hs, ← Finset.mul_sum, ← mul_assoc,
        ENNReal.mul_inv_cancel hn'0 hn't, one_mul]
    rw [hB, ← mul_assoc, mul_comm p (n' : ENNReal), hk, hA]
    ring

end Split

/-! ### The Scarf bound (RC_SPEC I6 / L3) -/
section Scarf

/-- Scarf's stop-loss bound: `E (Z - y)⁺ ≤ scarf y μ V` when `E Z = μ` and `Var Z ≤ V`. -/
noncomputable def scarf (y μ V : ℝ) : ℝ := ((μ - y) + Real.sqrt ((μ - y) ^ 2 + V)) / 2

theorem scarf_mono {y μ μ' V V' : ℝ} (hμ : μ ≤ μ') (hV : V ≤ V') (hV0 : 0 ≤ V) :
    scarf y μ V ≤ scarf y μ' V' := by
  unfold scarf
  have h1 : Real.sqrt ((μ' - y) ^ 2 + V) ≤ Real.sqrt ((μ' - y) ^ 2 + V') :=
    Real.sqrt_le_sqrt (by linarith)
  set u := μ - y with hu_def
  set u' := μ' - y with hu'_def
  have hu : u ≤ u' := by linarith
  set A := Real.sqrt (u ^ 2 + V) with hA_def
  set A' := Real.sqrt (u' ^ 2 + V) with hA'_def
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hA'0 : 0 ≤ A' := Real.sqrt_nonneg _
  have hAs : A ^ 2 = u ^ 2 + V := Real.sq_sqrt (by positivity)
  have hA's : A' ^ 2 = u' ^ 2 + V := Real.sq_sqrt (by positivity)
  have hAu : -u ≤ A := (neg_le_abs u).trans (Real.abs_le_sqrt (by linarith))
  have hA'u : -u' ≤ A' := (neg_le_abs u').trans (Real.abs_le_sqrt (by linarith))
  have h2 : u + A ≤ u' + A' := by
    by_cases hs : A + A' = 0
    · have : A = 0 := by linarith
      have : A' = 0 := by linarith
      linarith
    · have hpos : 0 < A + A' := lt_of_le_of_ne (by positivity) (Ne.symm hs)
      have hmul := mul_le_mul_of_nonneg_left (show -(u + u') ≤ A + A' by linarith)
        (show 0 ≤ u' - u by linarith)
      have key : (A - A') * (A + A') ≤ (u' - u) * (A + A') := by nlinarith
      have := le_of_mul_le_mul_right key hpos
      linarith
  linarith

theorem ofReal_tsub_max (p z : ENNReal) (hp : p ≠ ⊤) (hz : z ≠ ⊤) (θ : ℝ) (hθ : 0 ≤ θ) :
    (p + z) - ENNReal.ofReal θ = ENNReal.ofReal (max 0 (z.toReal - (θ - p.toReal))) := by
  have hpz : p + z = ENNReal.ofReal (p.toReal + z.toReal) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hp, ENNReal.ofReal_toReal hz]
  rw [hpz, ← ENNReal.ofReal_sub _ hθ, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_right zero_le]
  congr 1
  ring

/-- Scarf's bound for a law average, from a mean bound and a second-moment (variance) bound. -/
theorem scarf_law {γ : Type} [Fintype γ] (w : γ → ENNReal) (hw : ∑ c, w c = 1) (T : ℕ)
    (Z : List γ → ENNReal) (hZ : ∀ W, Z W ≠ ⊤) (p : ENNReal) (hp : p ≠ ⊤)
    (θ μ V : ℝ) (hθ : 0 ≤ θ) (hμ : 0 ≤ μ) (hV : 0 ≤ V)
    (hmean : lawAvg w T Z ≤ ENNReal.ofReal μ)
    (hsq : lawAvg w T (fun W => Z W ^ 2) ≤ (lawAvg w T Z) ^ 2 + ENNReal.ofReal V) :
    lawAvg w T (fun W => (p + Z W) - ENNReal.ofReal θ) ≤
      ENNReal.ofReal (scarf (θ - p.toReal) μ V) := by
  set y : ℝ := θ - p.toReal with hy
  set e := lawAvg w T Z with he_def
  set e2 := lawAvg w T (fun W => Z W ^ 2) with he2_def
  set E1 := lawAvg w T (fun W => (p + Z W) - ENNReal.ofReal θ) with hE1_def
  have he : e ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmean
  have he2 : e2 ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hsq
  have hE1 : E1 ≠ ⊤ := by
    have h : E1 ≤ lawAvg w T (fun W => p + Z W) := lawAvg_mono w T fun W => tsub_le_self
    rw [lawAvg_add, lawAvg_const w hw] at h
    exact ne_top_of_le_ne_top (by finiteness) h
  have hpt : ∀ W, (p + Z W) - ENNReal.ofReal θ = ENNReal.ofReal (max 0 ((Z W).toReal - y)) :=
    fun W => ofReal_tsub_max p (Z W) hp (hZ W) θ hθ
  have hzW : ∀ W, Z W = ENNReal.ofReal (Z W).toReal := fun W => (ENNReal.ofReal_toReal (hZ W)).symm
  set μ0 := e.toReal with hμ0_def
  set M2 := e2.toReal with hM2_def
  have hμ0 : μ0 ≤ μ := ENNReal.toReal_le_of_le_ofReal hμ hmean
  have hμ00 : 0 ≤ μ0 := ENNReal.toReal_nonneg
  have hM2 : M2 ≤ μ0 ^ 2 + V := by
    have h := ENNReal.toReal_mono (by finiteness) hsq
    rwa [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hV] at h
  -- the quadratic stop-loss majorant at a free slope `s`
  have hquad : ∀ s : ℝ, 0 < s → 4 * s * E1.toReal ≤ (μ0 - y + s) ^ 2 + V := by
    intro s hs
    by_cases hc : s ≤ y
    · set c := y - s with hc_def
      have hc0 : 0 ≤ c := by linarith
      have hpoint : ∀ W, ENNReal.ofReal (4 * s) * ((p + Z W) - ENNReal.ofReal θ) +
          ENNReal.ofReal (2 * c) * Z W ≤ Z W ^ 2 + ENNReal.ofReal (c ^ 2) := by
        intro W
        rw [hpt W, hzW W, ENNReal.toReal_ofReal ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        set z := (Z W).toReal
        have hz : 0 ≤ z := ENNReal.toReal_nonneg
        rcases le_total z y with hzy | hzy
        · rw [max_eq_left (by linarith)]
          nlinarith [sq_nonneg (z - c)]
        · rw [max_eq_right (by linarith)]
          nlinarith [sq_nonneg (z - y - s)]
      have hint := lawAvg_mono w T hpoint
      rw [lawAvg_add, lawAvg_mul_left, lawAvg_mul_left, lawAvg_add, lawAvg_const w hw] at hint
      have h := ENNReal.toReal_mono (by finiteness) hint
      rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_add he2 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at h
      have : μ0 - y + s = μ0 - c := by rw [hc_def]; ring
      rw [this]
      nlinarith
    · set d := s - y with hd_def
      have hd0 : 0 ≤ d := by linarith
      have hpoint : ∀ W, ENNReal.ofReal (4 * s) * ((p + Z W) - ENNReal.ofReal θ) ≤
          Z W ^ 2 + ENNReal.ofReal (2 * d) * Z W + ENNReal.ofReal (d ^ 2) := by
        intro W
        rw [hpt W, hzW W, ENNReal.toReal_ofReal ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow ENNReal.toReal_nonneg,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        set z := (Z W).toReal
        have hz : 0 ≤ z := ENNReal.toReal_nonneg
        rcases le_total z y with hzy | hzy
        · rw [max_eq_left (by linarith)]
          nlinarith
        · rw [max_eq_right (by linarith)]
          nlinarith [sq_nonneg (z - y - s)]
      have hint := lawAvg_mono w T hpoint
      rw [lawAvg_mul_left, lawAvg_add, lawAvg_add, lawAvg_mul_left, lawAvg_const w hw] at hint
      have h := ENNReal.toReal_mono (by finiteness) hint
      rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
        ENNReal.toReal_add he2 (by finiteness), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_ofReal (by positivity)] at h
      have : μ0 - y + s = μ0 + d := by rw [hd_def]; ring
      rw [this]
      nlinarith
  -- optimise the slope
  have hE1r : E1.toReal ≤ scarf y μ0 V := by
    set s0 := Real.sqrt ((μ0 - y) ^ 2 + V) with hs0_def
    have hs00 : 0 ≤ s0 := Real.sqrt_nonneg _
    have hs0sq : s0 ^ 2 = (μ0 - y) ^ 2 + V := Real.sq_sqrt (by positivity)
    unfold scarf
    rw [← hs0_def]
    rcases eq_or_lt_of_le hs00 with h0 | hpos
    · -- degenerate law: `V = 0` and `μ0 = y`
      have hV0 : V = 0 := by nlinarith [sq_nonneg (μ0 - y)]
      have hμy : μ0 - y = 0 := by nlinarith [sq_nonneg (μ0 - y)]
      rw [← h0, hμy]
      norm_num
      by_contra hneg
      push Not at hneg
      have hq := hquad (E1.toReal) hneg
      rw [hμy, hV0] at hq
      nlinarith
    · have hq := hquad s0 hpos
      have : (μ0 - y + s0) ^ 2 + V = 2 * s0 * (s0 + (μ0 - y)) := by nlinarith
      rw [this] at hq
      nlinarith
  calc E1 = ENNReal.ofReal E1.toReal := (ENNReal.ofReal_toReal hE1).symm
    _ ≤ ENNReal.ofReal (scarf y μ0 V) := ENNReal.ofReal_le_ofReal hE1r
    _ ≤ ENNReal.ofReal (scarf y μ V) := ENNReal.ofReal_le_ofReal (scarf_mono hμ0 le_rfl hV)

end Scarf

/-! ### The pointwise split (RC_SPEC I1 + I2 / L1) -/
section Pointwise
variable {α : Type} [Fintype α] [DecidableEq α]

/-- `(∑ xᵢ - θ)⁺` is paid by the clipped background, one large short-row bucket on top of the
clipped others, the excess of every large bucket when another bucket is large, and long rows. -/
theorem split_finset (x : α → ENNReal) (short : α → Prop) [DecidablePred short] (c θ : ENNReal) :
    (∑ i, x i) - θ ≤
      ((∑ i, min (x i) c) - θ) +
      ∑ j, (if short j ∧ c < x j then (x j + ∑ i ∈ univ.erase j, min (x i) c) - θ else 0) +
      ∑ j, (x j - c) * ∑ i ∈ univ.erase j, (if c < x i then (1 : ENNReal) else 0) +
      ∑ j, (if short j then 0 else x j) := by
  classical
  set vv : α → ENNReal := fun i => if short i then x i else 0 with hvv
  set tt : α → ENNReal := fun i => if short i then 0 else x i with htt
  set Y : ENNReal := ∑ i, min (x i) c with hY
  set K1 : ENNReal := ∑ j, (if short j ∧ c < x j then (x j + ∑ i ∈ univ.erase j, min (x i) c) - θ else 0)
  set K2 : ENNReal := ∑ j, (x j - c) * ∑ i ∈ univ.erase j, (if c < x i then (1 : ENNReal) else 0)
  have hsplit : (∑ i, x i) = (∑ i, vv i) + ∑ i, tt i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hvv, htt]
    split_ifs <;> simp
  have hstep : (∑ i, x i) - θ ≤ ((∑ i, vv i) - θ) + ∑ i, tt i := by
    rw [hsplit]
    exact tsub_le_iff_right.mpr (by
      calc (∑ i, vv i) + ∑ i, tt i ≤ (((∑ i, vv i) - θ) + θ) + ∑ i, tt i :=
            add_le_add le_tsub_add le_rfl
        _ = _ := by ring)
  have hsmall : ∀ i, ¬(short i ∧ c < x i) → vv i ≤ min (x i) c := by
    intro i hi
    simp only [hvv]
    split_ifs with hs
    · have : x i ≤ c := not_lt.mp (fun h => hi ⟨hs, h⟩)
      exact le_min le_rfl this
    · exact zero_le
  have hcore : (∑ i, vv i) - θ ≤ (Y - θ) + K1 + K2 := by
    by_cases hnone : ∀ j, ¬(short j ∧ c < x j)
    · have : (∑ i, vv i) ≤ Y := Finset.sum_le_sum fun i _ => hsmall i (hnone i)
      calc (∑ i, vv i) - θ ≤ Y - θ := tsub_le_tsub_right this θ
        _ ≤ (Y - θ) + K1 + K2 := by rw [add_assoc]; exact le_self_add
    · push Not at hnone
      obtain ⟨j0, hj0⟩ := hnone
      by_cases hone : ∀ i ∈ univ.erase j0, ¬(short i ∧ c < x i)
      · have hv0 : vv j0 = x j0 := by simp only [hvv, if_pos hj0.1]
        have hle : (∑ i, vv i) ≤ x j0 + ∑ i ∈ univ.erase j0, min (x i) c := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0), hv0]
          exact add_le_add le_rfl (Finset.sum_le_sum fun i hi => hsmall i (hone i hi))
        have hterm : (x j0 + ∑ i ∈ univ.erase j0, min (x i) c) - θ ≤ K1 := by
          have := Finset.single_le_sum (f := fun j => if short j ∧ c < x j then
            (x j + ∑ i ∈ univ.erase j, min (x i) c) - θ else 0) (fun j _ => zero_le) (Finset.mem_univ j0)
          simpa only [if_pos hj0] using this
        calc (∑ i, vv i) - θ ≤ (x j0 + ∑ i ∈ univ.erase j0, min (x i) c) - θ := tsub_le_tsub_right hle θ
          _ ≤ K1 := hterm
          _ ≤ (Y - θ) + K1 + K2 := by
            rw [add_assoc]; exact le_add_left (le_self_add)
      · push Not at hone
        obtain ⟨j1, hj1m, hj1⟩ := hone
        have hj10 : j1 ≠ j0 := Finset.ne_of_mem_erase hj1m
        have hper : ∀ i, vv i ≤ min (x i) c +
            (x i - c) * ∑ k ∈ univ.erase i, (if c < x k then (1 : ENNReal) else 0) := by
          intro i
          by_cases hbig : short i ∧ c < x i
          · have hvi : vv i = x i := by simp only [hvv, if_pos hbig.1]
            have hmin : min (x i) c = c := min_eq_right hbig.2.le
            have hone' : (1 : ENNReal) ≤ ∑ k ∈ univ.erase i, (if c < x k then (1 : ENNReal) else 0) := by
              by_cases hi0 : i = j0
              · have hm : j1 ∈ univ.erase i := Finset.mem_erase.mpr ⟨by rw [hi0]; exact hj10, mem_univ _⟩
                have := Finset.single_le_sum (f := fun k => if c < x k then (1 : ENNReal) else 0)
                  (fun k _ => zero_le) hm
                simpa only [if_pos hj1.2] using this
              · have hm : j0 ∈ univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hi0, mem_univ _⟩
                have := Finset.single_le_sum (f := fun k => if c < x k then (1 : ENNReal) else 0)
                  (fun k _ => zero_le) hm
                simpa only [if_pos hj0.2] using this
            rw [hvi, hmin]
            calc x i = c + (x i - c) := (add_tsub_cancel_of_le hbig.2.le).symm
              _ ≤ c + (x i - c) * ∑ k ∈ univ.erase i, (if c < x k then (1 : ENNReal) else 0) := by
                gcongr
                exact le_mul_of_one_le_right' hone'
          · exact (hsmall i hbig).trans le_self_add
        have hle : (∑ i, vv i) ≤ Y + K2 := by
          rw [hY, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun i _ => hper i
        calc (∑ i, vv i) - θ ≤ (Y + K2) - θ := tsub_le_tsub_right hle θ
          _ ≤ (Y - θ) + K2 := by
            apply tsub_le_iff_right.mpr
            calc Y + K2 ≤ ((Y - θ) + θ) + K2 := add_le_add le_tsub_add le_rfl
              _ = _ := by ring
          _ ≤ (Y - θ) + K1 + K2 := add_le_add (le_self_add) le_rfl
  calc (∑ i, x i) - θ ≤ ((∑ i, vv i) - θ) + ∑ i, tt i := hstep
    _ ≤ ((Y - θ) + K1 + K2) + ∑ i, tt i := add_le_add hcore le_rfl

end Pointwise

/-! ### Assembly (RC_SPEC L5 + L6) -/
section Assembly
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] (v : β → ENNReal)

omit [Fintype α] [DecidableEq α] in
theorem lawAvg_mono_length (r : ℕ) {f g : List β → ENNReal}
    (h : ∀ L, L.length = r → f L ≤ g L) : lawAvg v r f ≤ lawAvg v r g := by
  induction r generalizing f g with
  | zero => exact h [] rfl
  | succ r ih =>
    rw [lawAvg_succ, lawAvg_succ]
    exact Finset.sum_le_sum fun b _ =>
      mul_le_mul' le_rfl (ih fun L hL => h (b :: L) (by simp [hL]))

omit [Fintype α] [DecidableEq α] in
theorem lawAvg_zero_fun (r : ℕ) : lawAvg v r (fun _ => (0 : ENNReal)) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [lawAvg_succ, ih]

theorem law_marked_sum' [Nonempty α] (hv : ∑ b, v b = 1) (T : ℕ) (f : List β → ENNReal) :
    lawAvg (marked (α := α) v) T (fun W => ∑ i : α, f (atIndex i W)) =
      (Fintype.card α : ENNReal) * coordAverage (Fintype.card α : ENNReal)⁻¹ v T f := by
  rw [lawAvg_sum]
  simp only [law_marked_atIndex v hv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rfl

theorem exp_majorant (x θ a : ℝ) (ha : 0 < a) :
    max 0 (x - θ) ≤ (3 / (8 * a)) * (Real.exp (-a * θ) * Real.exp (a * x)) := by
  have he := Real.exp_one_gt_d9
  set E := Real.exp (-a * θ) * Real.exp (a * x) with hE
  have hEpos : 0 < E := by positivity
  have hu := Real.add_one_le_exp (a * (x - θ) - 1)
  have h1 : Real.exp (a * (x - θ) - 1) = E / Real.exp 1 := by
    rw [Real.exp_sub, show a * (x - θ) = -a * θ + a * x by ring, Real.exp_add]
  have h2 : a * (x - θ) ≤ E / Real.exp 1 := by linarith
  have h3 : E / Real.exp 1 ≤ (3 / 8) * E := by
    rw [div_le_iff₀ (Real.exp_pos 1)]
    nlinarith
  apply max_le (by positivity)
  have h4 : a * (x - θ) ≤ a * ((3 / (8 * a)) * E) := by
    have : a * ((3 / (8 * a)) * E) = (3 / 8) * E := by field_simp
    rw [this]
    linarith
  exact le_of_mul_le_mul_left h4 ha

/-- The clipped background (RC_SPEC I3 + I4): Chernoff bound through bucket product dependence. -/
theorem clipped_excess [Nonempty α] (hv : ∑ b, v b = 1) (T : ℕ) (Y : List β → ENNReal)
    (hY : ∀ L, Y L ≠ ⊤) (hmono : ∀ L b R, Y (L ++ R) ≤ Y (L ++ b :: R))
    (θ a B : ℝ) (hθ : 0 ≤ θ) (ha : 0 < a) (hB : 0 ≤ B)
    (hmgf : (∑ _i : α, coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => ENNReal.ofReal (Real.exp (a * (Y L).toReal)) - 1)) ≤ ENNReal.ofReal B) :
    lawAvg (marked (α := α) v) T (fun W => (∑ i, Y (atIndex i W)) - ENNReal.ofReal θ) ≤
      ENNReal.ofReal ((3 / (8 * a)) * Real.exp (B - a * θ)) := by
  have hexp := law_marked_exp_sum_general v hv T (fun _ L => Y L) a B ha.le hB
    (fun _ L => hY L) (fun _ L b R => hmono L b R) hmgf
  set k := ENNReal.ofReal ((3 / (8 * a)) * Real.exp (-a * θ)) with hk
  have hpoint : ∀ W : List (α × β), (∑ i : α, Y (atIndex i W)) - ENNReal.ofReal θ ≤
      k * ENNReal.ofReal (Real.exp (a * (∑ i : α, Y (atIndex i W)).toReal)) := by
    intro W
    set s := ∑ i : α, Y (atIndex i W)
    have hs : s ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hY _
    have hrw : s - ENNReal.ofReal θ = ENNReal.ofReal (max 0 (s.toReal - θ)) := by
      rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_right zero_le, ENNReal.ofReal_sub _ hθ,
        ENNReal.ofReal_toReal hs]
    rw [hrw, hk, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := exp_majorant s.toReal θ a ha
    linarith
  calc lawAvg (marked (α := α) v) T (fun W => (∑ i, Y (atIndex i W)) - ENNReal.ofReal θ)
      ≤ lawAvg (marked (α := α) v) T
          (fun W => k * ENNReal.ofReal (Real.exp (a * (∑ i, Y (atIndex i W)).toReal))) :=
        lawAvg_mono _ _ hpoint
    _ = k * lawAvg (marked (α := α) v) T
          (fun W => ENNReal.ofReal (Real.exp (a * (∑ i, Y (atIndex i W)).toReal))) := lawAvg_mul_left _ _ _ _
    _ ≤ k * ENNReal.ofReal (Real.exp B) := mul_le_mul' le_rfl hexp
    _ = ENNReal.ofReal ((3 / (8 * a)) * Real.exp (B - a * θ)) := by
      rw [hk, ← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
      congr 3
      ring

/-- One large bucket on a short row (RC_SPEC I5-I7): exact conditional law and the Scarf bound. -/
theorem large_index_bound [Nonempty α] (hv : ∑ b, v b = 1) (hcard : 1 < Fintype.card α) (j : α)
    (T rows : ℕ) (pb : List β → ENNReal) (hpb : ∀ L, pb L ≠ ⊤)
    (hmono : ∀ L b R, pb (L ++ R) ≤ pb (L ++ b :: R))
    (c0 θ m vv : ℝ) (hθ : 0 ≤ θ) (hm0 : 0 ≤ m) (hvv0 : 0 ≤ vv)
    (hempty : pb [] ≤ ENNReal.ofReal c0)
    (hmean : ∀ r, 1 ≤ r → r ≤ rows →
      ((Fintype.card α - 1 : ℕ) : ENNReal) * coordAverage ((Fintype.card α - 1 : ℕ) : ENNReal)⁻¹ v (T - r)
        (fun L => min (pb L) (ENNReal.ofReal c0)) ≤ ENNReal.ofReal m)
    (hsecond : ∀ r, 1 ≤ r → r ≤ rows →
      ((Fintype.card α - 1 : ℕ) : ENNReal) * coordAverage ((Fintype.card α - 1 : ℕ) : ENNReal)⁻¹ v (T - r)
        (fun L => min (pb L) (ENNReal.ofReal c0) ^ 2) ≤ ENNReal.ofReal vv) :
    lawAvg (marked (α := α) v) T (fun W =>
      if (atIndex j W).length ≤ rows ∧ ENNReal.ofReal c0 < pb (atIndex j W) then
        (pb (atIndex j W) + ∑ i ∈ univ.erase j, min (pb (atIndex i W)) (ENNReal.ofReal c0)) -
          ENNReal.ofReal θ
      else 0) ≤
    coordAverage (Fintype.card α : ENNReal)⁻¹ v T (fun L =>
      if L.length ≤ rows ∧ ENNReal.ofReal c0 < pb L then
        ENNReal.ofReal (scarf (θ - (pb L).toReal) m vv) else 0) := by
  set c := ENNReal.ofReal c0 with hc
  set Y : List β → ENNReal := fun L => min (pb L) c with hYdef
  have hYtop : ∀ L, Y L ≠ ⊤ := fun L => ne_top_of_le_ne_top (hpb L) (min_le_left _ _)
  have hYcons : ∀ a L, Y L ≤ Y (a :: L) := fun a L =>
    min_le_min (by simpa using hmono [] a L) le_rfl
  set F : List β → List ({i // i ≠ j} × β) → ENNReal := fun L R =>
    if L.length ≤ rows ∧ c < pb L then (pb L + ∑ i' : {i // i ≠ j}, Y (atIndex i' R)) - ENNReal.ofReal θ
    else 0 with hF
  have hrw : (fun W : List (α × β) =>
      if (atIndex j W).length ≤ rows ∧ c < pb (atIndex j W) then
        (pb (atIndex j W) + ∑ i ∈ univ.erase j, min (pb (atIndex i W)) c) - ENNReal.ofReal θ
      else 0) = fun W => F (atIndex j W) (eraseIdx j W) := by
    funext W
    have hs : ∑ i ∈ univ.erase j, min (pb (atIndex i W)) c =
        ∑ i' : {i // i ≠ j}, Y (atIndex i' (eraseIdx j W)) := by
      rw [Finset.sum_subtype (univ.erase j) (p := fun a => a ≠ j) (fun x => by simp)]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [atIndex_eraseIdx]
    simp only [hF, hs]
  rw [hrw, law_marked_split v hv j hcard T F]
  unfold coordAverage
  apply binomialAverage_mono
  intro r
  apply lawAvg_mono_length v r
  intro L hL
  simp only [hF]
  split_ifs with hbig
  · have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · exfalso
        rw [h0, List.length_eq_zero_iff] at hL
        rw [hL] at hbig
        exact absurd hempty (not_le.mpr hbig.2)
      · exact h0
    have hrr : r ≤ rows := hL ▸ hbig.1
    obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card hcard j
    haveI : Nonempty {i // i ≠ j} := ⟨⟨k, hk⟩⟩
    have hcardj : (Fintype.card {i // i ≠ j} : ENNReal) = ((Fintype.card α - 1 : ℕ) : ENNReal) := by
      rw [card_ne_subtype]
    have hmeanL : lawAvg (marked (α := {i // i ≠ j}) v) (T - r)
        (fun R => ∑ i' : {i // i ≠ j}, Y (atIndex i' R)) ≤ ENNReal.ofReal m := by
      rw [law_marked_sum' v hv, hcardj]
      exact hmean r hr1 hrr
    have hsqL : lawAvg (marked (α := {i // i ≠ j}) v) (T - r)
        (fun R => (∑ i' : {i // i ≠ j}, Y (atIndex i' R)) ^ 2) ≤
        (lawAvg (marked (α := {i // i ≠ j}) v) (T - r)
          (fun R => ∑ i' : {i // i ≠ j}, Y (atIndex i' R))) ^ 2 + ENNReal.ofReal vv := by
      have hcross : ∀ first second : {i // i ≠ j}, first ≠ second →
          lawAvg (marked (α := {i // i ≠ j}) v) (T - r)
            (fun R => Y (atIndex first R) * Y (atIndex second R)) ≤
          lawAvg (marked (α := {i // i ≠ j}) v) (T - r) (fun R => Y (atIndex first R)) *
            lawAvg (marked (α := {i // i ≠ j}) v) (T - r) (fun R => Y (atIndex second R)) :=
        fun first second hne => law_marked_negative_correlation v hv first second hne (T - r) Y Y
          hYcons hYcons
      have h := lawAvg_sum_square_le (marked (α := {i // i ≠ j}) v) (T - r)
        (fun i' R => Y (atIndex i' R)) hcross
      have hsq : ∑ i' : {i // i ≠ j}, lawAvg (marked (α := {i // i ≠ j}) v) (T - r)
          (fun R => Y (atIndex i' R) ^ 2) ≤ ENNReal.ofReal vv := by
        have := (lawAvg_sum (marked (α := {i // i ≠ j}) v) (T - r) univ
          (fun i' R => Y (atIndex i' R) ^ 2)).symm.trans
          (law_marked_sum' v hv (T - r) (fun L => Y L ^ 2))
        rw [this, hcardj]
        exact hsecond r hr1 hrr
      calc _ ≤ _ := h
        _ ≤ (lawAvg (marked (α := {i // i ≠ j}) v) (T - r)
              (fun R => ∑ i' : {i // i ≠ j}, Y (atIndex i' R))) ^ 2 + ENNReal.ofReal vv := by
          rw [← lawAvg_sum]
          exact add_le_add le_rfl hsq
    exact scarf_law (marked (α := {i // i ≠ j}) v) (marked_sum_one v hv) (T - r)
      (fun R => ∑ i' : {i // i ≠ j}, Y (atIndex i' R))
      (fun R => ENNReal.sum_ne_top.mpr fun i' _ => hYtop _) (pb L) (hpb L) θ m vv hθ hm0 hvv0
      hmeanL hsqL
  · exact (lawAvg_zero_fun _ _).le

/-- Route C excess bound for a marked-index bank: the generic statement (RC_SPEC TOTAL). -/
theorem excess_route_c [Nonempty α] (hv : ∑ b, v b = 1) (hcard : 1 < Fintype.card α)
    (T rows : ℕ) (pb : List β → ENNReal) (hpb : ∀ L, pb L ≠ ⊤)
    (hmono : ∀ L b R, pb (L ++ R) ≤ pb (L ++ b :: R))
    (c0 θ a B m vv K1 O Λ tF : ℝ) (hθ : 0 ≤ θ) (ha : 0 < a) (hB : 0 ≤ B) (hm0 : 0 ≤ m)
    (hvv0 : 0 ≤ vv) (hK10 : 0 ≤ K1) (hO0 : 0 ≤ O) (hΛ0 : 0 ≤ Λ) (htF0 : 0 ≤ tF)
    (hempty : pb [] ≤ ENNReal.ofReal c0)
    (hmgf : (∑ _i : α, coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => ENNReal.ofReal (Real.exp (a * (min (pb L) (ENNReal.ofReal c0)).toReal)) - 1)) ≤
        ENNReal.ofReal B)
    (hmean : ∀ r, 1 ≤ r → r ≤ rows →
      ((Fintype.card α - 1 : ℕ) : ENNReal) * coordAverage ((Fintype.card α - 1 : ℕ) : ENNReal)⁻¹ v (T - r)
        (fun L => min (pb L) (ENNReal.ofReal c0)) ≤ ENNReal.ofReal m)
    (hsecond : ∀ r, 1 ≤ r → r ≤ rows →
      ((Fintype.card α - 1 : ℕ) : ENNReal) * coordAverage ((Fintype.card α - 1 : ℕ) : ENNReal)⁻¹ v (T - r)
        (fun L => min (pb L) (ENNReal.ofReal c0) ^ 2) ≤ ENNReal.ofReal vv)
    (hK1 : (Fintype.card α : ENNReal) * coordAverage (Fintype.card α : ENNReal)⁻¹ v T (fun L =>
      if L.length ≤ rows ∧ ENNReal.ofReal c0 < pb L then
        ENNReal.ofReal (scarf (θ - (pb L).toReal) m vv) else 0) ≤ ENNReal.ofReal K1)
    (hover : (Fintype.card α : ENNReal) * coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => pb L - ENNReal.ofReal c0) ≤ ENNReal.ofReal O)
    (hcount : (Fintype.card α : ENNReal) * coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => if ENNReal.ofReal c0 < pb L then 1 else 0) ≤ ENNReal.ofReal Λ)
    (htail : (Fintype.card α : ENNReal) * coordAverage (Fintype.card α : ENNReal)⁻¹ v T
      (fun L => if rows < L.length then pb L else 0) ≤ ENNReal.ofReal tF) :
    lawAvg (marked (α := α) v) T (fun W => (∑ i, pb (atIndex i W)) - ENNReal.ofReal θ) ≤
      ENNReal.ofReal ((3 / (8 * a)) * Real.exp (B - a * θ) + K1 + O * Λ + tF) := by
  set c := ENNReal.ofReal c0 with hc
  set n := (Fintype.card α : ENNReal) with hn
  have hpoint : ∀ W : List (α × β), (∑ i, pb (atIndex i W)) - ENNReal.ofReal θ ≤
      ((∑ i, min (pb (atIndex i W)) c) - ENNReal.ofReal θ) +
      ∑ j, (if (atIndex j W).length ≤ rows ∧ c < pb (atIndex j W) then
        (pb (atIndex j W) + ∑ i ∈ univ.erase j, min (pb (atIndex i W)) c) - ENNReal.ofReal θ else 0) +
      ∑ j, (pb (atIndex j W) - c) * ∑ i ∈ univ.erase j, (if c < pb (atIndex i W) then (1 : ENNReal) else 0) +
      ∑ j, (if rows < (atIndex j W).length then pb (atIndex j W) else 0) := by
    intro W
    have h := split_finset (fun i => pb (atIndex i W)) (fun i => (atIndex i W).length ≤ rows) c
      (ENNReal.ofReal θ)
    have ht : ∀ j, (if (atIndex j W).length ≤ rows then 0 else pb (atIndex j W)) =
        (if rows < (atIndex j W).length then pb (atIndex j W) else 0) := by
      intro j
      split_ifs with h1 h2 h2 <;> first | rfl | omega
    simpa only [ht] using h
  refine (lawAvg_mono _ _ hpoint).trans ?_
  rw [lawAvg_add, lawAvg_add, lawAvg_add, lawAvg_sum, lawAvg_sum, lawAvg_sum]
  -- the clipped background
  have h0 := clipped_excess v hv T (fun L => min (pb L) c)
    (fun L => ne_top_of_le_ne_top (hpb L) (min_le_left _ _))
    (fun L b R => min_le_min (hmono L b R) le_rfl) θ a B hθ ha hB hmgf
  -- one large bucket
  have h1 : (∑ j, lawAvg (marked (α := α) v) T (fun W =>
      if (atIndex j W).length ≤ rows ∧ c < pb (atIndex j W) then
        (pb (atIndex j W) + ∑ i ∈ univ.erase j, min (pb (atIndex i W)) c) - ENNReal.ofReal θ else 0)) ≤
      ENNReal.ofReal K1 := by
    refine (Finset.sum_le_sum fun j _ =>
      large_index_bound v hv hcard j T rows pb hpb hmono c0 θ m vv hθ hm0 hvv0 hempty hmean hsecond).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact hK1
  -- two large buckets
  have hfcons : ∀ a L, pb L - c ≤ pb (a :: L) - c := fun a L =>
    tsub_le_tsub_right (by simpa using hmono [] a L) c
  have hgcons : ∀ a L, (if c < pb L then (1 : ENNReal) else 0) ≤ (if c < pb (a :: L) then 1 else 0) := by
    intro a L
    by_cases h : c < pb L
    · rw [if_pos h, if_pos (lt_of_lt_of_le h (by simpa using hmono [] a L))]
    · rw [if_neg h]; exact zero_le
  have h2 : (∑ j, lawAvg (marked (α := α) v) T (fun W =>
      (pb (atIndex j W) - c) * ∑ i ∈ univ.erase j, (if c < pb (atIndex i W) then (1 : ENNReal) else 0))) ≤
      ENNReal.ofReal O * ENNReal.ofReal Λ := by
    have hj : ∀ j, lawAvg (marked (α := α) v) T (fun W =>
        (pb (atIndex j W) - c) * ∑ i ∈ univ.erase j, (if c < pb (atIndex i W) then (1 : ENNReal) else 0)) ≤
        ∑ _i : α, coordAverage n⁻¹ v T (fun L => pb L - c) *
          coordAverage n⁻¹ v T (fun L => if c < pb L then 1 else 0) := by
      intro j
      simp_rw [Finset.mul_sum]
      rw [lawAvg_sum]
      refine (Finset.sum_le_sum fun i hi => ?_).trans
        (Finset.sum_le_sum_of_subset (Finset.erase_subset j univ))
      have hne : j ≠ i := Ne.symm (Finset.ne_of_mem_erase hi)
      refine (law_marked_negative_correlation v hv j i hne T (fun L => pb L - c)
        (fun L => if c < pb L then 1 else 0) hfcons hgcons).trans_eq ?_
      rw [law_marked_atIndex v hv j T (fun L => pb L - c),
        law_marked_atIndex v hv i T (fun L => if c < pb L then 1 else 0)]
      rfl
    calc _ ≤ ∑ _j : α, ∑ _i : α, coordAverage n⁻¹ v T (fun L => pb L - c) *
          coordAverage n⁻¹ v T (fun L => if c < pb L then 1 else 0) := Finset.sum_le_sum fun j _ => hj j
      _ = (n * coordAverage n⁻¹ v T (fun L => pb L - c)) *
          (n * coordAverage n⁻¹ v T (fun L => if c < pb L then 1 else 0)) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
        ring
      _ ≤ ENNReal.ofReal O * ENNReal.ofReal Λ := mul_le_mul' hover hcount
  -- long rows
  have h3 : (∑ j, lawAvg (marked (α := α) v) T (fun W =>
      if rows < (atIndex j W).length then pb (atIndex j W) else 0)) ≤ ENNReal.ofReal tF := by
    have := (lawAvg_sum (marked (α := α) v) T univ (fun j W =>
      if rows < (atIndex j W).length then pb (atIndex j W) else 0)).symm.trans
      (law_marked_sum' v hv T (fun L => if rows < L.length then pb L else 0))
    rw [this]
    exact htail
  calc _ ≤ ENNReal.ofReal ((3 / (8 * a)) * Real.exp (B - a * θ)) + ENNReal.ofReal K1 +
        ENNReal.ofReal O * ENNReal.ofReal Λ + ENNReal.ofReal tF :=
      add_le_add (add_le_add (add_le_add h0 h1) h2) h3
    _ = _ := by
      rw [← ENNReal.ofReal_mul hO0, ← ENNReal.ofReal_add (by positivity) hK10,
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) htF0]

end Assembly

end ClaudeWCT.Numerics.RouteC

/-! Route C fee vectors (R6 campaign, stream RC, RC_SPEC L7).

A fee vector is a list of runs `(lo, hi, fee)` over the 7210 forest bins of `SharedFees`. A run is
sound for a cost `f` when `f x ≤ x * fee / feeScale` for every price `x` in the run's bin range
`[lowerQ g lo, upperQ g hi]` (bin `j` holds prices `g/2^66 * coverage` in
`[g/2^66 * (100/101)^13 * (101/100)^j, g/2^66 * (101/100)^j]`). Each `*Ok` below is a decidable
run check, and `*Ok_sound` proves it sound. The six route-C costs are the clipped mean, clipped
square, large-bucket count, excess over the clip, clipped exponential, and the Scarf payment. -/

namespace ClaudeWCT.Numerics.RouteCFees
open ClaudeWCT.Numerics.RouteC (scarf)

/-- Fee scale: fees are stored as `feeScale * (cost / price)`. -/
def feeScale : ℕ := 2 ^ 64

/-- Route C parameters: gate, clip `c0`, Chernoff slope `a`, threshold `θ`, certified conditional
mean `m`, variance `vv`, and `sv ≥ √vv`. -/
structure Par where
  g : ℕ
  c0 : ℚ
  a : ℚ
  θ : ℚ
  m : ℚ
  vv : ℚ
  sv : ℚ

/-- Upper price of bin `j` at gate `g`. -/
def upperQ (g j : ℕ) : ℚ := mkRat (g * 101 ^ j) (2 ^ 66 * 100 ^ j)
/-- Lower price of bin `j` at gate `g` (13 roundings below the upper price). -/
def lowerQ (g j : ℕ) : ℚ := mkRat (g * 101 ^ j * 100 ^ 13) (2 ^ 66 * 100 ^ j * 101 ^ 13)

/-! ### Run checks -/

def meanOk (P : Par) (L _U : ℚ) (fee : ℕ) : Bool :=
  decide ((feeScale : ℚ) ≤ fee) || (decide (P.c0 ≤ L) && decide ((feeScale : ℚ) * P.c0 ≤ fee * L))

def secOk (P : Par) (L U : ℚ) (fee : ℕ) : Bool :=
  decide ((feeScale : ℚ) * P.c0 ≤ fee) || (decide (U ≤ P.c0) && decide ((feeScale : ℚ) * U ≤ fee)) ||
    (decide (P.c0 ≤ L) && decide ((feeScale : ℚ) * (P.c0 * P.c0) ≤ fee * L))

def countOk (P : Par) (L U : ℚ) (fee : ℕ) : Bool :=
  decide (U ≤ P.c0) || decide ((feeScale : ℚ) ≤ fee * P.c0) || decide ((feeScale : ℚ) ≤ fee * L)

def overOk (P : Par) (_L U : ℚ) (fee : ℕ) : Bool :=
  decide (U ≤ P.c0) || decide ((feeScale : ℚ) ≤ fee) || (decide (0 < U) && decide ((feeScale : ℚ) * (U - P.c0) ≤ fee * U))

/-- `expUpper` argument for `a * x` (`SharedFees.scale` units, rounded up). -/
def expArg (a x : ℚ) : ℕ := ⌈a * x * (ClaudeWCT.Numerics.SharedFees.scale : ℚ)⌉.toNat

/-- Upper bound of `exp (a * x) - 1` as a rational. -/
def expm1Up (a x : ℚ) : ℚ :=
  ((ClaudeWCT.Numerics.SharedFees.expUpper (expArg a x) : ℚ) - ClaudeWCT.Numerics.SharedFees.scale) /
    ClaudeWCT.Numerics.SharedFees.scale

def mgfOk (P : Par) (L U : ℚ) (fee : ℕ) : Bool :=
  decide ((feeScale : ℚ) * expm1Up P.a P.c0 ≤ fee * P.c0) ||
    (decide (U ≤ P.c0) && decide (0 < U) &&
      decide (expArg P.a U ≤ 8 * ClaudeWCT.Numerics.SharedFees.scale) &&
      decide ((feeScale : ℚ) * expm1Up P.a U ≤ fee * U)) ||
    (decide (P.c0 ≤ L) && decide ((feeScale : ℚ) * expm1Up P.a P.c0 ≤ fee * L))

/-- `scarf (θ - x) m vv ≤ x * fee / feeScale`, in rational arithmetic without square roots. -/
def scarfPointOk (P : Par) (x : ℚ) (fee : ℕ) : Bool :=
  let w := P.m - P.θ + x
  let t := 2 * x * fee / feeScale - w
  decide (0 ≤ t) && decide (w * w + P.vv ≤ t * t)

def scarfOk (P : Par) (L U : ℚ) (fee : ℕ) : Bool :=
  decide (U ≤ P.c0) || (scarfPointOk P (max L P.c0) fee && scarfPointOk P U fee && decide (max L P.c0 ≤ U))

/-! ### Costs -/

noncomputable def costMean (P : Par) (x : ℝ) : ℝ := min x P.c0
noncomputable def costSec (P : Par) (x : ℝ) : ℝ := min x P.c0 ^ 2
noncomputable def costCount (P : Par) (x : ℝ) : ℝ := if (P.c0 : ℝ) < x then 1 else 0
noncomputable def costOver (P : Par) (x : ℝ) : ℝ := max 0 (x - P.c0)
noncomputable def costMgf (P : Par) (x : ℝ) : ℝ := Real.exp (P.a * min x P.c0) - 1
noncomputable def costScarf (P : Par) (x : ℝ) : ℝ :=
  if (P.c0 : ℝ) < x then scarf (P.θ - x) P.m P.vv else 0

/-! ### Soundness of the run checks -/

theorem feeScale_pos : (0 : ℝ) < feeScale := by norm_num [feeScale]

theorem div_fee_mono {x y fee : ℝ} (hxy : x ≤ y) (hfee : 0 ≤ fee) :
    x * fee / feeScale ≤ y * fee / feeScale := by
  have := feeScale_pos
  gcongr

theorem meanOk_sound (P : Par) (hc : 0 ≤ (P.c0 : ℝ)) (L U : ℚ) (fee : ℕ) (h : meanOk P L U fee = true)
    (x : ℝ) (hx : 0 ≤ x) (hL : (L : ℝ) ≤ x) : costMean P x ≤ x * fee / feeScale := by
  have hS := feeScale_pos
  unfold meanOk at h
  unfold costMean
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨h1, h2⟩
  · have h' : (feeScale : ℝ) ≤ fee := by exact_mod_cast h
    calc min x P.c0 ≤ x := min_le_left _ _
      _ ≤ x * fee / feeScale := by rw [le_div_iff₀ hS]; nlinarith
  · have h1' : (P.c0 : ℝ) ≤ L := by exact_mod_cast h1
    have h2' : (feeScale : ℝ) * P.c0 ≤ fee * L := by exact_mod_cast h2
    calc min x P.c0 ≤ P.c0 := min_le_right _ _
      _ ≤ L * fee / feeScale := by rw [le_div_iff₀ hS]; linarith
      _ ≤ x * fee / feeScale := div_fee_mono hL (Nat.cast_nonneg _)

theorem secOk_sound (P : Par) (hc : 0 ≤ (P.c0 : ℝ)) (L U : ℚ) (fee : ℕ) (h : secOk P L U fee = true)
    (x : ℝ) (hx : 0 ≤ x) (hL : (L : ℝ) ≤ x) (hU : x ≤ (U : ℝ)) : costSec P x ≤ x * fee / feeScale := by
  have hS := feeScale_pos
  unfold secOk at h
  unfold costSec
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  have hmin0 : 0 ≤ min x (P.c0 : ℝ) := le_min hx hc
  rcases h with (h | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · have h' : (feeScale : ℝ) * P.c0 ≤ fee := by exact_mod_cast h
    have hsq : min x (P.c0 : ℝ) ^ 2 ≤ x * P.c0 := by
      rcases le_total x P.c0 with hxc | hxc
      · rw [min_eq_left hxc]; nlinarith
      · rw [min_eq_right hxc]; nlinarith
    calc min x (P.c0 : ℝ) ^ 2 ≤ x * P.c0 := hsq
      _ ≤ x * fee / feeScale := by rw [le_div_iff₀ hS]; nlinarith
  · have h1' : (U : ℝ) ≤ P.c0 := by exact_mod_cast h1
    have h2' : (feeScale : ℝ) * U ≤ fee := by exact_mod_cast h2
    rw [min_eq_left (hU.trans h1')]
    rw [le_div_iff₀ hS]
    have h3 : x * (feeScale : ℝ) ≤ fee := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h3 hx]
  · have h1' : (P.c0 : ℝ) ≤ L := by exact_mod_cast h1
    have h2' : (feeScale : ℝ) * (P.c0 * P.c0) ≤ fee * L := by exact_mod_cast h2
    rw [min_eq_right (h1'.trans hL)]
    calc (P.c0 : ℝ) ^ 2 ≤ L * fee / feeScale := by rw [le_div_iff₀ hS]; nlinarith
      _ ≤ x * fee / feeScale := div_fee_mono hL (Nat.cast_nonneg _)

theorem countOk_sound (P : Par) (L U : ℚ) (fee : ℕ) (h : countOk P L U fee = true)
    (x : ℝ) (hx : 0 ≤ x) (hL : (L : ℝ) ≤ x) (hU : x ≤ (U : ℝ)) : costCount P x ≤ x * fee / feeScale := by
  have hS := feeScale_pos
  unfold countOk at h
  unfold costCount
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  have hpos : 0 ≤ x * fee / feeScale := by positivity
  split_ifs with hcx
  · rcases h with (h | h) | h
    · have h' : (U : ℝ) ≤ P.c0 := by exact_mod_cast h
      linarith
    · have h' : (feeScale : ℝ) ≤ fee * P.c0 := by exact_mod_cast h
      rw [le_div_iff₀ hS]
      nlinarith [mul_le_mul_of_nonneg_left hcx.le (Nat.cast_nonneg fee : (0 : ℝ) ≤ fee)]
    · have h' : (feeScale : ℝ) ≤ fee * L := by exact_mod_cast h
      rw [le_div_iff₀ hS]
      nlinarith [mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg fee : (0 : ℝ) ≤ fee)]
  · exact hpos

theorem overOk_sound (P : Par) (hc : 0 ≤ (P.c0 : ℝ)) (L U : ℚ) (fee : ℕ) (h : overOk P L U fee = true)
    (x : ℝ) (hx : 0 ≤ x) (hU : x ≤ (U : ℝ)) : costOver P x ≤ x * fee / feeScale := by
  have hS := feeScale_pos
  unfold overOk at h
  unfold costOver
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  have hpos : 0 ≤ x * fee / feeScale := by positivity
  apply max_le hpos
  rcases h with (h | h) | ⟨h0, h⟩
  · have h' : (U : ℝ) ≤ P.c0 := by exact_mod_cast h
    linarith
  · have h' : (feeScale : ℝ) ≤ fee := by exact_mod_cast h
    rw [le_div_iff₀ hS]
    nlinarith
  · have h0' : (0 : ℝ) < U := by exact_mod_cast h0
    have h' : (feeScale : ℝ) * (U - P.c0) ≤ fee * U := by exact_mod_cast h
    rw [le_div_iff₀ hS]
    -- (x - c0) * U ≤ x * (U - c0) and x * (U - c0) * S ≤ x * fee * U
    have h1 : (x - P.c0) * U ≤ x * (U - P.c0) := by nlinarith
    have h2 : x * ((feeScale : ℝ) * (U - P.c0)) ≤ x * (fee * U) := mul_le_mul_of_nonneg_left h' hx
    nlinarith

theorem expm1Up_sound (a x : ℚ) (hax : 0 ≤ a * x)
    (h8 : expArg a x ≤ 8 * ClaudeWCT.Numerics.SharedFees.scale) :
    Real.exp ((a : ℝ) * x) - 1 ≤ (expm1Up a x : ℝ) := by
  have hS : (0 : ℝ) < ClaudeWCT.Numerics.SharedFees.scale := by
    exact_mod_cast ClaudeWCT.Numerics.SharedFees.scale_pos
  set X := expArg a x with hX
  have hceil : (a : ℝ) * x * ClaudeWCT.Numerics.SharedFees.scale ≤ X := by
    have h1 : a * x * (ClaudeWCT.Numerics.SharedFees.scale : ℚ) ≤ ⌈a * x * (ClaudeWCT.Numerics.SharedFees.scale : ℚ)⌉ :=
      Int.le_ceil _
    have h0 : 0 ≤ ⌈a * x * (ClaudeWCT.Numerics.SharedFees.scale : ℚ)⌉ :=
      Int.ceil_nonneg (by positivity)
    have h2 : ((X : ℤ) : ℚ) = ⌈a * x * (ClaudeWCT.Numerics.SharedFees.scale : ℚ)⌉ := by
      rw [hX, expArg, Int.toNat_of_nonneg h0]
    have h3 := h1.trans_eq h2.symm
    have h4 : a * x * (ClaudeWCT.Numerics.SharedFees.scale : ℚ) ≤ (X : ℚ) := by exact_mod_cast h3
    exact_mod_cast h4
  have he := ClaudeWCT.Numerics.SharedFees.expUpper_sound X h8
  have hmono : Real.exp ((a : ℝ) * x) ≤ Real.exp ((X : ℝ) / ClaudeWCT.Numerics.SharedFees.scale) := by
    apply Real.exp_le_exp.mpr
    rw [le_div_iff₀ hS]
    exact hceil
  have hcast : (expm1Up a x : ℝ) =
      ((ClaudeWCT.Numerics.SharedFees.expUpper X : ℝ) - ClaudeWCT.Numerics.SharedFees.scale) /
        ClaudeWCT.Numerics.SharedFees.scale := by
    simp only [expm1Up, ← hX]
    push_cast
    ring
  rw [hcast, sub_div, div_self hS.ne']
  linarith

theorem expm1Up_nonneg (a x : ℚ) (hax : 0 ≤ a * x)
    (h8 : expArg a x ≤ 8 * ClaudeWCT.Numerics.SharedFees.scale) : 0 ≤ (expm1Up a x : ℝ) := by
  have h := expm1Up_sound a x hax h8
  have : 0 ≤ Real.exp ((a : ℝ) * x) - 1 := by
    have : (0 : ℝ) ≤ (a : ℝ) * x := by exact_mod_cast hax
    linarith [Real.add_one_le_exp ((a : ℝ) * x)]
  linarith

/-- The clipped exponential cost per unit price, below and above the clip. -/
theorem mgf_ratio (P : Par) (hc : 0 < (P.c0 : ℝ)) (ha : 0 ≤ (P.a : ℝ))
    (h8c : expArg P.a P.c0 ≤ 8 * ClaudeWCT.Numerics.SharedFees.scale) (x : ℝ) (hx : 0 ≤ x) :
    costMgf P x ≤ x * (expm1Up P.a P.c0 : ℝ) / P.c0 := by
  have hac : 0 ≤ P.a * P.c0 := by
    have : (0 : ℝ) ≤ (P.a : ℝ) * P.c0 := mul_nonneg ha hc.le
    exact_mod_cast this
  have hE := expm1Up_sound P.a P.c0 hac h8c
  have hE0 := expm1Up_nonneg P.a P.c0 hac h8c
  unfold costMgf
  rcases le_total x P.c0 with hxc | hxc
  · rw [min_eq_left hxc]
    have hs := ClaudeWCT.Numerics.SharedPathWinsor.exp_secant (P.a : ℝ) x P.c0 hx hxc hc
    calc Real.exp (P.a * x) - 1 ≤ (x / P.c0) * (Real.exp (P.a * P.c0) - 1) := hs
      _ ≤ (x / P.c0) * (expm1Up P.a P.c0 : ℝ) := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = x * (expm1Up P.a P.c0 : ℝ) / P.c0 := by ring
  · rw [min_eq_right hxc]
    calc Real.exp (P.a * P.c0) - 1 ≤ (expm1Up P.a P.c0 : ℝ) := hE
      _ ≤ x * (expm1Up P.a P.c0 : ℝ) / P.c0 := by
        rw [le_div_iff₀ hc]; nlinarith

theorem mgfOk_sound (P : Par) (hc : 0 < (P.c0 : ℝ)) (ha : 0 ≤ (P.a : ℝ))
    (h8c : expArg P.a P.c0 ≤ 8 * ClaudeWCT.Numerics.SharedFees.scale)
    (L U : ℚ) (fee : ℕ) (h : mgfOk P L U fee = true)
    (x : ℝ) (hx : 0 ≤ x) (hL : (L : ℝ) ≤ x) (hU : x ≤ (U : ℝ)) : costMgf P x ≤ x * fee / feeScale := by
  have hS := feeScale_pos
  have hac : 0 ≤ P.a * P.c0 := by
    have : (0 : ℝ) ≤ (P.a : ℝ) * P.c0 := mul_nonneg ha hc.le
    exact_mod_cast this
  have hE := expm1Up_sound P.a P.c0 hac h8c
  have hE0 := expm1Up_nonneg P.a P.c0 hac h8c
  unfold mgfOk at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with (h | ⟨⟨⟨h1, h0⟩, h8⟩, h2⟩) | ⟨h1, h2⟩
  · have h' : (feeScale : ℝ) * (expm1Up P.a P.c0 : ℝ) ≤ fee * P.c0 := by exact_mod_cast h
    refine (mgf_ratio P hc ha h8c x hx).trans ?_
    rw [div_le_div_iff₀ hc hS]
    nlinarith [mul_le_mul_of_nonneg_left h' hx]
  · have h1' : (U : ℝ) ≤ P.c0 := by exact_mod_cast h1
    have h0' : (0 : ℝ) < U := by exact_mod_cast h0
    have h2' : (feeScale : ℝ) * (expm1Up P.a U : ℝ) ≤ fee * U := by exact_mod_cast h2
    have haU : 0 ≤ P.a * U := by
      have : (0 : ℝ) ≤ (P.a : ℝ) * U := mul_nonneg ha h0'.le
      exact_mod_cast this
    have hEU := expm1Up_sound P.a U haU h8
    unfold costMgf
    rw [min_eq_left (hU.trans h1')]
    have hs := ClaudeWCT.Numerics.SharedPathWinsor.exp_secant (P.a : ℝ) x U hx hU h0'
    calc Real.exp (P.a * x) - 1 ≤ (x / U) * (Real.exp (P.a * U) - 1) := hs
      _ ≤ (x / U) * (expm1Up P.a U : ℝ) := mul_le_mul_of_nonneg_left hEU (by positivity)
      _ ≤ x * fee / feeScale := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ h0' hS]
        nlinarith [mul_le_mul_of_nonneg_left h2' hx]
  · have h1' : (P.c0 : ℝ) ≤ L := by exact_mod_cast h1
    have h2' : (feeScale : ℝ) * (expm1Up P.a P.c0 : ℝ) ≤ fee * L := by exact_mod_cast h2
    unfold costMgf
    rw [min_eq_right (h1'.trans hL)]
    calc Real.exp (P.a * P.c0) - 1 ≤ (expm1Up P.a P.c0 : ℝ) := hE
      _ ≤ L * fee / feeScale := by rw [le_div_iff₀ hS]; linarith
      _ ≤ x * fee / feeScale := div_fee_mono hL (Nat.cast_nonneg _)

/-! ### Scarf payments -/

theorem sqrt_convex (u1 u2 v t : ℝ) (hv : 0 ≤ v) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.sqrt (((1 - t) * u1 + t * u2) ^ 2 + v) ≤
      (1 - t) * Real.sqrt (u1 ^ 2 + v) + t * Real.sqrt (u2 ^ 2 + v) := by
  set A1 := Real.sqrt (u1 ^ 2 + v)
  set A2 := Real.sqrt (u2 ^ 2 + v)
  have hA1 : 0 ≤ A1 := Real.sqrt_nonneg _
  have hA2 : 0 ≤ A2 := Real.sqrt_nonneg _
  have hA1s : A1 ^ 2 = u1 ^ 2 + v := Real.sq_sqrt (by positivity)
  have hA2s : A2 ^ 2 = u2 ^ 2 + v := Real.sq_sqrt (by positivity)
  have hprod : u1 * u2 + v ≤ A1 * A2 := by
    have hsq : (u1 * u2 + v) ^ 2 ≤ (A1 * A2) ^ 2 := by
      rw [mul_pow, hA1s, hA2s]
      nlinarith [sq_nonneg (u1 - u2), mul_nonneg hv (sq_nonneg (u1 - u2))]
    by_contra hcon
    push Not at hcon
    have h0 : 0 ≤ A1 * A2 := mul_nonneg hA1 hA2
    nlinarith
  have hR : 0 ≤ (1 - t) * A1 + t * A2 := by
    have : 0 ≤ 1 - t := by linarith
    positivity
  rw [Real.sqrt_le_left hR]
  have h1t : 0 ≤ (1 - t) * t := mul_nonneg (by linarith) ht0
  nlinarith [mul_le_mul_of_nonneg_left hprod h1t]

theorem scarf_affine (θ m vv x1 x2 t : ℝ) (hvv : 0 ≤ vv) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    scarf (θ - ((1 - t) * x1 + t * x2)) m vv ≤ (1 - t) * scarf (θ - x1) m vv + t * scarf (θ - x2) m vv := by
  unfold scarf
  have hw : m - (θ - ((1 - t) * x1 + t * x2)) = (1 - t) * (m - (θ - x1)) + t * (m - (θ - x2)) := by ring
  rw [hw]
  have := sqrt_convex (m - (θ - x1)) (m - (θ - x2)) vv t hvv ht0 ht1
  linarith

theorem scarfPointOk_sound (P : Par) (x0 : ℚ) (fee : ℕ) (h : scarfPointOk P x0 fee = true) :
    scarf (P.θ - x0) P.m P.vv ≤ x0 * fee / feeScale := by
  unfold scarfPointOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨ht, hsq⟩ := h
  set w : ℚ := P.m - P.θ + x0
  set t : ℚ := 2 * x0 * fee / feeScale - w
  have ht' : (0 : ℝ) ≤ t := by exact_mod_cast ht
  have hsq' : (w : ℝ) * w + P.vv ≤ (t : ℝ) * t := by exact_mod_cast hsq
  have hsqrt : Real.sqrt ((w : ℝ) ^ 2 + P.vv) ≤ t := by
    rw [Real.sqrt_le_left ht']
    nlinarith
  have hwc : ((P.m : ℝ) - (P.θ - x0)) = w := by simp only [w]; push_cast; ring
  have htc : (t : ℝ) = 2 * x0 * fee / feeScale - w := by simp only [t, feeScale]; push_cast; ring
  unfold scarf
  rw [hwc]
  have := feeScale_pos
  rw [htc] at hsqrt
  have : (2 : ℝ) * x0 * fee / feeScale = 2 * (x0 * fee / feeScale) := by ring
  linarith

theorem scarf_interp (θ m vv F x1 x2 x : ℝ) (hvv : 0 ≤ vv)
    (h1 : scarf (θ - x1) m vv ≤ x1 * F) (h2 : scarf (θ - x2) m vv ≤ x2 * F)
    (hx1 : x1 ≤ x) (hx2 : x ≤ x2) : scarf (θ - x) m vv ≤ x * F := by
  rcases eq_or_lt_of_le (hx1.trans hx2) with heq | hlt
  · have : x = x1 := le_antisymm (heq ▸ hx2) hx1
    rw [this]; exact h1
  · set t := (x - x1) / (x2 - x1) with ht
    have hd : 0 < x2 - x1 := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
    have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith)
    have hx : x = (1 - t) * x1 + t * x2 := by
      rw [ht]; field_simp; ring
    rw [hx]
    have ha := scarf_affine θ m vv x1 x2 t hvv ht0 ht1
    have hb := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 - t by linarith)
    have hc := mul_le_mul_of_nonneg_left h2 ht0
    nlinarith

theorem scarfOk_sound (P : Par) (hvv : 0 ≤ (P.vv : ℝ)) (L U : ℚ) (fee : ℕ) (h : scarfOk P L U fee = true)
    (x : ℝ) (hx : 0 ≤ x) (hL : (L : ℝ) ≤ x) (hU : x ≤ (U : ℝ)) : costScarf P x ≤ x * fee / feeScale := by
  have hS := feeScale_pos
  have hpos : 0 ≤ x * fee / feeScale := by positivity
  unfold costScarf
  split_ifs with hcx
  · unfold scarfOk at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨⟨h1, h2⟩, h3⟩
    · have h' : (U : ℝ) ≤ P.c0 := by exact_mod_cast h
      linarith
    · have p1 := scarfPointOk_sound P (max L P.c0) fee h1
      have p2 := scarfPointOk_sound P U fee h2
      have hcast : ((max L P.c0 : ℚ) : ℝ) = max (L : ℝ) (P.c0 : ℝ) := Rat.cast_max L P.c0
      rw [hcast] at p1
      have hF : ∀ y : ℝ, y * fee / feeScale = y * ((fee : ℝ) / feeScale) := fun y => by ring
      rw [hF] at p1 p2 ⊢
      exact scarf_interp P.θ P.m P.vv _ _ _ x hvv p1 p2 (max_le hL hcx.le) hU
  · exact hpos

/-! ### Global (unbinned) fees -/


theorem sec_global (P : Par) (hc : 0 ≤ (P.c0 : ℝ)) (G : ℕ) (hG : (feeScale : ℚ) * P.c0 ≤ G)
    (x : ℝ) (hx : 0 ≤ x) : costSec P x ≤ x * G / feeScale := by
  have hS := feeScale_pos
  have h' : (feeScale : ℝ) * P.c0 ≤ G := by exact_mod_cast hG
  have hsq : min x (P.c0 : ℝ) ^ 2 ≤ x * P.c0 := by
    rcases le_total x P.c0 with hxc | hxc
    · rw [min_eq_left hxc]; nlinarith
    · rw [min_eq_right hxc]; nlinarith
  unfold costSec
  calc min x (P.c0 : ℝ) ^ 2 ≤ x * P.c0 := hsq
    _ ≤ x * G / feeScale := by rw [le_div_iff₀ hS]; nlinarith

theorem count_global (P : Par) (hc : 0 < (P.c0 : ℝ)) (G : ℕ) (hG : (feeScale : ℚ) ≤ G * P.c0)
    (x : ℝ) (hx : 0 ≤ x) : costCount P x ≤ x * G / feeScale := by
  have hS := feeScale_pos
  have h' : (feeScale : ℝ) ≤ G * P.c0 := by exact_mod_cast hG
  unfold costCount
  split_ifs with hcx
  · rw [le_div_iff₀ hS]
    nlinarith [mul_le_mul_of_nonneg_left hcx.le (Nat.cast_nonneg G : (0 : ℝ) ≤ G)]
  · positivity

theorem over_global (P : Par) (hc : 0 ≤ (P.c0 : ℝ)) (G : ℕ) (hG : (feeScale : ℚ) ≤ G)
    (x : ℝ) (hx : 0 ≤ x) : costOver P x ≤ x * G / feeScale := by
  have hS := feeScale_pos
  have h' : (feeScale : ℝ) ≤ G := by exact_mod_cast hG
  unfold costOver
  apply max_le (by positivity)
  rw [le_div_iff₀ hS]
  nlinarith

theorem mgf_global (P : Par) (hc : 0 < (P.c0 : ℝ)) (ha : 0 ≤ (P.a : ℝ))
    (h8c : expArg P.a P.c0 ≤ 8 * ClaudeWCT.Numerics.SharedFees.scale) (G : ℕ)
    (hG : (feeScale : ℚ) * expm1Up P.a P.c0 ≤ G * P.c0)
    (x : ℝ) (hx : 0 ≤ x) : costMgf P x ≤ x * G / feeScale := by
  have hS := feeScale_pos
  have h' : (feeScale : ℝ) * (expm1Up P.a P.c0 : ℝ) ≤ G * P.c0 := by exact_mod_cast hG
  refine (mgf_ratio P hc ha h8c x hx).trans ?_
  rw [div_le_div_iff₀ hc hS]
  nlinarith [mul_le_mul_of_nonneg_left h' hx]

theorem scarf_global (P : Par) (hc : 0 < (P.c0 : ℝ)) (hmθ : (P.m : ℝ) ≤ P.θ) (hsv : 0 ≤ (P.sv : ℝ))
    (hsv2 : (P.vv : ℝ) ≤ (P.sv : ℝ) ^ 2) (hvv : 0 ≤ (P.vv : ℝ)) (G : ℕ)
    (hG : (feeScale : ℚ) * (1 + P.sv / (2 * P.c0)) ≤ G)
    (x : ℝ) (hx : 0 ≤ x) : costScarf P x ≤ x * G / feeScale := by
  have hS := feeScale_pos
  have h' : (feeScale : ℝ) * (1 + P.sv / (2 * P.c0)) ≤ G := by exact_mod_cast hG
  unfold costScarf
  split_ifs with hcx
  · unfold scarf
    set w : ℝ := P.m - (P.θ - x)
    have hw : w ≤ x := by simp only [w]; linarith
    have hsq : Real.sqrt (w ^ 2 + P.vv) ≤ |w| + P.sv := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [sq_abs w, abs_nonneg w]
    have hb : (w + Real.sqrt (w ^ 2 + P.vv)) / 2 ≤ x + P.sv / 2 := by
      rcases le_total 0 w with h0 | h0
      · rw [abs_of_nonneg h0] at hsq; linarith
      · rw [abs_of_nonpos h0] at hsq; linarith
    have hc2 : x + (P.sv : ℝ) / 2 ≤ x * (1 + P.sv / (2 * P.c0)) := by
      have : (P.sv : ℝ) / 2 ≤ x * (P.sv / (2 * P.c0)) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    calc (w + Real.sqrt (w ^ 2 + P.vv)) / 2 ≤ x * (1 + P.sv / (2 * P.c0)) := hb.trans hc2
      _ ≤ x * G / feeScale := by
        rw [le_div_iff₀ hS]
        nlinarith [mul_le_mul_of_nonneg_left h' hx]
  · positivity

/-! ### The six kinds, uniformly -/

/-- Run check of kind `k` (0 mean, 1 second moment, 2 count, 3 over, 4 clipped mgf, 5 Scarf). -/
def okOf : ℕ → Par → ℚ → ℚ → ℕ → Bool
  | 0 => meanOk | 1 => secOk | 2 => countOk | 3 => overOk | 4 => mgfOk | _ => scarfOk

noncomputable def costOf : ℕ → Par → ℝ → ℝ
  | 0 => costMean | 1 => costSec | 2 => costCount | 3 => costOver | 4 => costMgf | _ => costScarf

/-- Global (all prices) fee check of kind `k`. -/
def globOk (k : ℕ) (P : Par) (G : ℕ) : Bool :=
  match k with
  | 0 => decide ((feeScale : ℚ) ≤ G)
  | 1 => decide ((feeScale : ℚ) * P.c0 ≤ G)
  | 2 => decide ((feeScale : ℚ) ≤ G * P.c0)
  | 3 => decide ((feeScale : ℚ) ≤ G)
  | 4 => decide ((feeScale : ℚ) * expm1Up P.a P.c0 ≤ G * P.c0)
  | _ => decide ((feeScale : ℚ) * (1 + P.sv / (2 * P.c0)) ≤ G)

/-- Admissible route-C parameters. -/
def parOk (P : Par) : Bool :=
  decide (0 < P.c0) && decide (0 ≤ P.a) &&
    decide (expArg P.a P.c0 ≤ 8 * ClaudeWCT.Numerics.SharedFees.scale) &&
    decide (0 ≤ P.vv) && decide (0 ≤ P.sv) && decide (P.vv ≤ P.sv ^ 2) && decide (P.m ≤ P.θ) &&
    decide (0 ≤ P.m)

structure ParFacts (P : Par) : Prop where
  c0 : 0 < (P.c0 : ℝ)
  a : 0 ≤ (P.a : ℝ)
  h8 : expArg P.a P.c0 ≤ 8 * ClaudeWCT.Numerics.SharedFees.scale
  vv : 0 ≤ (P.vv : ℝ)
  sv : 0 ≤ (P.sv : ℝ)
  svsq : (P.vv : ℝ) ≤ (P.sv : ℝ) ^ 2
  mθ : (P.m : ℝ) ≤ P.θ
  m : 0 ≤ (P.m : ℝ)

theorem parFacts_of_ok (P : Par) (h : parOk P = true) : ParFacts P := by
  unfold parOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, h3, by exact_mod_cast h4, by exact_mod_cast h5,
    by exact_mod_cast h6, by exact_mod_cast h7, by exact_mod_cast h8⟩

theorem ok_sound (k : ℕ) (P : Par) (hP : ParFacts P) (L U : ℚ) (fee : ℕ) (h : okOf k P L U fee = true)
    (x : ℝ) (hx : 0 ≤ x) (hL : (L : ℝ) ≤ x) (hU : x ≤ (U : ℝ)) : costOf k P x ≤ x * fee / feeScale := by
  match k, h with
  | 0, h => exact meanOk_sound P hP.c0.le L U fee h x hx hL
  | 1, h => exact secOk_sound P hP.c0.le L U fee h x hx hL hU
  | 2, h => exact countOk_sound P L U fee h x hx hL hU
  | 3, h => exact overOk_sound P hP.c0.le L U fee h x hx hU
  | 4, h => exact mgfOk_sound P hP.c0 hP.a hP.h8 L U fee h x hx hL hU
  | k + 5, h => exact scarfOk_sound P hP.vv L U fee h x hx hL hU

theorem glob_sound (k : ℕ) (P : Par) (hP : ParFacts P) (G : ℕ) (h : globOk k P G = true)
    (x : ℝ) (hx : 0 ≤ x) : costOf k P x ≤ x * G / feeScale := by
  have hS := feeScale_pos
  match k, h with
  | 0, h =>
    have h' : (feeScale : ℝ) ≤ G := by
      have := of_decide_eq_true h; exact_mod_cast this
    show min x (P.c0 : ℝ) ≤ _
    rw [le_div_iff₀ hS]
    nlinarith [min_le_left x (P.c0 : ℝ), min_le_right x (P.c0 : ℝ), le_min hx hP.c0.le]
  | 1, h => exact sec_global P hP.c0.le G (of_decide_eq_true h) x hx
  | 2, h => exact count_global P hP.c0 G (of_decide_eq_true h) x hx
  | 3, h => exact over_global P hP.c0.le G (of_decide_eq_true h) x hx
  | 4, h => exact mgf_global P hP.c0 hP.a hP.h8 G (of_decide_eq_true h) x hx
  | k + 5, h => exact scarf_global P hP.c0 hP.mθ hP.sv hP.svsq hP.vv G (of_decide_eq_true h) x hx

theorem costOf_nonneg (k : ℕ) (P : Par) (hP : ParFacts P) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ costOf k P x := by
  match k with
  | 0 => exact le_min hx hP.c0.le
  | 1 => exact sq_nonneg _
  | 2 => show 0 ≤ (if (P.c0 : ℝ) < x then (1 : ℝ) else 0); split_ifs <;> norm_num
  | 3 => exact le_max_left _ _
  | 4 =>
    show 0 ≤ Real.exp (P.a * min x P.c0) - 1
    have : 0 ≤ (P.a : ℝ) * min x P.c0 := mul_nonneg hP.a (le_min hx hP.c0.le)
    linarith [Real.add_one_le_exp ((P.a : ℝ) * min x P.c0)]
  | k + 5 =>
    show 0 ≤ (if (P.c0 : ℝ) < x then scarf (P.θ - x) P.m P.vv else 0)
    split_ifs
    · unfold scarf
      have h1 : |(P.m : ℝ) - (P.θ - x)| ≤ Real.sqrt (((P.m : ℝ) - (P.θ - x)) ^ 2 + P.vv) :=
        Real.abs_le_sqrt (by linarith [hP.vv])
      have h2 := neg_abs_le ((P.m : ℝ) - (P.θ - x))
      linarith
    · exact le_rfl

theorem scarf_shift (θ m vv z : ℝ) : scarf (θ - z) m vv = scarf θ (m + z) vv := by
  unfold scarf; ring_nf

/-- Every route-C cost is monotone in the bucket price (needed for the cap-777 thinning). -/
theorem costOf_mono (k : ℕ) (P : Par) (hP : ParFacts P) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    costOf k P x ≤ costOf k P y := by
  match k with
  | 0 => exact min_le_min hxy le_rfl
  | 1 => exact pow_le_pow_left₀ (le_min hx hP.c0.le) (min_le_min hxy le_rfl) 2
  | 2 =>
    show (if (P.c0 : ℝ) < x then (1 : ℝ) else 0) ≤ (if (P.c0 : ℝ) < y then (1 : ℝ) else 0)
    by_cases h : (P.c0 : ℝ) < x
    · rw [if_pos h, if_pos (lt_of_lt_of_le h hxy)]
    · rw [if_neg h]; split_ifs <;> norm_num
  | 3 => exact max_le_max le_rfl (sub_le_sub_right hxy _)
  | 4 =>
    show Real.exp (P.a * min x P.c0) - 1 ≤ Real.exp (P.a * min y P.c0) - 1
    exact sub_le_sub_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (min_le_min hxy le_rfl) hP.a)) 1
  | k + 5 =>
    show (if (P.c0 : ℝ) < x then scarf (P.θ - x) P.m P.vv else 0) ≤
      (if (P.c0 : ℝ) < y then scarf (P.θ - y) P.m P.vv else 0)
    by_cases h : (P.c0 : ℝ) < x
    · rw [if_pos h, if_pos (lt_of_lt_of_le h hxy), scarf_shift, scarf_shift]
      exact RouteC.scarf_mono (by linarith) le_rfl hP.vv
    · rw [if_neg h]
      exact costOf_nonneg (k + 5) P hP y (hx.trans hxy)

/-! ### Bins at a general gate -/

theorem upperQ_real (g j : ℕ) : (upperQ g j : ℝ) = (g : ℝ) / 2 ^ 66 * ((101 : ℝ) / 100) ^ j := by
  unfold upperQ
  rw [Rat.mkRat_eq_div]
  push_cast
  rw [div_pow]
  ring

theorem lowerQ_real (g j : ℕ) :
    (lowerQ g j : ℝ) = (g : ℝ) / 2 ^ 66 * (((100 : ℝ) / 101) ^ 13 * ((101 : ℝ) / 100) ^ j) := by
  unfold lowerQ
  rw [Rat.mkRat_eq_div]
  push_cast
  rw [div_pow, div_pow]
  ring

theorem upperQ_mono (g : ℕ) {i j : ℕ} (hij : i ≤ j) : (upperQ g i : ℝ) ≤ upperQ g j := by
  rw [upperQ_real, upperQ_real]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 101 / 100) hij

theorem lowerQ_mono (g : ℕ) {i j : ℕ} (hij : i ≤ j) : (lowerQ g i : ℝ) ≤ lowerQ g j := by
  rw [lowerQ_real, lowerQ_real]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 101 / 100) hij

theorem bin_bounds (g : ℕ) {bin : ℕ} {cov : ℝ}
    (h : ClaudeWCT.Numerics.SharedPathList.RoundedInterval 13 bin cov) :
    (lowerQ g bin : ℝ) ≤ (g : ℝ) / 2 ^ 66 * cov ∧ (g : ℝ) / 2 ^ 66 * cov ≤ upperQ g bin := by
  rw [lowerQ_real, upperQ_real]
  have hg : (0 : ℝ) ≤ (g : ℝ) / 2 ^ 66 := by positivity
  exact ⟨mul_le_mul_of_nonneg_left h.lower hg, mul_le_mul_of_nonneg_left h.upper hg⟩

/-! ### Run tables -/

/-- The bins of each run, with the run fee. -/
def runEntries (runs : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ) :=
  runs.flatMap fun e => (List.range' e.1 (e.2.1 - e.1 + 1)).map fun i => (i, e.2.2)

/-- The fee of bin `j` in a run table. -/
def runFee (runs : List (ℕ × ℕ × ℕ)) (j : ℕ) : ℕ := ((runEntries runs)[j]?.map Prod.snd).getD 0

/-- The runs tile `[s, n)` consecutively, each with `start ≤ end` (a linear check that replaces
comparing the expanded 7210-entry list with `List.range 7210` in the kernel). -/
def runsContig : List (ℕ × ℕ × ℕ) → ℕ → ℕ → Bool
  | [], s, n => s == n
  | e :: rest, s, n => e.1 == s && decide (e.1 ≤ e.2.1) && runsContig rest (e.2.1 + 1) n

theorem runsContig_le : ∀ (runs : List (ℕ × ℕ × ℕ)) (s n : ℕ), runsContig runs s n = true → s ≤ n
  | [], s, n, h => by simp only [runsContig, beq_iff_eq] at h; omega
  | e :: rest, s, n, h => by
      simp only [runsContig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      have := runsContig_le rest (e.2.1 + 1) n h.2
      omega

theorem runsContig_entries : ∀ (runs : List (ℕ × ℕ × ℕ)) (s n : ℕ), runsContig runs s n = true →
    (runEntries runs).map Prod.fst = List.range' s (n - s)
  | [], s, n, h => by
      simp only [runsContig, beq_iff_eq] at h
      subst h
      simp [runEntries]
  | e :: rest, s, n, h => by
      simp only [runsContig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have ih := runsContig_entries rest (e.2.1 + 1) n h3
      have hle := runsContig_le rest (e.2.1 + 1) n h3
      have hcons : runEntries (e :: rest) =
          (List.range' e.1 (e.2.1 - e.1 + 1)).map (fun i => (i, e.2.2)) ++ runEntries rest := by
        simp [runEntries, List.flatMap_cons]
      rw [hcons, List.map_append, ih, List.map_map]
      have hid : (Prod.fst ∘ fun i => (i, e.2.2)) = (id : ℕ → ℕ) := rfl
      rw [hid, List.map_id, h1]
      have hs : e.2.1 + 1 = s + (e.2.1 - s + 1) := by omega
      rw [hs, List.range'_append_1]
      congr 1
      omega

theorem entries_of_contig (runs : List (ℕ × ℕ × ℕ)) (h : runsContig runs 0 7210 = true) :
    (runEntries runs).map Prod.fst = List.range 7210 := by
  rw [runsContig_entries runs 0 7210 h, List.range_eq_range']

theorem runFee_lookup (runs : List (ℕ × ℕ × ℕ)) (n : ℕ) (hord : ∀ e ∈ runs, e.1 ≤ e.2.1)
    (hidx : (runEntries runs).map Prod.fst = List.range n) (j : ℕ) (hj : j < n) :
    ∃ e ∈ runs, e.1 ≤ j ∧ j ≤ e.2.1 ∧ runFee runs j = e.2.2 := by
  have hlen : (runEntries runs).length = n := by
    have := congrArg List.length hidx
    simpa using this
  have hjl : j < (runEntries runs).length := by omega
  set p := (runEntries runs)[j] with hp
  have hfst : p.1 = j := by
    have h1 : ((runEntries runs).map Prod.fst)[j]'(by simpa using hjl) = p.1 := by
      simp [hp]
    rw [← h1]
    simp [hidx]
  have hmem : p ∈ runEntries runs := List.getElem_mem hjl
  unfold runEntries at hmem
  rw [List.mem_flatMap] at hmem
  obtain ⟨e, he, hm⟩ := hmem
  rw [List.mem_map] at hm
  obtain ⟨i, hi, hpi⟩ := hm
  rw [List.mem_range'] at hi
  obtain ⟨k, hk, hik⟩ := hi
  have hij : i = j := by rw [← hfst, ← hpi]
  have hoe := hord e he
  refine ⟨e, he, by omega, by omega, ?_⟩
  unfold runFee
  rw [List.getElem?_eq_getElem hjl, ← hp, ← hpi]
  rfl

end ClaudeWCT.Numerics.RouteCFees
end
-- ==== merged from ClaudeWCT_Numerics_RouteCData ====
section

/-! Route C data at the installed gate (generated by rc938/lean-notes/gen/rcgen938.py; RC938, cap-777 thinned envelope). -/

namespace ClaudeWCT.Numerics.RouteCData
open ClaudeWCT.Numerics.RouteCFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def rcPar : Par := ⟨791, (9 / 16 : ℚ), (101 / 10 : ℚ), (6387083 / 3200000 : ℚ), (45619 / 50000 : ℚ), (75397 / 10000000 : ℚ), (869 / 10000 : ℚ)⟩

def runs0 : List (ℕ × ℕ × ℕ) := [(0, 3882, 18446744073709551616), (3883, 3883, 18286430543930636023), (3884, 3884, 18105376776168946558), (3885, 3885, 17926115619969254018), (3886, 3886, 17748629326702231701), (3887, 3887, 17572900323467556139), (3888, 3888, 17398911211354015979), (3889, 3889, 17226644763716847504), (3890, 3890, 17056083924472126242), (3891, 3891, 16887211806408045784), (3892, 3892, 16720011689512916618), (3893, 3893, 16554467019319719424), (3894, 3894, 16390561405267048934), (3895, 3895, 16228278619076286074), (3896, 3896, 16067602593144837697), (3897, 3897, 15908517418955284848), (3898, 3898, 15751007345500282028), (3899, 3899, 15595056777723051513), (3900, 3900, 15440650274973318329), (3901, 3901, 15287772549478532999), (3902, 3902, 15136408464830230693), (3903, 3903, 14986543034485376923), (3904, 3904, 14838161420282551409), (3905, 3905, 14691248930972823177), (3906, 3906, 14545791020765171463), (3907, 3907, 14401773287886308379), (3908, 3908, 14259181473154760771), (3909, 3909, 14118001458569070071), (3910, 3910, 13978219265909970367), (3911, 3911, 13839821055356406304), (3912, 3912, 13702793124115253766), (3913, 3913, 13567121905064607689), (3914, 3914, 13432793965410502663), (3915, 3915, 13299796005356933329), (3916, 3916, 13168114856789042900), (3917, 3917, 13037737481969349406), (3918, 3918, 12908650972246880600), (3919, 3919, 12780842546779089703), (3920, 3920, 12654299551266425449), (3921, 3921, 12529009456699431138), (3922, 3922, 12404959858118248651), (3923, 3923, 12282138473384404605), (3924, 3924, 12160533141964757035), (3925, 3925, 12040131823727482213), (3926, 3926, 11920922597749982389), (3927, 3927, 11802893661138596424), (3928, 3928, 11686033327859996460), (3929, 3929, 11570330027584154911), (3930, 3930, 11455772304538767238), (3931, 3931, 11342348816375017068), (3932, 3932, 11230048333044571354), (3933, 3933, 11118859735687694410), (3934, 3934, 11008772015532370703), (3935, 3935, 10899774272804327429), (3936, 3936, 10791855715647848939), (3937, 3937, 10685005659057276178), (3938, 3938, 10579213523819085324), (3939, 3939, 10474468835464440915), (3940, 3940, 10370761223232119718), (3941, 3941, 10268080419041702691), (3942, 3942, 10166416256476933358), (3943, 3943, 10065758669779141938), (3944, 3944, 9966097692850635582), (3945, 3945, 9867423458267956022), (3946, 3946, 9769726196304906953), (3947, 3947, 9672996233965254409), (3948, 3948, 9577223994025004365), (3949, 3949, 9482399994084162738), (3950, 3950, 9388514845627883899), (3951, 3951, 9295559253096914751), (3952, 3952, 9203524012967242328), (3953, 3953, 9112400012838853790), (3954, 3954, 9022178230533518604), (3955, 3955, 8932849733201503568), (3956, 3956, 8844405676437132246), (3957, 3957, 8756837303403101233), (3958, 3958, 8670135943963466568), (3959, 3959, 8584293013825214423), (3960, 3960, 8499300013688331112), (3961, 3961, 8415148528404288230), (3962, 3962, 8331830226142859634), (3963, 3963, 8249336857567187756), (3964, 3964, 8167660255017017580), (3965, 3965, 8086792331700017406), (3966, 3966, 8006725080891106343), (3967, 3967, 7927450575139709250), (3968, 3968, 7848960965484860644), (3969, 3969, 7771248480678079846), (3970, 3970, 7694305426413940441), (3971, 3971, 7618124184568257862), (3972, 3972, 7542697212443819666), (3973, 3973, 7468017042023583828), (3974, 3974, 7394076279231271116), (3975, 3975, 7320867603199278333), (3976, 3976, 7248383765543839934), (3977, 3977, 7176617589647366271), (3978, 3978, 7105561969947887397), (3979, 3979, 7035209871235532076), (3980, 3980, 6965554327955972353), (3981, 3981, 6896588443520764706), (3982, 3982, 6828305389624519511), (3983, 3983, 6760698405568831199), (3984, 3984, 6693760797592902177), (3985, 3985, 6627485938210794235), (3986, 3986, 6561867265555241816), (3987, 3987, 6496898282727962194), (3988, 3988, 6432572557156398212), (3989, 3989, 6368883719956829913), (3990, 3990, 6305825465303791993), (3991, 3991, 6243391549805734647), (3992, 3992, 6181575791886865987), (3993, 3993, 6120372071175114839), (3994, 3994, 6059774327896153306), (3995, 3995, 5999776562273419114), (3996, 3996, 5940372833934078331), (3997, 3997, 5881557261320869635), (3998, 3998, 5823324021109771916), (3999, 3999, 5765667347633437540), (4000, 4000, 5708581532310334198), (4001, 4001, 5652060923079538810), (4002, 4002, 5596099923841127535), (4003, 4003, 5540692993902106470), (4004, 4004, 5485834647427828188), (4005, 4005, 5431519452898839790), (4006, 4006, 5377742032573108703), (4007, 4007, 5324497061953572974), (4008, 4008, 5271779269260963340), (4009, 4009, 5219583434911844891), (4010, 4010, 5167904391001826625), (4011, 4011, 5116737020793887748), (4012, 4012, 5066076258211770047), (4013, 4013, 5015917087338386185), (4014, 4014, 4966254541919194243), (4015, 4015, 4917083704870489349), (4016, 4016, 4868399707792563712), (4017, 4017, 4820197730487686844), (4018, 4018, 4772473000482858261), (4019, 4019, 4725220792557285407), (4020, 4020, 4678436428274540007), (4021, 4021, 4632115275519346542), (4022, 4022, 4586252748038956972), (4023, 4023, 4540844304989066309), (4024, 4024, 4495885450484224068), (4025, 4025, 4451371733152697097), (4026, 4026, 4407298745695739700), (4027, 4027, 4363662124451227426), (4028, 4028, 4320457548961611313), (4029, 4029, 4277680741546149815), (4030, 4030, 4235327466877376054), (4031, 4031, 4193393531561758469), (4032, 4032, 4151874783724513336), (4033, 4033, 4110767112598528056), (4034, 4034, 4070066448117354510), (4035, 4035, 4029768760512232189), (4036, 4036, 3989870059913101177), (4037, 4037, 3950366395953565522), (4038, 4038, 3911253857379767843), (4039, 4039, 3872528571663136478), (4040, 4040, 3834186704616966810), (4041, 4041, 3796224460016798822), (4042, 4042, 3758638079224553289), (4043, 4043, 3721423840816389395), (4044, 4044, 3684578060214246926), (4045, 4045, 3648097089321036560), (4046, 4046, 3611977316159442139), (4047, 4047, 3576215164514299147), (4048, 4048, 3540807093578514007), (4049, 4049, 3505749597602489116), (4050, 4050, 3471039205547018927), (4051, 4051, 3436672480739622700), (4052, 4052, 3402646020534279901), (4053, 4053, 3368956455974534555), (4054, 4054, 3335600451459935203), (4055, 4055, 3302574704415777429), (4056, 4056, 3269875944966116266), (4057, 4057, 3237500935610016105), (4058, 4058, 3205446470901006045), (4059, 4059, 3173709377129708955), (4060, 4060, 3142286512009612827), (4061, 4061, 3111174764365953294), (4062, 4062, 3080371053827676529), (4063, 4063, 3049872330522452009), (4064, 4064, 3019675574774704959), (4065, 4065, 2989777796806638574), (4066, 4066, 2960176036442216409), (4067, 4067, 2930867362814075653), (4068, 4068, 2901848874073342231), (4069, 4069, 2873117697102319040), (4070, 4070, 2844670987230018852), (4071, 4071, 2816505927950513715), (4072, 4072, 2788619730644072985), (4073, 4073, 2761009634301062361), (4074, 4074, 2733672905248576595), (4075, 4075, 2706606836879778807), (4076, 4076, 2679808749385919611), (4077, 4077, 2653275989491009516), (4078, 4078, 2627005930189118333), (4079, 4079, 2600995970484275577), (4080, 4080, 2575243535132946116), (4081, 4081, 2549746074389055560), (4082, 4082, 2524501063751540158), (4083, 4083, 2499506003714396196), (4084, 4084, 2474758419519204155), (4085, 4085, 2450255860910103124), (4086, 4086, 2425995901891191212), (4087, 4087, 2401976140486327932), (4088, 4088, 2378194198501314784), (4089, 4089, 2354647721288430480), (4090, 4090, 2331334377513297505), (4091, 4091, 2308251858924056935), (4092, 4092, 2285397880122828649), (4093, 4093, 2262770178339434306), (4094, 4094, 2240366513207360699), (4095, 4095, 2218184666541941286), (4096, 4096, 2196222442120733946), (4097, 4097, 2174477665466073214), (4098, 4098, 2152948183629775460), (4099, 4099, 2131631864979975703), (4100, 4100, 2110526598990074953), (4101, 4101, 2089630296029777181), (4102, 4102, 2068940887158195229), (4103, 4103, 2048456323919005177), (4104, 4104, 2028174578137628888), (4105, 4105, 2008093641720424642), (4106, 4106, 1988211526455865982), (4107, 4107, 1968526263817689091), (4108, 4108, 1949035904769989199), (4109, 4109, 1929738519574246732), (4110, 4110, 1910632197598264091), (4111, 4111, 1891715047126994150), (4112, 4112, 1872985195175241732), (4113, 4113, 1854440787302219537), (4114, 4114, 1836079987427940136), (4115, 4115, 1817900977651425877), (4116, 4116, 1799901958070718690), (4117, 4117, 1782081146604671970), (4118, 4118, 1764436778816506901), (4119, 4119, 1746967107739115744), (4120, 4120, 1729670403702094796), (4121, 4121, 1712544954160489897), (4122, 4122, 1695589063525237522), (4123, 4123, 1678801052995284675), (4124, 4124, 1662179260391370965), (4125, 4125, 1645722039991456401), (4126, 4126, 1629427762367778615), (4127, 4127, 1613294814225523381), (4128, 4128, 1597321598243092457), (4129, 4129, 1581506532913952927), (4130, 4130, 1565848052390052403), (4131, 4131, 1550344606326784558), (4132, 4132, 1534994659729489661), (4133, 4133, 1519796692801474912), (4134, 4134, 1504749200793539517), (4135, 4135, 1489850693854989621), (4136, 4136, 1475099696886128337), (4137, 4137, 1460494749392206275), (4138, 4138, 1446034405338818094), (4139, 4139, 1431717233008730786), (4140, 4140, 1417541814860129491), (4141, 4141, 1403506747386266823), (4142, 4142, 1389610640976501805), (4143, 4143, 1375852119778714658), (4144, 4144, 1362229821563083820), (4145, 4145, 1348742397587211703), (4146, 4146, 1335388512462585844), (4147, 4147, 1322166844022362222), (4148, 4148, 1309076083190457646), (4149, 4149, 1296114933851938263), (4150, 4150, 1283282112724691350), (4151, 4151, 1270576349232367673), (4152, 4152, 1257996385378581854), (4153, 4153, 1245540975622358272), (4154, 4154, 1233208886754810170), (4155, 4155, 1220998897777039772), (4156, 4156, 1208909799779247299), (4157, 4157, 1196940395821036930), (4158, 4158, 1185089500812907851), (4159, 4159, 1173355941398918665), (4160, 4160, 1161738555840513530), (4161, 4161, 1150236193901498544), (4162, 4162, 1138847716734156974), (4163, 4163, 1127571996766492054), (4164, 4164, 1116407917590586192), (4165, 4165, 1105354373852065537), (4166, 4166, 1094410271140658947), (4167, 4167, 1083574525881840542), (4168, 4168, 1072846065229545091), (4169, 4169, 1062223826959945634), (4170, 4170, 1051706759366282806), (4171, 4171, 1041293821154735452), (4172, 4172, 1030983981341322230), (4173, 4173, 1020776219149823990), (4174, 4174, 1010669523910716821), (4175, 4175, 1000662894961105764), (4176, 4176, 990755341545649271), (4177, 4177, 980945882718464625), (4178, 4178, 971233547246004579), (4179, 4179, 961617373510895623), (4180, 4180, 952096409416728339), (4181, 4181, 942669712293790435), (4182, 4182, 933336348805733104), (4183, 4183, 924095394857161489), (4184, 4184, 914945935502140088), (4185, 4185, 905887064853604048), (4186, 4186, 896917885993667374), (4187, 4187, 888037510884819182), (4188, 4188, 879245060281999190), (4189, 4189, 870539663645543753), (4190, 4190, 861920459054993815), (4191, 4191, 853386593123756252), (4192, 4192, 844937220914610151), (4193, 4193, 836571505856049654), (4194, 4194, 828288619659455103), (4195, 4195, 820087742237084261), (4196, 4196, 811968061620875506), (4197, 4197, 803928773882054956), (4198, 4198, 795969083051539560), (4199, 4199, 788088201041128278), (4200, 4200, 780285347565473542), (4201, 4201, 772559750064825289), (4202, 4202, 764910643628539890), (4203, 4203, 757337270919346426), (4204, 4204, 749838882098362798), (4205, 4205, 742414734750854256), (4206, 4206, 735064093812726986), (4207, 4207, 727786231497749491), (4208, 4208, 720580427225494545), (4209, 4209, 713445967549994599), (4210, 4210, 706382146089103564), (4211, 4211, 699388263454557984), (4212, 4212, 692463627182730677), (4213, 4213, 685607551666069977), (4214, 4214, 678819358085217799), (4215, 4215, 672098374341799801), (4216, 4216, 665443934991880992), (4217, 4217, 658855381180080190), (4218, 4218, 652332060574336821), (4219, 4219, 645873327301323586), (4220, 4220, 639478541882498600), (4221, 4221, 633147071170790693), (4222, 4222, 626878288287911577), (4223, 4223, 620671572562288690), (4224, 4224, 614526309467612564), (4225, 4225, 608441890561992638), (4226, 4226, 602417713427715483), (4227, 4227, 596453181611599488), (4228, 4228, 590547704565940087), (4229, 4229, 584700697590039690), (4230, 4230, 578911581772316525), (4231, 4231, 573179783932986659), (4232, 4232, 567504736567313523), (4233, 4233, 561885877789419330), (4234, 4234, 556322651276652802), (4235, 4235, 550814506214507725), (4236, 4236, 545360897242086856), (4237, 4237, 539961284398105798), (4238, 4238, 534615133067431484), (4239, 4239, 529321913928149984), (4240, 4240, 524081102899158400), (4241, 4241, 518892181088275643), (4242, 4242, 513754634740866974), (4243, 4243, 508667955188977202), (4244, 4244, 503631638800967526), (4245, 4245, 498645186931651016), (4246, 4246, 493708105872921798), (4247, 4247, 488819906804873067), (4248, 4248, 483980105747399077), (4249, 4249, 479188223512276314), (4250, 4250, 474443785655719122), (4251, 4251, 469746322431405072), (4252, 4252, 465095368743965417), (4253, 4253, 460490464102936057), (4254, 4254, 455931152577164413), (4255, 4255, 451416982749667735), (4256, 4256, 446947507672938352), (4257, 4257, 442522284824691438), (4258, 4258, 438140876064050928), (4259, 4259, 433802847588169236), (4260, 4260, 429507769889276471), (4261, 4261, 425255217712154922), (4262, 4262, 421044770012034576), (4263, 4263, 416876009912905521), (4264, 4264, 412748524666243090), (4265, 4265, 408661905610141673), (4266, 4266, 404615748128853142), (4267, 4267, 400609651612725883), (4268, 4268, 396643219418540478), (4269, 4269, 392716058830238097), (4270, 4270, 388827781020037720), (4271, 4271, 384978001009938337), (4272, 4272, 381166337633602314), (4273, 4273, 377392413498616152), (4274, 4274, 373655854949124903), (4275, 4275, 369956292028836538), (4276, 4276, 366293358444392612), (4277, 4277, 362666691529101596), (4278, 4278, 359075932207031283), (4279, 4279, 355520724957456716), (4280, 4280, 352000717779660115), (4281, 4281, 348515562158079321), (4282, 4282, 345064913027801308), (4283, 4283, 341648428740397335), (4284, 4284, 338265771030096371), (4285, 4285, 334916604980293437), (4286, 4286, 331600598990389542), (4287, 4287, 328317424742959942), (4288, 4288, 325066757171247467), (4289, 4289, 321848274426977691), (4290, 4290, 318661657848492763), (4291, 4291, 315506591929200755), (4292, 4292, 312382764286337382), (4293, 4293, 309289865630037011), (4294, 4294, 306227589732709912), (4295, 4295, 303195633398722685), (4296, 4296, 300193696434378897), (4297, 4297, 297221481618196927), (4298, 4298, 294278694671482106), (4299, 4299, 291365044229190204), (4300, 4300, 288480241811079410), (4301, 4301, 285624001793147931), (4302, 4302, 282796041379354387), (4303, 4303, 279996080573618205), (4304, 4304, 277223842152097233), (4305, 4305, 274479051635739834), (4306, 4306, 271761437263108747), (4307, 4307, 269070729963474007), (4308, 4308, 266406663330172284), (4309, 4309, 263768973594229984), (4310, 4310, 261157399598247509), (4311, 4311, 258571682770542088), (4312, 4312, 256011567099546622), (4313, 4313, 253476799108462002), (4314, 4314, 250967127830160398), (4315, 4315, 248482304782337028), (4316, 4316, 246022083942907948), (4317, 4317, 243586221725651434), (4318, 4318, 241174476956090528), (4319, 4319, 238786610847614385), (4320, 4320, 236422386977836024), (4321, 4321, 234081571265184183), (4322, 4322, 231763931945726913), (4323, 4323, 229469239550224667), (4324, 4324, 227197266881410561), (4325, 4325, 224947788991495605), (4326, 4326, 222720583159896639), (4327, 4327, 220515428871184791), (4328, 4328, 218332107793252268), (4329, 4329, 216170403755695315), (4330, 4330, 214030102728411203), (4331, 4331, 211910992800407132), (4332, 4332, 209812864158818942), (4333, 4333, 207735509068137567), (4334, 4334, 205678721849641155), (4335, 4335, 203642298861030847), (4336, 4336, 201626038476268165), (4337, 4337, 199629741065612045), (4338, 4338, 197653208975853509), (4339, 4339, 195696246510746049), (4340, 4340, 193758659911629751), (4341, 4341, 191840257338247279), (4342, 4342, 189940848849749781), (4343, 4343, 188060246385890872), (4344, 4344, 186198263748406804), (4345, 4345, 184354716582580994), (4346, 4346, 182529422358991083), (4347, 4347, 180722200355436716), (4348, 4348, 178932871639046254), (4349, 4349, 177161259048560647), (4350, 4350, 175407187176792720), (4351, 4351, 173670482353260119), (4352, 7209, 171950972626990217)]

def glob0 : ℕ := 18446744073709551616

def runs1 : List (ℕ × ℕ × ℕ) := [(0, 3000, 1820697685370222), (3001, 3001, 1838904662223924), (3002, 3002, 1857293708846164), (3003, 3003, 1875866645934625), (3004, 3004, 1894625312393971), (3005, 3005, 1913571565517911), (3006, 3006, 1932707281173090), (3007, 3007, 1952034353984821), (3008, 3008, 1971554697524669), (3009, 3009, 1991270244499916), (3010, 3010, 2011182946944915), (3011, 3011, 2031294776414364), (3012, 3012, 2051607724178508), (3013, 3013, 2072123801420293), (3014, 3014, 2092845039434496), (3015, 3015, 2113773489828841), (3016, 3016, 2134911224727129), (3017, 3017, 2156260336974401), (3018, 3018, 2177822940344145), (3019, 3019, 2199601169747586), (3020, 3020, 2221597181445062), (3021, 3021, 2243813153259513), (3022, 3022, 2266251284792108), (3023, 3023, 2288913797640029), (3024, 3024, 2311802935616429), (3025, 3025, 2334920964972593), (3026, 3026, 2358270174622319), (3027, 3027, 2381852876368542), (3028, 3028, 2405671405132228), (3029, 3029, 2429728119183550), (3030, 3030, 2454025400375386), (3031, 3031, 2478565654379139), (3032, 3032, 2503351310922931), (3033, 3033, 2528384824032160), (3034, 3034, 2553668672272482), (3035, 3035, 2579205358995207), (3036, 3036, 2604997412585159), (3037, 3037, 2631047386711010), (3038, 3038, 2657357860578120), (3039, 3039, 2683931439183902), (3040, 3040, 2710770753575741), (3041, 3041, 2737878461111498), (3042, 3042, 2765257245722613), (3043, 3043, 2792909818179839), (3044, 3044, 2820838916361637), (3045, 3045, 2849047305525254), (3046, 3046, 2877537778580506), (3047, 3047, 2906313156366311), (3048, 3048, 2935376287929974), (3049, 3049, 2964730050809274), (3050, 3050, 2994377351317367), (3051, 3051, 3024321124830541), (3052, 3052, 3054564336078846), (3053, 3053, 3085109979439634), (3054, 3054, 3115961079234031), (3055, 3055, 3147120690026371), (3056, 3056, 3178591896926635), (3057, 3057, 3210377815895901), (3058, 3058, 3242481594054860), (3059, 3059, 3274906409995409), (3060, 3060, 3307655474095363), (3061, 3061, 3340732028836316), (3062, 3062, 3374139349124680), (3063, 3063, 3407880742615926), (3064, 3064, 3441959550042086), (3065, 3065, 3476379145542507), (3066, 3066, 3511142936997932), (3067, 3067, 3546254366367911), (3068, 3068, 3581716910031590), (3069, 3069, 3617534079131906), (3070, 3070, 3653709419923225), (3071, 3071, 3690246514122457), (3072, 3072, 3727148979263682), (3073, 3073, 3764420469056319), (3074, 3074, 3802064673746882), (3075, 3075, 3840085320484351), (3076, 3076, 3878486173689194), (3077, 3077, 3917271035426086), (3078, 3078, 3956443745780347), (3079, 3079, 3996008183238150), (3080, 3080, 4035968265070532), (3081, 3081, 4076327947721237), (3082, 3082, 4117091227198450), (3083, 3083, 4158262139470434), (3084, 3084, 4199844760865138), (3085, 3085, 4241843208473790), (3086, 3086, 4284261640558528), (3087, 3087, 4327104256964113), (3088, 3088, 4370375299533754), (3089, 3089, 4414079052529092), (3090, 3090, 4458219843054382), (3091, 3091, 4502802041484926), (3092, 3092, 4547830061899776), (3093, 3093, 4593308362518773), (3094, 3094, 4639241446143961), (3095, 3095, 4685633860605401), (3096, 3096, 4732490199211455), (3097, 3097, 4779815101203569), (3098, 3098, 4827613252215605), (3099, 3099, 4875889384737761), (3100, 3100, 4924648278585138), (3101, 3101, 4973894761370990), (3102, 3102, 5023633708984700), (3103, 3103, 5073870046074547), (3104, 3104, 5124608746535292), (3105, 3105, 5175854834000645), (3106, 3106, 5227613382340652), (3107, 3107, 5279889516164058), (3108, 3108, 5332688411325699), (3109, 3109, 5386015295438956), (3110, 3110, 5439875448393345), (3111, 3111, 5494274202877279), (3112, 3112, 5549216944906051), (3113, 3113, 5604709114355112), (3114, 3114, 5660756205498663), (3115, 3115, 5717363767553650), (3116, 3116, 5774537405229186), (3117, 3117, 5832282779281478), (3118, 3118, 5890605607074293), (3119, 3119, 5949511663145036), (3120, 3120, 6009006779776486), (3121, 3121, 6069096847574251), (3122, 3122, 6129787816049993), (3123, 3123, 6191085694210493), (3124, 3124, 6252996551152598), (3125, 3125, 6315526516664124), (3126, 3126, 6378681781830766), (3127, 3127, 6442468599649073), (3128, 3128, 6506893285645564), (3129, 3129, 6571962218502020), (3130, 3130, 6637681840687040), (3131, 3131, 6704058659093910), (3132, 3132, 6771099245684849), (3133, 3133, 6838810238141698), (3134, 3134, 6907198340523115), (3135, 3135, 6976270323928346), (3136, 3136, 7046033027167629), (3137, 3137, 7116493357439306), (3138, 3138, 7187658291013699), (3139, 3139, 7259534873923836), (3140, 3140, 7332130222663074), (3141, 3141, 7405451524889705), (3142, 3142, 7479506040138602), (3143, 3143, 7554301100539988), (3144, 3144, 7629844111545388), (3145, 3145, 7706142552660841), (3146, 3146, 7783203978187450), (3147, 3147, 7861036017969324), (3148, 3148, 7939646378149018), (3149, 3149, 8019042841930508), (3150, 3150, 8099233270349813), (3151, 3151, 8180225603053311), (3152, 3152, 8262027859083844), (3153, 3153, 8344648137674683), (3154, 3154, 8428094619051429), (3155, 3155, 8512375565241944), (3156, 3156, 8597499320894363), (3157, 3157, 8683474314103307), (3158, 3158, 8770309057244340), (3159, 3159, 8858012147816783), (3160, 3160, 8946592269294951), (3161, 3161, 9036058191987900), (3162, 3162, 9126418773907779), (3163, 3163, 9217682961646857), (3164, 3164, 9309859791263326), (3165, 3165, 9402958389175959), (3166, 3166, 9496987973067719), (3167, 3167, 9591957852798396), (3168, 3168, 9687877431326380), (3169, 3169, 9784756205639644), (3170, 3170, 9882603767696040), (3171, 3171, 9981429805373000), (3172, 3172, 10081244103426730), (3173, 3173, 10182056544460998), (3174, 3174, 10283877109905608), (3175, 3175, 10386715881004664), (3176, 3176, 10490583039814710), (3177, 3177, 10595488870212857), (3178, 3178, 10701443758914986), (3179, 3179, 10808458196504136), (3180, 3180, 10916542778469177), (3181, 3181, 11025708206253869), (3182, 3182, 11135965288316408), (3183, 3183, 11247324941199572), (3184, 3184, 11359798190611568), (3185, 3185, 11473396172517683), (3186, 3186, 11588130134242860), (3187, 3187, 11704011435585289), (3188, 3188, 11821051549941141), (3189, 3189, 11939262065440553), (3190, 3190, 12058654686094958), (3191, 3191, 12179241232955908), (3192, 3192, 12301033645285467), (3193, 3193, 12424043981738322), (3194, 3194, 12548284421555705), (3195, 3195, 12673767265771262), (3196, 3196, 12800504938428975), (3197, 3197, 12928509987813264), (3198, 3198, 13057795087691397), (3199, 3199, 13188373038568311), (3200, 3200, 13320256768953994), (3201, 3201, 13453459336643534), (3202, 3202, 13587993930009969), (3203, 3203, 13723873869310069), (3204, 3204, 13861112608003170), (3205, 3205, 13999723734083201), (3206, 3206, 14139720971424033), (3207, 3207, 14281118181138274), (3208, 3208, 14423929362949656), (3209, 3209, 14568168656579153), (3210, 3210, 14713850343144945), (3211, 3211, 14860988846576394), (3212, 3212, 15009598735042158), (3213, 3213, 15159694722392579), (3214, 3214, 15311291669616505), (3215, 3215, 15464404586312670), (3216, 3216, 15619048632175797), (3217, 3217, 15775239118497555), (3218, 3218, 15932991509682531), (3219, 3219, 16092321424779356), (3220, 3220, 16253244639027149), (3221, 3221, 16415777085417421), (3222, 3222, 16579934856271595), (3223, 3223, 16745734204834311), (3224, 3224, 16913191546882654), (3225, 3225, 17082323462351481), (3226, 3226, 17253146696974995), (3227, 3227, 17425678163944745), (3228, 3228, 17599934945584193), (3229, 3229, 17775934295040035), (3230, 3230, 17953693637990435), (3231, 3231, 18133230574370339), (3232, 3232, 18314562880114043), (3233, 3233, 18497708508915183), (3234, 3234, 18682685594004335), (3235, 3235, 18869512449944378), (3236, 3236, 19058207574443822), (3237, 3237, 19248789650188260), (3238, 3238, 19441277546690143), (3239, 3239, 19635690322157045), (3240, 3240, 19832047225378615), (3241, 3241, 20030367697632401), (3242, 3242, 20230671374608725), (3243, 3243, 20432978088354812), (3244, 3244, 20637307869238360), (3245, 3245, 20843680947930744), (3246, 3246, 21052117757410051), (3247, 3247, 21262638934984152), (3248, 3248, 21475265324333994), (3249, 3249, 21690017977577333), (3250, 3250, 21906918157353107), (3251, 3251, 22125987338926638), (3252, 3252, 22347247212315904), (3253, 3253, 22570719684439063), (3254, 3254, 22796426881283454), (3255, 3255, 23024391150096288), (3256, 3256, 23254635061597251), (3257, 3257, 23487181412213224), (3258, 3258, 23722053226335356), (3259, 3259, 23959273758598710), (3260, 3260, 24198866496184697), (3261, 3261, 24440855161146544), (3262, 3262, 24685263712758009), (3263, 3263, 24932116349885589), (3264, 3264, 25181437513384445), (3265, 3265, 25433251888518289), (3266, 3266, 25687584407403472), (3267, 3267, 25944460251477507), (3268, 3268, 26203904853992282), (3269, 3269, 26465943902532205), (3270, 3270, 26730603341557527), (3271, 3271, 26997909374973102), (3272, 3272, 27267888468722833), (3273, 3273, 27540567353410062), (3274, 3274, 27815973026944162), (3275, 3275, 28094132757213604), (3276, 3276, 28375074084785740), (3277, 3277, 28658824825633597), (3278, 3278, 28945413073889933), (3279, 3279, 29234867204628833), (3280, 3280, 29527215876675121), (3281, 3281, 29822488035441872), (3282, 3282, 30120712915796291), (3283, 3283, 30421920044954254), (3284, 3284, 30726139245403796), (3285, 3285, 31033400637857834), (3286, 3286, 31343734644236413), (3287, 3287, 31657171990678777), (3288, 3288, 31973743710585564), (3289, 3289, 32293481147691420), (3290, 3290, 32616415959168334), (3291, 3291, 32942580118760018), (3292, 3292, 33272005919947618), (3293, 3293, 33604725979147094), (3294, 3294, 33940773238938565), (3295, 3295, 34280180971327951), (3296, 3296, 34622982781041230), (3297, 3297, 34969212608851642), (3298, 3298, 35318904734940159), (3299, 3299, 35672093782289560), (3300, 3300, 36028814720112456), (3301, 3301, 36389102867313580), (3302, 3302, 36752993895986716), (3303, 3303, 37120523834946583), (3304, 3304, 37491729073296049), (3305, 3305, 37866646364029010), (3306, 3306, 38245312827669300), (3307, 3307, 38627765955945993), (3308, 3308, 39014043615505453), (3309, 3309, 39404184051660507), (3310, 3310, 39798225892177112), (3311, 3311, 40196208151098883), (3312, 3312, 40598170232609872), (3313, 3313, 41004151934935971), (3314, 3314, 41414193454285331), (3315, 3315, 41828335388828184), (3316, 3316, 42246618742716466), (3317, 3317, 42669084930143631), (3318, 3318, 43095775779445067), (3319, 3319, 43526733537239517), (3320, 3320, 43962000872611913), (3321, 3321, 44401620881338032), (3322, 3322, 44845637090151412), (3323, 3323, 45294093461052926), (3324, 3324, 45747034395663455), (3325, 3325, 46204504739620090), (3326, 3326, 46666549787016291), (3327, 3327, 47133215284886454), (3328, 3328, 47604547437735318), (3329, 3329, 48080592912112672), (3330, 3330, 48561398841233798), (3331, 3331, 49047012829646136), (3332, 3332, 49537482957942598), (3333, 3333, 50032857787522024), (3334, 3334, 50533186365397244), (3335, 3335, 51038518229051216), (3336, 3336, 51548903411341728), (3337, 3337, 52064392445455146), (3338, 3338, 52585036369909697), (3339, 3339, 53110886733608794), (3340, 3340, 53641995600944882), (3341, 3341, 54178415556954331), (3342, 3342, 54720199712523874), (3343, 3343, 55267401709649113), (3344, 3344, 55820075726745604), (3345, 3345, 56378276484013060), (3346, 3346, 56942059248853191), (3347, 3347, 57511479841341723), (3348, 3348, 58086594639755140), (3349, 3349, 58667460586152691), (3350, 3350, 59254135192014218), (3351, 3351, 59846676543934360), (3352, 3352, 60445143309373704), (3353, 3353, 61049594742467441), (3354, 3354, 61660090689892115), (3355, 3355, 62276691596791036), (3356, 3356, 62899458512758947), (3357, 3357, 63528453097886536), (3358, 3358, 64163737628865402), (3359, 3359, 64805375005154056), (3360, 3360, 65453428755205596), (3361, 3361, 66107963042757652), (3362, 3362, 66769042673185229), (3363, 3363, 67436733099917081), (3364, 3364, 68111100430916252), (3365, 3365, 68792211435225414), (3366, 3366, 69480133549577668), (3367, 3367, 70174934885073445), (3368, 3368, 70876684233924179), (3369, 3369, 71585451076263421), (3370, 3370, 72301305587026055), (3371, 3371, 73024318642896316), (3372, 3372, 73754561829325279), (3373, 3373, 74492107447618532), (3374, 3374, 75237028522094717), (3375, 3375, 75989398807315664), (3376, 3376, 76749292795388821), (3377, 3377, 77516785723342709), (3378, 3378, 78291953580576136), (3379, 3379, 79074873116381898), (3380, 3380, 79865621847545717), (3381, 3381, 80664278066021174), (3382, 3382, 81470920846681386), (3383, 3383, 82285630055148199), (3384, 3384, 83108486355699681), (3385, 3385, 83939571219256678), (3386, 3386, 84778966931449245), (3387, 3387, 85626756600763737), (3388, 3388, 86483024166771375), (3389, 3389, 87347854408439089), (3390, 3390, 88221332952523479), (3391, 3391, 89103546282048714), (3392, 3392, 89994581744869201), (3393, 3393, 90894527562317893), (3394, 3394, 91803472837941072), (3395, 3395, 92721507566320483), (3396, 3396, 93648722641983688), (3397, 3397, 94585209868403525), (3398, 3398, 95531061967087560), (3399, 3399, 96486372586758436), (3400, 3400, 97451236312626020), (3401, 3401, 98425748675752280), (3402, 3402, 99410006162509803), (3403, 3403, 100404106224134901), (3404, 3404, 101408147286376250), (3405, 3405, 102422228759240012), (3406, 3406, 103446451046832413), (3407, 3407, 104480915557300737), (3408, 3408, 105525724712873744), (3409, 3409, 106580981960002481), (3410, 3410, 107646791779602506), (3411, 3411, 108723259697398531), (3412, 3412, 109810492294372517), (3413, 3413, 110908597217316242), (3414, 3414, 112017683189489404), (3415, 3415, 113137860021384298), (3416, 3416, 114269238621598141), (3417, 3417, 115411931007814123), (3418, 3418, 116566050317892264), (3419, 3419, 117731710821071186), (3420, 3420, 118909027929281898), (3421, 3421, 120098118208574717), (3422, 3422, 121299099390660465), (3423, 3423, 122512090384567069), (3424, 3424, 123737211288412740), (3425, 3425, 124974583401296867), (3426, 3426, 126224329235309836), (3427, 3427, 127486572527662934), (3428, 3428, 128761438252939564), (3429, 3429, 130049052635468959), (3430, 3430, 131349543161823649), (3431, 3431, 132663038593441885), (3432, 3432, 133989668979376304), (3433, 3433, 135329565669170067), (3434, 3434, 136682861325861768), (3435, 3435, 138049689939120386), (3436, 3436, 139430186838511589), (3437, 3437, 140824488706896705), (3438, 3438, 142232733593965672), (3439, 3439, 143655060929905329), (3440, 3440, 145091611539204382), (3441, 3441, 146542527654596426), (3442, 3442, 148007952931142390), (3443, 3443, 149488032460453814), (3444, 3444, 150982912785058352), (3445, 3445, 152492741912908936), (3446, 3446, 154017669332038025), (3447, 3447, 155557846025358406), (3448, 3448, 157113424485611990), (3449, 3449, 158684558730468109), (3450, 3450, 160271404317772791), (3451, 3451, 161874118360950518), (3452, 3452, 163492859544560024), (3453, 3453, 165127788140005624), (3454, 3454, 166779066021405680), (3455, 3455, 168446856681619737), (3456, 3456, 170131325248435934), (3457, 3457, 171832638500920294), (3458, 3458, 173550964885929497), (3459, 3459, 175286474534788791), (3460, 3460, 177039339280136679), (3461, 3461, 178809732672938046), (3462, 3462, 180597829999667427), (3463, 3463, 182403808299664101), (3464, 3464, 184227846382660742), (3465, 3465, 186070124846487349), (3466, 3466, 187930826094952223), (3467, 3467, 189810134355901745), (3468, 3468, 191708235699460762), (3469, 3469, 193625318056455370), (3470, 3470, 195561571237019924), (3471, 3471, 197517186949390123), (3472, 3472, 199492358818884024), (3473, 3473, 201487282407072864), (3474, 3474, 203502155231143593), (3475, 3475, 205537176783455029), (3476, 3476, 207592548551289579), (3477, 3477, 209668474036802475), (3478, 3478, 211765158777170500), (3479, 3479, 213882810364942205), (3480, 3480, 216021638468591627), (3481, 3481, 218181854853277543), (3482, 3482, 220363673401810319), (3483, 3483, 222567310135828422), (3484, 3484, 224792983237186706), (3485, 3485, 227040913069558573), (3486, 3486, 229311322200254159), (3487, 3487, 231604435422256700), (3488, 3488, 233920479776479267), (3489, 3489, 236259684574244060), (3490, 3490, 238622281419986501), (3491, 3491, 241008504234186366), (3492, 3492, 243418589276528229), (3493, 3493, 245852775169293512), (3494, 3494, 248311302920986447), (3495, 3495, 250794415950196311), (3496, 3496, 253302360109698274), (3497, 3497, 255835383710795257), (3498, 3498, 258393737547903210), (3499, 3499, 260977674923382242), (3500, 3500, 263587451672616064), (3501, 3501, 266223326189342225), (3502, 3502, 268885559451235647), (3503, 3503, 271574415045748003), (3504, 3504, 274290159196205483), (3505, 3505, 277033060788167538), (3506, 3506, 279803391396049214), (3507, 3507, 282601425310009706), (3508, 3508, 285427439563109803), (3509, 3509, 288281713958740901), (3510, 3510, 291164531098328310), (3511, 3511, 294076176409311593), (3512, 3512, 297016938173404709), (3513, 3513, 299987107555138756), (3514, 3514, 302986978630690143), (3515, 3515, 306016848416997045), (3516, 3516, 309077016901167015), (3517, 3517, 312167787070178686), (3518, 3518, 315289464940880472), (3519, 3519, 318442359590289277), (3520, 3520, 321626783186192170), (3521, 3521, 324843051018054092), (3522, 3522, 328091481528234632), (3523, 3523, 331372396343516979), (3524, 3524, 334686120306952149), (3525, 3525, 338032981510021670), (3526, 3526, 341413311325121887), (3527, 3527, 344827444438373106), (3528, 3528, 348275718882756837), (3529, 3529, 351758476071584405), (3530, 3530, 355276060832300249), (3531, 3531, 358828821440623252), (3532, 3532, 362417109655029484), (3533, 3533, 366041280751579779), (3534, 3534, 369701693559095577), (3535, 3535, 373398710494686532), (3536, 3536, 377132697599633398), (3537, 3537, 380904024575629732), (3538, 3538, 384713064821386029), (3539, 3539, 388560195469599889), (3540, 3540, 392445797424295888), (3541, 3541, 396370255398538847), (3542, 3542, 400333957952524236), (3543, 3543, 404337297532049478), (3544, 3544, 408380670507369973), (3545, 3545, 412464477212443672), (3546, 3546, 416589121984568109), (3547, 3547, 420755013204413790), (3548, 3548, 424962563336457928), (3549, 3549, 429212188969822507), (3550, 3550, 433504310859520732), (3551, 3551, 437839353968115940), (3552, 3552, 442217747507797099), (3553, 3553, 446639924982875070), (3554, 3554, 451106324232703821), (3555, 3555, 455617387475030859), (3556, 3556, 460173561349781168), (3557, 3557, 464775296963278979), (3558, 3558, 469423049932911769), (3559, 3559, 474117280432240887), (3560, 3560, 478858453236563296), (3561, 3561, 483647037768928929), (3562, 3562, 488483508146618218), (3563, 3563, 493368343228084400), (3564, 3564, 498302026660365244), (3565, 3565, 503285046926968896), (3566, 3566, 508317897396238585), (3567, 3567, 513401076370200971), (3568, 3568, 518535087133902981), (3569, 3569, 523720438005242011), (3570, 3570, 528957642385294431), (3571, 3571, 534247218809147375), (3572, 3572, 539589690997238849), (3573, 3573, 544985587907211237), (3574, 3574, 550435443786283350), (3575, 3575, 555939798224146183), (3576, 3576, 561499196206387645), (3577, 3577, 567114188168451522), (3578, 3578, 572785330050136037), (3579, 3579, 578513183350637397), (3580, 3580, 584298315184143771), (3581, 3581, 590141298335985209), (3582, 3582, 596042711319345061), (3583, 3583, 602003138432538512), (3584, 3584, 608023169816863897), (3585, 3585, 614103401515032536), (3586, 3586, 620244435530182861), (3587, 3587, 626446879885484690), (3588, 3588, 632711348684339536), (3589, 3589, 639038462171182932), (3590, 3590, 645428846792894761), (3591, 3591, 651883135260823709), (3592, 3592, 658401966613431946), (3593, 3593, 664985986279566265), (3594, 3594, 671635846142361928), (3595, 3595, 678352204603785547), (3596, 3596, 685135726649823403), (3597, 3597, 691987083916321637), (3598, 3598, 698906954755484853), (3599, 3599, 705896024303039702), (3600, 3600, 712954984546070099), (3601, 3601, 720084534391530800), (3602, 3602, 727285379735446108), (3603, 3603, 734558233532800569), (3604, 3604, 741903815868128574), (3605, 3605, 749322854026809860), (3606, 3606, 756816082567077959), (3607, 3607, 764384243392748738), (3608, 3608, 772028085826676226), (3609, 3609, 779748366684942988), (3610, 3610, 787545850351792418), (3611, 3611, 795421308855310342), (3612, 3612, 803375521943863445), (3613, 3613, 811409277163302080), (3614, 3614, 819523369934935101), (3615, 3615, 827718603634284452), (3616, 3616, 835995789670627296), (3617, 3617, 844355747567333569), (3618, 3618, 852799305043006905), (3619, 3619, 861327298093436974), (3620, 3620, 869940571074371343), (3621, 3621, 878639976785115057), (3622, 3622, 887426376552966207), (3623, 3623, 896300640318495869), (3624, 3624, 905263646721680828), (3625, 3625, 914316283188897636), (3626, 3626, 923459446020786613), (3627, 3627, 932694040480994479), (3628, 3628, 942020980885804424), (3629, 3629, 951441190694662468), (3630, 3630, 960955602601609093), (3631, 3631, 970565158627625184), (3632, 3632, 980270810213901435), (3633, 3633, 990073518316040450), (3634, 3634, 999974253499200854), (3635, 3635, 1009973996034192863), (3636, 3636, 1020073735994534791), (3637, 3637, 1030274473354480139), (3638, 3638, 1040577218088024941), (3639, 3639, 1050982990268905190), (3640, 3640, 1061492820171594242), (3641, 3641, 1072107748373310184), (3642, 3642, 1082828825857043286), (3643, 3643, 1093657114115613719), (3644, 3644, 1104593685256769856), (3645, 3645, 1115639622109337555), (3646, 3646, 1126796018330430930), (3647, 3647, 1138063978513735240), (3648, 3648, 1149444618298872592), (3649, 3649, 1160939064481861318), (3650, 3650, 1172548455126679931), (3651, 3651, 1184273939677946730), (3652, 3652, 1196116679074726198), (3653, 3653, 1208077845865473460), (3654, 3654, 1220158624324128194), (3655, 3655, 1232360210567369476), (3656, 3656, 1244683812673043171), (3657, 3657, 1257130650799773603), (3658, 3658, 1269701957307771339), (3659, 3659, 1282398976880849052), (3660, 3660, 1295222966649657543), (3661, 3661, 1308175196316154118), (3662, 3662, 1321256948279315659), (3663, 3663, 1334469517762108816), (3664, 3664, 1347814212939729904), (3665, 3665, 1361292355069127203), (3666, 3666, 1374905278619818475), (3667, 3667, 1388654331406016660), (3668, 3668, 1402540874720076826), (3669, 3669, 1416566283467277595), (3670, 3670, 1430731946301950371), (3671, 3671, 1445039265764969874), (3672, 3672, 1459489658422619573), (3673, 3673, 1474084555006845769), (3674, 3674, 1488825400556914226), (3675, 3675, 1503713654562483369), (3676, 3676, 1518750791108108202), (3677, 3677, 1533938299019189284), (3678, 3678, 1549277682009381177), (3679, 3679, 1564770458829474989), (3680, 3680, 1580418163417769739), (3681, 3681, 1596222345051947436), (3682, 3682, 1612184568502466911), (3683, 3683, 1628306414187491580), (3684, 3684, 1644589478329366496), (3685, 3685, 1661035373112660160), (3686, 3686, 1677645726843786762), (3687, 3687, 1694422184112224630), (3688, 3688, 1711366405953346876), (3689, 3689, 1728480070012880345), (3690, 3690, 1745764870713009148), (3691, 3691, 1763222519420139240), (3692, 3692, 1780854744614340632), (3693, 3693, 1798663292060484038), (3694, 3694, 1816649924981088879), (3695, 3695, 1834816424230899768), (3696, 3696, 1853164588473208765), (3697, 3697, 1871696234357940853), (3698, 3698, 1890413196701520261), (3699, 3699, 1909317328668535464), (3700, 3700, 1928410501955220819), (3701, 3701, 1947694606974773027), (3702, 3702, 1967171553044520757), (3703, 3703, 1986843268574965965), (3704, 3704, 2006711701260715624), (3705, 3705, 2026778818273322780), (3706, 3706, 2047046606456056008), (3707, 3707, 2067517072520616568), (3708, 3708, 2088192243245822734), (3709, 3709, 2109074165678280961), (3710, 3710, 2130164907335063771), (3711, 3711, 2151466556408414409), (3712, 3712, 2172981221972498553), (3713, 3713, 2194711034192223538), (3714, 3714, 2216658144534145774), (3715, 3715, 2238824725979487231), (3716, 3716, 2261212973239282104), (3717, 3717, 2283825102971674925), (3718, 3718, 2306663354001391674), (3719, 3719, 2329729987541405591), (3720, 3720, 2353027287416819647), (3721, 3721, 2376557560290987843), (3722, 3722, 2400323135893897722), (3723, 3723, 2424326367252836699), (3724, 3724, 2448569630925365066), (3725, 3725, 2473055327234618716), (3726, 3726, 2497785880506964904), (3727, 3727, 2522763739312034553), (3728, 3728, 2547991376705154898), (3729, 3729, 2573471290472206447), (3730, 3730, 2599206003376928512), (3731, 3731, 2625198063410697797), (3732, 3732, 2651450044044804775), (3733, 3733, 2677964544485252822), (3734, 3734, 2704744189930105351), (3735, 3735, 2731791631829406404), (3736, 3736, 2759109548147700468), (3737, 3737, 2786700643629177473), (3738, 3738, 2814567650065469247), (3739, 3739, 2842713326566123940), (3740, 3740, 2871140459831785179), (3741, 3741, 2899851864430103031), (3742, 3742, 2928850383074404061), (3743, 3743, 2958138886905148102), (3744, 3744, 2987720275774199583), (3745, 3745, 3017597478531941579), (3746, 3746, 3047773453317260995), (3747, 3747, 3078251187850433605), (3748, 3748, 3109033699728937941), (3749, 3749, 3140124036726227320), (3750, 3750, 3171525277093489593), (3751, 3751, 3203240529864424489), (3752, 3752, 3235272935163068734), (3753, 3753, 3267625664514699421), (3754, 3754, 3300301921159846416), (3755, 3755, 3333304940371444880), (3756, 3756, 3366637989775159329), (3757, 3757, 3400304369672910922), (3758, 3758, 3434307413369640031), (3759, 3759, 3468650487503336431), (3760, 3760, 3503336992378369796), (3761, 3761, 3538370362302153494), (3762, 3762, 3573754065925175029), (3763, 3763, 3609491606584426779), (3764, 3764, 3645586522650271047), (3765, 3765, 3682042387876773757), (3766, 3766, 3718862811755541495), (3767, 3767, 3756051439873096910), (3768, 3768, 3793611954271827879), (3769, 3769, 3831548073814546157), (3770, 3770, 3869863554552691619), (3771, 3771, 3908562190098218535), (3772, 3772, 3947647811999200721), (3773, 3773, 3987124290119192728), (3774, 3774, 4026995533020384655), (3775, 3775, 4067265488350588502), (3776, 3776, 4107938143234094387), (3777, 3777, 4149017524666435330), (3778, 3778, 4190507699913099684), (3779, 3779, 4232412776912230681), (3780, 3780, 4274736904681352987), (3781, 3781, 4317484273728166517), (3782, 3782, 4360659116465448182), (3783, 3783, 4404265707630102664), (3784, 3784, 4448308364706403691), (3785, 3785, 4492791448353467728), (3786, 3786, 4537719362837002405), (3787, 3787, 4583096556465372429), (3788, 3788, 4628927522030026153), (3789, 3789, 4675216797250326415), (3790, 3790, 4721968965222829679), (3791, 3791, 4769188654875057976), (3792, 3792, 4816880541423808556), (3793, 3793, 4865049346838046641), (3794, 3794, 4913699840306427108), (3795, 3795, 4962836838709491379), (3796, 3796, 5012465207096586292), (3797, 3797, 5062589859167552155), (3798, 3798, 5113215757759227677), (3799, 3799, 5164347915336819954), (3800, 3800, 5215991394490188153), (3801, 3801, 5268151308435090035), (3802, 3802, 5320832821519440935), (3803, 3803, 5374041149734635344), (3804, 3804, 5427781561231981698), (3805, 3805, 5482059376844301515), (3806, 3806, 5536879970612744530), (3807, 3807, 5592248770318871975), (3808, 3808, 5648171258022060695), (3809, 3809, 5704652970602281302), (3810, 3810, 5761699500308304115), (3811, 3811, 5819316495311387156), (3812, 3812, 5877509660264501028), (3813, 3813, 5936284756867146038), (3814, 3814, 5995647604435817498), (3815, 3815, 6055604080480175673), (3816, 3816, 6116160121284977430), (3817, 3817, 6177321722497827204), (3818, 3818, 6239094939722805476), (3819, 3819, 6301485889120033531), (3820, 3820, 6364500748011233866), (3821, 3821, 6428145755491346205), (3822, 3822, 6492427213046259667), (3823, 3823, 6557351485176722264), (3824, 3824, 6622925000028489486), (3825, 3825, 6689154250028774381), (3826, 3826, 6756045792529062125), (3827, 3827, 6823606250454352746), (3828, 3828, 6891842312958896274), (3829, 3829, 6960760736088485236), (3830, 3830, 7030368343449370089), (3831, 3831, 7100672026883863790), (3832, 3832, 7171678747152702428), (3833, 3833, 7243395534624229452), (3834, 3834, 7315829489970471746), (3835, 3835, 7388987784870176464), (3836, 3836, 7462877662718878228), (3837, 3837, 7537506439346067011), (3838, 3838, 7612881503739527681), (3839, 3839, 7689010318776922958), (3840, 3840, 7765900421964692187), (3841, 3841, 7843559426184339109), (3842, 3842, 7921995020446182500), (3843, 3843, 8001214970650644325), (3844, 3844, 8081227120357150768), (3845, 3845, 8162039391560722276), (3846, 3846, 8243659785476329499), (3847, 3847, 8326096383331092794), (3848, 3848, 8409357347164403722), (3849, 3849, 8493450920636047759), (3850, 3850, 8578385429842408237), (3851, 3851, 8664169284140832319), (3852, 3852, 8750810976982240642), (3853, 3853, 8838319086752063049), (3854, 3854, 8926702277619583679), (3855, 3855, 9015969300395779516), (3856, 3856, 9106128993399737311), (3857, 3857, 9197190283333734684), (3858, 3858, 9289162186167072031), (3859, 3859, 9382053808028742751), (3860, 3860, 9475874346109030179), (3861, 3861, 9570633089570120480), (3862, 3862, 9666339420465821685), (3863, 3863, 9763002814670479902), (3864, 3864, 9860632842817184701), (3865, 3865, 9959239171245356548), (3866, 3866, 10058831562957810114), (3867, 3867, 10159419878587388215), (3868, 3868, 10261014077373262097), (3869, 3869, 10363624218146994718), (3870, 3882, 10376293541461622784), (3883, 3883, 10286117180960982763), (3884, 3884, 10184274436595032439), (3885, 3885, 10083440036232705385), (3886, 3886, 9983603996270005332), (3887, 3887, 9884756431950500328), (3888, 3888, 9786887556386633989), (3889, 3889, 9689987679590726721), (3890, 3890, 9594047207515571011), (3891, 3891, 9499056641104525754), (3892, 3892, 9405006575351015598), (3893, 3893, 9311887698367342176), (3894, 3894, 9219690790462715026), (3895, 3895, 9128406723230410917), (3896, 3896, 9038026458643971205), (3897, 3897, 8948541048162347727), (3898, 3898, 8859941631843908641), (3899, 3899, 8772219437469216476), (3900, 3900, 8685365779672491561), (3901, 3901, 8599372059081674812), (3902, 3902, 8514229761467004765), (3903, 3903, 8429930456898024520), (3904, 3904, 8346465798908935168), (3905, 3905, 8263827523672213038), (3906, 3906, 8182007449180408948), (3907, 3907, 8100997474436048463), (3908, 3908, 8020789578649552934), (3909, 3909, 7941375820445101915), (3910, 3910, 7862748337074358332), (3911, 3911, 7784899343637978546), (3912, 3912, 7707821132314830244), (3913, 3913, 7631506071598841826), (3914, 3914, 7555946605543407748), (3915, 3915, 7481135253013274998), (3916, 3916, 7407064606943836632), (3917, 3917, 7333727333607759041), (3918, 3918, 7261116171888870338), (3919, 3919, 7189223932563237958), (3920, 3920, 7118043497587364315), (3921, 3921, 7047567819393430015), (3922, 3922, 6977789920191514866), (3923, 3923, 6908702891278727591), (3924, 3924, 6840299892355175832), (3925, 3925, 6772574150846708745), (3926, 3926, 6705518961234365094), (3927, 3927, 6639127684390460489), (3928, 3928, 6573393746921248009), (3929, 3929, 6508310640516087138), (3930, 3930, 6443871921303056572), (3931, 3931, 6380071209210947101), (3932, 3932, 6316902187337571387), (3933, 3933, 6254358601324328106), (3934, 3934, 6192434258736958521), (3935, 3935, 6131123028452434179), (3936, 3936, 6070418840051915029), (3937, 3937, 6010315683219717850), (3938, 3938, 5950807607148235495), (3939, 3939, 5891888719948748015), (3940, 3940, 5833553188068067342), (3941, 3941, 5775795235710957764), (3942, 3942, 5718609144268275014), (3943, 3943, 5661989251750767340), (3944, 3944, 5605929952228482515), (3945, 3945, 5550425695275725263), (3946, 3946, 5495470985421510161), (3947, 3947, 5441060381605455605), (3948, 3948, 5387188496639064955), (3949, 3949, 5333849996672341540), (3950, 3950, 5281039600665684693), (3951, 3951, 5228752079867014548), (3952, 3952, 5176982257294073810), (3953, 3953, 5125725007221855257), (3954, 3954, 5074975254675104215), (3955, 3955, 5024727974925845757), (3956, 3956, 4974978192995886888), (3957, 3957, 4925720983164244444), (3958, 3958, 4876951468479449945), (3959, 3959, 4828664820276683113), (3960, 3960, 4780856257699686251), (3961, 3961, 4733521047227412130), (3962, 3962, 4686654502205358544), (3963, 3963, 4640251982381543113), (3964, 3964, 4594308893447072389), (3965, 3965, 4548820686581259791), (3966, 3966, 4503782858001247318), (3967, 3967, 4459190948516086454), (3968, 3968, 4415040543085234112), (3969, 3969, 4371327270381419913), (3970, 3970, 4328046802357841498), (3971, 3971, 4285194853819645048), (3972, 3972, 4242767181999648562), (3973, 3973, 4200759586138265903), (3974, 3974, 4159167907067590003), (3975, 3975, 4117988026799594063), (3976, 3976, 4077215868118409963), (3977, 3977, 4036847394176643528), (3978, 3978, 3996878608095686661), (3979, 3979, 3957305552569986793), (3980, 3980, 3918124309475234449), (3981, 3981, 3879330999480430147), (3982, 3982, 3840921781663792225), (3983, 3983, 3802892853132467549), (3984, 3984, 3765240448646007475), (3985, 3985, 3727960840243571757), (3986, 3986, 3691050336874823522), (3987, 3987, 3654505284034478735), (3988, 3988, 3618322063400473995), (3989, 3989, 3582497092475716826), (3990, 3990, 3547026824233382996), (3991, 3991, 3511907746765725739), (3992, 3992, 3477136382936362118), (3993, 3993, 3442709290036002097), (3994, 3994, 3408623059441586235), (3995, 3995, 3374874316278798252), (3996, 3996, 3341459719087919061), (3997, 3997, 3308375959492989170), (3998, 3998, 3275619761874246703), (3999, 3999, 3243187883043808617), (4000, 4000, 3211077111924562987), (4001, 4001, 3179284269232240581), (4002, 4002, 3147806207160634239), (4003, 4003, 3116639809069934890), (4004, 4004, 3085781989178153356), (4005, 4005, 3055229692255597382), (4006, 4006, 3024979893322373646), (4007, 4007, 2995029597348884798), (4008, 4008, 2965375838959291879), (4009, 4009, 2936015682137912752), (4010, 4010, 2906946219938527477), (4011, 4011, 2878164574196561858), (4012, 4012, 2849667895244120652), (4013, 4013, 2821453361627842229), (4014, 4014, 2793518179829546762), (4015, 4015, 2765859583989650259), (4016, 4016, 2738474835633317088), (4017, 4017, 2711361223399323850), (4018, 4018, 2684516062771607772), (4019, 4019, 2657936695813473042), (4020, 4020, 2631620490904428754), (4021, 4021, 2605564842479632430), (4022, 4022, 2579767170771913297), (4023, 4023, 2554224921556349799), (4024, 4024, 2528935565897376039), (4025, 4025, 2503896599898392117), (4026, 4026, 2479105544453853582), (4027, 4027, 2454559945003815427), (4028, 4028, 2430257371290906364), (4029, 4029, 2406195417119709271), (4030, 4030, 2382371700118524031), (4031, 4031, 2358783861503489139), (4032, 4032, 2335429565845038752), (4033, 4033, 2312306500836672031), (4034, 4034, 2289412377066011912), (4035, 4035, 2266744927788130606), (4036, 4036, 2244301908701119412), (4037, 4037, 2222081097723880606), (4038, 4038, 2200080294776119412), (4039, 4039, 2178297321560514269), (4040, 4040, 2156730021347043831), (4041, 4041, 2135376258759449338), (4042, 4042, 2114233919563811225), (4043, 4043, 2093300910459219035), (4044, 4044, 2072575158870513896), (4045, 4045, 2052054612743083065), (4046, 4046, 2031737240339686203), (4047, 4047, 2011621030039293271), (4048, 4048, 1991703990137914129), (4049, 4049, 1971984148651400128), (4050, 4050, 1952459553120198147), (4051, 4051, 1933128270416037769), (4052, 4052, 1913988386550532445), (4053, 4053, 1895038006485675688), (4054, 4054, 1876275253946213552), (4055, 4055, 1857698271233874804), (4056, 4056, 1839305219043440400), (4057, 4057, 1821094276280634060), (4058, 4058, 1803063639881815901), (4059, 4059, 1785211524635461288), (4060, 4060, 1767536163005407216), (4061, 4061, 1750035804955848728), (4062, 4062, 1732708717778068048), (4063, 4063, 1715553185918879255), (4064, 4064, 1698567510810771540), (4065, 4065, 1681750010703734198), (4066, 4066, 1665099020498746731), (4067, 4067, 1648612891582917555), (4068, 4068, 1632289991666255005), (4069, 4069, 1616128704620054460), (4070, 4070, 1600127430316885604), (4071, 4071, 1584284584472163965), (4072, 4072, 1568598598487291054), (4073, 4073, 1553067919294347578), (4074, 4074, 1537691009202324335), (4075, 4075, 1522466345744875579), (4076, 4076, 1507392421529579781), (4077, 4077, 1492467744088692853), (4078, 4078, 1477690835731379062), (4079, 4079, 1463060233397405012), (4080, 4080, 1448574488512282190), (4081, 4081, 1434232166843843753), (4082, 4082, 1420031848360241339), (4083, 4083, 1405972127089347861), (4084, 4084, 1392051610979552337), (4085, 4085, 1378268921761933007), (4086, 4086, 1364622694813795057), (4087, 4087, 1351111579023559462), (4088, 4088, 1337734236656989566), (4089, 4089, 1324489343224742145), (4090, 4090, 1311375587351229847), (4091, 4091, 1298391670644782026), (4092, 4092, 1285536307569091115), (4093, 4093, 1272808225315931797), (4094, 4094, 1260206163679140393), (4095, 4095, 1247728874929841974), (4096, 4096, 1235375123692912845), (4097, 4097, 1223143686824666183), (4098, 4098, 1211033353291748696), (4099, 4099, 1199042924051236333), (4100, 4100, 1187171211931917161), (4101, 4101, 1175417041516749665), (4102, 4102, 1163779249026484817), (4103, 4103, 1152256682204440412), (4104, 4104, 1140848200202416250), (4105, 4105, 1129552673467738861), (4106, 4106, 1118368983631424615), (4107, 4107, 1107296023397450114), (4108, 4108, 1096332696433118925), (4109, 4109, 1085477917260513787), (4110, 4110, 1074730611149023551), (4111, 4111, 1064089714008934209), (4112, 4112, 1053554172286073475), (4113, 4113, 1043122942857498490), (4114, 4114, 1032794992928216326), (4115, 4115, 1022569299928927056), (4116, 4116, 1012444851414779263), (4117, 4117, 1002420644965127983), (4118, 4118, 992495688084285132), (4119, 4119, 982668998103252606), (4120, 4120, 972939602082428323), (4121, 4121, 963306536715275567), (4122, 4122, 953768848232946106), (4123, 4123, 944325592309847630), (4124, 4124, 934975833970146168), (4125, 4125, 925718647495194226), (4126, 4126, 916553116331875471), (4127, 4127, 907478333001856902), (4128, 4128, 898493399011739507), (4129, 4129, 889597424764098522), (4130, 4130, 880789529469404477), (4131, 4131, 872068841058816314), (4132, 4132, 863434496097837935), (4133, 4133, 854885639700829638), (4134, 4134, 846421425446365979), (4135, 4135, 838041015293431662), (4136, 4136, 829743579498447190), (4137, 4137, 821528296533116030), (4138, 4138, 813394353003085178), (4139, 4139, 805340943567411067), (4140, 4140, 797367270858822839), (4141, 4141, 789472545404775088), (4142, 4142, 781655985549282265), (4143, 4143, 773916817375526995), (4144, 4144, 766254274629234649), (4145, 4145, 758667598642806583), (4146, 4146, 751156038260204538), (4147, 4147, 743718849762578750), (4148, 4148, 736355296794632426), (4149, 4149, 729064650291715273), (4150, 4150, 721846188407638884), (4151, 4151, 714699196443206816), (4152, 4152, 707622966775452293), (4153, 4153, 700616798787576528), (4154, 4154, 693679998799580721), (4155, 4155, 686811879999584872), (4156, 4156, 680011762375826606), (4157, 4157, 673278972649333273), (4158, 4158, 666612844207260667), (4159, 4159, 660012717036891749), (4160, 4160, 653477937660288861), (4161, 4161, 647007859069592931), (4162, 4162, 640601840662963298), (4163, 4163, 634259248181151781), (4164, 4164, 627979453644704733), (4165, 4165, 621761835291786865), (4166, 4166, 615605777516620658), (4167, 4167, 609510670808535305), (4168, 4168, 603475911691619114), (4169, 4169, 597500902664969420), (4170, 4170, 591585052143534079), (4171, 4171, 585727774399538692), (4172, 4172, 579928489504493754), (4173, 4173, 574186623271775994), (4174, 4174, 568501607199778212), (4175, 4175, 562872878415621992), (4176, 4176, 557299879619427715), (4177, 4177, 551782059029136352), (4178, 4178, 546318870325877576), (4179, 4179, 540909772599878788), (4180, 4180, 535554230296909691), (4181, 4181, 530251713165257120), (4182, 4182, 525001696203224871), (4183, 4183, 519803659607153338), (4184, 4184, 514657088719953800), (4185, 4185, 509561473980152277), (4186, 4186, 504516310871437898), (4187, 4187, 499521099872710790), (4188, 4188, 494575346408624545), (4189, 4189, 489678560800618361), (4190, 4190, 484830258218434021), (4191, 4191, 480029958632112892), (4192, 4192, 475277186764468210), (4193, 4193, 470571472044027931), (4194, 4194, 465912348558443496), (4195, 4195, 461299355008359897), (4196, 4196, 456732034661742472), (4197, 4197, 452209935308655913), (4198, 4198, 447732609216491003), (4199, 4199, 443299613085634656), (4200, 4200, 438910508005578868), (4201, 4201, 434564859411464225), (4202, 4202, 430262237041053689), (4203, 4203, 426002214892132365), (4204, 4204, 421784371180329074), (4205, 4205, 417608288297355519), (4206, 4206, 413473552769658930), (4207, 4207, 409379755217484089), (4208, 4208, 405326490314340682), (4209, 4209, 401313356746871962), (4210, 4210, 397339957175120755), (4211, 4211, 393405898193188866), (4212, 4212, 389510790290286006), (4213, 4213, 385654247812164363), (4214, 4214, 381835888922935012), (4215, 4215, 378055335567262389), (4216, 4216, 374312213432933058), (4217, 4217, 370606151913795107), (4218, 4218, 366936784073064462), (4219, 4219, 363303746606994517), (4220, 4220, 359706679808905462), (4221, 4221, 356145227533569765), (4222, 4222, 352619037161950262), (4223, 4223, 349127759566287388), (4224, 4224, 345671049075532068), (4225, 4225, 342248563441120859), (4226, 4226, 338859963803089959), (4227, 4227, 335504914656524712), (4228, 4228, 332183083818341299), (4229, 4229, 328894142394397326), (4230, 4230, 325637764746928046), (4231, 4231, 322413628462304996), (4232, 4232, 319221414319113857), (4233, 4233, 316060806256548373), (4234, 4234, 312931491343117201), (4235, 4235, 309833159745660595), (4236, 4236, 306765504698673857), (4237, 4237, 303728222473934512), (4238, 4238, 300721012350430210), (4239, 4239, 297743576584584366), (4240, 4240, 294795620380776600), (4241, 4241, 291876851862155050), (4242, 4242, 288986982041737673), (4243, 4243, 286125724793799676), (4244, 4244, 283292796825544234), (4245, 4245, 280487917649053697), (4246, 4246, 277710809553518512), (4247, 4247, 274961197577741101), (4248, 4248, 272238809482911981), (4249, 4249, 269543375725655427), (4250, 4250, 266874629431342007), (4251, 4251, 264232306367665353), (4252, 4252, 261616144918480548), (4253, 4253, 259025886057901532), (4254, 4254, 256461273324654982), (4255, 4255, 253922052796688101), (4256, 4256, 251407973066027823), (4257, 4257, 248918785213888934), (4258, 4258, 246454242786028647), (4259, 4259, 244014101768345195), (4260, 4260, 241598120562718015), (4261, 4261, 239206059963087144), (4262, 4262, 236837683131769449), (4263, 4263, 234492755576009356), (4264, 4264, 232171045124761738), (4265, 4265, 229872321905704692), (4266, 4266, 227596358322479893), (4267, 4267, 225342929032158309), (4268, 4268, 223111810922929019), (4269, 4269, 220902783092008930), (4270, 4270, 218715626823771218), (4271, 4271, 216550125568090315), (4272, 4272, 214406064918901302), (4273, 4273, 212283232592971586), (4274, 4274, 210181418408882758), (4275, 4275, 208100414266220553), (4276, 4276, 206040014124970844), (4277, 4277, 204000013985119648), (4278, 4278, 201980211866455097), (4279, 4279, 199980407788569403), (4280, 4280, 198000403751058815), (4281, 4281, 196040003713919619), (4282, 4282, 194099013578138236), (4283, 4283, 192177241166473501), (4284, 4284, 190274496204429209), (4285, 4285, 188390590301415058), (4286, 4286, 186525336932094117), (4287, 4287, 184678551417914968), (4288, 4288, 182850050908826701), (4289, 4289, 181039654365174951), (4290, 4290, 179247182539777179), (4291, 4291, 177472457960175425), (4292, 4292, 175715304911064777), (4293, 4293, 173975549416895819), (4294, 4294, 172253019224649326), (4295, 4295, 170547543786781511), (4296, 4296, 168858954244338130), (4297, 4297, 167187083410235772), (4298, 4298, 165531765752708685), (4299, 4299, 163892837378919490), (4300, 4300, 162270136018732168), (4301, 4301, 160663501008645711), (4302, 4302, 159072773275886843), (4303, 4303, 157497795322660240), (4304, 4304, 155938411210554694), (4305, 4305, 154394466545103657), (4306, 4306, 152865808460498670), (4307, 4307, 151352285604454129), (4308, 4308, 149853748123221910), (4309, 4309, 148370047646754366), (4310, 4310, 146901037274014224), (4311, 4311, 145446571558429925), (4312, 4312, 144006506493494975), (4313, 4313, 142580699498509876), (4314, 4314, 141169009404465224), (4315, 4315, 139771296440064578), (4316, 4316, 138387422217885721), (4317, 4317, 137017249720678932), (4318, 4318, 135660643287800922), (4319, 4319, 134317468601783092), (4320, 4320, 132987592675032764), (4321, 4321, 131670883836666103), (4322, 4322, 130367211719471389), (4323, 4323, 129076447247001375), (4324, 4324, 127798462620793441), (4325, 4325, 126533131307716278), (4326, 4326, 125280328027441860), (4327, 4327, 124039928740041445), (4328, 4328, 122811810633704401), (4329, 4329, 121595852112578615), (4330, 4330, 120391932784731302), (4331, 4331, 119199933450229012), (4332, 4332, 118019736089335655), (4333, 4333, 116851223850827381), (4334, 4334, 115694281040423150), (4335, 4335, 114548793109329851), (4336, 4336, 113414646642900843), (4337, 4337, 112291729349406775), (4338, 4338, 111179930048917599), (4339, 4339, 110079138662294653), (4340, 4340, 108989246200291735), (4341, 4341, 107910144752764094), (4342, 4342, 106841727477984252), (4343, 4343, 105783888592063616), (4344, 4344, 104736523358478828), (4345, 4345, 103699528077701809), (4346, 4346, 102672800076932485), (4347, 4347, 101656237699933153), (4348, 4348, 100649740296963518), (4349, 4349, 99653208214815364), (4350, 4350, 98666542786945905), (4351, 4351, 97689646323708817), (4352, 7209, 96722422102681997)]

def glob1 : ℕ := 10376293541461622784

def runs2 : List (ℕ × ℕ × ℕ) := [(0, 3869, 0), (3870, 3882, 32794211686594758429), (3883, 3883, 32509209855876686263), (3884, 3884, 32187336490967016102), (3885, 3885, 31868649991056451586), (3886, 3886, 31553118803026189689), (3887, 3887, 31240711686164544247), (3888, 3888, 30931397709073806185), (3889, 3889, 30625146246607728896), (3890, 3890, 30321926976839335541), (3891, 3891, 30021709878058748060), (3892, 3892, 29724465225800740654), (3893, 3893, 29430163589901723419), (3894, 3894, 29138775831585864772), (3895, 3895, 28850273100580064130), (3896, 3896, 28564626832257489238), (3897, 3897, 28281808744809395285), (3898, 3898, 28001790836444945827), (3899, 3899, 27724545382618758245), (3900, 3900, 27450044933285899252), (3901, 3901, 27178262310184058665), (3902, 3902, 26909170604142632342), (3903, 3903, 26642743172418447863), (3904, 3904, 26378953636057869172), (3905, 3905, 26117775877285018982), (3906, 3906, 25859184036915860378), (3907, 3907, 25603152511797881562), (3908, 3908, 25349655952275130260), (3909, 3909, 25098669259678346792), (3910, 3910, 24850167583839947319), (3911, 3911, 24604126320633611207), (3912, 3912, 24360521109538228917), (3913, 3913, 24119327831225969225), (3914, 3914, 23880522605174226956), (3915, 3915, 23644081787301214808), (3916, 3916, 23409981967624965156), (3917, 3917, 23178199967945510056), (3918, 3918, 22948712839550009956), (3919, 3919, 22721497860940603917), (3920, 3920, 22496532535584756353), (3921, 3921, 22273794589687877577), (3922, 3922, 22053261969987997601), (3923, 3923, 21834912841572274853), (3924, 3924, 21618725585715123617), (3925, 3925, 21404678797737746155), (3926, 3926, 21192751284888857579), (3927, 3927, 20982922064246393643), (3928, 3928, 20775170360639993706), (3929, 3929, 20569475604594053174), (3930, 3930, 20365817430291141757), (3931, 3931, 20164175673555585898), (3932, 3932, 19964530369857015740), (3933, 3933, 19766861752333678951), (3934, 3934, 19571150249835325694), (3935, 3935, 19377376484985470984), (3936, 3936, 19185521272262842558), (3937, 3937, 18995565616101824315), (3938, 3938, 18807490709011707243), (3939, 3939, 18621277929714561627), (3940, 3940, 18436908841301546165), (3941, 3941, 18254365189407471450), (3942, 3942, 18073628900403437080), (3943, 3943, 17894682079607363445), (3944, 3944, 17717507009512241035), (3945, 3945, 17542086148031921817), (3946, 3946, 17368402126764279026), (3947, 3947, 17196437749271563393), (3948, 3948, 17026175989377785537), (3949, 3949, 16857599989482955977), (3950, 3950, 16690693058894015819), (3951, 3951, 16525438672172292890), (3952, 3952, 16361820467497319693), (3953, 3953, 16199822245046851182), (3954, 3954, 16039427965392921962), (3955, 3955, 15880621747913784121), (3956, 3956, 15723387869221568436), (3957, 3957, 15567710761605513303), (3958, 3958, 15413575011490607231), (3959, 3959, 15260965357911492308), (3960, 3960, 15109866691001477533), (3961, 3961, 14960264050496512409), (3962, 3962, 14812142624253972682), (3963, 3963, 14665487746786111566), (3964, 3964, 14520284897808031254), (3965, 3965, 14376519700800030944), (3966, 3966, 14234177921584189054), (3967, 3967, 14093245466915038667), (3968, 3968, 13953708383084196700), (3969, 3969, 13815552854538808614), (3970, 3970, 13678765202513671895), (3971, 3971, 13543331883676902866), (3972, 3972, 13409239488789012739), (3973, 3973, 13276474741375260137), (3974, 3974, 13145024496411148651), (3975, 3975, 13014875739020939258), (3976, 3976, 12886015583189048771), (3977, 3977, 12758431270484206704), (3978, 3978, 12632110168796244261), (3979, 3979, 12507039771085390357), (3980, 3980, 12383207694143950849), (3981, 3981, 12260601677370248365), (3982, 3982, 12139209581554701352), (3983, 3983, 12019019387677922131), (3984, 3984, 11900019195720714981), (3985, 3985, 11782197223485856417), (3986, 3986, 11665541805431541007), (3987, 3987, 11550041391516377234), (3988, 3988, 11435684546055819044), (3989, 3989, 11322459946589919845), (3990, 3990, 11210356382762296877), (3991, 3991, 11099362755210194927), (3992, 3992, 10989468074465539532), (3993, 3993, 10880661459866870824), (3994, 3994, 10772932138482050321), (3995, 3995, 10666269444041633981), (3996, 3996, 10560662815882805922), (3997, 3997, 10456101797903768239), (3998, 3998, 10352576037528483405), (3999, 3999, 10250075284681666738), (4000, 4000, 10148589390773927463), (4001, 4001, 10048108307696957884), (4002, 4002, 9948622086828671173), (4003, 4003, 9850120878048189280), (4004, 4004, 9752594928760583445), (4005, 4005, 9656034582931270738), (4006, 4006, 9560430280129971028), (4007, 4007, 9465772554584129730), (4008, 4008, 9372052034241712604), (4009, 4009, 9279259439843279806), (4010, 4010, 9187385584003247333), (4011, 4011, 9096421370300244884), (4012, 4012, 9006357792376480083), (4013, 4013, 8917185933046019884), (4014, 4014, 8828896963411900876), (4015, 4015, 8741482141991981065), (4016, 4016, 8654932813853446599), (4017, 4017, 8569240409755887722), (4018, 4018, 8484396445302859131), (4019, 4019, 8400392520101840723), (4020, 4020, 8317220316932515568), (4021, 4021, 8234871600923282740), (4022, 4022, 8153338218735923505), (4023, 4023, 8072612097758340104), (4024, 4024, 7992685245305287232), (4025, 4025, 7913549747827017061), (4026, 4026, 7835197770125759467), (4027, 4027, 7757621554579959868), (4028, 4028, 7680813420376197889), (4029, 4029, 7604765762748710781), (4030, 4030, 7529471052226446318), (4031, 4031, 7454921833887570612), (4032, 4032, 7381110726621357041), (4033, 4033, 7308030422397383209), (4034, 4034, 7235673685541963574), (4035, 4035, 7164033352021746113), (4036, 4036, 7093102328734402092), (4037, 4037, 7022873592806338705), (4038, 4038, 6953340190897365054), (4039, 4039, 6884495238512242628), (4040, 4040, 6816331919319052107), (4041, 4041, 6748843484474309017), (4042, 4042, 6682023251954761403), (4043, 4043, 6615864605895803369), (4044, 4044, 6550360995936438979), (4045, 4045, 6485505936570731662), (4046, 4046, 6421293006505674913), (4047, 4047, 6357715848025420706), (4048, 4048, 6294768166361802679), (4049, 4049, 6232443729071091762), (4050, 4050, 6170736365416922537), (4051, 4051, 6109639965759329244), (4052, 4052, 6049148480949830935), (4053, 4053, 5989255921732505876), (4054, 4054, 5929956358150995917), (4055, 4055, 5871243918961382096), (4056, 4056, 5813112791050873362), (4057, 4057, 5755557218862250854), (4058, 4058, 5698571503824010746), (4059, 4059, 5642150003786149254), (4060, 4060, 5586287132461533915), (4061, 4061, 5530977358872805856), (4062, 4062, 5476215206804758273), (4063, 4063, 5421995254262136904), (4064, 4064, 5368312132932808816), (4065, 4065, 5315160527656246353), (4066, 4066, 5262535175897273616), (4067, 4067, 5210430867225023383), (4068, 4068, 5158842442797052854), (4069, 4069, 5107764794848567182), (4070, 4070, 5057192866186700180), (4071, 4071, 5007121649689802159), (4072, 4072, 4957546187811685306), (4073, 4073, 4908461572090777531), (4074, 4074, 4859862942664136169), (4075, 4075, 4811745487786273434), (4076, 4076, 4764104443352745975), (4077, 4077, 4716935092428461361), (4078, 4078, 4670232764780654813), (4079, 4079, 4623992836416489914), (4080, 4080, 4578210729125237539), (4081, 4081, 4532881910024987662), (4082, 4082, 4488001891113849170), (4083, 4083, 4443566228825593238), (4084, 4084, 4399570523589696275), (4085, 4085, 4356010419395738886), (4086, 4086, 4312881603362117709), (4087, 4087, 4270179805309027435), (4088, 4088, 4227900797335670728), (4089, 4089, 4186040393401654186), (4090, 4090, 4144594448912528897), (4091, 4091, 4103558860309434551), (4092, 4092, 4062929564662806486), (4093, 4093, 4022702539270105432), (4094, 4094, 3982873801257530131), (4095, 4095, 3943439407185673397), (4096, 4096, 3904395452659082571), (4097, 4097, 3865738071939685714), (4098, 4098, 3827463437564045261), (4099, 4099, 3789567759964401249), (4100, 4100, 3752047287093466583), (4101, 4101, 3714898304052937211), (4102, 4102, 3678117132725680407), (4103, 4103, 3641700131411564759), (4104, 4104, 3605643694466895801), (4105, 4105, 3569944251947421585), (4106, 4106, 3534598269254872857), (4107, 4107, 3499602246787002829), (4108, 4108, 3464952719591091909), (4109, 4109, 3430646257020883079), (4110, 4110, 3396679462396913939), (4111, 4111, 3363048972670211821), (4112, 4112, 3329751458089318635), (4113, 4113, 3296783621870612510), (4114, 4114, 3264142199871893574), (4115, 4115, 3231823960269201558), (4116, 4116, 3199825703236833226), (4117, 4117, 3168144260630527947), (4118, 4118, 3136776495673790046), (4119, 4119, 3105719302647316877), (4120, 4120, 3074969606581501859), (4121, 4121, 3044524362951982038), (4122, 4122, 3014380557378200038), (4123, 4123, 2984535205324950533), (4124, 4124, 2954985351806881716), (4125, 4125, 2925728071095922491), (4126, 4126, 2896760466431606426), (4127, 4127, 2868079669734263789), (4128, 4128, 2839682841321053256), (4129, 4129, 2811567169624805204), (4130, 4130, 2783729870915648717), (4131, 4131, 2756168189025394769), (4132, 4132, 2728879395074648286), (4133, 4133, 2701860787202622066), (4134, 4134, 2675109690299625808), (4135, 4135, 2648623455742203770), (4136, 4136, 2622399461130894822), (4137, 4137, 2596435110030588932), (4138, 4138, 2570727831713454388), (4139, 4139, 2545275080904410286), (4140, 4140, 2520074337529119095), (4141, 4141, 2495123106464474351), (4142, 4142, 2470418917291558763), (4143, 4143, 2445959324051048281), (4144, 4144, 2421741905001037902), (4145, 4145, 2397764262377265249), (4146, 4146, 2374024022155708168), (4147, 4147, 2350518833817532839), (4148, 4148, 2327246370116369148), (4149, 4149, 2304204326847890245), (4150, 4150, 2281390422621673510), (4151, 4151, 2258802398635320307), (4152, 4152, 2236438018450812185), (4153, 4153, 2214295067773081371), (4154, 4154, 2192371354230773635), (4155, 4155, 2170664707159181817), (4156, 4156, 2149172977385328532), (4157, 4157, 2127894037015176764), (4158, 4158, 2106825779222947291), (4159, 4159, 2085966118042522070), (4160, 4160, 2065312988160912941), (4161, 4161, 2044864344713775189), (4162, 4162, 2024618163082945732), (4163, 4163, 2004572438695985873), (4164, 4164, 1984725186827708785), (4165, 4165, 1965074442403672065), (4166, 4166, 1945618259805615906), (4167, 4167, 1926354712678827629), (4168, 4168, 1907281893741413494), (4169, 4169, 1888397914595458905), (4170, 4170, 1869700905540058322), (4171, 4171, 1851189015386196358), (4172, 4172, 1832860411273461741), (4173, 4173, 1814713278488575981), (4174, 4174, 1796745820285718793), (4175, 4175, 1778956257708632469), (4176, 4176, 1761342829414487593), (4177, 4177, 1743903791499492666), (4178, 4178, 1726637417326230362), (4179, 4179, 1709541997352703329), (4180, 4180, 1692615838963072603), (4181, 4181, 1675857266300071884), (4182, 4182, 1659264620099081074), (4183, 4183, 1642836257523842647), (4184, 4184, 1626570552003804601), (4185, 4185, 1610465893073073862), (4186, 4186, 1594520686210964220), (4187, 4187, 1578733352684122990), (4188, 4188, 1563102329390220783), (4189, 4189, 1547626068703188894), (4190, 4190, 1532303038319989004), (4191, 4191, 1517131721108900004), (4192, 4192, 1502110614959306934), (4193, 4193, 1487238232632977163), (4194, 4194, 1472513101616809072), (4195, 4195, 1457933763977038685), (4196, 4196, 1443498776214889787), (4197, 4197, 1429206709123653255), (4198, 4198, 1415056147647181440), (4199, 4199, 1401045690739783604), (4200, 4200, 1387173951227508519), (4201, 4201, 1373439555670800514), (4202, 4202, 1359841144228515360), (4203, 4203, 1346377370523282535), (4204, 4204, 1333046901508200530), (4205, 4205, 1319848417334852010), (4206, 4206, 1306780611222625752), (4207, 4207, 1293842189329332428), (4208, 4208, 1281031870623101414), (4209, 4209, 1268348386755545954), (4210, 4210, 1255790481936184113), (4211, 4211, 1243356912808103082), (4212, 4212, 1231046448324854537), (4213, 4213, 1218857869628568848), (4214, 4214, 1206789969929276087), (4215, 4215, 1194841554385421869), (4216, 4216, 1183011439985566207), (4217, 4217, 1171298455431253670), (4218, 4218, 1159701441021043238), (4219, 4219, 1148219248535686374), (4220, 4220, 1136850741124441954), (4221, 4221, 1125594793192516787), (4222, 4222, 1114450290289620581), (4223, 4223, 1103416128999624337), (4224, 4224, 1092491216831311225), (4225, 4225, 1081674472110209134), (4226, 4226, 1070964823871494192), (4227, 4227, 1060361211753954645), (4228, 4228, 1049862585895004599), (4229, 4229, 1039467906826737227), (4230, 4230, 1029176145373007156), (4231, 4231, 1018986282547531837), (4232, 4232, 1008897309453001819), (4233, 4233, 998908227181189920), (4234, 4234, 989018046714049426), (4235, 4235, 979225788825791511), (4236, 4236, 969530483985932189), (4237, 4237, 959931172263299197), (4238, 4238, 950426903230989304), (4239, 4239, 941016735872266637), (4240, 4240, 931699738487392710), (4241, 4241, 922474988601378921), (4242, 4242, 913341572872652397), (4243, 4243, 904298587002626136), (4244, 4244, 895345135646164491), (4245, 4245, 886480332322935139), (4246, 4246, 877703299329638752), (4247, 4247, 869013167653107675), (4248, 4248, 860409076884265025), (4249, 4249, 851890175132935668), (4250, 4250, 843455618943500662), (4251, 4251, 835104573211386794), (4252, 4252, 826836211100382964), (4253, 4253, 818649713960775212), (4254, 4254, 810544271248292289), (4255, 4255, 802519080443853751), (4256, 4256, 794573346974112625), (4257, 4257, 786706284132784777), (4258, 4258, 778917113002757205), (4259, 4259, 771205062378967530), (4260, 4260, 763569368692047060), (4261, 4261, 756009275932719861), (4262, 4262, 748524035576950357), (4263, 4263, 741112906511832037), (4264, 4264, 733775154962209938), (4265, 4265, 726510054418029641), (4266, 4266, 719316885562405585), (4267, 4267, 712194936200401570), (4268, 4268, 705143501188516406), (4269, 4269, 698161882364867728), (4270, 4270, 691249388480067058), (4271, 4271, 684405335128779265), (4272, 4272, 677629044681959668), (4273, 4273, 670919846219762048), (4274, 4274, 664277075465110939), (4275, 4275, 657700074717931622), (4276, 4276, 651188192790031309), (4277, 4277, 644740784940625059), (4278, 4278, 638357212812500058), (4279, 4279, 632036844368811939), (4280, 4280, 625779053830506870), (4281, 4281, 619583221614363238), (4282, 4282, 613448734271646770), (4283, 4283, 607374984427373040), (4284, 4284, 601361370720171326), (4285, 4285, 595407297742743887), (4286, 4286, 589512175982914740), (4287, 4287, 583675421765262119), (4288, 4288, 577896457193328831), (4289, 4289, 572174710092404783), (4290, 4290, 566509613952876023), (4291, 4291, 560900607874134676), (4292, 4292, 555347136509044233), (4293, 4293, 549848650008954687), (4294, 4294, 544404603969262066), (4295, 4295, 539014459375506996), (4296, 4296, 533677682550006927), (4297, 4297, 528393745099016759), (4298, 4298, 523162123860412633), (4299, 4299, 517982300851893696), (4300, 4300, 512853763219696729), (4301, 4301, 507776003187818543), (4302, 4302, 502748518007741132), (4303, 4303, 497770809908654586), (4304, 4304, 492842386048172857), (4305, 4305, 487962758463537483), (4306, 4306, 483131444023304438), (4307, 4307, 478347964379509345), (4308, 4308, 473611845920306282), (4309, 4309, 468922619723075527), (4310, 4310, 464279821507995571), (4311, 4311, 459682991592074823), (4312, 4312, 455131674843638438), (4313, 4313, 450625420637265781), (4314, 4314, 446163782809174040), (4315, 4315, 441746319613043604), (4316, 4316, 437372593676280796), (4317, 4317, 433042171956713660), (4318, 4318, 428754625699716495), (4319, 4319, 424509530395758906), (4320, 4320, 420306465738375154), (4321, 4321, 416145015582549658), (4322, 4322, 412024767903514512), (4323, 4323, 407945314755954963), (4324, 4324, 403906252233618775), (4325, 4325, 399907180429325520), (4326, 4326, 395947703395371802), (4327, 4327, 392027429104328517), (4328, 4328, 388145969410226254), (4329, 4329, 384302940010125004), (4330, 4330, 380497960406064360), (4331, 4331, 376730653867390456), (4332, 4332, 373000647393455897), (4333, 4333, 369307571676689007), (4334, 4334, 365651061066028720), (4335, 4335, 362030753530721505), (4336, 4336, 358446290624476737), (4337, 4337, 354897317449976968), (4338, 4338, 351383482623739572), (4339, 4339, 347904438241326309), (4340, 4340, 344459839842897335), (4341, 4341, 341049346379106273), (4342, 4342, 337672620177332943), (4343, 4343, 334329326908250439), (4344, 4344, 331019135552723207), (4345, 4345, 327741718369032878), (4346, 4346, 324496750860428592), (4347, 4347, 321283911742998606), (4348, 4348, 318102882913860006), (4349, 4349, 314953349419663372), (4350, 4350, 311834999425409280), (4351, 4351, 308747524183573544), (4352, 7209, 305690618003538163)]

def glob2 : ℕ := 32794211686594758429

def runs3 : List (ℕ × ℕ × ℕ) := [(0, 3869, 0), (3870, 3870, 160313529778915594), (3871, 3871, 341367297540605059), (3872, 3872, 520628453740297599), (3873, 3873, 698114747007319916), (3874, 3874, 873843750241995478), (3875, 3875, 1047832862355535638), (3876, 3876, 1220099309992704113), (3877, 3877, 1390660149237425375), (3878, 3878, 1559532267301505833), (3879, 3879, 1726732384196634999), (3880, 3880, 1892277054389832193), (3881, 3881, 2056182668442502683), (3882, 3882, 2218465454633265543), (3883, 3883, 2379141480564713920), (3884, 3884, 2538226654754266769), (3885, 3885, 2695736728209269589), (3886, 3886, 2851687295986500104), (3887, 3887, 3006093798736233288), (3888, 3888, 3158971524231018618), (3889, 3889, 3310335608879320924), (3890, 3890, 3460201039224174694), (3891, 3891, 3608582653427000208), (3892, 3892, 3755495142736728440), (3893, 3893, 3900953052944380154), (3894, 3894, 4044970785823243238), (3895, 3895, 4187562600554790846), (3896, 3896, 4328742615140481546), (3897, 3897, 4468524807799581250), (3898, 3898, 4606923018353145313), (3899, 3899, 4743950949594297851), (3900, 3900, 4879622168644943928), (3901, 3901, 5013950108299048954), (3902, 3902, 5146948068352618288), (3903, 3903, 5278629216920508717), (3904, 3904, 5409006591740202211), (3905, 3905, 5538093101462671017), (3906, 3906, 5665901526930461914), (3907, 3907, 5792444522443126168), (3908, 3908, 5917734617010120479), (3909, 3909, 6041784215591302966), (3910, 3910, 6164605600325147012), (3911, 3911, 6286210931744794582), (3912, 3912, 6406612249982069404), (3913, 3913, 6525821475959569228), (3914, 3914, 6643850412570955193), (3915, 3915, 6760710745849555157), (3916, 3916, 6876414046125396706), (3917, 3917, 6990971769170784379), (3918, 3918, 7104395257334534549), (3919, 3919, 7216695740664980263), (3920, 3920, 7327884338021857207), (3921, 3921, 7437972058177180914), (3922, 3922, 7546969800905224188), (3923, 3923, 7654888358061702678), (3924, 3924, 7761738414652275439), (3925, 3925, 7867530549890466293), (3926, 3926, 7972275238245110702), (3927, 3927, 8075982850477431899), (3928, 3928, 8178663654667848926), (3929, 3929, 8280327817232618259), (3930, 3930, 8380985403930409679), (3931, 3931, 8480646380858916035), (3932, 3932, 8579320615441595595), (3933, 3933, 8677017877404644664), (3934, 3934, 8773747839744297208), (3935, 3935, 8869520079684547252), (3936, 3936, 8964344079625388879), (3937, 3937, 9058229228081667718), (3938, 3938, 9151184820612636866), (3939, 3939, 9243220060742309289), (3940, 3940, 9334344060870697827), (3941, 3941, 9424565843176033013), (3942, 3942, 9513894340508048049), (3943, 3943, 9602338397272419371), (3944, 3944, 9689906770306450384), (3945, 3945, 9776608129746085049), (3946, 3946, 9862451059884337194), (3947, 3947, 9947444060021220505), (3948, 3948, 10031595545305263387), (3949, 3949, 10114913847566691983), (3950, 3950, 10197407216142363861), (3951, 3951, 10279083818692534037), (3952, 3952, 10359951742009534211), (3953, 3953, 10440018992818445274), (3954, 3954, 10519293498569842367), (3955, 3955, 10597783108224690973), (3956, 3956, 10675495593031471771), (3957, 3957, 10752438647295611176), (3958, 3958, 10828619889141293755), (3959, 3959, 10904046861265731951), (3960, 3960, 10978727031685967789), (3961, 3961, 11052667794478280501), (3962, 3962, 11125876470510273284), (3963, 3963, 11198360308165711683), (3964, 3964, 11270126484062185346), (3965, 3965, 11341182103761664220), (3966, 3966, 11411534202474019541), (3967, 3967, 11481189745753579264), (3968, 3968, 11550155630188786911), (3969, 3969, 11618438684085032106), (3970, 3970, 11686045668140720418), (3971, 3971, 11752983276116649440), (3972, 3972, 11819258135498757382), (3973, 3973, 11884876808154309801), (3974, 3974, 11949845790981589423), (3975, 3975, 12014171516553153405), (3976, 3976, 12077860353752721704), (3977, 3977, 12140918608405759624), (3978, 3978, 12203352523903816970), (3979, 3979, 12265168281822685630), (3980, 3980, 12326372002534436778), (3981, 3981, 12386969745813398311), (3982, 3982, 12446967511436132503), (3983, 3983, 12506371239775473286), (3984, 3984, 12565186812388681982), (3985, 3985, 12623420052599779701), (3986, 3986, 12681076726076114077), (3987, 3987, 12738162541399217419), (3988, 3988, 12794683150630012807), (3989, 3989, 12850644149868424082), (3990, 3990, 12906051079807445147), (3991, 3991, 12960909426281723429), (3992, 3992, 13015224620810711827), (3993, 3993, 13069002041136442914), (3994, 3994, 13122247011755978643), (3995, 3995, 13174964804448588277), (3996, 3996, 13227160638797706726), (3997, 3997, 13278839682707724992), (3998, 3998, 13330007052915663869), (3999, 3999, 13380667815497781570), (4000, 4000, 13430826986371165432), (4001, 4001, 13480489531790357374), (4002, 4002, 13529660368839062268), (4003, 4003, 13578344365916987905), (4004, 4004, 13626546343221864773), (4005, 4005, 13674271073226693356), (4006, 4006, 13721523281152266210), (4007, 4007, 13768307645435011610), (4008, 4008, 13814628798190205075), (4009, 4009, 13860491325670594645), (4010, 4010, 13905899768720485308), (4011, 4011, 13950858623225327549), (4012, 4012, 13995372340556854520), (4013, 4013, 14039445328013811917), (4014, 4014, 14083081949258324191), (4015, 4015, 14126286524747940304), (4016, 4016, 14169063332163401802), (4017, 4017, 14211416606832175563), (4018, 4018, 14253350542147793148), (4019, 4019, 14294869289985038281), (4020, 4020, 14335976961111023561), (4021, 4021, 14376677625592197107), (4022, 4022, 14416975313197319428), (4023, 4023, 14456874013796450440), (4024, 4024, 14496377677755986095), (4025, 4025, 14535490216329783774), (4026, 4026, 14574215502046415139), (4027, 4027, 14612557369092584807), (4028, 4028, 14650519613692752795), (4029, 4029, 14688105994484998328), (4030, 4030, 14725320232893162222), (4031, 4031, 14762166013495304691), (4032, 4032, 14798646984388515057), (4033, 4033, 14834766757550109478), (4034, 4034, 14870528909195252470), (4035, 4035, 14905936980131037610), (4036, 4036, 14940994476107062501), (4037, 4037, 14975704868162532690), (4038, 4038, 15010071592969928917), (4039, 4039, 15044098053175271716), (4040, 4040, 15077787617735017062), (4041, 4041, 15111143622249616414), (4042, 4042, 15144169369293774188), (4043, 4043, 15176868128743435351), (4044, 4044, 15209243138099535512), (4045, 4045, 15241297602808545572), (4046, 4046, 15273034696579842662), (4047, 4047, 15304457561699938790), (4048, 4048, 15335569309343598323), (4049, 4049, 15366373019881875088), (4050, 4050, 15396871743187099608), (4051, 4051, 15427068498934846658), (4052, 4052, 15456966276902913043), (4053, 4053, 15486568037267335208), (4054, 4054, 15515876710895475964), (4055, 4055, 15544895199636209386), (4056, 4056, 15573626376607232577), (4057, 4057, 15602073086479532765), (4058, 4058, 15630238145759037902), (4059, 4059, 15658124343065478632), (4060, 4060, 15685734439408489256), (4061, 4061, 15713071168460975022), (4062, 4062, 15740137236829772810), (4063, 4063, 15766935324323632006), (4064, 4064, 15793468084218542101), (4065, 4065, 15819738143520433284), (4066, 4066, 15845748103225276040), (4067, 4067, 15871500538576605501), (4068, 4068, 15896997999320496057), (4069, 4069, 15922243009958011459), (4070, 4070, 15947238069995155421), (4071, 4071, 15971985654190347462), (4072, 4072, 15996488212799448493), (4073, 4073, 16020748171818360405), (4074, 4074, 16044767933223223685), (4075, 4075, 16068549875208236833), (4076, 4076, 16092096352421121137), (4077, 4077, 16115409696196254112), (4078, 4078, 16138492214785494682), (4079, 4079, 16161346193586722968), (4080, 4080, 16183973895370117311), (4081, 4081, 16206377560502190918), (4082, 4082, 16228559407167610331), (4083, 4083, 16250521631588817671), (4084, 4084, 16272266408243478403), (4085, 4085, 16293795890079776157), (4086, 4086, 16315112208729575914), (4087, 4087, 16336217474719476664), (4088, 4088, 16357113777679774436), (4089, 4089, 16377803186551356388), (4090, 4090, 16398287749790546440), (4091, 4091, 16418569495571922729), (4092, 4092, 16438650431989126975), (4093, 4093, 16458532547253685635), (4094, 4094, 16478217809891862526), (4095, 4095, 16497708168939562418), (4096, 4096, 16517005554135304885), (4097, 4097, 16536111876111287526), (4098, 4098, 16555029026582557467), (4099, 4099, 16573758878534309885), (4100, 4100, 16592303286407332080), (4101, 4101, 16610664086281611481), (4102, 4102, 16628843096058125740), (4103, 4103, 16646842115638832927), (4104, 4104, 16664662927104879647), (4105, 4105, 16682307294893044716), (4106, 4106, 16699776965970435873), (4107, 4107, 16717073670007456821), (4108, 4108, 16734199119549061720), (4109, 4109, 16751155010184314095), (4110, 4110, 16767943020714266942), (4111, 4111, 16784564813318180652), (4112, 4112, 16801022033718095216), (4113, 4113, 16817316311341773002), (4114, 4114, 16833449259484028236), (4115, 4115, 16849422475466459160), (4116, 4116, 16865237540795598690), (4117, 4117, 16880896021319499214), (4118, 4118, 16896399467382767059), (4119, 4119, 16911749413980061956), (4120, 4120, 16926947380908076705), (4121, 4121, 16941994872916012100), (4122, 4122, 16956893379854561996), (4123, 4123, 16971644376823423280), (4124, 4124, 16986249324317345342), (4125, 4125, 17000709668370733523), (4126, 4126, 17015026840700820831), (4127, 4127, 17029202258849422126), (4128, 4128, 17043237326323284794), (4129, 4129, 17057133432733049812), (4130, 4130, 17070891953930836959), (4131, 4131, 17084514252146467797), (4132, 4132, 17098001676122339914), (4133, 4133, 17111355561246965773), (4134, 4134, 17124577229687189395), (4135, 4135, 17137667990519093971), (4136, 4136, 17150629139857613354), (4137, 4137, 17163461960984860267), (4138, 4138, 17176167724477183944), (4139, 4139, 17188747688330969763), (4140, 4140, 17201203098087193345), (4141, 4141, 17213535186954741447), (4142, 4142, 17225745175932511845), (4143, 4143, 17237834273930304318), (4144, 4144, 17249803677888514687), (4145, 4145, 17261654572896643766), (4146, 4146, 17273388132310632952), (4147, 4147, 17285005517869038087), (4148, 4148, 17296507879808053073), (4149, 4149, 17307896356975394643), (4150, 4150, 17319172076943059563), (4151, 4151, 17330336156118965425), (4152, 4152, 17341389699857486080), (4153, 4153, 17352333802568892670), (4154, 4154, 17363169547827711075), (4155, 4155, 17373898008480006526), (4156, 4156, 17384520246749605983), (4157, 4157, 17395037314343268811), (4158, 4158, 17405450252554816165), (4159, 4159, 17415760092368229387), (4160, 4160, 17425967854559727627), (4161, 4161, 17436074549798834796), (4162, 4162, 17446081178748445853), (4163, 4163, 17455988732163902346), (4164, 4164, 17465798190991086992), (4165, 4165, 17475510526463547038), (4166, 4166, 17485126700198655994), (4167, 4167, 17494647664292823278), (4168, 4168, 17504074361415761182), (4169, 4169, 17513407724903818513), (4170, 4170, 17522648678852390128), (4171, 4171, 17531798138207411529), (4172, 4172, 17540857008855947569), (4173, 4173, 17549826187715884243), (4174, 4174, 17558706562824732435), (4175, 4175, 17567499013427552427), (4176, 4176, 17576204410064007864), (4177, 4177, 17584823614654557802), (4178, 4178, 17593357480585795365), (4179, 4179, 17601806852794941466), (4180, 4180, 17610172567853501963), (4181, 4181, 17618455454050096514), (4182, 4182, 17626656331472467356), (4183, 4183, 17634776012088676111), (4184, 4184, 17642815299827496661), (4185, 4185, 17650774990658012057), (4186, 4186, 17658655872668423339), (4187, 4187, 17666458726144078075), (4188, 4188, 17674184323644726328), (4189, 4189, 17681833430081011727), (4190, 4190, 17689406802790205191), (4191, 4191, 17696905191611188819), (4192, 4192, 17704329338958697361), (4193, 4193, 17711679979896824631), (4194, 4194, 17718957842211802126), (4195, 4195, 17726163646484057072), (4196, 4196, 17733298106159557018), (4197, 4197, 17740361927620448053), (4198, 4198, 17747355810254993633), (4199, 4199, 17754280446526820940), (4200, 4200, 17761136522043481640), (4201, 4201, 17767924715624333818), (4202, 4202, 17774645699367751816), (4203, 4203, 17781300138717670625), (4204, 4204, 17787888692529471427), (4205, 4205, 17794412013135214796), (4206, 4206, 17800870746408228031), (4207, 4207, 17807265531827053017), (4208, 4208, 17813597002538760924), (4209, 4209, 17819865785421640040), (4210, 4210, 17826072501147262927), (4211, 4211, 17832217764241939053), (4212, 4212, 17838302183147558979), (4213, 4213, 17844326360281836134), (4214, 4214, 17850290892097952129), (4215, 4215, 17856196369143611530), (4216, 4216, 17862043376119511927), (4217, 4217, 17867832491937235092), (4218, 4218, 17873564289776564958), (4219, 4219, 17879239337142238094), (4220, 4220, 17884858195920132287), (4221, 4221, 17890421422432898815), (4222, 4222, 17895929567495043892), (4223, 4223, 17901383176467464761), (4224, 4224, 17906782789311445819), (4225, 4225, 17912128940642120133), (4226, 4226, 17917422159781401633), (4227, 4227, 17922662970810393217), (4228, 4228, 17927851892621275974), (4229, 4229, 17932989438968684643), (4230, 4230, 17938076118520574415), (4231, 4231, 17943112434908584091), (4232, 4232, 17948098886777900601), (4233, 4233, 17953035967836629819), (4234, 4234, 17957924166904678550), (4235, 4235, 17962763967962152540), (4236, 4236, 17967555850197275303), (4237, 4237, 17972300288053832495), (4238, 4238, 17976997751278146545), (4239, 4239, 17981648704965586200), (4240, 4240, 17986253609606615560), (4241, 4241, 17990812921132387204), (4242, 4242, 17995327090959883882), (4243, 4243, 17999796566036613265), (4244, 4244, 18004221788884860179), (4245, 4245, 18008603197645500689), (4246, 4246, 18012941226121382381), (4247, 4247, 18017236303820275146), (4248, 4248, 18021488855997396695), (4249, 4249, 18025699303697517041), (4250, 4250, 18029868063796646096), (4251, 4251, 18033995549043308527), (4252, 4252, 18038082168099409944), (4253, 4253, 18042128325580698475), (4254, 4254, 18046134422096825734), (4255, 4255, 18050100854291011139), (4256, 4256, 18054028014879313520), (4257, 4257, 18057916292689513897), (4258, 4258, 18061766072699613280), (4259, 4259, 18065577736075949303), (4260, 4260, 18069351660210935465), (4261, 4261, 18073088218760426714), (4262, 4262, 18076787781680715079), (4263, 4263, 18080450715265159005), (4264, 4264, 18084077382180450021), (4265, 4265, 18087668141502520334), (4266, 4266, 18091223348752094901), (4267, 4267, 18094743355929891502), (4268, 4268, 18098228511551472296), (4269, 4269, 18101679160681750309), (4270, 4270, 18105095644969154282), (4271, 4271, 18108478302679455246), (4272, 4272, 18111827468729258180), (4273, 4273, 18115143474719162075), (4274, 4274, 18118426648966591675), (4275, 4275, 18121677316538304150), (4276, 4276, 18124895799282573926), (4277, 4277, 18128082415861058854), (4278, 4278, 18131237481780350862), (4279, 4279, 18134361309423214235), (4280, 4280, 18137454208079514606), (4281, 4281, 18140516483976841705), (4282, 4282, 18143548440310828932), (4283, 4283, 18146550377275172720), (4284, 4284, 18149522592091354690), (4285, 4285, 18152465379038069511), (4286, 4286, 18155379029480361413), (4287, 4287, 18158263831898472207), (4288, 4288, 18161120071916403686), (4289, 4289, 18163948032330197230), (4290, 4290, 18166747993135933412), (4291, 4291, 18169520231557454384), (4292, 4292, 18172265022073811783), (4293, 4293, 18174982636446442870), (4294, 4294, 18177673343746077610), (4295, 4295, 18180337410379379333), (4296, 4296, 18182975100115321633), (4297, 4297, 18185586674111304108), (4298, 4298, 18188172390939009529), (4299, 4299, 18190732506610004995), (4300, 4300, 18193267274601089615), (4301, 4301, 18195776945879391219), (4302, 4302, 18198261768927214589), (4303, 4303, 18200721989766643669), (4304, 4304, 18203157851983900183), (4305, 4305, 18205569596753461089), (4306, 4306, 18207957462861937232), (4307, 4307, 18210321686731715593), (4308, 4308, 18212662502444367434), (4309, 4309, 18214980141763824704), (4310, 4310, 18217274834159326950), (4311, 4311, 18219546806828141056), (4312, 4312, 18221796284718056012), (4313, 4313, 18224023490549654978), (4314, 4314, 18226228644838366826), (4315, 4315, 18228411965916299349), (4316, 4316, 18230573669953856302), (4317, 4317, 18232713970981140414), (4318, 4318, 18234833080909144485), (4319, 4319, 18236931209550732675), (4320, 4320, 18239008564641414050), (4321, 4321, 18241065351859910462), (4322, 4322, 18243101774848520770), (4323, 4323, 18245118035233283452), (4324, 4324, 18247114332643939572), (4325, 4325, 18249090864733698108), (4326, 4326, 18251047827198805568), (4327, 4327, 18252985413797921866), (4328, 4328, 18254903816371304338), (4329, 4329, 18256803224859801836), (4330, 4330, 18258683827323660745), (4331, 4331, 18260545809961144813), (4332, 4332, 18262389357126970623), (4333, 4333, 18264214651350560534), (4334, 4334, 18266021873354114901), (4335, 4335, 18267811202070505363), (4336, 4336, 18269582814660990970), (4337, 4337, 18271336886532758897), (4338, 4338, 18273073591356291498), (4339, 4339, 18274793101082561400), (4340, 4340, 18276495585960056353), (4341, 4341, 18278181214551635514), (4342, 4342, 18279850153751218842), (4343, 4343, 18281502568800311245), (4344, 4344, 18283138623304363130), (4345, 4345, 18284758479248968957), (4346, 4346, 18286362297015905419), (4347, 4347, 18287950235399010827), (4348, 4348, 18289522451619907270), (4349, 4349, 18291079101343567115), (4350, 4350, 18292620338693725378), (4351, 4351, 18294146316268139499), (4352, 7209, 18446744073709483530)]

def glob3 : ℕ := 18446744073709551616

def runs4 : List (ℕ × ℕ × ℕ) := [(0, 3000, 186405010695675589627), (3001, 3001, 186405939963010406700), (3002, 3002, 186406878529287802304), (3003, 3003, 186407826487623262050), (3004, 3004, 186408783932065961673), (3005, 3005, 186409750957608154935), (3006, 3006, 186410727660194656434), (3007, 3007, 186411714136732420290), (3008, 3008, 186412710485100215688), (3009, 3009, 186413716804158400259), (3010, 3010, 186414733193758792314), (3011, 3011, 186415759754754642932), (3012, 3012, 186416796589010708922), (3013, 3013, 186417843799413427705), (3014, 3014, 186418901489881195135), (3015, 3015, 186419969765374747338), (3016, 3016, 186421048731907647618), (3017, 3017, 186422138496556879509), (3018, 3018, 186423239167473547066), (3019, 3019, 186424350853893683481), (3020, 3020, 186425473666149169154), (3021, 3021, 186426607715678760319), (3022, 3022, 186427753115039229372), (3023, 3023, 186428909977916618047), (3024, 3024, 186430078419137604585), (3025, 3025, 186431258554680986084), (3026, 3026, 186432450501689277194), (3027, 3027, 186433654378480426364), (3028, 3028, 186434870304559650843), (3029, 3029, 186436098400631391652), (3030, 3030, 186437338788611389765), (3031, 3031, 186438591591638884744), (3032, 3032, 186439856934088937079), (3033, 3033, 186441134941584875514), (3034, 3034, 186442425741010870639), (3035, 3035, 186443729460524636052), (3036, 3036, 186445046229570258394), (3037, 3037, 186446376178891157594), (3038, 3038, 186447719440543178659), (3039, 3039, 186449076147907816364), (3040, 3040, 186450446435705574208), (3041, 3041, 186451830440009459032), (3042, 3042, 186453228298258612677), (3043, 3043, 186454640149272082116), (3044, 3044, 186456066133262729467), (3045, 3045, 186457506391851283354), (3046, 3046, 186458961068080533050), (3047, 3047, 186460430306429666892), (3048, 3048, 186461914252828756454), (3049, 3049, 186463413054673387980), (3050, 3050, 186464926860839442602), (3051, 3051, 186466455821698026877), (3052, 3052, 186468000089130555201), (3053, 3053, 186469559816543985672), (3054, 3054, 186471135158886210978), (3055, 3055, 186472726272661605931), (3056, 3056, 186474333315946733254), (3057, 3057, 186475956448406209267), (3058, 3058, 186477595831308731130), (3059, 3059, 186479251627543267308), (3060, 3060, 186480924001635412962), (3061, 3061, 186482613119763911961), (3062, 3062, 186484319149777347263), (3063, 3063, 186486042261211001391), (3064, 3064, 186487782625303888784), (3065, 3065, 186489540415015961804), (3066, 3066, 186491315805045492198), (3067, 3067, 186493108971846629843), (3068, 3068, 186494920093647140621), (3069, 3069, 186496749350466325272), (3070, 3070, 186498596924133121122), (3071, 3071, 186500462998304388587), (3072, 3072, 186502347758483384367), (3073, 3073, 186504251392038423284), (3074, 3074, 186506174088221730726), (3075, 3075, 186508116038188487682), (3076, 3076, 186510077435016070378), (3077, 3077, 186512058473723486547), (3078, 3078, 186514059351291010371), (3079, 3079, 186516080266680018192), (3080, 3080, 186518121420853027064), (3081, 3081, 186520183016793938286), (3082, 3082, 186522265259528488040), (3083, 3083, 186524368356144907314), (3084, 3084, 186526492515814793294), (3085, 3085, 186528637949814194438), (3086, 3086, 186530804871544911462), (3087, 3087, 186532993496556016514), (3088, 3088, 186535204042565592815), (3089, 3089, 186537436729482697068), (3090, 3090, 186539691779429546992), (3091, 3091, 186541969416763936325), (3092, 3092, 186544269868101879695), (3093, 3093, 186546593362340489768), (3094, 3094, 186548940130681089109), (3095, 3095, 186551310406652559239), (3096, 3096, 186553704426134929361), (3097, 3097, 186556122427383207299), (3098, 3098, 186558564651051455175), (3099, 3099, 186561031340217112430), (3100, 3100, 186563522740405568769), (3101, 3101, 186566039099614989681), (3102, 3102, 186568580668341397190), (3103, 3103, 186571147699604008535), (3104, 3104, 186573740448970835501), (3105, 3105, 186576359174584547153), (3106, 3106, 186579004137188598753), (3107, 3107, 186581675600153629686), (3108, 3108, 186584373829504133231), (3109, 3109, 186587099093945401053), (3110, 3110, 186589851664890745336), (3111, 3111, 186592631816489001489), (3112, 3112, 186595439825652314408), (3113, 3113, 186598275972084211288), (3114, 3114, 186601140538307964043), (3115, 3115, 186604033809695244403), (3116, 3116, 186606956074495074791), (3117, 3117, 186609907623863078133), (3118, 3118, 186612888751891029779), (3119, 3119, 186615899755636714745), (3120, 3120, 186618940935154093542), (3121, 3121, 186622012593523779858), (3122, 3122, 186625115036883833436), (3123, 3123, 186628248574460871509), (3124, 3124, 186631413518601502179), (3125, 3125, 186634610184804083196), (3126, 3126, 186637838891750809599), (3127, 3127, 186641099961340133754), (3128, 3128, 186644393718719521322), (3129, 3129, 186647720492318546780), (3130, 3130, 186651080613882332111), (3131, 3131, 186654474418505332354), (3132, 3132, 186657902244665471737), (3133, 3133, 186661364434258634141), (3134, 3134, 186664861332633511722), (3135, 3135, 186668393288626815524), (3136, 3136, 186671960654598851986), (3137, 3137, 186675563786469469271), (3138, 3138, 186679203043754377419), (3139, 3139, 186682878789601846325), (3140, 3140, 186686591390829785643), (3141, 3141, 186690341217963210723), (3142, 3142, 186694128645272098755), (3143, 3143, 186697954050809639328), (3144, 3144, 186701817816450883689), (3145, 3145, 186705720327931796998), (3146, 3146, 186709661974888717945), (3147, 3147, 186713643150898230162), (3148, 3148, 186717664253517449870), (3149, 3149, 186721725684324734299), (3150, 3150, 186725827848960815442), (3151, 3151, 186729971157170363771), (3152, 3152, 186734156022843986583), (3153, 3153, 186738382864060665718), (3154, 3154, 186742652103130639433), (3155, 3155, 186746964166638733269), (3156, 3156, 186751319485488144813), (3157, 3157, 186755718494944687319), (3158, 3158, 186760161634681497185), (3159, 3159, 186764649348824210383), (3160, 3160, 186769182085996612948), (3161, 3161, 186773760299366770743), (3162, 3162, 186778384446693643741), (3163, 3163, 186783054990374190142), (3164, 3164, 186787772397490965710), (3165, 3165, 186792537139860223762), (3166, 3166, 186797349694080521330), (3167, 3167, 186802210541581837053), (3168, 3168, 186807120168675206453), (3169, 3169, 186812079066602880289), (3170, 3170, 186817087731589011764), (3171, 3171, 186822146664890878434), (3172, 3172, 186827256372850644726), (3173, 3173, 186832417366947671045), (3174, 3174, 186837630163851375528), (3175, 3175, 186842895285474654576), (3176, 3176, 186848213259027868352), (3177, 3177, 186853584617073397529), (3178, 3178, 186859009897580777645), (3179, 3179, 186864489643982417468), (3180, 3180, 186870024405229907900), (3181, 3181, 186875614735850927998), (3182, 3182, 186881261196006754754), (3183, 3183, 186886964351550383413), (3184, 3184, 186892724774085265119), (3185, 3185, 186898543041024668822), (3186, 3186, 186904419735651674429), (3187, 3187, 186910355447179804271), (3188, 3188, 186916350770814300062), (3189, 3189, 186922406307814052596), (3190, 3190, 186928522665554191518), (3191, 3191, 186934700457589342607), (3192, 3192, 186940940303717560088), (3193, 3193, 186947242830044941591), (3194, 3194, 186953608669050933465), (3195, 3195, 186960038459654334237), (3196, 3196, 186966532847280004145), (3197, 3197, 186973092483926288713), (3198, 3198, 186979718028233164478), (3199, 3199, 186986410145551115070), (3200, 3200, 186993169508010745934), (3201, 3201, 186999996794593146107), (3202, 3202, 187006892691201005551), (3203, 3203, 187013857890730496656), (3204, 3204, 187020893093143928641), (3205, 3205, 187027999005543183674), (3206, 3206, 187035176342243943665), (3207, 3207, 187042425824850716778), (3208, 3208, 187049748182332672835), (3209, 3209, 187057144151100296890), (3210, 3210, 187064614475082870388), (3211, 3211, 187072159905806789412), (3212, 3212, 187079781202474729685), (3213, 3213, 187087479132045668056), (3214, 3214, 187095254469315770394), (3215, 3215, 187103107997000155889), (3216, 3216, 187111040505815547889), (3217, 3217, 187119052794563821580), (3218, 3218, 187127145670216458874), (3219, 3219, 187135319947999921075), (3220, 3220, 187143576451481949977), (3221, 3221, 187151916012658808208), (3222, 3222, 187160339472043469779), (3223, 3223, 187168847678754771922), (3224, 3224, 187177441490607539450), (3225, 3225, 187186121774203693031), (3226, 3226, 187194889405024352897), (3227, 3227, 187203745267522949666), (3228, 3228, 187212690255219354122), (3229, 3229, 187221725270795037919), (3230, 3230, 187230851226189277371), (3231, 3231, 187240069042696412624), (3232, 3232, 187249379651064174668), (3233, 3233, 187258783991593092829), (3234, 3234, 187268283014236995530), (3235, 3235, 187277877678704617281), (3236, 3236, 187287568954562325047), (3237, 3237, 187297357821337977284), (3238, 3238, 187307245268625929157), (3239, 3239, 187317232296193197575), (3240, 3240, 187327319914086799921), (3241, 3241, 187337509142742280487), (3242, 3242, 187347801013093438854), (3243, 3243, 187358196566683274618), (3244, 3244, 187368696855776163071), (3245, 3245, 187379302943471276646), (3246, 3246, 187390015903817267116), (3247, 3247, 187400836821928223761), (3248, 3248, 187411766794100922921), (3249, 3249, 187422806927933384533), (3250, 3250, 187433958342444751508), (3251, 3251, 187445222168196507989), (3252, 3252, 187456599547415052744), (3253, 3253, 187468091634115644210), (3254, 3254, 187479699594227733873), (3255, 3255, 187491424605721704963), (3256, 3256, 187503267858737033606), (3257, 3257, 187515230555711889883), (3258, 3258, 187527313911514196427), (3259, 3259, 187539519153574162465), (3260, 3260, 187551847522018311462), (3261, 3261, 187564300269805020753), (3262, 3262, 187576878662861591831), (3263, 3263, 187589583980222870202), (3264, 3264, 187602417514171433987), (3265, 3265, 187615380570379370729), (3266, 3266, 187628474468051662117), (3267, 3267, 187641700540071196634), (3268, 3268, 187655060133145430412), (3269, 3269, 187668554607954716854), (3270, 3270, 187682185339302325897), (3271, 3271, 187695953716266174054), (3272, 3272, 187709861142352286703), (3273, 3273, 187723909035650014383), (3274, 3274, 187738098828989025166), (3275, 3275, 187752431970098095484), (3276, 3276, 187766909921765722145), (3277, 3277, 187781534162002578538), (3278, 3278, 187796306184205838418), (3279, 3279, 187811227497325390967), (3280, 3280, 187826299626031971167), (3281, 3281, 187841524110887229885), (3282, 3282, 187856902508515768422), (3283, 3283, 187872436391779162622), (3284, 3284, 187888127349952002014), (3285, 3285, 187903976988899969844), (3286, 3286, 187919986931259990198), (3287, 3287, 187936158816622468848), (3288, 3288, 187952494301715654796), (3289, 3289, 187968995060592149919), (3290, 3290, 187985662784817594527), (3291, 3291, 188002499183661557020), (3292, 3292, 188019505984290656296), (3293, 3293, 188036684931963945948), (3294, 3294, 188054037790230589742), (3295, 3295, 188071566341129858309), (3296, 3296, 188089272385393477405), (3297, 3297, 188107157742650358588), (3298, 3298, 188125224251633743594), (3299, 3299, 188143473770390794167), (3300, 3300, 188161908176494659601), (3301, 3301, 188180529367259054705), (3302, 3302, 188199339259955381420), (3303, 3303, 188218339792032427824), (3304, 3304, 188237532921338678749), (3305, 3305, 188256920626347272795), (3306, 3306, 188276504906383641006), (3307, 3307, 188296287781855863072), (3308, 3308, 188316271294487777420), (3309, 3309, 188336457507554882145), (3310, 3310, 188356848506123064291), (3311, 3311, 188377446397290195578), (3312, 3312, 188398253310430633257), (3313, 3313, 188419271397442665365), (3314, 3314, 188440502832998940285), (3315, 3315, 188461949814799921118), (3316, 3316, 188483614563830406014), (3317, 3317, 188505499324619156257), (3318, 3318, 188527606365501674547), (3319, 3319, 188549937978886176590), (3320, 3320, 188572496481522799794), (3321, 3321, 188595284214776093554), (3322, 3322, 188618303544900836314), (3323, 3323, 188641556863321225309), (3324, 3324, 188665046586913485624), (3325, 3325, 188688775158291945953), (3326, 3326, 188712745046098629180), (3327, 3327, 188736958745296406698), (3328, 3328, 188761418777465766154), (3329, 3329, 188786127691105243099), (3330, 3330, 188811088061935567859), (3331, 3331, 188836302493207579744), (3332, 3332, 188861773616013961571), (3333, 3333, 188887504089604848345), (3334, 3334, 188913496601707364792), (3335, 3335, 188939753868849147348), (3336, 3336, 188966278636685907114), (3337, 3337, 188993073680333091209), (3338, 3338, 189020141804701700892), (3339, 3339, 189047485844838325791), (3340, 3340, 189075108666269454545), (3341, 3341, 189103013165350123176), (3342, 3342, 189131202269616963507), (3343, 3343, 189159678938145714983), (3344, 3344, 189188446161913264307), (3345, 3345, 189217506964164278373), (3346, 3346, 189246864400782497080), (3347, 3347, 189276521560666753707), (3348, 3348, 189306481566111791687), (3349, 3349, 189336747573193947759), (3350, 3350, 189367322772161772668), (3351, 3351, 189398210387831661776), (3352, 3352, 189429413679988569176), (3353, 3353, 189460935943791880155), (3354, 3354, 189492780510186518116), (3355, 3355, 189524950746319363369), (3356, 3356, 189557450055961062531), (3357, 3357, 189590281879933308615), (3358, 3358, 189623449696541673261), (3359, 3359, 189656957022014073974), (3360, 3360, 189690807410944960653), (3361, 3361, 189725004456745307155), (3362, 3362, 189759551792098495121), (3363, 3363, 189794453089422178809), (3364, 3364, 189829712061336221224), (3365, 3365, 189865332461136793397), (3366, 3366, 189901318083276730292), (3367, 3367, 189937672763852238440), (3368, 3368, 189974400381096052070), (3369, 3369, 190011504855877136225), (3370, 3370, 190048990152207037068), (3371, 3371, 190086860277752981374), (3372, 3372, 190125119284357828985), (3373, 3373, 190163771268566983888), (3374, 3374, 190202820372162371415), (3375, 3375, 190242270782703591001), (3376, 3376, 190282126734076355910), (3377, 3377, 190322392507048333288), (3378, 3378, 190363072429832500001), (3379, 3379, 190404170878658131732), (3380, 3380, 190445692278349544985), (3381, 3381, 190487641102912713764), (3382, 3382, 190530021876129884937), (3383, 3383, 190572839172162318522), (3384, 3384, 190616097616161281450), (3385, 3385, 190659801884887425696), (3386, 3386, 190703956707338684058), (3387, 3387, 190748566865386819334), (3388, 3388, 190793637194422765103), (3389, 3389, 190839172584010898897), (3390, 3390, 190885177978552391125), (3391, 3391, 190931658377957775784), (3392, 3392, 190978618838328891681), (3393, 3393, 191026064472650345664), (3394, 3394, 191074000451490652186), (3395, 3395, 191122432003713206403), (3396, 3396, 191171364417197250947), (3397, 3397, 191220803039568999519), (3398, 3398, 191270753278943083533), (3399, 3399, 191321220604674491136), (3400, 3400, 191372210548121171177), (3401, 3401, 191423728703417477913), (3402, 3402, 191475780728258635624), (3403, 3403, 191528372344696405677), (3404, 3404, 191581509339946142092), (3405, 3405, 191635197567205425183), (3406, 3406, 191689442946484466518), (3407, 3407, 191744251465448482106), (3408, 3408, 191799629180272234556), (3409, 3409, 191855582216506948767), (3410, 3410, 191912116769959809732), (3411, 3411, 191969239107586254999), (3412, 3412, 192026955568395278529), (3413, 3413, 192085272564367966871), (3414, 3414, 192144196581389492889), (3415, 3415, 192203734180194796680), (3416, 3416, 192263891997328187835), (3417, 3417, 192324676746117107765), (3418, 3418, 192386095217660295556), (3419, 3419, 192448154281830605560), (3420, 3420, 192510860888292729910), (3421, 3421, 192574222067536084106), (3422, 3422, 192638244931923118968), (3423, 3423, 192702936676753327517), (3424, 3424, 192768304581343220662), (3425, 3425, 192834356010122551095), (3426, 3426, 192901098413747070355), (3427, 3427, 192968539330228109792), (3428, 3428, 193036686386079281979), (3429, 3429, 193105547297480605141), (3430, 3430, 193175129871460359268), (3431, 3431, 193245442007094988852), (3432, 3432, 193316491696727373599), (3433, 3433, 193388287027203794986), (3434, 3434, 193460836181129933279), (3435, 3435, 193534147438146236415), (3436, 3436, 193608229176223009232), (3437, 3437, 193683089872975578619), (3438, 3438, 193758738106999897554), (3439, 3439, 193835182559228958475), (3440, 3440, 193912432014310394074), (3441, 3441, 193990495362005651509), (3442, 3442, 194069381598611134016), (3443, 3443, 194149099828401712134), (3444, 3444, 194229659265097015186), (3445, 3445, 194311069233350922216), (3446, 3446, 194393339170264680445), (3447, 3447, 194476478626924088278), (3448, 3448, 194560497269961189136), (3449, 3449, 194645404883140931820), (3450, 3450, 194731211368973262783), (3451, 3451, 194817926750351125573), (3452, 3452, 194905561172214852827), (3453, 3453, 194994124903243446572), (3454, 3454, 195083628337573253193), (3455, 3455, 195174081996544550290), (3456, 3456, 195265496530476573775), (3457, 3457, 195357882720471524933), (3458, 3458, 195451251480248108861), (3459, 3459, 195545613858005167602), (3460, 3460, 195640981038315983560), (3461, 3461, 195737364344053841266), (3462, 3462, 195834775238349448436), (3463, 3463, 195933225326580830360), (3464, 3464, 196032726358396325138), (3465, 3465, 196133290229771321072), (3466, 3466, 196234928985099391615), (3467, 3467, 196337654819318497787), (3468, 3468, 196441480080072942745), (3469, 3469, 196546417269911778416), (3470, 3470, 196652479048524379631), (3471, 3471, 196759678235013917187), (3472, 3472, 196868027810209477534), (3473, 3473, 196977540919017593604), (3474, 3474, 197088230872813968397), (3475, 3475, 197200111151876190566), (3476, 3476, 197313195407858259249), (3477, 3477, 197427497466307753877), (3478, 3478, 197543031329226503644), (3479, 3479, 197659811177675630717), (3480, 3480, 197777851374425861186), (3481, 3481, 197897166466654018175), (3482, 3482, 198017771188686632432), (3483, 3483, 198139680464791627206), (3484, 3484, 198262909412019056196), (3485, 3485, 198387473343091895950), (3486, 3486, 198513387769347917205), (3487, 3487, 198640668403733683415), (3488, 3488, 198769331163851749048), (3489, 3489, 198899392175062155219), (3490, 3490, 199030867773639345808), (3491, 3491, 199163774509985653546), (3492, 3492, 199298129151902532442), (3493, 3493, 199433948687920740658), (3494, 3494, 199571250330690706254), (3495, 3495, 199710051520434337400), (3496, 3496, 199850369928459568499), (3497, 3497, 199992223460738964359), (3498, 3498, 200135630261553736016), (3499, 3499, 200280608717204554118), (3500, 3500, 200427177459790578941), (3501, 3501, 200575355371058160150), (3502, 3502, 200725161586320694356), (3503, 3503, 200876615498451164393), (3504, 3504, 201029736761948921078), (3505, 3505, 201184545297082306023), (3506, 3506, 201341061294108752917), (3507, 3507, 201499305217574044538), (3508, 3508, 201659297810692443756), (3509, 3509, 201821060099809458789), (3510, 3510, 201984613398949046227), (3511, 3511, 202149979314447099650), (3512, 3512, 202317179749673117313), (3513, 3513, 202486236909841989119), (3514, 3514, 202657173306917891278), (3515, 3515, 202830011764612326410), (3516, 3516, 203004775423478397680), (3517, 3517, 203181487746103457714), (3518, 3518, 203360172522402326674), (3519, 3519, 203540853875013328982), (3520, 3520, 203723556264799454840), (3521, 3521, 203908304496457010887), (3522, 3522, 204095123724234184214), (3523, 3523, 204284039457762005448), (3524, 3524, 204475077568000259904), (3525, 3525, 204668264293300960794), (3526, 3526, 204863626245592065370), (3527, 3527, 205061190416684183647), (3528, 3528, 205260984184703100020), (3529, 3529, 205463035320651000839), (3530, 3530, 205667371995099375789), (3531, 3531, 205874022785016637847), (3532, 3532, 206083016680733585704), (3533, 3533, 206294383093049913997), (3534, 3534, 206508151860485060378), (3535, 3535, 206724353256676764681), (3536, 3536, 206943017997930804083), (3537, 3537, 207164177250925459389), (3538, 3538, 207387862640574361508), (3539, 3539, 207614106258051463777), (3540, 3540, 207842940668981985299), (3541, 3541, 208074398921803272822), (3542, 3542, 208308514556299634103), (3543, 3543, 208545321612315304209), (3544, 3544, 208784854638649817904), (3545, 3545, 209027148702140176356), (3546, 3546, 209272239396934314802), (3547, 3547, 209520162853960499829), (3548, 3548, 209770955750597410569), (3549, 3549, 210024655320549787493), (3550, 3550, 210281299363934665807), (3551, 3551, 210540926257583347760), (3552, 3552, 210803574965564409632), (3553, 3553, 211069285049933184965), (3554, 3554, 211338096681713315739), (3555, 3555, 211610050652116118005), (3556, 3556, 211885188384003667959), (3557, 3557, 212163551943601678848), (3558, 3558, 212445184052468408525), (3559, 3559, 212730128099726012154), (3560, 3560, 213018428154560934599), (3561, 3561, 213310128979000122722), (3562, 3562, 213605276040970029178), (3563, 3563, 213903915527645576730), (3564, 3564, 214206094359096455617), (3565, 3565, 214511860202238336471), (3566, 3566, 214821261485096797800), (3567, 3567, 215134347411391990419), (3568, 3568, 215451167975452291622), (3569, 3569, 215771773977465439641), (3570, 3570, 216096217039075884181), (3571, 3571, 216424549619337341984), (3572, 3572, 216756825031029807523), (3573, 3573, 217093097457350538529), (3574, 3574, 217433421968988814321), (3575, 3575, 217777854541594552080), (3576, 3576, 218126452073651162788), (3577, 3577, 218479272404763334625), (3578, 3578, 218836374334370747761), (3579, 3579, 219197817640899050854), (3580, 3580, 219563663101359766683), (3581, 3581, 219933972511411142476), (3582, 3582, 220308808705892320133), (3583, 3583, 220688235579843573019), (3584, 3584, 221072318110025739791), (3585, 3585, 221461122376952382273), (3586, 3586, 221854715587448604124), (3587, 3587, 222253166097750890486), (3588, 3588, 222656543437162766408), (3589, 3589, 223064918332281524188), (3590, 3590, 223478362731811737347), (3591, 3591, 223896949831981762298), (3592, 3592, 224320754102579928615), (3593, 3593, 224749851313627635504), (3594, 3594, 225184318562707106541), (3595, 3595, 225624234302962107385), (3596, 3596, 226069678371790502868), (3597, 3597, 226520732020248121163), (3598, 3598, 226977477943184004521), (3599, 3599, 227440000310127758977), (3600, 3600, 227908384796950370383), (3601, 3601, 228382718618320531871), (3602, 3602, 228863090560979229283), (3603, 3603, 229349591017856057166), (3604, 3604, 229842312023051489485), (3605, 3605, 230341347287710107303), (3606, 3606, 230846792236810591300), (3607, 3607, 231358744046899121230), (3608, 3608, 231877301684793688334), (3609, 3609, 232402565947287721510), (3610, 3610, 232934639501882354916), (3611, 3611, 233473626928577624809), (3612, 3612, 234019634762753878224), (3613, 3613, 234572771539175706874), (3614, 3614, 235133147837151787795), (3615, 3615, 235700876326885119311), (3616, 3616, 236276071817049288390), (3617, 3617, 236858851303627594918), (3618, 3618, 237449334020053091682), (3619, 3619, 238047641488688877487), (3620, 3620, 238653897573689306836), (3621, 3621, 239268228535284154720), (3622, 3622, 239890763085529201463), (3623, 3623, 240521632445568182124), (3624, 3624, 241160970404452580030), (3625, 3625, 241808913379567336720), (3626, 3626, 242465600478712203369), (3627, 3627, 243131173563890174068), (3628, 3628, 243805777316856221715), (3629, 3629, 244489559306481405484), (3630, 3630, 245182670057989337611), (3631, 3631, 245885263124123989557), (3632, 3632, 246597495158309886572), (3633, 3633, 247319525989867888393), (3634, 3634, 248051518701351985756), (3635, 3635, 248793639708074861003), (3636, 3636, 249546058839892369959), (3637, 3637, 250308949425319605421), (3638, 3638, 251082488378053803843), (3639, 3639, 251866856285982060481), (3640, 3640, 252662237502754628700), (3641, 3641, 253468820242007500893), (3642, 3642, 254286796674321006395), (3643, 3643, 255116363027004320890), (3644, 3644, 255957719686799067310), (3645, 3645, 256811071305598605745), (3646, 3646, 257676626909283165033), (3647, 3647, 258554600009774667669), (3648, 3648, 259445208720418948649), (3649, 3649, 260348675874807074589), (3650, 3650, 261265229149151638768), (3651, 3651, 262195101188338248027), (3652, 3652, 263138529735776936159), (3653, 3653, 264095757767182943766), (3654, 3654, 265067033628421204674), (3655, 3655, 266052611177553982850), (3656, 3656, 267052749931236420419), (3657, 3657, 268067715215610296628), (3658, 3658, 269097778321852069423), (3659, 3659, 270143216666537286432), (3660, 3660, 271204313956989721674), (3661, 3661, 272281360361790129968), (3662, 3662, 273374652686626324998), (3663, 3663, 274484494555673392335), (3664, 3664, 275611196598700258756), (3665, 3665, 276755076644106568357), (3666, 3666, 277916459918101878950), (3667, 3667, 279095679250247604899), (3668, 3668, 280293075285590911282), (3669, 3669, 281508996703628926316), (3670, 3670, 282743800444351202715), (3671, 3671, 283997851941618342937), (3672, 3672, 285271525364145128443), (3673, 3673, 286565203864367380111), (3674, 3674, 287879279835483148129), (3675, 3675, 289214155176970708370), (3676, 3676, 290570241568898253048), (3677, 3677, 291947960755353132220), (3678, 3678, 293347744837332056671), (3679, 3679, 294770036575447840581), (3680, 3680, 296215289702823074279), (3681, 3681, 297683969248556605114), (3682, 3682, 299176551872164901507), (3683, 3683, 300693526209417316768), (3684, 3684, 302235393230001992540), (3685, 3685, 303802666607477685687), (3686, 3686, 305395873101986208538), (3687, 3687, 307015552956220483940), (3688, 3688, 308662260305164479427), (3689, 3689, 310336563600143547377), (3690, 3690, 312039046047747011136), (3691, 3691, 313770306064209254653), (3692, 3692, 315530957745861151767), (3693, 3693, 317321631356290470913), (3694, 3694, 319142973830877974746), (3695, 3695, 320995649299405368788), (3696, 3696, 322880339627462109060), (3697, 3697, 324797744977410430209), (3698, 3698, 326748584389701881378), (3699, 3699, 328733596385374240026), (3700, 3700, 330753539590595001855), (3701, 3701, 332809193384156810539), (3702, 3702, 334901358568871292180), (3703, 3703, 337030858067850899912), (3704, 3704, 339198537646713663447), (3705, 3705, 341405266662793292528), (3706, 3706, 343651938842487024865), (3707, 3707, 345939473087926067980), (3708, 3708, 348268814314208597864), (3709, 3709, 350640934318493190830), (3710, 3710, 353056832682311432539), (3711, 3711, 355517537708522432835), (3712, 3712, 358024107394399249671), (3713, 3713, 360577630442407973039), (3714, 3714, 363179227310314634415), (3715, 3715, 365830051302333394577), (3716, 3716, 368531289703111840672), (3717, 3717, 371284164956435923426), (3718, 3718, 374089935890628332686), (3719, 3719, 376949898992710204212), (3720, 3720, 379865389733497249140), (3721, 3721, 382837783945907992700), (3722, 3722, 385868499258874112052), (3723, 3723, 388958996589361204772), (3724, 3724, 392110781695133050754), (3725, 3725, 395325406791023923907), (3726, 3726, 398604472231622162362), (3727, 3727, 401949628263414438204), (3728, 3728, 405362576849594427748), (3729, 3729, 408845073570902347421), (3730, 3730, 412398929606033594745), (3731, 3731, 416026013795336057878), (3732, 3732, 419728254791707103887), (3733, 3733, 423507643302803436055), (3734, 3734, 427366234428890573802), (3735, 3735, 431306150100884347499), (3736, 3736, 435329581623375251754), (3737, 3737, 439438792327678550214), (3738, 3738, 443636120340219509783), (3739, 3739, 447923981471844954792), (3740, 3740, 452304872233950423791), (3741, 3741, 456781372987627598077), (3742, 3742, 461356151232370434781), (3743, 3743, 466031965041231733621), (3744, 3744, 470811666649695928692), (3745, 3745, 475698206205930041644), (3746, 3746, 480694635690494366578), (3747, 3747, 485804113014039082113), (3748, 3748, 491029906301984207563), (3749, 3749, 496375398375679853515), (3750, 3750, 501844091440073396499), (3751, 3751, 507439611988471994232), (3752, 3752, 513165715935584850243), (3753, 3753, 519026293990662079320), (3754, 3754, 525025377283218320979), (3755, 3755, 531167143254541969065), (3756, 3756, 537455921828947786394), (3757, 3757, 543896201879534704524), (3758, 3758, 550492638004064931865), (3759, 3759, 557250057627488497031), (3760, 3760, 564173468448602671374), (3761, 3761, 571268066249362241077), (3762, 3762, 578539243086448514344), (3763, 3763, 585992595885866737760), (3764, 3764, 593633935462578071543), (3765, 3765, 601469295988488604591), (3766, 3766, 609504944933519627928), (3767, 3767, 617747393505976493093), (3768, 3768, 626203407620024269092), (3769, 3769, 634880019419773967549), (3770, 3770, 643784539391290739162), (3771, 3771, 652924569095763125042), (3772, 3772, 662308014559128748816), (3773, 3773, 671943100355645989463), (3774, 3774, 681838384425243118153), (3775, 3775, 692002773666976818110), (3776, 3776, 702445540353602466128), (3777, 3777, 713176339415111465519), (3778, 3778, 724205226642139681382), (3779, 3779, 735542677863410089146), (3780, 3780, 747199609154857694411), (3781, 3781, 759187398141812437803), (3782, 3782, 771517906459604322447), (3783, 3783, 784203503442224004006), (3784, 3784, 797257091113242748126), (3785, 3785, 810692130558090879853), (3786, 3786, 824522669762038370620), (3787, 3787, 838763373003841791183), (3788, 3788, 853429551901047451737), (3789, 3789, 868537198209402479600), (3790, 3790, 884103018485757761596), (3791, 3791, 900144470731285826005), (3792, 3792, 916679803139822639863), (3793, 3793, 933728095084718063836), (3794, 3794, 951309300486792076474), (3795, 3795, 969444293715893539343), (3796, 3796, 988154918189200214282), (3797, 3797, 1007464037840842644929), (3798, 3798, 1027395591649745173029), (3799, 3799, 1047974651425825152778), (3800, 3800, 1069227483068952820968), (3801, 3801, 1091181611530432393759), (3802, 3802, 1113865889723310171826), (3803, 3803, 1137310571645646059664), (3804, 3804, 1161547390000107931359), (3805, 3805, 1186609638613980179804), (3806, 3806, 1212532259986045422155), (3807, 3807, 1239351938310939912184), (3808, 3808, 1267107198357649376531), (3809, 3809, 1295838510606967014547), (3810, 3810, 1325588403083158475140), (3811, 3811, 1356401580347965307197), (3812, 3812, 1388325050160642178673), (3813, 3813, 1421408258346197271147), (3814, 3814, 1455703232455644495874), (3815, 3815, 1491264734847159096744), (3816, 3816, 1528150425865859438697), (3817, 3817, 1566421037852850627302), (3818, 3818, 1606140560771524889892), (3819, 3819, 1647376440301318874403), (3820, 3820, 1690199789316616862412), (3821, 3821, 1734685613741741051917), (3822, 3822, 1780913053852511550101), (3823, 3823, 1828965642181266566433), (3824, 3824, 1878931579276140824336), (3825, 3825, 1930904028667502806702), (3826, 3826, 1984981432505513025572), (3827, 3827, 2041267849453625627703), (3828, 3828, 2099873316554437469886), (3829, 3829, 2160914236927607863243), (3830, 3830, 2224513795315746203046), (3831, 3831, 2290802403664424414171), (3832, 3832, 2359918179108172418736), (3833, 3833, 2432007456936952109700), (3834, 3834, 2507225341338826572610), (3835, 3835, 2585736296956164735137), (3836, 3836, 2667714784556754237896), (3837, 3837, 2753345944409853625550), (3838, 3838, 2842826331272948099377), (3839, 3839, 2936364705240488622914), (3840, 3840, 3034182883084186936525), (3841, 3841, 3136516655128823242905), (3842, 3842, 3243616773161668609022), (3843, 3843, 3355750015371595784734), (3844, 3844, 3473200334860256165631), (3845, 3845, 3596270098867334181615), (3846, 3846, 3725281426510398301458), (3847, 3847, 3860577633563405972651), (3848, 3848, 4002524793593326144315), (3849, 3849, 4151513425649217412047), (3850, 3850, 4307960319660893608719), (3851, 3851, 4472310511764425303420), (3852, 3852, 4645039422939633922467), (3853, 3853, 4826655175632096450729), (3854, 3854, 5017701104451990220336), (3855, 3855, 5218758478608863809839), (3856, 3856, 5430449455471295492242), (3857, 3857, 5653440286551453334517), (3858, 3858, 5888444799326975216406), (3859, 3859, 6136228180648894223880), (3860, 3860, 6397611090069769160257), (3861, 3861, 6673474134288971762115), (3862, 3862, 6964762737083846066121), (3863, 3863, 7272492442611617152263), (3864, 3864, 7597754693867207692722), (3865, 3865, 7941723132411087202430), (3866, 3866, 8305660470288963132524), (3867, 3867, 8690925990407730450601), (3868, 3868, 9098983737572807640905), (3869, 3869, 9531411469001869201058), (3870, 3882, 9586267722316378333136), (3883, 3883, 9502957171151932146666), (3884, 3884, 9408868486289041729372), (3885, 3885, 9315711372563407652844), (3886, 3886, 9223476606498423418657), (3887, 3887, 9132155055939033087780), (3888, 3888, 9041737679147557512653), (3889, 3889, 8952215523908472784805), (3890, 3890, 8863579726642052262183), (3891, 3891, 8775821511526784418003), (3892, 3892, 8688932189630479621785), (3893, 3893, 8602903158049979823550), (3894, 3894, 8517725899059385963911), (3895, 3895, 8433391979266718776149), (3896, 3896, 8349893048778929481336), (3897, 3897, 8267220840375177704293), (3898, 3898, 8185367168688294756726), (3899, 3899, 8104323929394351244283), (3900, 3900, 8024083098410248756716), (3901, 3901, 7944636731099256194768), (3902, 3902, 7865976961484412074028), (3903, 3903, 7788096001469714924780), (3904, 3904, 7710986140069024678000), (3905, 3905, 7634639742642598691089), (3906, 3906, 7559049250141186822860), (3907, 3907, 7484207178357610715703), (3908, 3908, 7410106117185753183865), (3909, 3909, 7336738729886884340460), (3910, 3910, 7264097752363251822238), (3911, 3911, 7192175992438863190334), (3912, 3912, 7120966329147389297361), (3913, 3913, 7050461712027118116199), (3914, 3914, 6980655160422889223959), (3915, 3915, 6911539762794939825702), (3916, 3916, 6843108676034593886834), (3917, 3917, 6775355124786726620628), (3918, 3918, 6708272400778937248146), (3919, 3919, 6641853862157363612026), (3920, 3920, 6576092932829072883194), (3921, 3921, 6510983101810963250687), (3922, 3922, 6446517922585112129393), (3923, 3923, 6382691012460507058805), (3924, 3924, 6319496051941096097827), (3925, 3925, 6256926784100095146363), (3926, 3926, 6194977013960490243924), (3927, 3927, 6133640607881673508836), (3928, 3928, 6072911492952151988946), (3929, 3929, 6012783656388269295986), (3930, 3930, 5953251144938880491076), (3931, 3931, 5894308064295921278293), (3932, 3932, 5835948578510813146824), (3933, 3933, 5778166909416646680024), (3934, 3934, 5720957336056085821806), (3935, 3935, 5664314194114936457234), (3936, 3936, 5608231875361323224984), (3937, 3937, 5552704827090419034638), (3938, 3938, 5497727551574672311522), (3939, 3939, 5443294605519477536161), (3940, 3940, 5389400599524235184318), (3941, 3941, 5336040197548747707245), (3942, 3942, 5283208116384898720045), (3943, 3943, 5230899125133563089153), (3944, 3944, 5179108044686696127874), (3945, 3945, 5127829747214550621658), (3946, 3946, 5077059155657970912533), (3947, 3947, 5026791243225713774785), (3948, 3948, 4977021032896746311668), (3949, 3949, 4927743596927471595711), (3950, 3950, 4878954056363833263080), (3951, 3951, 4830647580558250755525), (3952, 3952, 4782819386691337381708), (3953, 3953, 4735464739298353843275), (3954, 3954, 4688578949800350339876), (3955, 3955, 4642157376039950831561), (3956, 3956, 4596195421821733496595), (3957, 3957, 4550688536457161877817), (3958, 3958, 4505632214314021661205), (3959, 3959, 4461021994370318476440), (3960, 3960, 4416853459772592550931), (3961, 3961, 4373122237398606486070), (3962, 3962, 4329823997424362857495), (3963, 3963, 4286954452895408769797), (3964, 3964, 4244509359302384920591), (3965, 3965, 4202484514160777149100), (3966, 3966, 4160875756594828860495), (3967, 3967, 4119678966925573129203), (3968, 3968, 4078890066262943692281), (3969, 3969, 4038505016101924447803), (3970, 3970, 3998519817922697473072), (3971, 3971, 3958930512794749973338), (3972, 3972, 3919733180984900963701), (3973, 3973, 3880923941569208874952), (3974, 3974, 3842498952048721658368), (3975, 3975, 3804454407969031344919), (3976, 3976, 3766786542543595391009), (3977, 3977, 3729491626280787515851), (3978, 3978, 3692565966614641104802), (3979, 3979, 3656005907539248618616), (3980, 3980, 3619807829246780810511), (3981, 3981, 3583968147769089911397), (3982, 3982, 3548483314622861298413), (3983, 3983, 3513349816458278513280), (3984, 3984, 3478564174711166844832), (3985, 3985, 3444122945258581034487), (3986, 3986, 3410022718077803004443), (3987, 3987, 3376260116908715845983), (3988, 3988, 3342831798919520639587), (3989, 3989, 3309734454375763009492), (3990, 3990, 3276964806312636643062), (3991, 3991, 3244519610210531329764), (3992, 3992, 3212395653673793395806), (3993, 3993, 3180589756112666728521), (3994, 3994, 3149098768428382899525), (3995, 3995, 3117919572701369207451), (3996, 3996, 3087049081882543769753), (3997, 3997, 3056484239487667098766), (3998, 3998, 3026222019294719899768), (3999, 3999, 2996259425044277128483), (4000, 4000, 2966593490142848642063), (4001, 4001, 2937221277369157071349), (4002, 4002, 2908139878583323833019), (4003, 4003, 2879346414438934488138), (4004, 4004, 2850838034097954938750), (4005, 4005, 2822611914948470236386), (4006, 4006, 2794665262325218055828), (4007, 4007, 2766995309232889164186), (4008, 4008, 2739599316072167489293), (4009, 4009, 2712474570368482662666), (4010, 4010, 2685618386503448180858), (4011, 4011, 2659028105448958594909), (4012, 4012, 2632701094503919400900), (4013, 4013, 2606634747033583565247), (4014, 4014, 2580826482211468876483), (4015, 4015, 2555273744763830570775), (4016, 4016, 2529974004716663931460), (4017, 4017, 2504924757145211813327), (4018, 4018, 2480123521925952290423), (4019, 4019, 2455567843491041871706), (4020, 4020, 2431255290585189971986), (4021, 4021, 2407183456024940566323), (4022, 4022, 2383349956460337194379), (4023, 4023, 2359752432138947717207), (4024, 4024, 2336388546672225462581), (4025, 4025, 2313255986804183626318), (4026, 4026, 2290352462182360026057), (4027, 4027, 2267675705131049530750), (4028, 4028, 2245223470426781713614), (4029, 4029, 2222993535076021498627), (4030, 4030, 2200983698095070790720), (4031, 4031, 2179191780292149297743), (4032, 4032, 2157615624051632968062), (4033, 4033, 2136253093120428681250), (4034, 4034, 2115102072396464040841), (4035, 4035, 2094160467719271327566), (4036, 4036, 2073426205662644878778), (4037, 4037, 2052897233329351365126), (4038, 4038, 2032571518147872638739), (4039, 4039, 2012447047671161028455), (4040, 4040, 1992521829377387156886), (4041, 4041, 1972793890472660551372), (4042, 4042, 1953261277695703516210), (4043, 4043, 1933922057124458926940), (4044, 4044, 1914774313984612798951), (4045, 4045, 1895816152460012672229), (4046, 4046, 1877045695504963041811), (4047, 4047, 1858461084658379249317), (4048, 4048, 1840060479859781434968), (4049, 4049, 1821842059267110331651), (4050, 4050, 1803804019076346863021), (4051, 4051, 1785944573342917686159), (4052, 4052, 1768261953804868996197), (4053, 4053, 1750754409707791085344), (4054, 4054, 1733420207631476322123), (4055, 4055, 1716257631318293388240), (4056, 4056, 1699264981503260780436), (4057, 4057, 1682440575745802752907), (4058, 4058, 1665782748263171042482), (4059, 4059, 1649289849765515883646), (4060, 4060, 1632960247292589983808), (4061, 4061, 1616792324052069290899), (4062, 4062, 1600784479259474545444), (4063, 4063, 1584935127979677767767), (4064, 4064, 1569242700969977987888), (4065, 4065, 1553705644524730681077), (4066, 4066, 1538322420321515525819), (4067, 4067, 1523091505268827253286), (4068, 4068, 1508011391355274508204), (4069, 4069, 1493080585500271790301), (4070, 4070, 1478297609406209693367), (4071, 4071, 1463660999412088805314), (4072, 4072, 1449169306348602777539), (4073, 4073, 1434821095394656215385), (4074, 4074, 1420614945935303183549), (4075, 4075, 1406549451421092260940), (4076, 4076, 1392623219228804218752), (4077, 4077, 1378834870523568533418), (4078, 4078, 1365183040122345082592), (4079, 4079, 1351666376358757507517), (4080, 4080, 1338283540949264858928), (4081, 4081, 1325033208860658276166), (4082, 4082, 1311914068178869580363), (4083, 4083, 1298924819979078792438), (4084, 4084, 1286064178197107715285), (4085, 4085, 1273330869502086846817), (4086, 4086, 1260723633170383016651), (4087, 4087, 1248241220960775264011), (4088, 4088, 1235882396990866598030), (4089, 4089, 1223645937614719403990), (4090, 4090, 1211530631301702380189), (4091, 4091, 1199535278516537010088), (4092, 4092, 1187658691600531693156), (4093, 4093, 1175899694653991775402), (4094, 4094, 1164257123419793837032), (4095, 4095, 1152729825168112709932), (4096, 4096, 1141316658582289811814), (4097, 4097, 1130016493645831496846), (4098, 4098, 1118828211530526234501), (4099, 4099, 1107750704485669539110), (4100, 4100, 1096782875728385682287), (4101, 4101, 1085923639335035328997), (4102, 4102, 1075171920133698345542), (4103, 4103, 1064526653597721134200), (4104, 4104, 1053986785740317954653), (4105, 4105, 1043551273010215796686), (4106, 4106, 1033219082188332471967), (4107, 4107, 1022989190285477695016), (4108, 4108, 1012860584441067024769), (4109, 4109, 1002832261822838638385), (4110, 4110, 992903229527563008302), (4111, 4111, 983072504482735651784), (4112, 4112, 973339113349243219588), (4113, 4113, 963702092424993286721), (4114, 4114, 954160487549498303684), (4115, 4115, 944713354009404261073), (4116, 4116, 935359756444954713934), (4117, 4117, 926098768757380904885), (4118, 4118, 916929474017208816718), (4119, 4119, 907850964373474075958), (4120, 4120, 898862340963835718771), (4121, 4121, 889962713825579919575), (4122, 4122, 881151201807504870866), (4123, 4123, 872426932482678089967), (4124, 4124, 863789042062057514818), (4125, 4125, 855236675308967836454), (4126, 4126, 846768985454423600449), (4127, 4127, 838385134113290693514), (4128, 4128, 830084291201277914371), (4129, 4129, 821865634852750410268), (4130, 4130, 813728351339356841849), (4131, 4131, 805671634989462219653), (4132, 4132, 797694688108378435300), (4133, 4133, 789796720899384589406), (4134, 4134, 781976951385529296441), (4135, 4135, 774234605332207224199), (4136, 4136, 766568916170502202178), (4137, 4137, 758979124921289309087), (4138, 4138, 751464480120088424838), (4139, 4139, 744024237742661806771), (4140, 4140, 736657661131348323535), (4141, 4141, 729364020922127053005), (4142, 4142, 722142594972403022778), (4143, 4143, 714992668289507943344), (4144, 4144, 707913532959908854796), (4145, 4145, 700904488079117678016), (4146, 4146, 693964839682294730709), (4147, 4147, 687093900675539337336), (4148, 4148, 680290990767860730035), (4149, 4149, 673555436403822504985), (4150, 4150, 666886570696853965332), (4151, 4151, 660283733363221747854), (4152, 4152, 653746270656655195895), (4153, 4153, 647273535303619005836), (4154, 4154, 640864886439226738452), (4155, 4155, 634519689543788849952), (4156, 4156, 628237316379988960349), (4157, 4157, 622017144930682138959), (4158, 4158, 615858559337309048474), (4159, 4159, 609760949838919849975), (4160, 4160, 603723712711801831658), (4161, 4161, 597746250209704783820), (4162, 4162, 591827970504658201802), (4163, 4163, 585968287628374457230), (4164, 4164, 580166621414232135871), (4165, 4165, 574422397439833797892), (4166, 4166, 568735046970132473160), (4167, 4167, 563104006901121260555), (4168, 4168, 557528719704080455995), (4169, 4169, 552008633370376689104), (4170, 4170, 546543201356808603073), (4171, 4171, 541131882531493666409), (4172, 4172, 535774141120290758821), (4173, 4173, 530469446653753226555), (4174, 4174, 525217273914607155005), (4175, 4175, 520017102885749658421), (4176, 4176, 514868418698762038041), (4177, 4177, 509770711582932710931), (4178, 4178, 504723476814784862308), (4179, 4179, 499726214668103824068), (4180, 4180, 494778430364459231750), (4181, 4181, 489879634024217061139), (4182, 4182, 485029340618036694197), (4183, 4183, 480227069918848212076), (4184, 4184, 475472346454305160471), (4185, 4185, 470764699459708079675), (4186, 4186, 466103662831394138292), (4187, 4187, 461488775080588255734), (4188, 4188, 456919579287711144291), (4189, 4189, 452395623057139746823), (4190, 4190, 447916458472415590914), (4191, 4191, 443481642051896624667), (4192, 4192, 439090734704848143235), (4193, 4193, 434743301687968458649), (4194, 4194, 430438912562345008563), (4195, 4195, 426177141150836642141), (4196, 4196, 421957565495877863506), (4197, 4197, 417779767817700854957), (4198, 4198, 413643334472971143522), (4199, 4199, 409547855913832815368), (4200, 4200, 405492926647359223137), (4201, 4201, 401478145195405171422), (4202, 4202, 397503114054856605369), (4203, 4203, 393567439658273866702), (4204, 4204, 389670732334924620497), (4205, 4205, 385812606272202594551), (4206, 4206, 381992679477428311437), (4207, 4207, 378210573740028031126), (4208, 4208, 374465914594087159530), (4209, 4209, 370758331281274415377), (4210, 4210, 367087456714133084531), (4211, 4211, 363452927439735727259), (4212, 4212, 359854383603698739860), (4213, 4213, 356291468914553207782), (4214, 4214, 352763830608468522557), (4215, 4215, 349271119414325269858), (4216, 4216, 345812989519133930553), (4217, 4217, 342389098533795970844), (4218, 4218, 338999107459203931529), (4219, 4219, 335642680652677159930), (4220, 4220, 332319485794729861316), (4221, 4221, 329029193856168179521), (4222, 4222, 325771479065513049031), (4223, 4223, 322546018876745593100), (4224, 4224, 319352493937371874356), (4225, 4225, 316190588056803835996), (4226, 4226, 313059988175053302967), (4227, 4227, 309960384331735943531), (4228, 4228, 306891469635382122308), (4229, 4229, 303852940233051606246), (4230, 4230, 300844495280249115095), (4231, 4231, 297865836911137737718), (4232, 4232, 294916670209047265067), (4233, 4233, 291996703177274519868), (4234, 4234, 289105646710172791949), (4235, 4235, 286243214564527516781), (4236, 4236, 283409123331215363150), (4237, 4237, 280603092407143923911), (4238, 4238, 277824843967469231595), (4239, 4239, 275074102938088348113), (4240, 4240, 272350596968404305063), (4241, 4241, 269654056404360698082), (4242, 4242, 266984214261743265428), (4243, 4243, 264340806199745807354), (4244, 4244, 261723570494797829064), (4245, 4245, 259132248014651315905), (4246, 4246, 256566582192724075153), (4247, 4247, 254026319002697104112), (4248, 4248, 251511206933363469418), (4249, 4249, 249020996963726207344), (4250, 4250, 246555442538342779549), (4251, 4251, 244114299542913643118), (4252, 4252, 241697326280112517938), (4253, 4253, 239304283445655958355), (4254, 4254, 236934934104609859757), (4255, 4255, 234589043667930554215), (4256, 4256, 232266379869238172490), (4257, 4257, 229966712741819972763), (4258, 4258, 227689814595861359171), (4259, 4259, 225435459995902335813), (4260, 4260, 223203425738517164171), (4261, 4261, 220993490830215014031), (4262, 4262, 218805436465559419832), (4263, 4263, 216639046005504376072), (4264, 4264, 214494104955944926804), (4265, 4265, 212370400946480125548), (4266, 4266, 210267723709386262919), (4267, 4267, 208185865058798280118), (4268, 4268, 206124618870097307047), (4269, 4269, 204083781059502284205), (4270, 4270, 202063149563863647728), (4271, 4271, 200062524320657076958), (4272, 4272, 198081707248175323721), (4273, 4273, 196120502225916162100), (4274, 4274, 194178715075164516931), (4275, 4275, 192256153539766848446), (4276, 4276, 190352627267095889551), (4277, 4277, 188467947789203851041), (4278, 4278, 186601928504162228753), (4279, 4279, 184754384657586365102), (4280, 4280, 182925133324342935745), (4281, 4281, 181113993390438550242), (4282, 4282, 179320785535087673507), (4283, 4283, 177545332212958092581), (4284, 4284, 175787457636592170873), (4285, 4285, 174046987759002149379), (4286, 4286, 172323750256437771662), (4287, 4287, 170617574511324526398), (4288, 4288, 168928291595370818216), (4289, 4289, 167255734252842394273), (4290, 4290, 165599736884002370568), (4291, 4291, 163960135528715218384), (4292, 4292, 162336767850213087509), (4293, 4293, 160729473119022858920), (4294, 4294, 159138092197052335564), (4295, 4295, 157562467521833995608), (4296, 4296, 156002443090924748127), (4297, 4297, 154457864446460146660), (4298, 4298, 152928578659861531346), (4299, 4299, 151414434316694585492), (4300, 4300, 149915281501677807417), (4301, 4301, 148430971783839413285), (4302, 4302, 146961358201821201272), (4303, 4303, 145506295249327922051), (4304, 4304, 144065638860720714902), (4305, 4305, 142639246396753183072), (4306, 4306, 141226976630448696111), (4307, 4307, 139828689733117520902), (4308, 4308, 138444247260512396932), (4309, 4309, 137073512139121185081), (4310, 4310, 135716348652595232754), (4311, 4311, 134372622428312111637), (4312, 4312, 133042200424071397661), (4313, 4313, 131724950914922175902), (4314, 4314, 130420743480120966239), (4315, 4315, 129129448990218778455), (4316, 4316, 127850939594276018272), (4317, 4317, 126585088707203978487), (4318, 4318, 125331770997231661869), (4319, 4319, 124090862373496694919), (4320, 4320, 122862239973759103881), (4321, 4321, 121645782152236736516), (4322, 4322, 120441368467561125263), (4323, 4323, 119248879670852599270), (4324, 4324, 118068197693913464624), (4325, 4325, 116899205637538083786), (4326, 4326, 115741787759938696818), (4327, 4327, 114595829465285838434), (4328, 4328, 113461217292362216271), (4329, 4329, 112337838903328927001), (4330, 4330, 111225583072602898021), (4331, 4331, 110124339675844453486), (4332, 4332, 109033999679053914342), (4333, 4333, 107954455127776152814), (4334, 4334, 106885599136412032489), (4335, 4335, 105827325877635675732), (4336, 4336, 104779530571916510626), (4337, 4337, 103742109477145060026), (4338, 4338, 102714959878361445570), (4339, 4339, 101697980077585589673), (4340, 4340, 100691069383748108587), (4341, 4341, 99694128102720899591), (4342, 4342, 98707057527446435239), (4343, 4343, 97729759928164787365), (4344, 4344, 96762138542737413233), (4345, 4345, 95804097567066745775), (4346, 4346, 94855542145610639381), (4347, 4347, 93916378361990732061), (4348, 4348, 92986513229693794120), (4349, 4349, 92065854682865142693), (4350, 4350, 91154311567193210587), (4351, 4351, 90251793630884366918), (4352, 7209, 89358211515727095958)]

def glob4 : ℕ := 9586267722316378333136

def runs5 : List (ℕ × ℕ × ℕ) := [(0, 3869, 0), (3870, 3870, 117891411534340416), (3871, 3871, 118003365365884832), (3872, 3872, 118142497817915632), (3873, 3873, 118309778699485857), (3874, 3874, 118506243714614000), (3875, 3875, 118732999730220784), (3876, 3876, 118991230558057344), (3877, 3877, 119282203314409936), (3878, 3878, 119607275422740224), (3879, 3879, 119967902336898832), (3880, 3880, 120365646072327329), (3881, 3881, 120802184644082176), (3882, 3882, 121279322528089808), (3883, 3883, 121799002271972433), (3884, 3884, 122363317408463344), (3885, 3885, 122974526843601472), (3886, 3886, 123635070914907521), (3887, 3887, 124347589352211520), (3888, 3888, 125114941406960912), (3889, 3889, 125940228455300528), (3890, 3890, 126826819438714384), (3891, 3891, 127778379559761185), (3892, 3892, 128798902724762960), (3893, 3893, 129892748313806592), (3894, 3894, 131064682954494369), (3895, 3895, 132319928107586672), (3896, 3896, 133664214418711361), (3897, 3897, 135103843966575457), (3898, 3898, 136645761768737344), (3899, 3899, 138297638163438305), (3900, 3900, 140067964018727888), (3901, 3901, 141966161128713249), (3902, 3902, 144002710642594561), (3903, 3903, 146189303004746816), (3904, 3904, 148539013640060801), (3905, 3905, 151066509583775585), (3906, 3906, 153788293464148960), (3907, 3907, 156722992757395361), (3908, 3908, 159891704160726145), (3909, 3909, 163318405377699297), (3910, 3910, 167030449719337889), (3911, 3911, 171059162928193825), (3912, 3912, 175440566763683745), (3913, 3913, 180216260507876224), (3914, 3914, 185434500102719073), (3915, 3915, 191151525678276192), (3916, 3916, 197433202520812001), (3917, 3917, 204357058891022081), (3918, 3918, 212014827613510880), (3919, 3919, 220515627973213472), (3920, 3920, 229989960998007424), (3921, 3921, 240594734489693345), (3922, 3922, 252519581731511680), (3923, 3923, 265994782207947425), (3924, 3924, 281301116219915201), (3925, 3925, 298781950887863552), (3926, 3926, 318857690434342785), (3927, 3927, 342042298767298176), (3928, 3928, 368960704080666241), (3929, 3929, 400364225088966656), (3930, 3930, 437138426358489729), (3931, 3931, 480294070670984193), (3932, 3932, 530928245872545857), (3933, 3933, 590142582921125121), (3934, 3934, 658914142398665473), (3935, 3935, 737935713077946368), (3936, 3936, 827469559337250816), (3937, 3937, 927271573052938881), (3938, 3938, 1036621648475692416), (3939, 3939, 1154448406185838337), (3940, 3940, 1279496979139485696), (3941, 3941, 1410483865867179008), (3942, 3942, 1546206273351255040), (3943, 3943, 1685600929114503680), (3944, 3944, 1827763518724643073), (3945, 3945, 1971943812691030529), (3946, 3946, 2117528830955691777), (3947, 3947, 2264022026854268672), (3948, 3948, 2411022821884376576), (3949, 3949, 2558208430385116673), (3950, 3950, 2705318567214926336), (3951, 3951, 2852142969000679936), (3952, 3952, 2998511386676653056), (3953, 3953, 3144285634457051136), (3954, 3954, 3289353299096887297), (3955, 3955, 3433622766982113281), (3956, 3956, 3577019287673805313), (3957, 3957, 3719481849030545921), (3958, 3958, 3860960687223585792), (3959, 3959, 4001415293928939520), (3960, 3960, 4140812813770374657), (3961, 3961, 4279126749218910721), (3962, 3962, 4416335908675384832), (3963, 3963, 4552423547730956801), (3964, 3964, 4687376664582061056), (3965, 3965, 4821185419235733504), (3966, 3966, 4953842652286987264), (3967, 3967, 5085343484501226496), (3968, 3968, 5215684982066035712), (3969, 3969, 5344865875565355009), (3970, 3970, 5472886323037706240), (3971, 3971, 5599747709516388353), (3972, 3972, 5725452476586727424), (3973, 3973, 5850003977206705153), (3974, 3974, 5973406351318923265), (3975, 3975, 6095664419187760128), (3976, 3976, 6216783589480020992), (3977, 3977, 6336769779829523456), (3978, 3978, 6455629348064783360), (3979, 3979, 6573369032440078337), (3980, 3980, 6689995899539180544), (3981, 3981, 6805517298883980289), (3982, 3982, 6919940823039878144), (3983, 3983, 7033274272813022209), (3984, 3984, 7145525626449625088), (3985, 3985, 7256703012712546305), (3986, 3986, 7366814686915829761), (3987, 3987, 7475869009901645824), (3988, 3988, 7583874429354631168), (3989, 3989, 7690839463204995073), (3990, 3990, 7796772684905243648), (3991, 3991, 7901682710413874176), (3992, 3992, 8005578186467094528), (3993, 3993, 8108467780232053760), (3994, 3994, 8210360170041856001), (3995, 3995, 8311264037089482753), (3996, 3996, 8411188058084120577), (3997, 3997, 8510140898609178625), (3998, 3998, 8608131207209977856), (3999, 3999, 8705167610147400705), (4000, 4000, 8801258706569878528), (4001, 4001, 8896413064399250432), (4002, 4002, 8990639216446090240), (4003, 4003, 9083945657073672193), (4004, 4004, 9176340839115162624), (4005, 4005, 9267833171268960257), (4006, 4006, 9358431015557982209), (4007, 4007, 9448142685271375872), (4008, 4008, 9536976443044548608), (4009, 4009, 9624940499115116544), (4010, 4010, 9712043009858226176), (4011, 4011, 9798292076451244032), (4012, 4012, 9883695743717564417), (4013, 4013, 9968261999066140673), (4014, 4014, 10051998771661285377), (4015, 4015, 10134913931603816448), (4016, 4016, 10217015289331040257), (4017, 4017, 10298310594954119169), (4018, 4018, 10378807537878114304), (4019, 4019, 10458513746404161536), (4020, 4020, 10537436787374624769), (4021, 4021, 10615584165916690432), (4022, 4022, 10692963325354967040), (4023, 4023, 10769581646980722688), (4024, 4024, 10845446450031280128), (4025, 4025, 10920564991664721921), (4026, 4026, 10994944466934104065), (4027, 4027, 11068592008910272513), (4028, 4028, 11141514688732248065), (4029, 4029, 11213719515733825536), (4030, 4030, 11285213437645621248), (4031, 4031, 11356003340724269057), (4032, 4032, 11426096049950412800), (4033, 4033, 11495498329375770625), (4034, 4034, 11564216882217822209), (4035, 4035, 11632258351246991360), (4036, 4036, 11699629319066644480), (4037, 4037, 11766336308373221377), (4038, 4038, 11832385782276431873), (4039, 4039, 11897784144680148992), (4040, 4040, 11962537740640755713), (4041, 4041, 12026652856604276736), (4042, 4042, 12090135720951531521), (4043, 4043, 12152992504180953088), (4044, 4044, 12215229319483981825), (4045, 4045, 12276852222952859649), (4046, 4046, 12337867214109792257), (4047, 4047, 12398280236247289857), (4048, 4048, 12458097176833810432), (4049, 4049, 12517323867973664768), (4050, 4050, 12575966086746339328), (4051, 4051, 12634029555673120768), (4052, 4052, 12691519943137081345), (4053, 4053, 12748442863741550592), (4054, 4054, 12804803878860791808), (4055, 4055, 12860608496938309632), (4056, 4056, 12915862173989537793), (4057, 4057, 12970570313951676416), (4058, 4058, 13024738269253451777), (4059, 4059, 13078371341048631296), (4060, 4060, 13131474779851692033), (4061, 4061, 13184053785769633793), (4062, 4062, 13236113509072648193), (4063, 4063, 13287659050554912769), (4064, 4064, 13338695461972975617), (4065, 4065, 13389227746456561664), (4066, 4066, 13439260858985037824), (4067, 4067, 13488799706728802304), (4068, 4068, 13537849149522708480), (4069, 4069, 13586414000284688385), (4070, 4070, 13634499025378045953), (4071, 4071, 13682108945107535873), (4072, 4072, 13729248434077884417), (4073, 4073, 13775922121617960961), (4074, 4074, 13822134592189255681), (4075, 4075, 13867890385792131073), (4076, 4076, 13913193998369734657), (4077, 4077, 13958049882209560577), (4078, 4078, 14002462446342567937), (4079, 4079, 14046436056925763584), (4080, 4080, 14089975037706530817), (4081, 4081, 14133083670273685505), (4082, 4082, 14175766194586816513), (4083, 4083, 14218026809278097408), (4084, 4084, 14259869672106690560), (4085, 4085, 14301298900254402560), (4086, 4086, 14342318570774870017), (4087, 4087, 14382932720882987008), (4088, 4088, 14423145348470870016), (4089, 4089, 14462960412334180352), (4090, 4090, 14502381832625256449), (4091, 4091, 14541413491144904705), (4092, 4092, 14580059231775975424), (4093, 4093, 14618322860856791041), (4094, 4094, 14656208147390730240), (4095, 4095, 14693718823618004993), (4096, 4096, 14730858585131358208), (4097, 4097, 14767631091457839105), (4098, 4098, 14804039966182389761), (4099, 4099, 14840088797436243968), (4100, 4100, 14875781138221058048), (4101, 4101, 14911120506670323712), (4102, 4102, 14946110386441369600), (4103, 4103, 14980754227030507520), (4104, 4104, 15015055444115150849), (4105, 4105, 15049017419818088449), (4106, 4106, 15082643503118962689), (4107, 4107, 15115937010113015809), (4108, 4108, 15148901224326828032), (4109, 4109, 15181539397107202049), (4110, 4110, 15213854747764850688), (4111, 4111, 15245850464109584385), (4112, 4112, 15277529702512060416), (4113, 4113, 15308895588449632257), (4114, 4114, 15339951216576995329), (4115, 4115, 15370699651190962177), (4116, 4116, 15401143926448189441), (4117, 4117, 15431287046656487424), (4118, 4118, 15461131986625327104), (4119, 4119, 15490681691875033089), (4120, 4120, 15519939078920056833), (4121, 4121, 15548907035611873280), (4122, 4122, 15577588421417689088), (4123, 4123, 15605986067618557952), (4124, 4124, 15634102777660436481), (4125, 4125, 15661941327331280896), (4126, 4126, 15689504465185679360), (4127, 4127, 15716794912654323712), (4128, 4128, 15743815364401242113), (4129, 4129, 15770568488490336256), (4130, 4130, 15797056926817060865), (4131, 4131, 15823283295143870465), (4132, 4132, 15849250183511416832), (4133, 4133, 15874960156474347520), (4134, 4134, 15900415753270953984), (4135, 4135, 15925619488133058560), (4136, 4136, 15950573850514432000), (4137, 4137, 15975281305332742144), (4138, 4138, 15999744293209196544), (4139, 4139, 16023965230705944576), (4140, 4140, 16047946510561220608), (4141, 4141, 16071690501938317313), (4142, 4142, 16095199550575947776), (4143, 4143, 16118475979177457664), (4144, 4144, 16141522087492603905), (4145, 4145, 16164340152541380608), (4146, 4146, 16186932428997591041), (4147, 4147, 16209301149182648321), (4148, 4148, 16231448523444926464), (4149, 4149, 16253376740359571456), (4150, 4150, 16275087966877327361), (4151, 4151, 16296584348535928833), (4152, 4152, 16317868009751095297), (4153, 4153, 16338941053959079937), (4154, 4154, 16359805563822178304), (4155, 4155, 16380463601497749504), (4156, 4156, 16400917208758208513), (4157, 4157, 16421168407190544385), (4158, 4158, 16441219198476120065), (4159, 4159, 16461071564504573952), (4160, 4160, 16480727467650025472), (4161, 4161, 16500188850864515072), (4162, 4162, 16519457637950580737), (4163, 4163, 16538535733650673664), (4164, 4164, 16557425023998957568), (4165, 4165, 16576127376357519361), (4166, 4166, 16594644639599108096), (4167, 4167, 16612978644454250497), (4168, 4168, 16631131203441922048), (4169, 4169, 16649104111312961537), (4170, 4170, 16666899144960163840), (4171, 4171, 16684518063858835457), (4172, 4172, 16701962609972926464), (4173, 4173, 16719234508192768001), (4174, 4174, 16736335466254051329), (4175, 4175, 16753267175089133569), (4176, 4176, 16770031308892815360), (4177, 4177, 16786629525370474496), (4178, 4178, 16803063465800343552), (4179, 4179, 16819334755261732864), (4180, 4180, 16835445002777944064), (4181, 4181, 16851395801474367488), (4182, 4182, 16867188728751894529), (4183, 4183, 16882825346357628928), (4184, 4184, 16898307200723963905), (4185, 4185, 16913635822867445760), (4186, 4186, 16928812728792623104), (4187, 4187, 16943839419455266816), (4188, 4188, 16958717381011439617), (4189, 4189, 16973448084861974528), (4190, 4190, 16988032987983773697), (4191, 4191, 17002473532818632704), (4192, 4192, 17016771147686848513), (4193, 4193, 17030927246655838208), (4194, 4194, 17044943229934399488), (4195, 4195, 17058820483823378432), (4196, 4196, 17072560380954265601), (4197, 4197, 17086164280321939456), (4198, 4198, 17099633527606290433), (4199, 4199, 17112969455065597953), (4200, 4200, 17126173381855631361), (4201, 4201, 17139246614056992768), (4202, 4202, 17152190444906522625), (4203, 4203, 17165006154736123904), (4204, 4204, 17177695011356082177), (4205, 4205, 17190258269905432576), (4206, 4206, 17202697173233149952), (4207, 4207, 17215012951848882177), (4208, 4208, 17227206824044009472), (4209, 4209, 17239279996183918593), (4210, 4210, 17251233662585780225), (4211, 4211, 17263069005825736705), (4212, 4212, 17274787196769327105), (4213, 4213, 17286389394686830592), (4214, 4214, 17297876747436691456), (4215, 4215, 17309250391492294657), (4216, 4216, 17320511452036569088), (4217, 4217, 17331661043246092289), (4218, 4218, 17342700268141201408), (4219, 4219, 17353630218954596352), (4220, 4220, 17364451977048461312), (4221, 4221, 17375166613125115905), (4222, 4222, 17385775187245807617), (4223, 4223, 17396278749022089216), (4224, 4224, 17406678337736865793), (4225, 4225, 17416974982290305025), (4226, 4226, 17427169701475315713), (4227, 4227, 17437263503973634048), (4228, 4228, 17447257388559904769), (4229, 4229, 17457152344008429568), (4230, 4230, 17466949349434892288), (4231, 4231, 17476649374218561537), (4232, 4232, 17486253378115299329), (4233, 4233, 17495762311439632385), (4234, 4234, 17505177115088685057), (4235, 4235, 17514498720634986496), (4236, 4236, 17523728050488463360), (4237, 4237, 17532866017882425344), (4238, 4238, 17541913527051278337), (4239, 4239, 17550871473214574592), (4240, 4240, 17559740742840801280), (4241, 4241, 17568522213559478272), (4242, 4242, 17577216754335502336), (4243, 4243, 17585825225554997249), (4244, 4244, 17594348479022321664), (4245, 4245, 17602787358220032000), (4246, 4246, 17611142698233933825), (4247, 4247, 17619415325835397120), (4248, 4248, 17627606059739164673), (4249, 4249, 17635715710419951616), (4250, 4250, 17643745080456812544), (4251, 4251, 17651694964418512896), (4252, 4252, 17659566149047803905), (4253, 4253, 17667359413250873345), (4254, 4254, 17675075528262522880), (4255, 4255, 17682715257722435584), (4256, 4256, 17690279357662224384), (4257, 4257, 17697768576650784768), (4258, 4258, 17705183655850582016), (4259, 4259, 17712525329108570113), (4260, 4260, 17719794322940129280), (4261, 4261, 17726991356777963520), (4262, 4262, 17734117142883788801), (4263, 4263, 17741172386418587648), (4264, 4264, 17748157785689659393), (4265, 4265, 17755074031953530880), (4266, 4266, 17761921809750415360), (4267, 4267, 17768701796794394625), (4268, 4268, 17775414664040286208), (4269, 4269, 17782061075927656449), (4270, 4270, 17788641690179903488), (4271, 4271, 17795157158153674753), (4272, 4272, 17801608124618700800), (4273, 4273, 17807995228088363008), (4274, 4274, 17814319100687063040), (4275, 4275, 17820580368319490049), (4276, 4276, 17826779650643408897), (4277, 4277, 17832917561237809153), (4278, 4278, 17838994707574439936), (4279, 4279, 17845011691167025152), (4280, 4280, 17850969107541544961), (4281, 4281, 17856867546295033857), (4282, 4282, 17862707591225266176), (4283, 4283, 17868489820406372353), (4284, 4284, 17874214806067339264), (4285, 4285, 17879883114916562945), (4286, 4286, 17885495307929819137), (4287, 4287, 17891051940602320897), (4288, 4288, 17896553562896361472), (4289, 4289, 17902000719385147392), (4290, 4290, 17907393949199265792), (4291, 4291, 17912733786151548928), (4292, 4292, 17918020758789879809), (4293, 4293, 17923255390359871488), (4294, 4294, 17928438199053670401), (4295, 4295, 17933569697792421888), (4296, 4296, 17938650394563741697), (4297, 4297, 17943680792203028481), (4298, 4298, 17948661388622469120), (4299, 4299, 17953592676860354561), (4300, 4300, 17958475144968286209), (4301, 4301, 17963309276220936192), (4302, 4302, 17968095549163929601), (4303, 4303, 17972834437481488384), (4304, 4304, 17977526410294806528), (4305, 4305, 17982171932010786816), (4306, 4306, 17986771462457815040), (4307, 4307, 17991325456931244033), (4308, 4308, 17995834366166470657), (4309, 4309, 18000298636491436033), (4310, 4310, 18004718709798811649), (4311, 4311, 18009095023607693313), (4312, 4312, 18013428011106863105), (4313, 4313, 18017718101179617280), (4314, 4314, 18021965718518239232), (4315, 4315, 18026171283575957505), (4316, 4316, 18030335212590426112), (4317, 4317, 18034457917805193217), (4318, 4318, 18038539807240040448), (4319, 4319, 18042581285019844609), (4320, 4320, 18046582751125966848), (4321, 4321, 18050544601706430464), (4322, 4322, 18054467228934664193), (4323, 4323, 18058351021066328065), (4324, 4324, 18062196362567952385), (4325, 4325, 18066003634082793473), (4326, 4326, 18069773212468439040), (4327, 4327, 18073505470906372096), (4328, 4328, 18077200778830485504), (4329, 4329, 18080859502053953537), (4330, 4330, 18084482002715043841), (4331, 4331, 18088068639403323392), (4332, 4332, 18091619767213264897), (4333, 4333, 18095135737598461952), (4334, 4334, 18098616898659661824), (4335, 4335, 18102063594998302721), (4336, 4336, 18105476167768643585), (4337, 4337, 18108854954802044929), (4338, 4338, 18112200290549864448), (4339, 4339, 18115512506207082496), (4340, 4340, 18118791929636423680), (4341, 4341, 18122038885473210368), (4342, 4342, 18125253695157499905), (4343, 4343, 18128436676875272192), (4344, 4344, 18131588145771139072), (4345, 4345, 18134708413816420353), (4346, 4346, 18137797789839960064), (4347, 4347, 18140856579721895936), (4348, 4348, 18143885086242578432), (4349, 4349, 18146883609221339137), (4350, 4350, 18149852445437298688), (4351, 4351, 18152791888840192000), (4352, 7209, 18446744073727864833)]

def glob5 : ℕ := 19871652571492093870

/-- Every run of kind `k` is ordered, sound and below the global fee. -/
def runsOk (k : ℕ) (runs : List (ℕ × ℕ × ℕ)) (G : ℕ) : Bool :=
  runs.all fun e => decide (e.1 ≤ e.2.1) && okOf k rcPar (lowerQ rcPar.g e.1) (upperQ rcPar.g e.2.1) e.2.2 &&
    decide (e.2.2 ≤ G)

theorem runs0_ok : runsOk 0 runs0 glob0 = true := by decide +kernel
theorem runs1_ok : runsOk 1 runs1 glob1 = true := by decide +kernel
theorem runs2_ok : runsOk 2 runs2 glob2 = true := by decide +kernel
theorem runs3_ok : runsOk 3 runs3 glob3 = true := by decide +kernel
theorem runs4_ok : runsOk 4 runs4 glob4 = true := by decide +kernel
theorem runs5_ok : runsOk 5 runs5 glob5 = true := by decide +kernel

theorem entries0 : (runEntries runs0).map Prod.fst = List.range 7210 :=
  entries_of_contig runs0 (by decide +kernel)
theorem entries1 : (runEntries runs1).map Prod.fst = List.range 7210 :=
  entries_of_contig runs1 (by decide +kernel)
theorem entries2 : (runEntries runs2).map Prod.fst = List.range 7210 :=
  entries_of_contig runs2 (by decide +kernel)
theorem entries3 : (runEntries runs3).map Prod.fst = List.range 7210 :=
  entries_of_contig runs3 (by decide +kernel)
theorem entries4 : (runEntries runs4).map Prod.fst = List.range 7210 :=
  entries_of_contig runs4 (by decide +kernel)
theorem entries5 : (runEntries runs5).map Prod.fst = List.range 7210 :=
  entries_of_contig runs5 (by decide +kernel)

theorem par_ok : parOk rcPar = true := by decide +kernel
theorem glob0_ok : globOk 0 rcPar glob0 = true := by decide +kernel
theorem glob1_ok : globOk 1 rcPar glob1 = true := by decide +kernel
theorem glob2_ok : globOk 2 rcPar glob2 = true := by decide +kernel
theorem glob3_ok : globOk 3 rcPar glob3 = true := by decide +kernel
theorem glob4_ok : globOk 4 rcPar glob4 = true := by decide +kernel
theorem glob5_ok : globOk 5 rcPar glob5 = true := by decide +kernel

/-- The packed (reversed, 4096-bit limbs) fee vector of a run table. -/
def packRuns (runs : List (ℕ × ℕ × ℕ)) : ℕ :=
  ClaudeWCT.Numerics.SharedFees.packList 4096 13 ((runEntries runs).map Prod.snd).reverse

open Lean Elab in
elab "rc_pack% " k:num : term => do
  let v := match k.getNat with
    | 0 => packRuns runs0 | 1 => packRuns runs1 | 2 => packRuns runs2
    | 3 => packRuns runs3 | 4 => packRuns runs4 | _ => packRuns runs5
  return ClaudeWCT.Numerics.SharedGeneratedCoordinate.limbExpr v

section ChunkPack
open Finset

/-- Horner packing of a short list: `∑ i, xs[i] * (2^bits)^i`. -/
def hornerPack (bits : ℕ) (xs : List ℕ) : ℕ := xs.foldr (fun x acc => x + (acc <<< bits)) 0

/-- Chunked packing (`k` chunks of `c` entries, Horner inside a chunk): the same value as
`SharedFees.packList`, with far fewer kernel list steps. -/
def chunkPack (bits c : ℕ) : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | k+1, xs => hornerPack bits (xs.take c) + (chunkPack bits c k (xs.drop c) <<< (bits * c))

theorem hornerPack_sum (bits : ℕ) : ∀ (xs : List ℕ) (n : ℕ), xs.length ≤ n →
    hornerPack bits xs = ∑ i ∈ range n, (xs[i]?.getD 0) * (2 ^ bits) ^ i
  | [], n, _ => by simp [hornerPack]
  | x :: xs, n, h => by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at h; omega⟩
      have ih := hornerPack_sum bits xs m (by simp at h; omega)
      have hstep : hornerPack bits (x :: xs) = x + hornerPack bits xs * 2 ^ bits := by
        simp only [hornerPack, List.foldr_cons, Nat.shiftLeft_eq]
      rw [hstep, ih, Finset.sum_range_succ', Finset.sum_mul]
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, pow_zero, mul_one,
        pow_succ, ← mul_assoc]
      ring

theorem sum_extend (B : ℕ) (xs : List ℕ) (n N : ℕ) (hl : xs.length ≤ n) (hN : n ≤ N) :
    ∑ i ∈ range N, (xs[i]?.getD 0) * B ^ i = ∑ i ∈ range n, (xs[i]?.getD 0) * B ^ i := by
  obtain ⟨d, rfl⟩ : ∃ d, N = n + d := ⟨N - n, by omega⟩
  rw [Finset.sum_range_add]
  have : ∑ j ∈ range d, (xs[n + j]?.getD 0) * B ^ (n + j) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [List.getElem?_eq_none (by omega)]
    simp
  rw [this, Nat.add_zero]

theorem chunkPack_sum (bits c : ℕ) : ∀ (k : ℕ) (xs : List ℕ), xs.length ≤ c * k →
    chunkPack bits c k xs = ∑ i ∈ range (c * k), (xs[i]?.getD 0) * (2 ^ bits) ^ i
  | 0, xs, _ => by simp [chunkPack]
  | k+1, xs, h => by
      have ih := chunkPack_sum bits c k (xs.drop c) (by simp; rw [Nat.mul_succ] at h; omega)
      have hh := hornerPack_sum bits (xs.take c) c (by simp)
      simp only [chunkPack]
      rw [ih, hh, Nat.shiftLeft_eq, show c * (k + 1) = c + c * k by ring, Finset.sum_range_add,
        Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [List.getElem?_take, if_pos (Finset.mem_range.mp hi)]
      · apply Finset.sum_congr rfl
        intro i _
        rw [List.getElem?_drop, pow_add, pow_mul]
        ring

theorem packList_sum (bits h : ℕ) (xs : List ℕ) :
    SharedFees.packList bits h xs = ∑ i ∈ range (2 ^ h), (xs[i]?.getD 0) * (2 ^ bits) ^ i := by
  rw [SharedFees.packList_eq_tree, SharedFees.packTree_sum]
  simp only [Nat.zero_add]

theorem packRuns_eq_chunk (runs : List (ℕ × ℕ × ℕ))
    (hidx : (runEntries runs).map Prod.fst = List.range 7210) :
    packRuns runs = chunkPack 4096 64 113 ((runEntries runs).map Prod.snd).reverse := by
  have hlen : (((runEntries runs).map Prod.snd).reverse).length = 7210 := by
    have := congrArg List.length hidx
    simpa using this
  rw [packRuns, packList_sum, chunkPack_sum _ _ _ _ (by omega),
    sum_extend _ _ (64 * 113) (2 ^ 13) (by omega) (by norm_num)]

end ChunkPack

noncomputable def Pack0 : ℕ := rc_pack% 0
noncomputable def Pack1 : ℕ := rc_pack% 1
noncomputable def Pack2 : ℕ := rc_pack% 2
noncomputable def Pack3 : ℕ := rc_pack% 3
noncomputable def Pack4 : ℕ := rc_pack% 4
noncomputable def Pack5 : ℕ := rc_pack% 5
theorem pack0_eq : packRuns runs0 = Pack0 :=
  (packRuns_eq_chunk runs0 entries0).trans (by decide +kernel)
theorem pack1_eq : packRuns runs1 = Pack1 :=
  (packRuns_eq_chunk runs1 entries1).trans (by decide +kernel)
theorem pack2_eq : packRuns runs2 = Pack2 :=
  (packRuns_eq_chunk runs2 entries2).trans (by decide +kernel)
theorem pack3_eq : packRuns runs3 = Pack3 :=
  (packRuns_eq_chunk runs3 entries3).trans (by decide +kernel)
theorem pack4_eq : packRuns runs4 = Pack4 :=
  (packRuns_eq_chunk runs4 entries4).trans (by decide +kernel)
theorem pack5_eq : packRuns runs5 = Pack5 :=
  (packRuns_eq_chunk runs5 entries5).trans (by decide +kernel)

end ClaudeWCT.Numerics.RouteCData
end
-- ==== merged from ClaudeWCT_Numerics_RouteCRows ====
section

/-! Route C row dot products and Poisson-envelope certificates at the installed gate (RC938: #938's
cap-777 law through the binomial thinning, so the envelope is `u = 13283369e-8`, `λ = 2018833e-6` on uniform
rows; generated by rc938/lean-notes/gen/rcgen938.py; R6 campaign stream RC, RC_SPEC L7 + L8). The forest numerals of rows 1..4 and the binned masses of rows 1..18
are cached once below, so the six envelope checks do not each re-evaluate them in the kernel. -/

namespace ClaudeWCT.Numerics.RouteCRows
open ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.RouteCData
open ClaudeWCT.Numerics.SharedMoments (forestMoment fieldSize alphabetSize)
open ClaudeWCT.Numerics.N600 (poissonCheckQ)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open Lean Elab Term ClaudeWCT.Numerics.SharedGeneratedCoordinate in
/-- Proposes the packed forest numeral of a small row (evaluated by the elaborator; the kernel
re-checks it in `forest_small_k`). -/
elab "rc_small_forest% " r:num : term => do
  return limbExpr (ClaudeWCT.Numerics.SharedPathPacked.forestFast r.getNat)

/-- Packed forest numerals of rows 1..4 (rows 5..18 are main's `SharedGeneratedForest.Forest_k`). -/
noncomputable def Forest_1 : ℕ := rc_small_forest% 1
noncomputable def Forest_2 : ℕ := rc_small_forest% 2
noncomputable def Forest_3 : ℕ := rc_small_forest% 3
noncomputable def Forest_4 : ℕ := rc_small_forest% 4

theorem forest_small_1 : SharedPathPacked.forest 1 = Forest_1 := by
  rw [SharedPathPacked.forest_eq_fast]; decide +kernel
theorem forest_small_2 : SharedPathPacked.forest 2 = Forest_2 := by
  rw [SharedPathPacked.forest_eq_fast]; decide +kernel
theorem forest_small_3 : SharedPathPacked.forest 3 = Forest_3 := by
  rw [SharedPathPacked.forest_eq_fast]; decide +kernel
theorem forest_small_4 : SharedPathPacked.forest 4 = Forest_4 := by
  rw [SharedPathPacked.forest_eq_fast]; decide +kernel

/-- Packed forest polynomial of row `r` (cached numerals for rows 1..18). -/
noncomputable def forestN (r : ℕ) : ℕ :=
  match r with
  | 1 => Forest_1
  | 2 => Forest_2
  | 3 => Forest_3
  | 4 => Forest_4
  | 5 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_5
  | 6 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_6
  | 7 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_7
  | 8 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_8
  | 9 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_9
  | 10 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_10
  | 11 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_11
  | 12 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_12
  | 13 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_13
  | 14 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_14
  | 15 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_15
  | 16 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_16
  | 17 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_17
  | 18 => ClaudeWCT.Numerics.SharedGeneratedForest.Forest_18
  | r => ClaudeWCT.Numerics.SharedPathPacked.forestFast r

/-- Row dot product: binned first moments times fees, plus the global fee on the unbinned mass. -/
noncomputable def dotRow (pack G r F : ℕ) : ℕ :=
  ClaudeWCT.Numerics.SharedFees.packedDot F pack +
    G * (forestMoment r - ClaudeWCT.Numerics.SharedFees.packedDot F
      ClaudeWCT.Numerics.SharedGeneratedFeeVector.MassFee)

open Lean Elab Term ClaudeWCT.Numerics.SharedGeneratedCoordinate in
/-- Proposes the binned mass `packedDot (forestN r) MassFee` of row `r` (re-checked by `mass_checked`). -/
elab "rc_mass% " r:num : term => do
  let k := r.getNat
  let fname := if k ≤ 4 then s!"ClaudeWCT.Numerics.RouteCRows.Forest_{k}"
    else s!"ClaudeWCT.Numerics.SharedGeneratedForest.Forest_{k}"
  let fInfo ← getConstInfo fname.toName
  let mInfo ← getConstInfo ``ClaudeWCT.Numerics.SharedGeneratedFeeVector.MassFee
  match limbValue? fInfo.value!, limbValue? mInfo.value! with
  | some f, some m => return limbExpr (ClaudeWCT.Numerics.SharedFees.packedDot f m)
  | _, _ => throwError "forest or mass vector is not a Nat literal"

/-- Binned masses of rows 1..18. -/
noncomputable def massN (r : ℕ) : ℕ :=
  match r with
  | 1 => rc_mass% 1
  | 2 => rc_mass% 2
  | 3 => rc_mass% 3
  | 4 => rc_mass% 4
  | 5 => rc_mass% 5
  | 6 => rc_mass% 6
  | 7 => rc_mass% 7
  | 8 => rc_mass% 8
  | 9 => rc_mass% 9
  | 10 => rc_mass% 10
  | 11 => rc_mass% 11
  | 12 => rc_mass% 12
  | 13 => rc_mass% 13
  | 14 => rc_mass% 14
  | 15 => rc_mass% 15
  | 16 => rc_mass% 16
  | 17 => rc_mass% 17
  | 18 => rc_mass% 18
  | r => ClaudeWCT.Numerics.SharedFees.packedDot (forestN r) ClaudeWCT.Numerics.SharedGeneratedFeeVector.MassFee

theorem mass_checked : ∀ r, r < 19 →
    ClaudeWCT.Numerics.SharedFees.packedDot (forestN r) ClaudeWCT.Numerics.SharedGeneratedFeeVector.MassFee =
      massN r := by
  decide +kernel

/-- `dotRow` with the cached binned mass. -/
noncomputable def dotRowC (pack G r : ℕ) : ℕ :=
  ClaudeWCT.Numerics.SharedFees.packedDot (forestN r) pack + G * (forestMoment r - massN r)

theorem dotRowC_eq (pack G r : ℕ) (h18 : r ≤ 18) : dotRowC pack G r = dotRow pack G r (forestN r) := by
  unfold dotRowC dotRow
  rw [mass_checked r (by omega)]

noncomputable def rowAll (pack G r : ℕ) : ℕ :=
  if 1 ≤ r ∧ r ≤ 18 then dotRowC pack G r else G * forestMoment r
def rowLong (r : ℕ) : ℕ := if 80 < r then feeScale * forestMoment r else 0

/-- Bank price scale at the gate: `2^31 * gate/2^66 * alphabetSize`. -/
def pst : ℕ := rcPar.g * 2 ^ 24 * 563 ^ 9

def meanN : ℕ := 91238
def meanD : ℕ := 100000
def secN : ℕ := 75397
def secD : ℕ := 10000000
def countN : ℕ := 46267
def countD : ℕ := 10000000
def overN : ℕ := 21443
def overD : ℕ := 10000000
def mgfN : ℕ := 11534
def mgfD : ℕ := 1000
def scarfN : ℕ := 10609
def scarfD : ℕ := 10000000
def longN : ℕ := 1
def longD : ℕ := 100000000000000000000000000000000000000000000000000

theorem env_mean : poissonCheckQ fieldSize 13283369 100000000 2018833 1000000
    (fun r => 16 ^ r * rowAll Pack0 glob0 r) (glob0 * alphabetSize) (glob0 * pst) feeScale meanN meanD 80 = true := by
  decide +kernel
theorem env_sec : poissonCheckQ fieldSize 13283369 100000000 2018833 1000000
    (fun r => 16 ^ r * rowAll Pack1 glob1 r) (glob1 * alphabetSize) (glob1 * pst) feeScale secN secD 80 = true := by
  decide +kernel
theorem env_count : poissonCheckQ fieldSize 13283369 100000000 2018833 1000000
    (fun r => 16 ^ r * rowAll Pack2 glob2 r) (glob2 * alphabetSize) (glob2 * pst) feeScale countN countD 80 = true := by
  decide +kernel
theorem env_over : poissonCheckQ fieldSize 13283369 100000000 2018833 1000000
    (fun r => 16 ^ r * rowAll Pack3 glob3 r) (glob3 * alphabetSize) (glob3 * pst) feeScale overN overD 80 = true := by
  decide +kernel
theorem env_mgf : poissonCheckQ fieldSize 13283369 100000000 2018833 1000000
    (fun r => 16 ^ r * rowAll Pack4 glob4 r) (glob4 * alphabetSize) (glob4 * pst) feeScale mgfN mgfD 80 = true := by
  decide +kernel
theorem env_scarf : poissonCheckQ fieldSize 13283369 100000000 2018833 1000000
    (fun r => 16 ^ r * rowAll Pack5 glob5 r) (glob5 * alphabetSize) (glob5 * pst) feeScale scarfN scarfD 80 = true := by
  decide +kernel
theorem env_long : poissonCheckQ fieldSize 13283369 100000000 2018833 1000000
    (fun r => 16 ^ r * rowLong r) (feeScale * alphabetSize) (feeScale * pst) feeScale longN longD 80 = true := by
  decide +kernel

/-! ### Parameter values and the route-C totals (generated) -/

theorem rc_c0 : (rcPar.c0 : ℝ) = (9 / 16 : ℝ) := by norm_num [rcPar]
theorem rc_a : (rcPar.a : ℝ) = (101 / 10 : ℝ) := by norm_num [rcPar]
theorem rc_θ : (rcPar.θ : ℝ) = 99847 / 50000 - 1 / 1024 := by norm_num [rcPar]
theorem rc_m : (rcPar.m : ℝ) = (meanN : ℝ) / meanD := by norm_num [rcPar, meanN, meanD]
theorem rc_vv : (rcPar.vv : ℝ) = (secN : ℝ) / secD := by norm_num [rcPar, secN, secD]

/-- `exp (B - a θ_mid) ≤ (449 / 2500000 : ℝ)` from the Taylor lower bound of `exp (a θ_mid - B)`. -/
theorem rc_exp_mid : Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ) ≤ (449 / 2500000 : ℝ) := by
  have hx : (mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ ≤ -(69 / 8 : ℝ) := by norm_num [rcPar, mgfN, mgfD]
  have h0 : (0 : ℝ) ≤ (69 / 8 : ℝ) := by norm_num
  have he := Real.sum_le_exp_of_nonneg h0 30
  have hs : (2500000 / 449 : ℝ) ≤ ∑ i ∈ Finset.range 30, (69 / 8 : ℝ) ^ i / (Nat.factorial i) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  refine (Real.exp_le_exp.mpr hx).trans ?_
  rw [Real.exp_neg, show (449 / 2500000 : ℝ) = ((2500000 / 449 : ℝ))⁻¹ by norm_num]
  exact inv_anti₀ (by norm_num) (hs.trans he)

/-- Route-C total at the middle threshold: `K0 + K1 + O Λ + tF ≤ (1153 / 1000000 : ℝ)`. -/
theorem rc_total_mid :
    3 / (8 * (rcPar.a : ℝ)) * Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * rcPar.θ) + (scarfN : ℝ) / scarfD +
      (overN : ℝ) / overD * ((countN : ℝ) / countD) + (longN : ℝ) / longD ≤ (1153 / 1000000 : ℝ) := by
  have hk : (0 : ℝ) ≤ 3 / (8 * (rcPar.a : ℝ)) := by rw [rc_a]; norm_num
  have h1 := mul_le_mul_of_nonneg_left rc_exp_mid hk
  have h2 : 3 / (8 * (rcPar.a : ℝ)) * (449 / 2500000 : ℝ) + (scarfN : ℝ) / scarfD +
      (overN : ℝ) / overD * ((countN : ℝ) / countD) + (longN : ℝ) / longD ≤ (1153 / 1000000 : ℝ) := by
    rw [rc_a]; norm_num [scarfN, scarfD, overN, overD, countN, countD, longN, longD]
  linarith

/-- Low threshold: `3/(8a) exp (B - a (1 - 1/1024)) + O ≤ 49/100`. -/
theorem rc_total_low :
    3 / (8 * (rcPar.a : ℝ)) * Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * (1 - 1 / 1024)) + (overN : ℝ) / overD ≤
      49 / 100 := by
  have hy : (mgfN : ℝ) / mgfD - rcPar.a * (1 - 1 / 1024) ≤ 2 := by norm_num [rcPar, mgfN, mgfD]
  have he : Real.exp ((mgfN : ℝ) / mgfD - rcPar.a * (1 - 1 / 1024)) ≤ (2.7182818286 : ℝ) ^ 2 := by
    refine (Real.exp_le_exp.mpr hy).trans ?_
    have hp : Real.exp (2 : ℝ) = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [hp]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le _
  have hk : (0 : ℝ) ≤ 3 / (8 * (rcPar.a : ℝ)) := by rw [rc_a]; norm_num
  have h1 := mul_le_mul_of_nonneg_left he hk
  have h2 : 3 / (8 * (rcPar.a : ℝ)) * (2.7182818286 : ℝ) ^ 2 + (overN : ℝ) / overD ≤ 49 / 100 := by
    rw [rc_a]; norm_num [overN, overD]
  linarith

end ClaudeWCT.Numerics.RouteCRows
end
-- ==== merged from ClaudeWCT_Numerics_V6Budgets ====
section

/-! # img-v6 keygen and expand moment certificates (opus-crumbs PORT v6 D, E; requests N1, N2 of the top-bytes porter)

* **N1 (keygen).** `z = 2^(1/2^20)`. For heights `h = 1..11` (`p_h = 2^-h`) the explicit rationals `m_h = keygenM (h-1)/2^128`
  satisfy `z·(p_h + (1 - p_h)·m_h) ≤ m_h` and `z ≤ m_h`, and `z^1003010 · Π_h m_h^(2^(12-h)) ≤ 2` (value 1.9993336;
  exact 1.99933317 with `m_h = z p/(1 - z(1-p))`; 1,003,010 = 1,007,104 − 4,094 first trials folded into `m_h`).
* **N2 (expand excess, max-of-two form).** `w = 2^((8/7)/2^20) = 2^(1/917504)`:
  `w^427665 · 2^-38 · Σ_{a,b<2^19} w^max(a,b) ≤ 2` (value ≈ 1.806; certified through 64 blocks of `2^13`, 1.8121).
Both are fixed-point certificates (`CanonicalCompression.powerUp`/`mulUp`, scale `2^128`): bounded literals only. -/

namespace ClaudeWCT.Numerics.V6Budgets
open CanonicalCompression Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## Generic fixed-point products -/

/-- `Π (b/scale)^e` over a list, rounded up. -/
def prodUp : List (Nat × Nat) → Nat
  | [] => scale
  | e :: es => mulUp (powerUp e.1 e.2) (prodUp es)

theorem prodUp_ratio_ge (l : List (Nat × Nat)) :
    (l.map fun e => ((e.1:ℝ)/scale)^e.2).prod ≤ (prodUp l:ℝ)/scale := by
  induction l with
  | nil => simp [prodUp, scale]
  | cons e es ih =>
    simp only [List.map_cons, List.prod_cons, prodUp]
    have hs : (0:ℝ) ≤ (powerUp e.1 e.2:ℝ)/scale := by positivity
    calc ((e.1:ℝ)/scale)^e.2 * (es.map fun e => ((e.1:ℝ)/scale)^e.2).prod
        ≤ ((powerUp e.1 e.2:ℝ)/scale) * ((prodUp es:ℝ)/scale) :=
          mul_le_mul (powerUp_ratio_ge _ _) ih (List.prod_nonneg (fun x hx => by
            obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx; positivity)) hs
      _ ≤ _ := mulUp_ratio_ge _ _

/-! ## N1: keygen -/

def keygenZNum : Nat := 10000000000 * 2^20
def keygenZDen : Nat := 10000000000 * 2^20 - 6931471808

theorem keygen_z_le : (2:ℝ)^(1/((2^20:ℕ):ℝ)) ≤ (keygenZNum:ℝ)/keygenZDen := by
  refine (SigGolfCandidate.Budget.rpow_two_inv_le (2^20) (by norm_num)).trans_eq ?_
  norm_num [keygenZNum, keygenZDen]

/-- `ceil(zK·2^128)` for `zK = keygenZNum/keygenZDen`. -/
def keygenZFix : Nat := 340282591860207742199512195861285667957

theorem keygenZ_fix : (keygenZNum:ℝ)/keygenZDen ≤ (keygenZFix:ℝ)/scale := by
  rw [div_le_div_iff₀ (by norm_num [keygenZDen]) (by norm_num [scale])]
  norm_num [keygenZNum, keygenZDen, keygenZFix, scale]

/-- Numerators (over `2^128`) of `m_h`, `h = 1..11`. -/
def keygenM (i : Fin 11) : Nat := [340282816799774407537068188648745253159, 340283266679799900375442987250372351646, 340284166443419551218384362561208825066, 340285965984933645675468342432275971788, 340289565125062062546873124227847124433, 340296763633728263433442488925276359072, 340311161564765781666276742203532247926, 340339961082202552920555136142458666879, 340397574742854560594048527114301253582, 340512860601946649704814937144529402626, 340743666749029370512803021620717668290].getD i.val 0

theorem keygen_step_zK : ∀ i : Fin 11,
    (keygenZNum:ℝ)/keygenZDen * (1/2^(i.val+1) + (1 - 1/2^(i.val+1)) * ((keygenM i:ℝ)/2^128)) ≤
      (keygenM i:ℝ)/2^128 ∧ (keygenZNum:ℝ)/keygenZDen ≤ (keygenM i:ℝ)/2^128 := by
  intro i
  fin_cases i <;> norm_num [keygenM, keygenZNum, keygenZDen]

/-- `m_h` is a geometric retry bound for every `0 ≤ z ≤ zK` (in particular `z = 2^(1/2^20)`). -/
theorem keygen_step (i : Fin 11) (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ (keygenZNum:ℝ)/keygenZDen) :
    z * (1/2^(i.val+1) + (1 - 1/2^(i.val+1)) * ((keygenM i:ℝ)/2^128)) ≤ (keygenM i:ℝ)/2^128 ∧
      z ≤ (keygenM i:ℝ)/2^128 := by
  obtain ⟨h1, h2⟩ := keygen_step_zK i
  have hq : (1:ℝ)/2^(i.val+1) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hp : 0 ≤ (1:ℝ)/2^(i.val+1) + (1 - 1/2^(i.val+1)) * ((keygenM i:ℝ)/2^128) := by
    have : 0 ≤ 1 - (1:ℝ)/2^(i.val+1) := by linarith
    positivity
  exact ⟨(mul_le_mul_of_nonneg_right hz hp).trans h1, hz.trans h2⟩

def keygenList : List (Nat × Nat) := [(keygenZFix,1003010),(340282816799774407537068188648745253159,2048),(340283266679799900375442987250372351646,1024),(340284166443419551218384362561208825066,512),(340285965984933645675468342432275971788,256),(340289565125062062546873124227847124433,128),(340296763633728263433442488925276359072,64),(340311161564765781666276742203532247926,32),(340339961082202552920555136142458666879,16),(340397574742854560594048527114301253582,8),(340512860601946649704814937144529402626,4),(340743666749029370512803021620717668290,2)]

theorem keygen_list_checked : prodUp keygenList * 100000 < 199934 * scale := by decide +kernel

attribute [irreducible] prodUp

theorem keygen_list_prod (x : ℝ) (m : Fin 11 → ℝ) (hm : ∀ i, m i = ((keygenM i:ℝ)/scale)) :
    (keygenList.map fun e => ((e.1:ℝ)/scale)^e.2).prod =
      ((keygenZFix:ℝ)/scale)^1003010 * ∏ i : Fin 11, (m i)^(2^(11-i.val)) := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, hm]
  simp only [keygenList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, keygenM]
  norm_num

theorem keygen_moment (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ (keygenZNum:ℝ)/keygenZDen) :
    z^1003010 * ∏ i : Fin 11, ((keygenM i:ℝ)/2^128)^(2^(11-i.val)) ≤ 2 := by
  have hs : (scale:ℝ) = 2^128 := by norm_num [scale]
  have hzf := hz.trans keygenZ_fix
  have hprod := prodUp_ratio_ge keygenList
  rw [keygen_list_prod 0 (fun i => (keygenM i:ℝ)/scale) (fun _ => rfl)] at hprod
  have hnum : (prodUp keygenList:ℝ)/scale < 199934/100000 := by
    have h := keygen_list_checked
    have h' : (prodUp keygenList:ℝ)*100000 < 199934*(scale:ℝ) := by exact_mod_cast h
    have hs0 : (0:ℝ) < scale := by norm_num [scale]
    generalize (prodUp keygenList:ℝ) = P at h' ⊢
    generalize (scale:ℝ) = S at h' hs0 ⊢
    rw [div_lt_iff₀ hs0]; linarith
  have hstep : z^1003010 * ∏ i : Fin 11, ((keygenM i:ℝ)/2^128)^(2^(11-i.val)) ≤
      ((keygenZFix:ℝ)/scale)^1003010 * ∏ i : Fin 11, ((keygenM i:ℝ)/scale)^(2^(11-i.val)) := by
    rw [hs] at hzf ⊢
    gcongr
  linarith


/-! ## N2: expand excess (max of two uniform 19-bit candidates) -/

def expandWNum : Nat := 10000000000 * 917504
def expandWDen : Nat := 10000000000 * 917504 - 6931471808

/-- `(8/7)/2^20 = 1/917504`. -/
theorem expand_w_le : (2:ℝ)^(1/((917504:ℕ):ℝ)) ≤ (expandWNum:ℝ)/expandWDen := by
  refine (SigGolfCandidate.Budget.rpow_two_inv_le 917504 (by norm_num)).trans_eq ?_
  norm_num [expandWNum, expandWDen]

def expandWFix : Nat := 340282623994413344176749661942838553419

theorem expandW_fix : (expandWNum:ℝ)/expandWDen ≤ (expandWFix:ℝ)/scale := by
  rw [div_le_div_iff₀ (by norm_num [expandWDen]) (by norm_num [scale])]
  norm_num [expandWNum, expandWDen, expandWFix, scale]

/-- `pw k ≥ (w^8192)^k · scale` (iterated rounded-up products). -/
def blockV : Nat := powerUp expandWFix 8192
def pw : Nat → Nat
  | 0 => scale
  | k + 1 => mulUp blockV (pw k)

theorem pw_ratio_ge (k : Nat) : (((blockV:ℝ)/scale))^k ≤ (pw k:ℝ)/scale := by
  induction k with
  | zero => simp [pw, scale]
  | succ k ih =>
    rw [pow_succ', pw]
    exact (mul_le_mul_of_nonneg_left ih (by positivity)).trans (mulUp_ratio_ge _ _)

def blockSum : Nat := ∑ i ∈ range 64, ∑ j ∈ range 64, pw (max i j + 1)

theorem expand_block_checked : mulUp (powerUp expandWFix 427665) blockSum * 100000 <
    181213 * scale * 4096 := by decide +kernel

theorem blockV_eq : blockV = powerUp expandWFix 8192 := rfl

attribute [irreducible] blockSum blockV

theorem sum_range_mul_div (F : ℕ → ℝ) (J L : ℕ) (hL : 0 < L) :
    ∑ a ∈ range (J*L), F (a / L) = L * ∑ i ∈ range J, F i := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    have h : ∀ x ∈ range L, F ((J*L + x) / L) = F J := by
      intro x hx
      congr 1
      rw [Finset.mem_range] at hx
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hx, Nat.zero_add]
    rw [Finset.sum_congr rfl h]
    simp

theorem max_block_le (a b L : ℕ) (hL : 0 < L) : max a b ≤ L * (max (a/L) (b/L) + 1) := by
  have ha := Nat.lt_mul_div_succ a hL
  have hb := Nat.lt_mul_div_succ b hL
  have h1 : L * (a/L + 1) ≤ L * (max (a/L) (b/L) + 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : L * (b/L + 1) ≤ L * (max (a/L) (b/L) + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem expand_excess_moment (w : ℝ) (hw1 : 1 ≤ w) (hw : w ≤ (expandWNum:ℝ)/expandWDen) :
    w^427665 * ((1:ℝ)/2^38 * ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b)) ≤ 2 := by
  have hwf := hw.trans expandW_fix
  have hw0 : 0 ≤ w := by linarith
  set v : ℝ := w^8192 with hv
  -- blocks: w^max a b ≤ v^(max (a/L) (b/L) + 1)
  have hpt : ∀ a b : ℕ, w^(max a b) ≤ v^(max (a/8192) (b/8192) + 1) := by
    intro a b
    rw [hv, ← pow_mul]
    exact pow_le_pow_right₀ hw1 (max_block_le a b 8192 (by norm_num))
  have hR : (2:ℕ)^19 = 64 * 8192 := by norm_num
  have hsum : ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b) ≤
      (8192:ℝ) * (8192 * ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1)) := by
    calc ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b)
        ≤ ∑ a ∈ range (64*8192), ∑ b ∈ range (64*8192), v^(max (a/8192) (b/8192) + 1) := by
          rw [hR]; exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
      _ = (8192:ℝ) * ∑ i ∈ range 64, ∑ b ∈ range (64*8192), v^(max i (b/8192) + 1) :=
          sum_range_mul_div (fun i => ∑ b ∈ range (64*8192), v^(max i (b/8192) + 1)) 64 8192 (by norm_num)
      _ = (8192:ℝ) * (8192 * ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1)) := by
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ =>
            sum_range_mul_div (fun j => v^(max i j + 1)) 64 8192 (by norm_num)
  -- fixed point: v ≤ blockV/scale, v^k ≤ pw k/scale
  have hvb : v ≤ (blockV:ℝ)/scale := by
    rw [hv]
    rw [blockV_eq]
    exact (pow_le_pow_left₀ hw0 hwf 8192).trans (powerUp_ratio_ge _ _)
  have hv0 : 0 ≤ v := by positivity
  have hterm : ∀ i j : ℕ, v^(max i j + 1) ≤ (pw (max i j + 1):ℝ)/scale := fun i j =>
    (pow_le_pow_left₀ hv0 hvb _).trans (pw_ratio_ge _)
  have hblock : ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1) ≤ (blockSum:ℝ)/scale := by
    calc ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1)
        ≤ ∑ i ∈ range 64, ∑ j ∈ range 64, (pw (max i j + 1):ℝ)/scale :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = (blockSum:ℝ)/scale := by
          simp only [blockSum, Nat.cast_sum, Finset.sum_div]
  have hK : w^427665 ≤ (powerUp expandWFix 427665:ℝ)/scale :=
    (pow_le_pow_left₀ hw0 hwf _).trans (powerUp_ratio_ge _ _)
  have hcheck : (mulUp (powerUp expandWFix 427665) blockSum:ℝ) * 100000 <
      181213 * (scale:ℝ) * 4096 := by exact_mod_cast expand_block_checked
  have hmul := mulUp_ratio_ge (powerUp expandWFix 427665) blockSum
  have hs : (0:ℝ) < scale := by norm_num [scale]
  have hS : (1:ℝ)/2^38 * ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b) ≤
      ((blockSum:ℝ)/scale) / 4096 := by
    have h2 : (1:ℝ)/2^38 * ((8192:ℝ) * (8192 * ((blockSum:ℝ)/scale))) = ((blockSum:ℝ)/scale) / 4096 := by
      generalize ((blockSum:ℝ)/scale) = B
      norm_num; ring
    rw [← h2]
    have h3 : (8192:ℝ) * (8192 * ∑ i ∈ range 64, ∑ j ∈ range 64, v^(max i j + 1)) ≤
        (8192:ℝ) * (8192 * ((blockSum:ℝ)/scale)) := by
      gcongr
    have h4 := hsum.trans h3
    have h5 : (0:ℝ) ≤ 1/2^38 := by positivity
    exact mul_le_mul_of_nonneg_left h4 h5
  have hB : w^427665 * ((1:ℝ)/2^38 * ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b)) ≤
      ((powerUp expandWFix 427665:ℝ)/scale) * (((blockSum:ℝ)/scale) / 4096) :=
    mul_le_mul hK hS
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => pow_nonneg hw0 _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hC : ((powerUp expandWFix 427665:ℝ)/scale) * (((blockSum:ℝ)/scale) / 4096) ≤
      ((mulUp (powerUp expandWFix 427665) blockSum:ℝ)/scale) / 4096 := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hmul (by norm_num)
  have hD : ((mulUp (powerUp expandWFix 427665) blockSum:ℝ)/scale) / 4096 ≤ 2 := by
    have hs0 : (0:ℝ) < scale := by norm_num [scale]
    generalize (mulUp (powerUp expandWFix 427665) blockSum:ℝ) = P at hcheck ⊢
    generalize (scale:ℝ) = S at hcheck hs0 ⊢
    rw [div_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith


/-! ## N2b in the top-bytes porter's exact form (drop-in for `SharedExpansionV6.ExpandExcessNumeric`)
`avgF φ = Σ_{c<2^19} (2^19)⁻¹·φ c` and `excessWeight c = 2^((8/7)·(427665 + c)/2^20)` in `ℝ≥0∞`
(`expandReplayExtra = 1900 + 425765 = 427665`). -/

noncomputable def avgF19 (φ : Nat → ENNReal) : ENNReal := ∑ c ∈ range (2 ^ 19), ((2 : ENNReal) ^ 19)⁻¹ * φ c

noncomputable def excessWeightV6 (c : Nat) : ENNReal :=
  (2 : ENNReal) ^ ((8 / 7 : ℝ) * ((427665 + c : ℕ) : ℝ) / 1048576)

theorem avgF19_ofReal (ψ : Nat → ℝ) (hψ : ∀ c, 0 ≤ ψ c) :
    avgF19 (fun c => ENNReal.ofReal (ψ c)) = ENNReal.ofReal (∑ c ∈ range (2^19), (1/2^19) * ψ c) := by
  unfold avgF19
  rw [ENNReal.ofReal_sum_of_nonneg (fun c _ => mul_nonneg (by positivity) (hψ c))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one, one_div]
  norm_num

theorem excessWeightV6_eq (c : Nat) :
    excessWeightV6 c = ENNReal.ofReal (((2:ℝ)^(1/((917504:ℕ):ℝ)))^(427665 + c)) := by
  unfold excessWeightV6
  rw [show (2:ENNReal) = ENNReal.ofReal 2 by norm_num, ENNReal.ofReal_rpow_of_pos (by norm_num)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  push_cast
  ring

/-- **N2b** (drop-in for `SigGolfCandidate.Research.SharedExpansionV6.expandExcessNumeric_holds`). -/
theorem expand_excess_numeric :
    avgF19 (fun c2 => avgF19 (fun c3 => excessWeightV6 (max c2 c3))) ≤ 2 := by
  set w : ℝ := (2:ℝ)^(1/((917504:ℕ):ℝ)) with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow (by norm_num) (by positivity)
  have hw0 : 0 ≤ w := by linarith
  have hin : ∀ c2, avgF19 (fun c3 => excessWeightV6 (max c2 c3)) =
      ENNReal.ofReal (∑ c3 ∈ range (2^19), (1/2^19) * w^(427665 + max c2 c3)) := by
    intro c2
    simp_rw [excessWeightV6_eq]
    exact avgF19_ofReal (fun c3 => w^(427665 + max c2 c3)) (fun _ => pow_nonneg hw0 _)
  simp_rw [hin]
  rw [avgF19_ofReal _ (fun _ => Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity) (pow_nonneg hw0 _))]
  have hreal : ∑ c2 ∈ range (2^19), (1/2^19) * ∑ c3 ∈ range (2^19), (1/2^19) * w^(427665 + max c2 c3) =
      w^427665 * ((1:ℝ)/2^38 * ∑ a ∈ range (2^19), ∑ b ∈ range (2^19), w^(max a b)) := by
    simp only [pow_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hreal]
  have h := expand_excess_moment w hw1 (by rw [hw]; exact expand_w_le)
  calc ENNReal.ofReal _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal h
    _ = 2 := by norm_num

end ClaudeWCT.Numerics.V6Budgets
end
-- ==== merged from ClaudeWCT_Numerics_WCTEnvelope ====
section

namespace ClaudeWCT.Numerics.WCTEnvelope
open Finset ENNReal
open ClaudeWCT.Numerics.Thinning (env ListCov)
open SigGolfResearch.Gate6.Moments (finiteAverage)
open SigGolfCandidate.T3.BPORS.History (atIndex)
open ClaudeWCT.Bank.WCT (WProposal proposal outIdx CoveredP scoreP price)
open ClaudeWCT.WCT9 (wordDigit Coord Child Rank)
theorem codeWords_eq : ClaudeWCT.WCT9.codeWords = N600.words := by decide +kernel
set_option maxRecDepth 100000 in
theorem ofFn_wordDigit_list :
    List.ofFn (fun r : Fin 563 => List.ofFn (wordDigit r)) = N600.words := by
  rw [← codeWords_eq]
  apply List.ext_getElem
  · exact (List.length_ofFn).trans ClaudeWCT.WCT9.codeWords_length.symm
  · intro i hi hj
    have hi' : i < 563 := by rwa [List.length_ofFn] at hi
    rw [List.getElem_ofFn]
    have h := ClaudeWCT.WCT9.ofFn_wordDigit ⟨i, hi'⟩
    rw [ClaudeWCT.WCT9.codeword_embed] at h
    exact h
theorem wordsOf_wordDigit : N600.WordsOf wordDigit := by
  unfold N600.WordsOf
  rw [Fin.univ_val_map, ofFn_wordDigit_list]
theorem w1Table_wordDigit : N600.W1Table wordDigit :=
  fun p => N600.w1_table wordsOf_wordDigit ClaudeWCT.WCT9.wordDigit_le_four p
theorem w2Table_wordDigit : N600.W2Table wordDigit :=
  fun p => N600.w2_table wordsOf_wordDigit ClaudeWCT.WCT9.wordDigit_le_four p
theorem wfTable_wordDigit (i : Fin 6) : N600.WFTable wordDigit i :=
  fun p => N600.wf_table wordsOf_wordDigit ClaudeWCT.WCT9.wordDigit_le_four i p
theorem card_rank : Fintype.card Rank = 563 := Fintype.card_fin 563
theorem card_child : Fintype.card Child = 128 := Fintype.card_fin 128
abbrev Coords := Coord → Child × Rank
theorem card_coords : Fintype.card Coords = N600.Q ^ 9 :=
  N600.card_table card_rank card_child
theorem mem_atIndex {α β : Type} [DecidableEq α] (index : α) (e : β) (W : List (α × β)) :
    e ∈ atIndex index W ↔ (index, e) ∈ W := by
  unfold atIndex
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨i, e'⟩, hmem, h⟩
    by_cases hi : i = index
    · simp only [hi, if_true, Option.some.injEq] at h
      rw [← hi, ← h]
      exact hmem
    · simp [hi] at h
  · intro h
    exact ⟨(index, e), h, by simp⟩
theorem coveredP_iff (W : List WProposal) (N : SigGolfCandidate.T3.HashOutput) :
    CoveredP W N ↔ ListCov wordDigit (atIndex (outIdx N) W) (proposal N).2 := by
  unfold CoveredP ClaudeWCT.Bank.WCT.SlotCoveredP ListCov
  refine forall_congr' fun k => forall_congr' fun t => ?_
  constructor
  · rintro ⟨p, hp, h1, h2, h3⟩
    refine ⟨p.2, (mem_atIndex _ _ _).mpr ?_, h2, h3⟩
    rw [← h1]
    exact hp
  · rintro ⟨e, he, h2, h3⟩
    exact ⟨(outIdx N, e), (mem_atIndex _ _ _).mp he, rfl, h2, h3⟩
theorem price_scale :
    (2 : ENNReal) ^ 128 * ((1353 * 2 ^ 58 : ℕ) : ENNReal) * ((N600.Q ^ 9 : ℕ) : ENNReal) *
        ((2 ^ 256 : ℕ) : ENNReal)⁻¹ = N600.priceScale := by
  rw [← div_eq_mul_inv]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by unfold N600.priceScale; finiteness)).mp
  unfold N600.priceScale
  norm_num [N600.Q, ENNReal.toReal_mul, ENNReal.toReal_div]
theorem price_eq (W : List WProposal) : price W = N600.priceN wordDigit W := by
  classical
  set g : WProposal → ENNReal := fun p => if ListCov wordDigit (atIndex p.1 W) p.2 then 1 else 0 with hg
  have hs : ∀ N, scoreP W N = if ClaudeWCT.WCT9.admissible N = true then g (proposal N) else 0 := by
    intro N
    unfold scoreP
    by_cases hadm : ClaudeWCT.WCT9.admissible N = true
    · simp only [hadm, true_and, if_true, hg]
      exact if_congr (coveredP_iff W N) rfl rfl
    · simp [hadm]
  have hsum : ∑ p, g p = ((N600.Q ^ 9 : ℕ) : ENNReal) *
      ∑ index : Fin (2 ^ 31), env (n := 9) wordDigit (atIndex index W) := by
    rw [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun index _ => ?_
    unfold env finiteAverage
    rw [card_coords, ENNReal.mul_div_cancel (by simp [N600.Q]) (by simp)]
  unfold price SigGolfCandidate.T3.BPORS.finiteAverage
  simp_rw [hs]
  rw [ClaudeWCT.Bank.WCT.sum_admissible g, hsum, Fintype.card_bitVec, N600.priceN, ← price_scale]
  unfold ClaudeWCT.WCT9.gateLimit
  simp only [div_eq_mul_inv]
  ring
end ClaudeWCT.Numerics.WCTEnvelope

namespace ClaudeWCT.Bank.Paired
open Finset ClaudeWCT.Numerics ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.Thinning
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
abbrev PairChoice (β : Type) := Fin 2 × (Fin 64 × β) × (Fin 64 × β)
abbrev ForestChoice (β : Type) := (Fin 4 → PairChoice β) × (Fin 128 × β)

def choice {β : Type} (a : AlphabetOf β) : ForestChoice β :=
  (fun p => ((a.1.1 p).1,
    ((a.1.1 p).2.1,a.2 ⟨2*p.val,by omega⟩),
    ((a.1.1 p).2.2,a.2 ⟨2*p.val+1,by omega⟩)),(a.1.2,a.2 8))
def unchoice {β : Type} (a : ForestChoice β) : AlphabetOf β :=
  ((fun p => ((a.1 p).1,(a.1 p).2.1.1,(a.1 p).2.2.1),a.2.1),
    fun k => if hk : k.val<8 then
      if k.val%2=0 then (a.1 ⟨k.val/2,by omega⟩).2.1.2
      else (a.1 ⟨k.val/2,by omega⟩).2.2.2
    else a.2.2)
def choiceEquiv (β : Type) : AlphabetOf β ≃ ForestChoice β where
  toFun := choice
  invFun := unchoice
  left_inv a := by
    apply Prod.ext
    · rfl
    · funext k; fin_cases k <;> rfl
  right_inv a := by
    apply Prod.ext
    · funext p
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · apply Prod.ext
          · rfl
          · fin_cases p <;> rfl
        · apply Prod.ext
          · rfl
          · fin_cases p <;> rfl
    · rfl

theorem covAt_splitRanks {β : Type} [Fintype β] {r : Nat}
    (val : β → Fin 6 → Nat) (o : Fin r → Fin 2) (A : Fin r → Fin 64 × β)
    (s : Fin 2) (target : Fin 64 × β) :
    CovAt val target.1 (val target.2) (splitRanks o A s) ↔
      ∀ t, ∃ j, o j=s ∧ (A j).1=target.1 ∧ val target.2 t ≤ val (A j).2 t := by
  constructor
  · intro h t
    obtain ⟨j,hj,hv⟩ := h t
    let z := (fiberIndex o s).symm j
    exact ⟨z.val,z.property,by simpa only [splitRanks_apply] using hj,
      by simpa only [splitRanks_apply] using hv⟩
  · intro h t
    obtain ⟨j,hj,hc,hv⟩ := h t
    refine ⟨fiberIndex o s ⟨j,hj⟩,?_,?_⟩
    · simpa only [splitRanks_apply, Equiv.symm_apply_apply] using hc
    · simpa only [splitRanks_apply, Equiv.symm_apply_apply] using hv

def PairCovered {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : PairHistory β r) (a : PairChoice β) : Prop :=
  CovAt val a.2.1.1 (val a.2.1.2) (splitRanks h.1 h.2.1 a.1) ∧
  CovAt val a.2.2.1 (val a.2.2.2) (splitRanks h.1 h.2.2 a.1)
def ForestCovered {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : ForestHistory β r) (a : ForestChoice β) : Prop :=
  (∀ p, PairCovered val (h.1 p) (a.1 p)) ∧ CovAt val a.2.1 (val a.2.2) h.2

theorem card_and_prod {α β : Type} [Fintype α] [Fintype β] (p : α → Prop) (q : β → Prop) :
    #{a : α × β | p a.1 ∧ q a.2} = #{a : α | p a} * #{b : β | q b} := by
  classical
  simp only [card_filter, Fintype.sum_prod_type]
  rw [sum_mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases hp : p a <;> by_cases hq : q b <;> simp [hp,hq]

noncomputable def pairCoveredEquiv {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : PairHistory β r) :
    {a : PairChoice β // PairCovered val h a} ≃
      (s : Fin 2) × {a : Fin 64 × β // CovAt val a.1 (val a.2) (splitRanks h.1 h.2.1 s)} ×
        {b : Fin 64 × β // CovAt val b.1 (val b.2) (splitRanks h.1 h.2.2 s)} where
  toFun a := ⟨a.val.1, ⟨a.val.2.1,a.property.1⟩,⟨a.val.2.2,a.property.2⟩⟩
  invFun a := ⟨(a.1,a.2.1.val,a.2.2.val),a.2.1.property,a.2.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem pairCovered_card {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : PairHistory β r) : #{a : PairChoice β | PairCovered val h a} = pairCoverage val h := by
  have he := Fintype.card_congr (pairCoveredEquiv val h)
  simp only [Fintype.card_subtype,Fintype.card_sigma,Fintype.card_prod] at he
  calc
    _ = ∑ s : Fin 2, coordinateCoverage val (splitRanks h.1 h.2.1 s) *
      coordinateCoverage val (splitRanks h.1 h.2.2 s) := he
    _ = _ := by rw [Fin.sum_univ_two]; rfl

noncomputable def forestCoveredEquiv {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : ForestHistory β r) :
    {a : ForestChoice β // ForestCovered val h a} ≃
      ((p : Fin 4) → {a : PairChoice β // PairCovered val (h.1 p) a}) ×
        {b : Fin 128 × β // CovAt val b.1 (val b.2) h.2} where
  toFun a := (fun p => ⟨a.val.1 p,a.property.1 p⟩,⟨a.val.2,a.property.2⟩)
  invFun a := ⟨(fun p => (a.1 p).val,a.2.val),(fun p => (a.1 p).property),a.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem forestCovered_card {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : ForestHistory β r) : #{a : ForestChoice β | ForestCovered val h a} = forestCoverage val h := by
  have he := Fintype.card_congr (forestCoveredEquiv val h)
  simp only [Fintype.card_subtype,Fintype.card_prod,Fintype.card_pi] at he
  calc
    _ = (∏ p, #{a : PairChoice β | PairCovered val (h.1 p) a}) * coordinateCoverage val h.2 := he
    _ = _ := by simp only [pairCovered_card]; rfl

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ClaudeWCT.Numerics ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.Thinning
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

theorem rawChild_first (s : Selectors) (p : Fin 4) :
    (rawChild s ⟨2*p.val,by omega⟩).val = 64*(s.1 p).1.val+(s.1 p).2.1.val := by
  fin_cases p <;> rfl

theorem rawChild_second (s : Selectors) (p : Fin 4) :
    (rawChild s ⟨2*p.val+1,by omega⟩).val = 2*(s.1 p).2.2.val+(s.1 p).1.val := by
  fin_cases p <;> rfl

theorem rawChild_first_eq (s u : Selectors) (p : Fin 4) :
    rawChild s ⟨2*p.val,by omega⟩ = rawChild u ⟨2*p.val,by omega⟩ ↔
      (s.1 p).1=(u.1 p).1 ∧ (s.1 p).2.1=(u.1 p).2.1 := by
  rw [Fin.ext_iff, rawChild_first, rawChild_first]
  have ha := (s.1 p).2.1.isLt
  have hb := (u.1 p).2.1.isLt
  simp only [Fin.ext_iff]
  omega

theorem rawChild_second_eq (s u : Selectors) (p : Fin 4) :
    rawChild s ⟨2*p.val+1,by omega⟩ = rawChild u ⟨2*p.val+1,by omega⟩ ↔
      (s.1 p).1=(u.1 p).1 ∧ (s.1 p).2.2=(u.1 p).2.2 := by
  rw [Fin.ext_iff, rawChild_second, rawChild_second]
  have ha := (s.1 p).1.isLt
  have hb := (u.1 p).1.isLt
  simp only [Fin.ext_iff]
  omega

def AlphabetCovered {β : Type} (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (a : AlphabetOf β) : Prop :=
  ∀ k : Fin 9, ∀ t : Fin 6, ∃ j,
    rawChild (h j).1 k = rawChild a.1 k ∧ val (a.2 k) t ≤ val ((h j).2 k) t

theorem forestCovered_choice {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (a : AlphabetOf β) :
    ForestCovered val (splitHistory h) (choice a) ↔ AlphabetCovered val h a := by
  have hfirst (p : Fin 4) :
      CovAt val ((choice a).1 p).2.1.1 (val ((choice a).1 p).2.1.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.1 ((choice a).1 p).1) ↔
      ∀ t : Fin 6, ∃ j, rawChild (h j).1 ⟨2*p.val,by omega⟩ = rawChild a.1 ⟨2*p.val,by omega⟩ ∧
        val (a.2 ⟨2*p.val,by omega⟩) t ≤ val ((h j).2 ⟨2*p.val,by omega⟩) t := by
    rw [covAt_splitRanks]
    simp only [splitHistory, choice, rawChild_first_eq, and_assoc]
  have hsecond (p : Fin 4) :
      CovAt val ((choice a).1 p).2.2.1 (val ((choice a).1 p).2.2.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.2 ((choice a).1 p).1) ↔
      ∀ t : Fin 6, ∃ j, rawChild (h j).1 ⟨2*p.val+1,by omega⟩ = rawChild a.1 ⟨2*p.val+1,by omega⟩ ∧
        val (a.2 ⟨2*p.val+1,by omega⟩) t ≤ val ((h j).2 ⟨2*p.val+1,by omega⟩) t := by
    rw [covAt_splitRanks]
    simp only [splitHistory, choice, rawChild_second_eq, and_assoc]
  constructor
  · rintro ⟨hp,hs⟩ k t
    have hA : ∀ p : Fin 4, ∃ j, rawChild (h j).1 ⟨2*p.val,by omega⟩ = rawChild a.1 ⟨2*p.val,by omega⟩ ∧
        val (a.2 ⟨2*p.val,by omega⟩) t ≤ val ((h j).2 ⟨2*p.val,by omega⟩) t :=
      fun p => ((hfirst p).mp (hp p).1) t
    have hB : ∀ p : Fin 4, ∃ j, rawChild (h j).1 ⟨2*p.val+1,by omega⟩ = rawChild a.1 ⟨2*p.val+1,by omega⟩ ∧
        val (a.2 ⟨2*p.val+1,by omega⟩) t ≤ val ((h j).2 ⟨2*p.val+1,by omega⟩) t :=
      fun p => ((hsecond p).mp (hp p).2) t
    fin_cases k
    · exact hA 0
    · exact hB 0
    · exact hA 1
    · exact hB 1
    · exact hA 2
    · exact hB 2
    · exact hA 3
    · exact hB 3
    · exact hs t
  · intro hc
    refine ⟨fun p => ⟨(hfirst p).mpr ?_,(hsecond p).mpr ?_⟩,?_⟩
    · exact hc ⟨2*p.val,by omega⟩
    · exact hc ⟨2*p.val+1,by omega⟩
    · exact hc 8

theorem alphabetCovered_card {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) :
    (Finset.univ.filter fun a => AlphabetCovered val h a).card = forestCoverage val (splitHistory h) := by
  classical
  have e := (choiceEquiv β).subtypeEquiv (fun a => (forestCovered_choice val h a).symm)
  have hc := Fintype.card_congr e
  simp only [Fintype.card_subtype] at hc
  exact hc.trans (forestCovered_card val (splitHistory h))

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open SigGolfResearch.Gate6.Moments (finiteAverage)
open SigGolfCandidate.T3.BPORS.History (atIndex)
open ClaudeWCT.Numerics.Thinning
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

def ListAlphabetCovered {β : Type} (val : β → Fin 6 → Nat)
    (W : List (AlphabetOf β)) (a : AlphabetOf β) : Prop :=
  ∀ k : Fin 9, ∀ t : Fin 6, ∃ e ∈ W,
    rawChild e.1 k = rawChild a.1 k ∧ val (a.2 k) t ≤ val (e.2 k) t
noncomputable def bucketEnv {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (W : List (AlphabetOf β)) : ENNReal :=
  finiteAverage (fun a => if ListAlphabetCovered val W a then 1 else 0)

theorem listAlphabetCovered_ofFn {β : Type} (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (a : AlphabetOf β) :
    ListAlphabetCovered val (List.ofFn h) a ↔ AlphabetCovered val h a := by
  simp only [ListAlphabetCovered, AlphabetCovered, List.mem_ofFn]
  refine forall_congr' fun k => forall_congr' fun t => ?_
  constructor
  · rintro ⟨e, ⟨j,rfl⟩, he⟩
    exact ⟨j,he⟩
  · rintro ⟨j,hj⟩
    exact ⟨h j,⟨j,rfl⟩,hj⟩

theorem bucketEnv_ofFn {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) :
    bucketEnv val (List.ofFn h) =
      (SharedCoverage.forestCoverage val (splitHistory h) : ENNReal)/Fintype.card (AlphabetOf β) := by
  unfold bucketEnv finiteAverage
  simp_rw [listAlphabetCovered_ofFn]
  rw [← natCast_card_filter, alphabetCovered_card]

theorem bucketEnv_mono {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (a : AlphabetOf β) (W : List (AlphabetOf β)) : bucketEnv val W ≤ bucketEnv val (a::W) := by
  unfold bucketEnv finiteAverage
  apply ENNReal.div_le_div_right
  apply sum_le_sum
  intro target _
  split_ifs with h1 h2
  · exact le_rfl
  · apply False.elim
    apply h2
    intro k t
    obtain ⟨e,he,hc⟩ := h1 k t
    exact ⟨e,List.mem_cons_of_mem a he,hc⟩
  · exact zero_le_one
  · exact le_rfl

theorem coveredP_bucket (W : List Proposal) (N : SigGolfCandidate.T3.HashOutput) :
    CoveredP W N ↔ ListAlphabetCovered ClaudeWCT.WCT9.wordDigit
      (atIndex (proposal N).1 W) (proposal N).2 := by
  unfold CoveredP SlotCoveredP ListAlphabetCovered
  refine forall_congr' fun k => forall_congr' fun t => ?_
  constructor
  · rintro ⟨p,hp,h1,h2,h3⟩
    refine ⟨p.2,(WCTEnvelope.mem_atIndex _ _ _).mpr ?_,h2,h3⟩
    rw [← h1]
    exact hp
  · rintro ⟨a,ha,h2,h3⟩
    exact ⟨((proposal N).1,a),(WCTEnvelope.mem_atIndex _ _ _).mp ha,rfl,h2,h3⟩

theorem price_scale :
    (2:ENNReal)^128 * ((791*2^62:Nat):ENNReal) *
      (SharedMoments.alphabetSize:ENNReal) * ((2^256:Nat):ENNReal)⁻¹ =
      (SharedMoments.priceScaleTotal:ENNReal)/(2^31) := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [SharedMoments.alphabetSize,SharedMoments.priceScaleTotal,ENNReal.toReal_mul,
    ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow]

theorem price_eq_buckets (W : List Proposal) :
    price W = (SharedMoments.priceScaleTotal:ENNReal)/(2^31) *
      ∑ index : Fin (2^31), bucketEnv ClaudeWCT.WCT9.wordDigit (atIndex index W) := by
  let g : Proposal → ENNReal := fun p =>
    if ListAlphabetCovered ClaudeWCT.WCT9.wordDigit (atIndex p.1 W) p.2 then 1 else 0
  have hs (N : SigGolfCandidate.T3.HashOutput) : scoreP W N =
      if admissible N=true then g (proposal N) else 0 := by
    unfold scoreP
    by_cases ha : admissible N=true
    · simp only [ha,true_and,if_true,g]
      exact if_congr (coveredP_bucket W N) rfl rfl
    · simp [ha]
  have hc : Fintype.card Alphabet=SharedMoments.alphabetSize := alphabet_card (Fintype.card_fin 563)
  have hsum : (∑ p,g p) = (SharedMoments.alphabetSize:ENNReal)*
      ∑ index : Fin (2^31), bucketEnv ClaudeWCT.WCT9.wordDigit (atIndex index W) := by
    rw [Fintype.sum_prod_type,mul_sum]
    apply sum_congr rfl
    intro index _
    unfold bucketEnv finiteAverage
    rw [hc,ENNReal.mul_div_cancel (by norm_num [SharedMoments.alphabetSize]) (by simp)]
  unfold price SigGolfCandidate.T3.BPORS.finiteAverage
  simp_rw [hs]
  rw [sum_admissible g,hsum,Fintype.card_bitVec,← price_scale]
  simp only [div_eq_mul_inv]
  ring

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open SigGolfCandidate.T3.BPORS.History (atIndex)
open SphincsSecurity.Concrete (binomialAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

/-- The actual cap-conditioned bucket law is bounded by the finite paired
history model, for any nonnegative payoff, including capped MGF and residual. -/
theorem law_bucket_payoff_le (r : Nat) (f : ENNReal → ENNReal) :
    Law.lawAvg honestCoordLaw r (fun W => f (bucketEnv ClaudeWCT.WCT9.wordDigit W)) ≤
      kappa^r * ((∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        f ((SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h : ENNReal)/
          SharedMoments.alphabetSize))/(SharedMoments.alphabetSize:ENNReal)^r) := by
  have hc : Fintype.card (AlphabetOf (Fin 563)) = SharedMoments.alphabetSize :=
    alphabet_card (Fintype.card_fin 563)
  have hf (h : Fin r → Alphabet) :
      f (bucketEnv ClaudeWCT.WCT9.wordDigit (List.ofFn h)) =
        f ((SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit (splitHistory h) : ENNReal)/
          SharedMoments.alphabetSize) :=
    congrArg f ((bucketEnv_ofFn ClaudeWCT.WCT9.wordDigit h).trans
      (congrArg (fun n : Nat =>
        (SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit (splitHistory h) : ENNReal)/(n:ENNReal)) hc))
  exact law_history_le r (fun W => f (bucketEnv ClaudeWCT.WCT9.wordDigit W))
    (fun h => f ((SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h : ENNReal)/
      SharedMoments.alphabetSize)) hf


end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SigGolfCandidate.T3.BPORS.History (atIndex)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

noncomputable def priceBucket (W : List Alphabet) : ENNReal :=
  (SharedMoments.priceScaleTotal : ENNReal)/(2^31) * bucketEnv ClaudeWCT.WCT9.wordDigit W

theorem price_eq_sum (W : List Proposal) :
    price W = ∑ index : Fin (2^31), priceBucket (atIndex index W) := by
  rw [price_eq_buckets]
  exact Finset.mul_sum ..

theorem bucketEnv_sublist {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {W V : List (AlphabetOf β)} (hWV : ∀ x ∈ W, x ∈ V) : bucketEnv val W ≤ bucketEnv val V := by
  unfold bucketEnv SigGolfResearch.Gate6.Moments.finiteAverage
  apply ENNReal.div_le_div_right
  apply sum_le_sum
  intro target _
  split_ifs with hW hV
  · exact le_rfl
  · apply False.elim
    apply hV
    intro k t
    obtain ⟨e,he,hc⟩ := hW k t
    exact ⟨e,hWV e he,hc⟩
  · exact zero_le_one
  · exact le_rfl

theorem priceBucket_insert (L R : List Alphabet) (a : Alphabet) :
    priceBucket (L++R) ≤ priceBucket (L++a::R) := by
  apply mul_le_mul' le_rfl
  apply bucketEnv_sublist
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact List.mem_append_left _ hx
  · exact List.mem_append_right _ (List.mem_cons_of_mem a hx)

/-- The actual paired price has the marked-index bank excess bound once its
single-bucket capped exponential and residual moments have been certified. -/
theorem price_excess_of_bucket_bounds (T : Nat) (cap : ENNReal) (hcap : cap ≠ ⊤)
    (theta slope bound residualBound resultBound : ℝ)
    (htheta : 0 ≤ theta) (hslope : 0 < slope) (hbound : 0 ≤ bound) (hresBound : 0 ≤ residualBound)
    (hmgf : (2^31:ENNReal) * Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T
      (fun L => ENNReal.ofReal (Real.exp (slope*(min (priceBucket L) cap).toReal))-1) ≤
        ENNReal.ofReal bound)
    (hres : (2^31:ENNReal) * Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T
      (fun L => priceBucket L-cap) ≤ ENNReal.ofReal residualBound)
    (hscalar : (3/(8*slope))*Real.exp (bound-slope*theta)+residualBound ≤ resultBound) :
    Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal theta) ≤ ENNReal.ofReal resultBound := by
  have hm : (∑ _i : Fin (2^31), Law.coordAverage (Fintype.card (Fin (2^31)):ENNReal)⁻¹
      honestCoordLaw T
      (fun L => ENNReal.ofReal (Real.exp (slope*(min (priceBucket L) cap).toReal))-1)) ≤
        ENNReal.ofReal bound := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_pow,Nat.cast_ofNat] using hmgf
  have hr : (∑ _i : Fin (2^31), Law.coordAverage (Fintype.card (Fin (2^31)):ENNReal)⁻¹
      honestCoordLaw T (fun L => priceBucket L-cap)) ≤ ENNReal.ofReal residualBound := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_pow,Nat.cast_ofNat] using hres
  have he : (fun W : List Proposal => price W-ENNReal.ofReal theta) =
      (fun W => (∑ i : Fin (2^31), priceBucket (atIndex i W))-ENNReal.ofReal theta) := by
    funext W
    rw [price_eq_sum]
  rw [he]
  exact SharedPathWinsor.law_bucket_excess_general honestCoordLaw honestCoordLaw_sum T
    priceBucket cap hcap theta slope bound residualBound resultBound htheta hslope hbound hresBound
    (fun L a R => priceBucket_insert L R a) hm hr hscalar

end ClaudeWCT.Bank.Paired


namespace ClaudeWCT.Bank.Paired
open ENNReal
 theorem normalize_row_arithmetic (a S M D κ fee : ENNReal) (r : Nat)
    (ha0 : a ≠ 0) (hat : a ≠ ⊤) (hS0 : S ≠ 0) (hSt : S ≠ ⊤)
    (hM0 : M ≠ 0) (hMt : M ≠ ⊤) (hD0 : D ≠ 0) (hDt : D ≠ ⊤) :
    (κ^r*((a/S)*fee)/D^r)/(M*a*D/S) = κ^r*fee/(M*D^(r+1)) := by
  have hMD : (M*D^r*D)⁻¹ = M⁻¹*(D^r)⁻¹*D⁻¹ := by
    rw [ENNReal.mul_inv (Or.inr hDt) (Or.inr hD0),
      ENNReal.mul_inv (Or.inl hM0) (Or.inl hMt)]
  have hMAD : (M*a*D*S⁻¹)⁻¹ = M⁻¹*a⁻¹*D⁻¹*S := by
    rw [ENNReal.mul_inv (Or.inr (by simp [hS0])) (Or.inr (by simp [hSt])),
      ENNReal.mul_inv (Or.inr hDt) (Or.inr hD0),
      ENNReal.mul_inv (Or.inl hM0) (Or.inl hMt), inv_inv]
  simp only [div_eq_mul_inv, pow_succ]
  rw [hMAD, ← mul_assoc M (D^r) D, hMD]
  calc
    _ = κ^r*fee*M⁻¹*(D^r)⁻¹*D⁻¹*(a*a⁻¹)*(S*S⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel ha0 hat, ENNReal.mul_inv_cancel hS0 hSt]; ring

end ClaudeWCT.Bank.Paired


namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] Finset.univ

noncomputable def feeCoefficient : ENNReal := 791/2^66

theorem price_coefficient :
    (SharedMoments.priceScaleTotal:ENNReal)/(2^31)/(SharedMoments.alphabetSize:ENNReal) = feeCoefficient := by
  apply (ENNReal.toReal_eq_toReal_iff' (by unfold SharedMoments.alphabetSize; finiteness)
    (by unfold feeCoefficient; finiteness)).mp
  norm_num [SharedMoments.priceScaleTotal,SharedMoments.alphabetSize,feeCoefficient,
    ENNReal.toReal_div]

theorem priceBucket_ofFn {r : Nat} (h : Fin r → Alphabet) :
    priceBucket (List.ofFn h) = feeCoefficient *
      (SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit (splitHistory h):ENNReal) := by
  have hc : Fintype.card (AlphabetOf (Fin 563)) = SharedMoments.alphabetSize :=
    alphabet_card (Fintype.card_fin 563)
  have hb := (bucketEnv_ofFn ClaudeWCT.WCT9.wordDigit h).trans
    (congrArg (fun n : Nat =>
      (SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit (splitHistory h):ENNReal)/(n:ENNReal)) hc)
  change (SharedMoments.priceScaleTotal:ENNReal)/(2^31)*_ = _
  rw [hb, ← price_coefficient]
  simp only [div_eq_mul_inv]
  ring

theorem law_priceBucket_payoff_le (r : Nat) (f : ENNReal → ENNReal) :
    Law.lawAvg honestCoordLaw r (fun W => f (priceBucket W)) ≤
      kappa^r * ((∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))/
        (SharedMoments.alphabetSize:ENNReal)^r) :=
  law_history_le r (fun W => f (priceBucket W))
    (fun h => f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))
    (fun h => congrArg f (priceBucket_ofFn h))

theorem lawAvg_div {β : Type} [Fintype β] (v : β → ENNReal) (r : Nat)
    (f : List β → ENNReal) (C : ENNReal) :
    Law.lawAvg v r (fun W => f W/C) = Law.lawAvg v r f/C := by
  simpa only [div_eq_mul_inv,mul_comm] using Law.lawAvg_mul_left v r C⁻¹ f

theorem law_normalized_fee_row (r : Nat) (f : ENNReal → ENNReal)
    (S M fee : ENNReal) (hS0 : S ≠ 0) (hSt : S ≠ ⊤) (hM0 : M ≠ 0) (hMt : M ≠ ⊤)
    (hfee : (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
        feeCoefficient/S*fee) :
    Law.lawAvg honestCoordLaw r
      (fun W => f (priceBucket W)/(M*feeCoefficient*SharedMoments.alphabetSize/S)) ≤
        kappa^r*fee/(M*(SharedMoments.alphabetSize:ENNReal)^(r+1)) := by
  rw [lawAvg_div]
  calc
    _ ≤ (kappa^r * ((∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))/
        (SharedMoments.alphabetSize:ENNReal)^r))/(M*feeCoefficient*SharedMoments.alphabetSize/S) :=
      ENNReal.div_le_div_right (law_priceBucket_payoff_le r f) _
    _ ≤ (kappa^r*((feeCoefficient/S)*fee)/(SharedMoments.alphabetSize:ENNReal)^r)/
        (M*feeCoefficient*SharedMoments.alphabetSize/S) := by
      apply ENNReal.div_le_div_right
      rw [mul_div_assoc]
      exact mul_le_mul' le_rfl (ENNReal.div_le_div_right hfee _)
    _ = _ := normalize_row_arithmetic feeCoefficient S M SharedMoments.alphabetSize kappa fee r
      (by norm_num [feeCoefficient]) (by unfold feeCoefficient; finiteness)
      hS0 hSt hM0 hMt (by norm_num [SharedMoments.alphabetSize]) (by finiteness)

end ClaudeWCT.Bank.Paired


namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem alphabet_power (r : Nat) :
    SharedMoments.alphabetSize^r * 16^r = SharedMoments.fieldSize^(9*r) := by
  rw [← mul_pow]
  have h : SharedMoments.alphabetSize*16=SharedMoments.fieldSize^9 := by
    norm_num [SharedMoments.alphabetSize,SharedMoments.fieldSize]
  rw [h,pow_mul]

 theorem normalized_denominator (r M fee : Nat) (hM : 0<M) (κ : ENNReal) :
    κ^r*(fee:ENNReal)/((M:ENNReal)*(SharedMoments.alphabetSize:ENNReal)^(r+1)) =
      κ^r*((16^r*fee:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) := by
  have hD : (0:ENNReal)<SharedMoments.alphabetSize := by norm_num [SharedMoments.alphabetSize]
  have hF : (0:ENNReal)<SharedMoments.fieldSize := by norm_num [SharedMoments.fieldSize]
  have hb0 : (M:ENNReal)*(SharedMoments.alphabetSize:ENNReal)^(r+1) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hM.ne') (pow_ne_zero _ hD.ne')
  have hbt : (M:ENNReal)*(SharedMoments.alphabetSize:ENNReal)^(r+1) ≠ ⊤ := by finiteness
  have hd0 : ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (Nat.mul_pos hM (by decide +kernel : 0<SharedMoments.alphabetSize))
      (Nat.pow_pos (by decide +kernel : 0<SharedMoments.fieldSize))).ne'
  have hdt : ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.div_eq_div_iff hd0 hdt hb0 hbt).2
  simp only [Nat.cast_mul,Nat.cast_pow,pow_succ]
  have hp : (SharedMoments.fieldSize:ENNReal)^(9*r) =
      (SharedMoments.alphabetSize:ENNReal)^r*(16:ENNReal)^r := by
    exact_mod_cast (alphabet_power r).symm
  rw [hp]
  ring

 theorem law_normalized_fee_row_fields (r M S fee : Nat) (hM : 0<M) (hS : 0<S)
    (f : ENNReal → ENNReal)
    (hfee : (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
        feeCoefficient/(S:ENNReal)*(fee:ENNReal)) :
    Law.lawAvg honestCoordLaw r
      (fun W => f (priceBucket W)/((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)) ≤
      kappa^r*((16^r*fee:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) := by
  rw [← normalized_denominator r M fee hM kappa]
  exact law_normalized_fee_row r f S M fee (by positivity) (by finiteness)
    (by positivity) (by finiteness) hfee

 theorem law_normalized_le_one (r : Nat) (f : List Alphabet → ENNReal) (C : ENNReal)
    (hC0 : C ≠ 0) (hCt : C ≠ ⊤) (hbound : ∀ W, f W≤C) :
    Law.lawAvg honestCoordLaw r (fun W => f W/C) ≤ 1 := by
  calc
    _ ≤ Law.lawAvg honestCoordLaw r (fun _ => (1:ENNReal)) :=
      Law.lawAvg_mono honestCoordLaw r (fun W =>
        (ENNReal.div_le_div_right (hbound W) C).trans_eq (ENNReal.div_self hC0 hCt))
    _ = 1 := Law.lawAvg_const honestCoordLaw honestCoordLaw_sum r 1

 theorem coordAverage_div {β : Type} [Fintype β] (v : β → ENNReal) (T : Nat)
    (f : List β → ENNReal) (C p : ENNReal) :
    Law.coordAverage p v T (fun W => f W/C) = Law.coordAverage p v T f/C := by
  unfold Law.coordAverage
  simp_rw [lawAvg_div,div_eq_mul_inv]
  exact binomialAverage_mul_right p C⁻¹ T (fun r => Law.lawAvg v r f)

 theorem coordAverage_scaled {β : Type} [Fintype β] (v : β → ENNReal) (T : Nat)
    (f : List β → ENNReal) (C I p : ENNReal) (hC0 : C≠0) (hCt : C≠⊤) :
    (I*C)*Law.coordAverage p v T (fun W => f W/C) = I*Law.coordAverage p v T f := by
  rw [coordAverage_div]
  simp only [div_eq_mul_inv]
  calc
    _ = I*Law.coordAverage p v T f*(C*C⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hC0 hCt,mul_one]

end ClaudeWCT.Bank.Paired

/-! ## Binomial thinning (opus-kappa)

The honest cap-conditioned coordinate law satisfies `vA ≤ kappa·vU`. For every statistic that is monotone
under insertion of one letter, `coordAverage p vA T f ≤ coordAverage (kappa·p) vU T f`: the honest
`Bin(T,p)` stream of accepted letters is the accepted part of a `Bin(T,kappa·p)` stream of uniform letters.
This replaces the `kappa^r` tilt by the Poisson weight `e^(-2 kappa) (2 kappa)^r / r!`. -/
namespace ClaudeWCT.Numerics.Law
open ENNReal Finset

theorem coordAverage_thin {β : Type} [Fintype β] (p κ : ENNReal) (vA vU : β → ENNReal)
    (hA : ∑ b, vA b = 1) (hU : ∑ b, vU b = 1) (hdens : ∀ b, vA b ≤ κ * vU b)
    (hκ : 1 ≤ κ) (hκp : κ * p ≤ 1) (T : ℕ) (f : List β → ENNReal)
    (hf : ∀ L b R, f (L ++ R) ≤ f (L ++ b :: R)) :
    coordAverage p vA T f ≤ coordAverage (κ * p) vU T f := by
  have hp1 : p ≤ κ * p := le_mul_of_one_le_left' hκ
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (hp1.trans hκp)
  have hsumd : ∑ b, (κ * vU b - vA b) = κ - 1 := by
    have h : ∑ b, (κ * vU b - vA b) + ∑ b, vA b = κ := by
      rw [← sum_add_distrib]
      simp_rw [tsub_add_cancel_of_le (hdens _)]
      rw [← mul_sum, hU, mul_one]
    rw [hA] at h
    exact ENNReal.eq_sub_of_add_eq one_ne_top h
  have hsplit : 1 - p = (1 - κ * p) + p * (κ - 1) := by
    rw [ENNReal.mul_sub (fun _ _ => hpt), mul_one, mul_comm p κ]
    exact (tsub_add_tsub_cancel hκp hp1).symm
  induction T generalizing f with
  | zero => exact le_rfl
  | succ T ih =>
    rw [coordAverage_succ, coordAverage_succ]
    have hf' : ∀ b : β, ∀ L c R, f (b :: (L ++ R)) ≤ f (b :: (L ++ c :: R)) :=
      fun b L c R => by simpa using hf (b :: L) c R
    set X := coordAverage (κ * p) vU T f with hXdef
    set Y : β → ENNReal := fun b => coordAverage (κ * p) vU T (fun L => f (b :: L)) with hYdef
    have hXY : ∀ b, X ≤ Y b := fun b =>
      coordAverage_mono _ _ _ fun L => by simpa using hf [] b L
    have h1 : coordAverage p vA T f ≤ X := ih f hf
    have h2 : ∀ b, coordAverage p vA T (fun L => f (b :: L)) ≤ Y b :=
      fun b => ih _ (fun L c R => hf' b L c R)
    calc (1 - p) * coordAverage p vA T f + p * ∑ b, vA b * coordAverage p vA T (fun L => f (b :: L))
        ≤ (1 - p) * X + p * ∑ b, vA b * Y b :=
          add_le_add (mul_le_mul' le_rfl h1)
            (mul_le_mul' le_rfl (sum_le_sum fun b _ => mul_le_mul' le_rfl (h2 b)))
      _ = (1 - κ * p) * X + p * ∑ b, ((κ * vU b - vA b) * X + vA b * Y b) := by
          rw [sum_add_distrib, ← sum_mul, hsumd, hsplit]
          ring
      _ ≤ (1 - κ * p) * X + p * ∑ b, ((κ * vU b - vA b) * Y b + vA b * Y b) := by
          gcongr with b
          exact hXY b
      _ = (1 - κ * p) * X + κ * p * ∑ b, vU b * Y b := by
          congr 1
          simp_rw [← add_mul, tsub_add_cancel_of_le (hdens _)]
          rw [mul_sum, mul_sum]
          exact sum_congr rfl fun b _ => by ring

end ClaudeWCT.Numerics.Law

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

noncomputable def uniformCoordLaw (_ : Alphabet) : ENNReal := (Fintype.card Alphabet : ENNReal)⁻¹

theorem uniformCoordLaw_sum : ∑ a, uniformCoordLaw a = 1 := by
  simp only [uniformCoordLaw, sum_const, card_univ, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

theorem uniformCoordLaw_density (a : Alphabet) :
    uniformCoordLaw a ≤ 1 * (Fintype.card Alphabet : ENNReal)⁻¹ := by
  simp [uniformCoordLaw]

theorem kappa_mul_rate_le_one : kappa * (2^31 : ENNReal)⁻¹ ≤ 1 := by
  rw [kappa_exact]
  have hc : (ClaudeWCT.Numerics.SharedFtsCount.count : ENNReal) ≠ 0 := by
    norm_num [ClaudeWCT.Numerics.SharedFtsCount.count]
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hc)
    (by simp)) (by finiteness)).mp
  norm_num [ClaudeWCT.Numerics.SharedFtsCount.total, ClaudeWCT.Numerics.SharedFtsCount.count,
    ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]

/-- The honest per-instance law is the thinning of the uniform law at rate `kappa * 2^-31`. -/
theorem coordAverage_honest_thin (T : ℕ) (f : List Alphabet → ENNReal)
    (hf : ∀ L b R, f (L ++ R) ≤ f (L ++ b :: R)) :
    Law.coordAverage (2^31 : ENNReal)⁻¹ honestCoordLaw T f ≤
      Law.coordAverage (kappa * (2^31 : ENNReal)⁻¹) uniformCoordLaw T f :=
  Law.coordAverage_thin _ _ _ _ honestCoordLaw_sum uniformCoordLaw_sum
    honestCoordLaw_density kappa_one_le kappa_mul_rate_le_one T f hf

theorem uniform_priceBucket_payoff_le (r : Nat) (f : ENNReal → ENNReal) :
    Law.lawAvg uniformCoordLaw r (fun W => f (priceBucket W)) ≤
      1^r * ((∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))/
        (SharedMoments.alphabetSize:ENNReal)^r) := by
  have h := Law.lawAvg_le_uniform uniformCoordLaw 1 uniformCoordLaw_density r
    (fun W => f (priceBucket W))
  rw [uniform_history_average r (fun W => f (priceBucket W))
    (fun h => f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))
    (fun h => congrArg f (priceBucket_ofFn h))] at h
  have hc : Fintype.card Alphabet = SharedMoments.alphabetSize := alphabet_card rfl
  simpa only [hc] using h

theorem uniform_normalized_fee_row_fields (r M S fee : Nat) (hM : 0<M) (hS : 0<S)
    (f : ENNReal → ENNReal)
    (hfee : (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
        feeCoefficient/(S:ENNReal)*(fee:ENNReal)) :
    Law.lawAvg uniformCoordLaw r
      (fun W => f (priceBucket W)/((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)) ≤
      1^r*((16^r*fee:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) := by
  rw [← normalized_denominator r M fee hM 1, lawAvg_div]
  calc
    _ ≤ (1^r * ((∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))/
        (SharedMoments.alphabetSize:ENNReal)^r))/((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S) :=
      ENNReal.div_le_div_right (uniform_priceBucket_payoff_le r f) _
    _ ≤ (1^r*((feeCoefficient/(S:ENNReal))*(fee:ENNReal))/(SharedMoments.alphabetSize:ENNReal)^r)/
        ((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S) := by
      apply ENNReal.div_le_div_right
      rw [mul_div_assoc]
      exact mul_le_mul' le_rfl (ENNReal.div_le_div_right hfee _)
    _ = _ := normalize_row_arithmetic feeCoefficient S M SharedMoments.alphabetSize 1 fee r
      (by norm_num [feeCoefficient]) (by unfold feeCoefficient; finiteness)
      (by positivity) (by finiteness) (by positivity) (by finiteness)
      (by norm_num [SharedMoments.alphabetSize]) (by finiteness)

theorem uniform_normalized_le_one (r : Nat) (f : List Alphabet → ENNReal) (C : ENNReal)
    (hC0 : C ≠ 0) (hCt : C ≠ ⊤) (hbound : ∀ W, f W≤C) :
    Law.lawAvg uniformCoordLaw r (fun W => f W/C) ≤ 1 := by
  calc
    _ ≤ Law.lawAvg uniformCoordLaw r (fun _ => (1:ENNReal)) :=
      Law.lawAvg_mono uniformCoordLaw r (fun W =>
        (ENNReal.div_le_div_right (hbound W) C).trans_eq (ENNReal.div_self hC0 hCt))
    _ = 1 := Law.lawAvg_const uniformCoordLaw uniformCoordLaw_sum r 1

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SigGolfResearch.Gate6.Moments (finiteAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem bucketEnv_le_one {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (W : List (AlphabetOf β)) : bucketEnv val W ≤ 1 := by
  classical
  unfold bucketEnv finiteAverage
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  calc
    _ ≤ ∑ _a : AlphabetOf β, (1:ENNReal) := Finset.sum_le_sum (fun a _ => by split_ifs <;> simp)
    _ = _ := by simp

 theorem fee_price_scale : feeCoefficient*(SharedMoments.alphabetSize:ENNReal) =
    (SharedMoments.priceScaleTotal:ENNReal)/(2^31) := by
  rw [← price_coefficient]
  exact ENNReal.div_mul_cancel (by norm_num [SharedMoments.alphabetSize]) (by finiteness)

 theorem priceBucket_le (W : List Alphabet) :
    priceBucket W ≤ feeCoefficient*(SharedMoments.alphabetSize:ENNReal) := by
  rw [fee_price_scale]
  exact (mul_le_mul' le_rfl (bucketEnv_le_one ClaudeWCT.WCT9.wordDigit W)).trans_eq (mul_one _)

 theorem priceBucket_ne_top (W : List Alphabet) : priceBucket W ≠ ⊤ :=
  ne_top_of_le_ne_top (by unfold feeCoefficient; finiteness) (priceBucket_le W)

 noncomputable def cappedIncrement (x : ENNReal) : ENNReal :=
  ENNReal.ofReal (Real.exp (6*(min x ((6:ENNReal)/5)).toReal))-1
 noncomputable def cappedResidual (x : ENNReal) : ENNReal := x-(6:ENNReal)/5

 theorem cappedIncrement_real (x : ENNReal) (hx : x ≠ ⊤) :
    cappedIncrement x = ENNReal.ofReal (Real.exp (6*min x.toReal (6/5))-1) := by
  rw [cappedIncrement,ENNReal.toReal_min hx (by finiteness),ENNReal.toReal_div]
  norm_num only [ENNReal.toReal_ofNat]
  rw [ENNReal.ofReal_sub _ (by norm_num),ENNReal.ofReal_one]

 theorem cappedResidual_real (x : ENNReal) (hx : x ≠ ⊤) :
    cappedResidual x = ENNReal.ofReal (max 0 (x.toReal-6/5)) := by
  rw [ENNReal.ofReal_max,ENNReal.ofReal_zero,max_eq_right (by positivity),
    ENNReal.ofReal_sub _ (by norm_num),ENNReal.ofReal_toReal hx]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<5)]
  norm_num [cappedResidual]

 theorem feeCoefficient_real : feeCoefficient.toReal = (791:ℝ)/2^66 := by
  norm_num [feeCoefficient,ENNReal.toReal_div]

 theorem cappedIncrement_nat (n : Nat) :
    cappedIncrement (feeCoefficient*(n:ENNReal)) =
      ENNReal.ofReal (Real.exp (6*min ((791:ℝ)/2^66*(n:ℝ)) (6/5))-1) := by
  rw [cappedIncrement_real _ (by unfold feeCoefficient; finiteness),
    ENNReal.toReal_mul,feeCoefficient_real,ENNReal.toReal_natCast]

 theorem cappedResidual_nat (n : Nat) :
    cappedResidual (feeCoefficient*(n:ENNReal)) =
      ENNReal.ofReal (max 0 ((791:ℝ)/2^66*(n:ℝ)-6/5)) := by
  rw [cappedResidual_real _ (by unfold feeCoefficient; finiteness),
    ENNReal.toReal_mul,feeCoefficient_real,ENNReal.toReal_natCast]

 theorem cappedResidual_bound (W : List Alphabet) :
    cappedResidual (priceBucket W) ≤ feeCoefficient*SharedMoments.alphabetSize :=
  (tsub_le_self).trans (priceBucket_le W)

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem normalizer_scale (M S : Nat) :
    (2^31:ENNReal)*((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S) =
      ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S := by
  have he : (2^31:ENNReal)*(feeCoefficient*SharedMoments.alphabetSize) =
      (SharedMoments.priceScaleTotal:ENNReal) := by
    rw [fee_price_scale]
    simp only [div_eq_mul_inv]
    calc
      _ = (SharedMoments.priceScaleTotal:ENNReal)*((2^31:ENNReal)*(2^31:ENNReal)⁻¹) := by ring
      _ = _ := by rw [ENNReal.mul_inv_cancel (by norm_num) (by finiteness),mul_one]
  simp only [div_eq_mul_inv,Nat.cast_mul]
  calc
    _ = (M:ENNReal)*((2^31:ENNReal)*(feeCoefficient*SharedMoments.alphabetSize))*(S:ENNReal)⁻¹ := by ring
    _ = _ := by rw [he]

 theorem uniform_coordAverage_bound_of_rows (T M S : Nat) (hM : 0<M) (hS : 0<S)
    (f : ENNReal → ENNReal) (fees : Nat → Nat) (bound : ENNReal)
    (hfees : ∀ r≤80, (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
        feeCoefficient/(S:ENNReal)*(fees r:ENNReal))
    (hpoint : ∀ W, f (priceBucket W) ≤
      (M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)
    (hcheck : ∀ g : Nat → ENNReal,
      (∀ r≤80, g r ≤ 1^r*((16^r*fees r:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal)) →
      (∀ r,80 < r → g r ≤ 1) →
      ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S *
        binomialAverage (kappa*(2^31:ENNReal)⁻¹) T g ≤ bound) :
    (2^31:ENNReal)*Law.coordAverage (kappa*(2^31:ENNReal)⁻¹) uniformCoordLaw T
      (fun W => f (priceBucket W)) ≤ bound := by
  let C : ENNReal := (M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S
  have hC0 : C≠0 := by
    have hMc : (M:ENNReal) ≠ 0 := by exact_mod_cast hM.ne'
    have hfc : feeCoefficient ≠ 0 := by norm_num [feeCoefficient]
    have hDc : (SharedMoments.alphabetSize:ENNReal) ≠ 0 := by norm_num [SharedMoments.alphabetSize]
    exact ENNReal.div_ne_zero.mpr ⟨mul_ne_zero (mul_ne_zero hMc hfc) hDc, ENNReal.natCast_ne_top S⟩
  have hCt : C≠⊤ := by dsimp [C,feeCoefficient]; finiteness
  let g : Nat → ENNReal := fun r => Law.lawAvg uniformCoordLaw r (fun W => f (priceBucket W)/C)
  have hg := hcheck g (fun r hr => uniform_normalized_fee_row_fields r M S (fees r) hM hS f (hfees r hr))
    (fun r _ => uniform_normalized_le_one r (fun W => f (priceBucket W)) C hC0 hCt hpoint)
  calc
    _ = ((2^31:ENNReal)*C)*Law.coordAverage (kappa*(2^31:ENNReal)⁻¹) uniformCoordLaw T
      (fun W => f (priceBucket W)/C) :=
      (coordAverage_scaled uniformCoordLaw T (fun W => f (priceBucket W)) C (2^31) _ hC0 hCt).symm
    _ = ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S *
        binomialAverage (kappa*(2^31:ENNReal)⁻¹) T g := by
      rw [show (2^31:ENNReal)*C=((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S from normalizer_scale M S]
      rfl
    _ ≤ bound := hg

/-- Thinned row certificate for the honest law: any payoff `f` monotone in the bucket price is
bounded through `coordAverage_honest_thin` and the uniform rows (no `kappa^r` tilt). -/
 theorem coordAverage_bound_of_rows (T M S : Nat) (hM : 0<M) (hS : 0<S)
    (f : ENNReal → ENNReal) (fees : Nat → Nat) (bound : ENNReal)
    (hmono : ∀ x y, x ≤ y → f x ≤ f y)
    (hfees : ∀ r≤80, (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
        feeCoefficient/(S:ENNReal)*(fees r:ENNReal))
    (hpoint : ∀ W, f (priceBucket W) ≤
      (M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)
    (hcheck : ∀ g : Nat → ENNReal,
      (∀ r≤80, g r ≤ 1^r*((16^r*fees r:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal)) →
      (∀ r,80 < r → g r ≤ 1) →
      ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S *
        binomialAverage (kappa*(2^31:ENNReal)⁻¹) T g ≤ bound) :
    (2^31:ENNReal)*Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T
      (fun W => f (priceBucket W)) ≤ bound :=
  (mul_le_mul' le_rfl (coordAverage_honest_thin T (fun W => f (priceBucket W))
    (fun L b R => hmono _ _ (priceBucket_insert L R b)))).trans
    (uniform_coordAverage_bound_of_rows T M S hM hS f fees bound hfees hpoint hcheck)

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SharedFees SharedMoments
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem cappedIncrement_bound (W : List Alphabet) :
    cappedIncrement (priceBucket W) ≤
      (maxFee:ENNReal)*feeCoefficient*alphabetSize/scale := by
  have hx := ENNReal.toReal_mono (by unfold feeCoefficient; finiteness) (priceBucket_le W)
  rw [ENNReal.toReal_mul,feeCoefficient_real,ENNReal.toReal_natCast] at hx
  have h := (capped_payoff_of_coverage_bound (priceBucket W).toReal
    ((791:ℝ)/2^66) (alphabetSize:ℝ) ENNReal.toReal_nonneg hx).1
  rw [cappedIncrement_real _ (priceBucket_ne_top W)]
  calc
    _ ≤ ENNReal.ofReal ((maxFee:ℝ)*((791:ℝ)/2^66)*(alphabetSize:ℝ)/scale) :=
      ENNReal.ofReal_le_ofReal h
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast scale_pos : (0:ℝ)<scale),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      simp only [ENNReal.ofReal_natCast]
      rw [← feeCoefficient_real, ENNReal.ofReal_toReal (by unfold feeCoefficient; finiteness)]

 theorem residual_normalizer :
    (scale:ENNReal)*feeCoefficient*alphabetSize/scale = feeCoefficient*alphabetSize := by
  have hs0 : (scale:ENNReal) ≠ 0 := by exact_mod_cast scale_pos.ne'
  have hst : (scale:ENNReal) ≠ ⊤ := by finiteness
  simp only [div_eq_mul_inv]
  calc _ = (feeCoefficient*alphabetSize)*((scale:ENNReal)*(scale:ENNReal)⁻¹) := by ring
       _ = _ := by rw [ENNReal.mul_inv_cancel hs0 hst,mul_one]

 theorem cappedResidual_normalized_bound (W : List Alphabet) :
    cappedResidual (priceBucket W) ≤
      (scale:ENNReal)*feeCoefficient*alphabetSize/scale := by
  rw [residual_normalizer]
  exact cappedResidual_bound W

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SharedFees SharedMoments SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- The finite coverage certificate still to be supplied by the paired
histogram calculation. All sampling and conditioning factors are outside it. -/
def FiniteFeeBound : Prop := ∀ r≤80,
  (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
    cappedIncrement (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
      feeCoefficient/(scale:ENNReal)*((certifiedPayoff r).1:ENNReal) ∧
  (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
    cappedResidual (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
      feeCoefficient/(scale:ENNReal)*((certifiedPayoff r).2:ENNReal)

 theorem fee_positive : 0 < maxFee := by
  by_contra hn
  have hz : maxFee=0 := Nat.eq_zero_of_not_pos hn
  have h := (capped_payoff_of_coverage_bound 1 1 1 (by norm_num) (by norm_num)).1
  rw [hz] at h
  norm_num at h

 theorem cappedIncrement_mono {x y : ENNReal} (h : x ≤ y) : cappedIncrement x ≤ cappedIncrement y := by
  unfold cappedIncrement
  apply tsub_le_tsub_right
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num))
    (min_le_right _ _)) (min_le_min h le_rfl)

 theorem cappedResidual_mono {x y : ENNReal} (h : x ≤ y) : cappedResidual x ≤ cappedResidual y :=
  tsub_le_tsub_right h _

 theorem kappa_toReal : kappa.toReal =
    (ClaudeWCT.Numerics.SharedFtsCount.total : ℝ) / ClaudeWCT.Numerics.SharedFtsCount.count := by
  rw [kappa_exact, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-- Window for the thinned rate `kappa * 2^-31` (rejection_ennreal style, tangent line of exp at 2):
`(1 - kappa 2^-31)^(T-80) ≤ 13283369e-8` for the cap-777 `kappa`. -/
 theorem thin_window (T : ℕ) (hT : 2 ^ 32 ≤ T) :
    (1 - kappa * (2^31 : ENNReal)⁻¹) ^ (T - 80) ≤
      ((13283369 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal) := by
  have hq1 := kappa_mul_rate_le_one
  have hfin : (1 - kappa * (2^31 : ENNReal)⁻¹) ^ (T - 80) ≠ ⊤ :=
    ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  apply (ENNReal.toReal_le_toReal hfin (by finiteness)).mp
  rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hq1 ENNReal.one_ne_top, ENNReal.toReal_mul,
    kappa_toReal, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  simp only [ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  set k : ℝ := (ClaudeWCT.Numerics.SharedFtsCount.total : ℝ) / ClaudeWCT.Numerics.SharedFtsCount.count with hk
  have hkv : k = 52416169542617085727767971710947931910569984 / 51927206731424509281114869451843031004872704 := by
    rw [hk]; norm_num [ClaudeWCT.Numerics.SharedFtsCount.total, ClaudeWCT.Numerics.SharedFtsCount.count]
  set n := T - 80 with hn
  have hn0 : (2:ℝ)^32 - 80 ≤ n := by
    have : 2^32 - 80 ≤ n := by omega
    have h' : ((2^32 - 80 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    norm_num at h' ⊢; linarith
  have h0 : (0 : ℝ) ≤ 1 - k * (2^31)⁻¹ := by rw [hkv]; norm_num
  have hp : (1 - k * (2^31)⁻¹ : ℝ) ≤ Real.exp (-(k * (2^31)⁻¹)) := Real.one_sub_le_exp_neg _
  have hpow : (1 - k * (2^31)⁻¹ : ℝ) ^ n ≤ Real.exp (-(n * (k * (2^31)⁻¹))) := by
    calc (1 - k * (2^31)⁻¹ : ℝ) ^ n ≤ Real.exp (-(k * (2^31)⁻¹)) ^ n := pow_le_pow_left₀ h0 hp n
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  set a0 : ℝ := ((2:ℝ)^32 - 80) * (k * (2^31)⁻¹) with ha0
  have ha : a0 ≤ n * (k * (2^31)⁻¹) :=
    mul_le_mul_of_nonneg_right hn0 (by rw [hkv]; norm_num)
  have hlow : (100000000 : ℝ) / 13283369 ≤ (2.7182818283 : ℝ) ^ 2 * (a0 - 1) := by
    rw [ha0, hkv]; norm_num
  have hexp : (100000000 : ℝ) / 13283369 ≤ Real.exp (n * (k * (2^31)⁻¹)) :=
    hlow.trans ((ClaudeWCT.Numerics.PoissonReflect.exp_lower a0).trans (Real.exp_le_exp.mpr ha))
  refine hpow.trans ?_
  rw [Real.exp_neg]
  have hpos : (0:ℝ) < 100000000 / 13283369 := by norm_num
  calc (Real.exp (n * (k * (2^31)⁻¹)))⁻¹ ≤ ((100000000 : ℝ) / 13283369)⁻¹ :=
        inv_anti₀ hpos hexp
    _ = ((13283369 : ℕ) : ℝ) / ((100000000 : ℕ) : ℝ) := by norm_num

/-- Thinned Poisson parameter: `2^32 · kappa · 2^-31 = 2 kappa ≤ 2.018833` (cap 777). -/
 theorem thin_lambda :
    ((2^32 : ℕ) : ENNReal) * (kappa * (2^31 : ENNReal)⁻¹) * 1 ≤
      ((2018833 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal) := by
  rw [mul_one, kappa_exact]
  have hc : (ClaudeWCT.Numerics.SharedFtsCount.count : ENNReal) ≠ 0 := by
    norm_num [ClaudeWCT.Numerics.SharedFtsCount.count]
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ENNReal.mul_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hc) (by simp))) (by finiteness)).mp
  norm_num [ClaudeWCT.Numerics.SharedFtsCount.total, ClaudeWCT.Numerics.SharedFtsCount.count,
    ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]

end ClaudeWCT.Bank.Paired

/-! Scalar endpoints for the cap-777 thinned certificate (shared MGF `6.945`, residual `7831e-7`). -/
namespace ClaudeWCT.Numerics.SharedPathWinsor.Rows18Thin
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

end ClaudeWCT.Numerics.SharedPathWinsor.Rows18Thin

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem tsub_convex (x theta eta a b : ENNReal) (hab : a+b=1) :
    x-(a*theta+b*eta) ≤ a*(x-theta)+b*(x-eta) := by
  apply (tsub_le_iff_right).2
  calc x = a*x+b*x := by rw [← add_mul,hab,one_mul]
       _ ≤ a*(theta+(x-theta))+b*(eta+(x-eta)) :=
         add_le_add (mul_le_mul' le_rfl le_add_tsub) (mul_le_mul' le_rfl le_add_tsub)
       _ = _ := by ring

 theorem price_excess_affine (T : Nat) (theta eta A B t : ℝ)
    (htheta : 0 ≤ theta) (heta : 0 ≤ eta) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hfirst : Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal theta) ≤ ENNReal.ofReal A)
    (hsecond : Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal eta) ≤ ENNReal.ofReal B) :
    Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal ((1-t)*theta+t*eta)) ≤
      ENNReal.ofReal ((1-t)*A+t*B) := by
  have ha0 : 0 ≤ 1-t := sub_nonneg.mpr ht1
  have hab : ENNReal.ofReal (1-t)+ENNReal.ofReal t=1 := by
    rw [←ENNReal.ofReal_add ha0 ht0]
    ring_nf
    exact ENNReal.ofReal_one
  have harg : ENNReal.ofReal ((1-t)*theta+t*eta) =
      ENNReal.ofReal (1-t)*ENNReal.ofReal theta+ENNReal.ofReal t*ENNReal.ofReal eta := by
    rw [ENNReal.ofReal_add (mul_nonneg ha0 htheta) (mul_nonneg ht0 heta),
      ENNReal.ofReal_mul ha0, ENNReal.ofReal_mul ht0]
  rw [harg]
  calc
    _ ≤ Law.lawAvg honestLaw T (fun W =>
      ENNReal.ofReal (1-t)*(price W-ENNReal.ofReal theta)+
      ENNReal.ofReal t*(price W-ENNReal.ofReal eta)) :=
        Law.lawAvg_mono _ _ (fun W => tsub_convex _ _ _ _ _ hab)
    _ = ENNReal.ofReal (1-t)*Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal theta)+
        ENNReal.ofReal t*Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal eta) := by
      rw [Law.lawAvg_add,Law.lawAvg_mul_left,Law.lawAvg_mul_left]
    _ ≤ ENNReal.ofReal (1-t)*ENNReal.ofReal A+ENNReal.ofReal t*ENNReal.ofReal B :=
      add_le_add (mul_le_mul' le_rfl hfirst) (mul_le_mul' le_rfl hsecond)
    _ = _ := by
      rw [←ENNReal.ofReal_mul ha0,←ENNReal.ofReal_mul ht0,
        ←ENNReal.ofReal_add (mul_nonneg ha0 hA) (mul_nonneg ht0 hB)]

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SharedMoments SphincsSecurity.Concrete
open SigGolfCandidate.T3.BPORS.History (atIndex)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem law_marked_sum {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β]
    (v : β → ENNReal) (hv : ∑ b,v b=1) (T : Nat) (f : List β → ENNReal) :
    Law.lawAvg (Law.marked (α:=α) v) T (fun W => ∑ i:α,f (atIndex i W)) =
      (Fintype.card α:ENNReal)*Law.coordAverage (Fintype.card α:ENNReal)⁻¹ v T f := by
  rw [Law.lawAvg_sum]
  simp only [Law.law_marked_atIndex v hv, Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rfl

 theorem law_price_coordAverage (T : Nat) :
    Law.lawAvg honestLaw T price =
      (2^31:ENNReal)*Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T priceBucket := by
  have he : price = fun W => ∑ i : Fin (2^31),priceBucket (atIndex i W) := funext price_eq_sum
  rw [he]
  have h := law_marked_sum (α:=Fin (2^31)) honestCoordLaw honestCoordLaw_sum T priceBucket
  simpa only [honestLaw,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] using h

 theorem first_finite_row (r : Nat) (hr : r≤80) :
    (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)) =
        feeCoefficient*(forestMoment r:ENNReal) := by
  rw [← Finset.mul_sum,←Nat.cast_sum]
  have h := SharedCoverage.forest_coverage_data ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563)
    WCTEnvelope.w1Table_wordDigit rows_checked r (by omega)
  exact congrArg (fun n : Nat => feeCoefficient*(n:ENNReal)) h

 theorem law_price_mean_bound : Law.lawAvg honestLaw (2^32) price ≤ (915:ENNReal)/1000 := by
  rw [law_price_coordAverage]
  apply coordAverage_bound_of_rows (2^32) 1 1 (by norm_num) (by norm_num)
    id forestMoment (915/1000) (fun _ _ h => h)
  · intro r hr
    simpa only [id_eq,Nat.cast_one,div_one] using (first_finite_row r hr).le
  · intro W
    simpa only [id_eq,Nat.cast_one,one_mul,div_one] using priceBucket_le W
  · intro g hp ht
    have h := first_bound_of_rows (2^32) _ kappa_mul_rate_le_one (thin_window _ le_rfl)
      1 le_rfl thin_lambda g (by simpa only [Nat.one_mul] using hp) ht
    simpa only [Nat.one_mul,Nat.cast_one,div_one] using h

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem uniform_history_le_of_le (r : Nat) (f : List Alphabet → ENNReal)
    (g : SharedCoverage.ForestHistory (Fin 563) r → ENNReal)
    (hfg : ∀ h : Fin r → Alphabet,f (List.ofFn h) ≤ g (splitHistory h)) :
    Law.lawAvg uniformCoordLaw r f ≤ 1^r *
      ((∑ h,g h)/(SharedMoments.alphabetSize:ENNReal)^r) := by
  have hu : SphincsSecurity.Concrete.uniformWordAverage r f ≤
      (∑ h,g h)/(SharedMoments.alphabetSize:ENNReal)^r := by
    rw [SigGolfResearch.Gate6.Moments.word_array_average]
    unfold SigGolfResearch.Gate6.Moments.finiteAverage
    have hc : Fintype.card Alphabet=SharedMoments.alphabetSize := alphabet_card rfl
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,hc]
    rw [←sum_history]
    exact ENNReal.div_le_div_right (Finset.sum_le_sum (fun h _ => hfg h)) _
  exact (Law.lawAvg_le_uniform uniformCoordLaw 1 uniformCoordLaw_density r f).trans
    (mul_le_mul' le_rfl hu)

 theorem uniform_normalized_history_row (r M S fee : Nat) (hM : 0<M) (hS : 0<S)
    (f : List Alphabet → ENNReal) (g : SharedCoverage.ForestHistory (Fin 563) r → ENNReal)
    (hfg : ∀ h : Fin r → Alphabet,f (List.ofFn h) ≤ g (splitHistory h))
    (hfee : (∑ h,g h) ≤ feeCoefficient/(S:ENNReal)*(fee:ENNReal)) :
    Law.lawAvg uniformCoordLaw r
      (fun W => f W/((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)) ≤
      1^r*((16^r*fee:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) := by
  rw [←normalized_denominator r M fee hM 1,lawAvg_div]
  calc
    _ ≤ (1^r*((∑ h,g h)/(SharedMoments.alphabetSize:ENNReal)^r))/
        ((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S) :=
      ENNReal.div_le_div_right (uniform_history_le_of_le r f g hfg) _
    _ ≤ (1^r*((feeCoefficient/(S:ENNReal))*(fee:ENNReal))/(SharedMoments.alphabetSize:ENNReal)^r)/
        ((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S) := by
      apply ENNReal.div_le_div_right
      rw [mul_div_assoc]
      exact mul_le_mul' le_rfl (ENNReal.div_le_div_right hfee _)
    _ = _ := normalize_row_arithmetic feeCoefficient S M SharedMoments.alphabetSize 1 fee r
      (by norm_num [feeCoefficient]) (by unfold feeCoefficient; finiteness)
      (by positivity) (by finiteness) (by positivity) (by finiteness)
      (by norm_num [SharedMoments.alphabetSize]) (by finiteness)

/-- Thinned history certificate: an insertion-monotone `f` is bounded through
`coordAverage_honest_thin` and uniform history rows (no `kappa^r` tilt). -/
 theorem coordAverage_history_bound (T M S : Nat) (hM : 0<M) (hS : 0<S)
    (f : List Alphabet → ENNReal)
    (g : (r : Nat) → SharedCoverage.ForestHistory (Fin 563) r → ENNReal)
    (fees : Nat → Nat) (bound : ENNReal)
    (hins : ∀ L b R,f (L++R) ≤ f (L++b::R))
    (hfg : ∀ r≤80,∀ h : Fin r → Alphabet,f (List.ofFn h) ≤ g r (splitHistory h))
    (hfees : ∀ r≤80,(∑ h,g r h) ≤ feeCoefficient/(S:ENNReal)*(fees r:ENNReal))
    (hpoint : ∀ W,f W≤(M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)
    (hcheck : ∀ v : Nat → ENNReal,
      (∀ r≤80,v r≤1^r*((16^r*fees r:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal)) →
      (∀ r,80 < r → v r≤1) →
      ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S *
        SphincsSecurity.Concrete.binomialAverage (kappa*(2^31:ENNReal)⁻¹) T v ≤ bound) :
    (2^31:ENNReal)*Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T f ≤ bound := by
  refine (mul_le_mul' le_rfl (coordAverage_honest_thin T f hins)).trans ?_
  let C : ENNReal := (M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S
  have hC0 : C≠0 := by
    have hMc : (M:ENNReal)≠0 := by exact_mod_cast hM.ne'
    have hfc : feeCoefficient≠0 := by norm_num [feeCoefficient]
    have hDc : (SharedMoments.alphabetSize:ENNReal)≠0 := by norm_num [SharedMoments.alphabetSize]
    exact ENNReal.div_ne_zero.mpr ⟨mul_ne_zero (mul_ne_zero hMc hfc) hDc,ENNReal.natCast_ne_top S⟩
  have hCt : C≠⊤ := by dsimp [C,feeCoefficient]; finiteness
  let v : Nat → ENNReal := fun r => Law.lawAvg uniformCoordLaw r (fun W => f W/C)
  have hv := hcheck v
    (fun r hr => uniform_normalized_history_row r M S (fees r) hM hS f (g r) (hfg r hr) (hfees r hr))
    (fun r _ => uniform_normalized_le_one r f C hC0 hCt hpoint)
  calc
    _ = ((2^31:ENNReal)*C)*Law.coordAverage (kappa*(2^31:ENNReal)⁻¹) uniformCoordLaw T (fun W => f W/C) :=
      (coordAverage_scaled uniformCoordLaw T f C (2^31) (kappa*(2^31:ENNReal)⁻¹) hC0 hCt).symm
    _ = ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S *
        SphincsSecurity.Concrete.binomialAverage (kappa*(2^31:ENNReal)⁻¹) T v := by
      rw [show (2^31:ENNReal)*C=((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S from normalizer_scale M S]
      rfl
    _ ≤ bound := hv

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ClaudeWCT.Numerics ClaudeWCT.Numerics.N600
open SharedCoverage Thinning
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

 theorem card_filter_congr_any {α : Type} [Fintype α] (P Q : α → Prop)
    (dP : DecidablePred P) (dQ : DecidablePred Q) (h : ∀ a,P a↔Q a) :
    (@Finset.filter α P dP Finset.univ).card = (@Finset.filter α Q dQ Finset.univ).card := by
  apply congrArg Finset.card
  ext a
  simp only [Finset.mem_filter]
  exact and_congr Iff.rfl (h a)

def PairNearAt {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : PairHistory β r) (side : Fin 2) (t : Fin 6) (a : PairChoice β) : Prop :=
  if side=0 then
    CovAtExcept val t a.2.1.1 (val a.2.1.2) (splitRanks h.1 h.2.1 a.1) ∧
    CovAt val a.2.2.1 (val a.2.2.2) (splitRanks h.1 h.2.2 a.1)
  else
    CovAt val a.2.1.1 (val a.2.1.2) (splitRanks h.1 h.2.1 a.1) ∧
    CovAtExcept val t a.2.2.1 (val a.2.2.2) (splitRanks h.1 h.2.2 a.1)

 theorem pairPredicate_card {β : Type} [Fintype β]
    (P Q : Fin 2 → Fin 64 × β → Prop) :
    #{a : PairChoice β | P a.1 a.2.1 ∧ Q a.1 a.2.2} =
      ∑ s : Fin 2, #{a | P s a} * #{b | Q s b} := by
  let e : {a : PairChoice β // P a.1 a.2.1 ∧ Q a.1 a.2.2} ≃
      (s : Fin 2) × {a : Fin 64 × β // P s a} × {b : Fin 64 × β // Q s b} :=
    { toFun := fun a => ⟨a.val.1,⟨a.val.2.1,a.property.1⟩,⟨a.val.2.2,a.property.2⟩⟩
      invFun := fun a => ⟨(a.1,a.2.1.val,a.2.2.val),a.2.1.property,a.2.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := Fintype.card_congr e
  simpa only [Fintype.card_subtype,Fintype.card_sigma,Fintype.card_prod] using he

 theorem pairNearAt_sum {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : PairHistory β r) :
    (∑ side : Fin 2, ∑ t : Fin 6, #{a : PairChoice β | PairNearAt val h side t a}) =
      pairNear val h := by
  have hleft (t : Fin 6) : #{a : PairChoice β | PairNearAt val h 0 t a} =
      ∑ s : Fin 2, #{a : Fin 64 × β | CovAtExcept val t a.1 (val a.2) (splitRanks h.1 h.2.1 s)} *
        coordinateCoverage val (splitRanks h.1 h.2.2 s) := by
    have hh := pairPredicate_card
      (fun s a => CovAtExcept val t a.1 (val a.2) (splitRanks h.1 h.2.1 s))
      (fun s a => CovAt val a.1 (val a.2) (splitRanks h.1 h.2.2 s))
    convert hh using 1
    · apply card_filter_congr_any; intro a; simp only [PairNearAt,ite_true]
    · apply Finset.sum_congr rfl
      intro z _
      apply congrArg₂ Nat.mul
      · apply card_filter_congr_any; intro a; rfl
      · unfold coordinateCoverage
        apply card_filter_congr_any; intro a; rfl
  have hright (t : Fin 6) : #{a : PairChoice β | PairNearAt val h 1 t a} =
      ∑ s : Fin 2, coordinateCoverage val (splitRanks h.1 h.2.1 s) *
        #{a : Fin 64 × β | CovAtExcept val t a.1 (val a.2) (splitRanks h.1 h.2.2 s)} := by
    have hh := pairPredicate_card
      (fun s a => CovAt val a.1 (val a.2) (splitRanks h.1 h.2.1 s))
      (fun s a => CovAtExcept val t a.1 (val a.2) (splitRanks h.1 h.2.2 s))
    convert hh using 1
    · apply card_filter_congr_any; intro a; simp only [PairNearAt,show (1:Fin 2)≠0 by decide,ite_false]
    · apply Finset.sum_congr rfl
      intro z _
      apply congrArg₂ Nat.mul
      · unfold coordinateCoverage
        apply card_filter_congr_any; intro a; rfl
      · apply card_filter_congr_any; intro a; rfl
  rw [Fin.sum_univ_two]
  simp_rw [hleft,hright]
  simp only [Fin.sum_univ_two,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum]
  unfold pairNear selectorKernel coordinateNear coordinateCoverage
  ring

abbrev ForestHole := (Fin 4 × Fin 2 × Fin 6) ⊕ Fin 6

def ForestNearAt {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : ForestHistory β r) (hole : ForestHole) (a : ForestChoice β) : Prop :=
  match hole with
  | .inl v => (∀ p, if p=v.1 then PairNearAt val (h.1 p) v.2.1 v.2.2 (a.1 p)
                    else PairCovered val (h.1 p) (a.1 p)) ∧ CovAt val a.2.1 (val a.2.2) h.2
  | .inr t => (∀ p, PairCovered val (h.1 p) (a.1 p)) ∧ CovAtExcept val t a.2.1 (val a.2.2) h.2

 theorem forestPredicate_card {β : Type} [Fintype β]
    (P : Fin 4 → PairChoice β → Prop) (Q : Fin 128 × β → Prop) :
    #{a : ForestChoice β | (∀ p, P p (a.1 p)) ∧ Q a.2} =
      (∏ p, #{a | P p a}) * #{b | Q b} := by
  let e : {a : ForestChoice β // (∀ p,P p (a.1 p)) ∧ Q a.2} ≃
      ((p:Fin 4) → {a : PairChoice β // P p a}) × {b : Fin 128 × β // Q b} :=
    { toFun := fun a => (fun p => ⟨a.val.1 p,a.property.1 p⟩,⟨a.val.2,a.property.2⟩)
      invFun := fun a => ⟨(fun p => (a.1 p).val,a.2.val),(fun p => (a.1 p).property),a.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := Fintype.card_congr e
  simpa only [Fintype.card_subtype,Fintype.card_prod,Fintype.card_pi] using he

 theorem sum_prod_replace {δ : Type} [Fintype δ] (p : Fin 4)
    (f : δ → Fin 4 → Nat) (g : Fin 4 → Nat) :
    (∑ d, ∏ i : Fin 4, if i=p then f d i else g i) =
      ∏ i : Fin 4, if i=p then ∑ d,f d i else g i := by
  fin_cases p <;> simp [Fin.prod_univ_succ,←Finset.sum_mul,←Finset.mul_sum]

 theorem forestNearAt_sum {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : ForestHistory β r) :
    (∑ hole : ForestHole, #{a : ForestChoice β | ForestNearAt val h hole a}) =
      forestNear val h := by
  have hleft (k : Fin 4) (side : Fin 2) (t : Fin 6) :
      #{a : ForestChoice β | ForestNearAt val h (.inl (k,side,t)) a} =
      (∏ p : Fin 4, #{a : PairChoice β | if p=k then PairNearAt val (h.1 p) side t a
        else PairCovered val (h.1 p) a}) * coordinateCoverage val h.2 := by
    have hh := forestPredicate_card
      (fun p a => if p=k then PairNearAt val (h.1 p) side t a else PairCovered val (h.1 p) a)
      (fun a => CovAt val a.1 (val a.2) h.2)
    convert hh using 1
    · apply card_filter_congr_any; intro a; rfl
    · apply congrArg₂ Nat.mul
      · apply Finset.prod_congr rfl
        intro p _
        apply card_filter_congr_any; intro a; rfl
      · unfold coordinateCoverage
        apply card_filter_congr_any; intro a; rfl
  have hright (t : Fin 6) :
      #{a : ForestChoice β | ForestNearAt val h (.inr t) a} =
      (∏ p : Fin 4, pairCoverage val (h.1 p)) *
        #{a : Fin 128 × β | CovAtExcept val t a.1 (val a.2) h.2} := by
    have hh := forestPredicate_card (fun p a => PairCovered val (h.1 p) a)
      (fun a => CovAtExcept val t a.1 (val a.2) h.2)
    simp only [pairCovered_card] at hh
    convert hh using 1
    · apply card_filter_congr_any; intro a; rfl
    · apply congrArg₂ Nat.mul
      · rfl
      · apply card_filter_congr_any; intro a; rfl
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  simp_rw [hleft,hright]
  have hcard (p k : Fin 4) (side : Fin 2) (t : Fin 6) :
      #{a : PairChoice β | if p=k then PairNearAt val (h.1 p) side t a else PairCovered val (h.1 p) a} =
        if p=k then #{a : PairChoice β | PairNearAt val (h.1 p) side t a} else pairCoverage val (h.1 p) := by
    by_cases hp : p=k <;> simp only [hp,ite_true,ite_false,pairCovered_card]
  simp_rw [hcard]
  simp only [←Finset.sum_mul,←Finset.mul_sum]
  have hsum (k : Fin 4) :
      (∑ side : Fin 2, ∑ t : Fin 6, ∏ p : Fin 4,
        if p=k then #{a : PairChoice β | PairNearAt val (h.1 p) side t a} else pairCoverage val (h.1 p)) =
      ∏ p : Fin 4, if p=k then pairNear val (h.1 p) else pairCoverage val (h.1 p) := by
    simp_rw [sum_prod_replace]
    simp only [sum_prod_replace,pairNearAt_sum]
  simp_rw [hsum]
  rfl

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ClaudeWCT.Numerics ClaudeWCT.Numerics.N600
open SharedCoverage Thinning
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

def pairCoord (p : Fin 4) (side : Fin 2) : Fin 9 := ⟨2*p.val+side.val,by omega⟩
def holeCoord : ForestHole → Fin 9 × Fin 6
  | .inl v => (pairCoord v.1 v.2.1,v.2.2)
  | .inr t => (8,t)
def coordHole (c : Fin 9 × Fin 6) : ForestHole :=
  if hc : c.1.val<8 then .inl (⟨c.1.val/2,by omega⟩,⟨c.1.val%2,by omega⟩,c.2)
  else .inr c.2

def holeEquiv : ForestHole ≃ Fin 9 × Fin 6 where
  toFun := holeCoord
  invFun := coordHole
  left_inv h := by
    rcases h with ⟨p,s,t⟩|t
    · fin_cases p <;> fin_cases s <;> simp [coordHole,holeCoord,pairCoord]
    · rfl
  right_inv c := by
    rcases c with ⟨k,t⟩
    fin_cases k <;> simp [coordHole,holeCoord,pairCoord]

 theorem pairCoord_inj (p q : Fin 4) (s t : Fin 2) :
    pairCoord p s=pairCoord q t ↔ p=q ∧ s=t := by
  simp only [pairCoord,Fin.ext_iff]
  have hs := s.isLt
  have ht := t.isLt
  omega

 theorem pairCoord_ne_singleton (p : Fin 4) (s : Fin 2) : pairCoord p s ≠ 8 := by
  intro he
  have hh := congrArg Fin.val he
  have hp := p.isLt
  have hs := s.isLt
  change 2*p.val+s.val=8 at hh
  omega

 theorem covAtExcept_splitRanks {β : Type} [Fintype β] {r : Nat}
    (val : β → Fin 6 → Nat) (o : Fin r → Fin 2) (A : Fin r → Fin 64 × β)
    (s : Fin 2) (target : Fin 64 × β) (t : Fin 6) :
    CovAtExcept val t target.1 (val target.2) (splitRanks o A s) ↔
      ∀ u,u≠t → ∃ j,o j=s ∧ (A j).1=target.1 ∧ val target.2 u≤val (A j).2 u := by
  constructor
  · intro h u hu
    obtain ⟨j,hj,hv⟩ := h u hu
    let z := (fiberIndex o s).symm j
    exact ⟨z.val,z.property,by simpa only [splitRanks_apply] using hj,
      by simpa only [splitRanks_apply] using hv⟩
  · intro h u hu
    obtain ⟨j,hj,hc,hv⟩ := h u hu
    refine ⟨fiberIndex o s ⟨j,hj⟩,?_,?_⟩
    · simpa only [splitRanks_apply,Equiv.symm_apply_apply] using hc
    · simpa only [splitRanks_apply,Equiv.symm_apply_apply] using hv

def AlphabetNearAt {β : Type} (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (hole : ForestHole) (a : AlphabetOf β) : Prop :=
  ∀ k : Fin 9, ∀ t : Fin 6, (k,t)≠holeCoord hole → ∃ j,
    rawChild (h j).1 k=rawChild a.1 k ∧ val (a.2 k) t≤val ((h j).2 k) t

 theorem alphabetNear_forest {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (hole : ForestHole) (a : AlphabetOf β)
    (hn : AlphabetNearAt val h hole a) : ForestNearAt val (splitHistory h) hole (choice a) := by
  let P : Fin 9 → Fin 6 → Prop := fun k t => ∃ j,
    rawChild (h j).1 k=rawChild a.1 k ∧ val (a.2 k) t≤val ((h j).2 k) t
  have hfirst (p : Fin 4) :
      CovAt val ((choice a).1 p).2.1.1 (val ((choice a).1 p).2.1.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.1 ((choice a).1 p).1) ↔
      ∀ t,P (pairCoord p 0) t := by
    rw [covAt_splitRanks]
    simp only [P,pairCoord,Fin.val_zero,Nat.add_zero]
    simp only [splitHistory,choice,rawChild_first_eq,and_assoc]
  have hsecond (p : Fin 4) :
      CovAt val ((choice a).1 p).2.2.1 (val ((choice a).1 p).2.2.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.2 ((choice a).1 p).1) ↔
      ∀ t,P (pairCoord p 1) t := by
    rw [covAt_splitRanks]
    simp only [P,pairCoord,Fin.val_one]
    simp only [splitHistory,choice,rawChild_second_eq,and_assoc]
  have hfirstE (p : Fin 4) (t : Fin 6) :
      CovAtExcept val t ((choice a).1 p).2.1.1 (val ((choice a).1 p).2.1.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.1 ((choice a).1 p).1) ↔
      ∀ u,u≠t → P (pairCoord p 0) u := by
    rw [covAtExcept_splitRanks]
    simp only [P,pairCoord,Fin.val_zero,Nat.add_zero]
    simp only [splitHistory,choice,rawChild_first_eq,and_assoc]
  have hsecondE (p : Fin 4) (t : Fin 6) :
      CovAtExcept val t ((choice a).1 p).2.2.1 (val ((choice a).1 p).2.2.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.2 ((choice a).1 p).1) ↔
      ∀ u,u≠t → P (pairCoord p 1) u := by
    rw [covAtExcept_splitRanks]
    simp only [P,pairCoord,Fin.val_one]
    simp only [splitHistory,choice,rawChild_second_eq,and_assoc]
  rcases hole with ⟨p,s,t⟩|t
  · refine ⟨?_,?_⟩
    · intro q
      by_cases hq:q=p
      · subst q
        rw [if_pos rfl]
        fin_cases s
        · refine ⟨(hfirstE p t).mpr ?_,(hsecond p).mpr ?_⟩
          · intro u hu
            exact hn _ _ (fun he => hu (congrArg Prod.snd he))
          · intro u
            apply hn
            intro he
            have hc := (pairCoord_inj p p 1 0).mp (congrArg Prod.fst he)
            exact (by decide : (1:Fin 2)≠0) hc.2
        · refine ⟨(hfirst p).mpr ?_,(hsecondE p t).mpr ?_⟩
          · intro u
            apply hn
            intro he
            have hc := (pairCoord_inj p p 0 1).mp (congrArg Prod.fst he)
            exact (by decide : (0:Fin 2)≠1) hc.2
          · intro u hu
            exact hn _ _ (fun he => hu (congrArg Prod.snd he))
      · rw [if_neg hq]
        refine ⟨(hfirst q).mpr ?_,(hsecond q).mpr ?_⟩ <;> intro u <;> apply hn <;> intro he
        · exact hq ((pairCoord_inj q p 0 s).mp (congrArg Prod.fst he)).1
        · exact hq ((pairCoord_inj q p 1 s).mp (congrArg Prod.fst he)).1
    · intro u
      exact hn 8 u (fun he => pairCoord_ne_singleton p s (congrArg Prod.fst he).symm)
  · refine ⟨?_,?_⟩
    · intro p
      refine ⟨(hfirst p).mpr ?_,(hsecond p).mpr ?_⟩ <;> intro u <;> apply hn <;> intro he
      · exact pairCoord_ne_singleton p 0 (congrArg Prod.fst he)
      · exact pairCoord_ne_singleton p 1 (congrArg Prod.fst he)
    · intro u hu
      exact hn 8 u (fun he => hu (congrArg Prod.snd he))

 theorem alphabetNear_sum_le {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) :
    (∑ hole : ForestHole, #{a : AlphabetOf β | AlphabetNearAt val h hole a}) ≤
      forestNear val (splitHistory h) := by
  rw [←forestNearAt_sum]
  apply Finset.sum_le_sum
  intro hole _
  let e : {a : AlphabetOf β // AlphabetNearAt val h hole a} ≃
      {a : ForestChoice β // AlphabetNearAt val h hole ((choiceEquiv β).symm a)} :=
    (choiceEquiv β).subtypeEquiv (fun a => by rw [(choiceEquiv β).symm_apply_apply a])
  have he := Fintype.card_congr e
  simp only [Fintype.card_subtype] at he
  rw [he]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨_,ha⟩ := Finset.mem_filter.mp ha
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  have hh := alphabetNear_forest val h hole ((choiceEquiv β).symm a) ha
  simpa only [show choice ((choiceEquiv β).symm a)=a from (choiceEquiv β).apply_symm_apply a] using hh

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open SigGolfResearch.Gate6.Moments (finiteAverage)
open SigGolfCandidate.T3.BPORS.History (atIndex)
open ClaudeWCT.Numerics.Thinning
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

def ListAlphabetNear {β : Type} (val : β → Fin 6 → Nat)
    (W : List (AlphabetOf β)) (a : AlphabetOf β) (hole : Fin 9 × Fin 6) : Prop :=
  ∀ k : Fin 9,∀ t : Fin 6,(k,t)≠hole → ∃ e∈W,
    rawChild e.1 k=rawChild a.1 k ∧ val (a.2 k) t≤val (e.2 k) t
noncomputable def nearBucket (W : List Alphabet) : ENNReal :=
  (SharedMoments.priceScaleTotal:ENNReal)/(2^31) *
    finiteAverage (fun a => ∑ hole : Fin 9 × Fin 6,
      if ListAlphabetNear ClaudeWCT.WCT9.wordDigit W a hole then 1 else 0)

def NearCoveredAtP (W : List Proposal) (N : SigGolfCandidate.T3.HashOutput)
    (hole : Fin 9 × Fin 6) : Prop :=
  ∀ k t,(k,t)≠hole → SlotCoveredP W N k t
noncomputable def nearScoreP (W : List Proposal) (N : SigGolfCandidate.T3.HashOutput) : ENNReal :=
  if admissible N=true then ∑ hole : Fin 9 × Fin 6,if NearCoveredAtP W N hole then 1 else 0 else 0
noncomputable def nearPrice (W : List Proposal) : ENNReal :=
  (2:ENNReal)^128 * SigGolfCandidate.T3.BPORS.finiteAverage (nearScoreP W)

 theorem listAlphabetNear_ofFn {β : Type} (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (a : AlphabetOf β) (hole : ForestHole) :
    ListAlphabetNear val (List.ofFn h) a (holeCoord hole) ↔ AlphabetNearAt val h hole a := by
  simp only [ListAlphabetNear,AlphabetNearAt,List.mem_ofFn]
  refine forall_congr' fun k => forall_congr' fun t => forall_congr' fun ht => ?_
  constructor
  · rintro ⟨e,⟨j,rfl⟩,he⟩
    exact ⟨j,he⟩
  · rintro ⟨j,hj⟩
    exact ⟨h j,⟨j,rfl⟩,hj⟩

 theorem nearBucket_ofFn_le {r : Nat} (h : Fin r → Alphabet) :
    nearBucket (List.ofFn h) ≤ feeCoefficient*
      (SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit (splitHistory h):ENNReal) := by
  have hc : Fintype.card Alphabet=SharedMoments.alphabetSize := alphabet_card (Fintype.card_fin 563)
  have hs : (∑ a : Alphabet,∑ hole : Fin 9 × Fin 6,
      if ListAlphabetNear ClaudeWCT.WCT9.wordDigit (List.ofFn h) a hole then (1:ENNReal) else 0) ≤
      (SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit (splitHistory h):ENNReal) := by
    rw [sum_comm]
    conv_lhs => rw [←Equiv.sum_comp holeEquiv]
    change (∑ hole : ForestHole,∑ a : Alphabet,if ListAlphabetNear ClaudeWCT.WCT9.wordDigit (List.ofFn h) a (holeCoord hole) then (1:ENNReal) else 0) ≤ _
    simp_rw [listAlphabetNear_ofFn,←natCast_card_filter]
    rw [←Nat.cast_sum]
    exact_mod_cast alphabetNear_sum_le ClaudeWCT.WCT9.wordDigit h
  unfold nearBucket finiteAverage
  rw [hc,←fee_price_scale]
  calc
    _ ≤ (feeCoefficient*SharedMoments.alphabetSize)*
        ((SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit (splitHistory h):ENNReal)/
          SharedMoments.alphabetSize) := mul_le_mul' le_rfl (ENNReal.div_le_div_right hs _)
    _ = _ := by
      rw [mul_assoc,ENNReal.mul_div_cancel
        (by norm_num [SharedMoments.alphabetSize]) (by simp)]

 theorem nearBucket_bound (W : List Alphabet) :
    nearBucket W ≤ (54:ENNReal)*feeCoefficient*SharedMoments.alphabetSize := by
  unfold nearBucket finiteAverage
  have hsum : (∑ a : Alphabet,∑ hole : Fin 9 × Fin 6,
      if ListAlphabetNear ClaudeWCT.WCT9.wordDigit W a hole then (1:ENNReal) else 0) ≤
      (Fintype.card Alphabet:ENNReal)*54 := by
    calc
      _ ≤ ∑ _ : Alphabet,∑ _ : Fin 9 × Fin 6,(1:ENNReal) := by
        apply sum_le_sum;intro a _;apply sum_le_sum;intro hole _;split_ifs <;> simp
      _ = _ := by simp
  have hc : Fintype.card Alphabet≠0 := Fintype.card_ne_zero
  have he := ENNReal.div_le_div_right hsum (Fintype.card Alphabet:ENNReal)
  rw [mul_div_assoc,ENNReal.mul_div_cancel (by exact_mod_cast hc) (by simp)] at he
  calc
    _ ≤ (SharedMoments.priceScaleTotal:ENNReal)/(2^31)*54 := mul_le_mul' le_rfl he
    _ = _ := by rw [←fee_price_scale];ring

 theorem nearCoveredAtP_bucket (W : List Proposal) (N : SigGolfCandidate.T3.HashOutput)
    (hole : Fin 9 × Fin 6) :
    NearCoveredAtP W N hole ↔ ListAlphabetNear ClaudeWCT.WCT9.wordDigit
      (atIndex (proposal N).1 W) (proposal N).2 hole := by
  unfold NearCoveredAtP SlotCoveredP ListAlphabetNear
  refine forall_congr' fun k => forall_congr' fun t => forall_congr' fun ht => ?_
  constructor
  · rintro ⟨p,hp,h1,h2,h3⟩
    refine ⟨p.2,(WCTEnvelope.mem_atIndex _ _ _).mpr ?_,h2,h3⟩
    rw [←h1];exact hp
  · rintro ⟨a,ha,h2,h3⟩
    exact ⟨((proposal N).1,a),(WCTEnvelope.mem_atIndex _ _ _).mp ha,rfl,h2,h3⟩

 theorem nearPrice_eq_sum (W : List Proposal) : nearPrice W =
    ∑ index : Fin (2^31),nearBucket (atIndex index W) := by
  let g : Proposal → ENNReal := fun p => ∑ hole : Fin 9 × Fin 6,
    if ListAlphabetNear ClaudeWCT.WCT9.wordDigit (atIndex p.1 W) p.2 hole then 1 else 0
  have hs (N : SigGolfCandidate.T3.HashOutput) : nearScoreP W N =
      if admissible N=true then g (proposal N) else 0 := by
    unfold nearScoreP
    congr 1
    apply sum_congr rfl
    intro hole _
    exact if_congr (nearCoveredAtP_bucket W N hole) rfl rfl
  have hc : Fintype.card Alphabet=SharedMoments.alphabetSize := alphabet_card (Fintype.card_fin 563)
  have hsum : (∑ p,g p) = (SharedMoments.alphabetSize:ENNReal)*
      ∑ index : Fin (2^31),finiteAverage (fun a => g (index,a)) := by
    rw [Fintype.sum_prod_type,mul_sum]
    apply sum_congr rfl;intro index _
    unfold finiteAverage
    rw [hc,ENNReal.mul_div_cancel (by norm_num [SharedMoments.alphabetSize]) (by simp)]
  unfold nearPrice SigGolfCandidate.T3.BPORS.finiteAverage
  simp_rw [hs]
  rw [sum_admissible g,hsum,Fintype.card_bitVec]
  unfold nearBucket
  rw [←mul_sum,←price_scale]
  simp only [div_eq_mul_inv]
  ring

 theorem nearBucket_insert (L R : List Alphabet) (b : Alphabet) :
    nearBucket (L++R) ≤ nearBucket (L++b::R) := by
  unfold nearBucket finiteAverage
  apply mul_le_mul' le_rfl
  apply ENNReal.div_le_div_right
  apply sum_le_sum
  intro a _
  apply sum_le_sum
  intro hole _
  by_cases h1 : ListAlphabetNear ClaudeWCT.WCT9.wordDigit (L++R) a hole
  · have h2 : ListAlphabetNear ClaudeWCT.WCT9.wordDigit (L++b::R) a hole := by
      intro k t hne
      obtain ⟨e,he,hc⟩ := h1 k t hne
      refine ⟨e,?_,hc⟩
      rcases List.mem_append.mp he with he|he
      · exact List.mem_append_left _ he
      · exact List.mem_append_right _ (List.mem_cons_of_mem b he)
    simp only [if_pos h1,if_pos h2,le_refl]
  · simp only [if_neg h1]
    exact zero_le

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics ClaudeWCT.Numerics.SharedMoments
open SigGolfCandidate.T3.BPORS.History (atIndex)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem law_nearPrice_coordAverage (T : Nat) :
    Law.lawAvg honestLaw T nearPrice =
      (2^31:ENNReal)*Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T nearBucket := by
  have he : nearPrice = fun W => ∑ i : Fin (2^31),nearBucket (atIndex i W) := funext nearPrice_eq_sum
  rw [he]
  have h := law_marked_sum (α:=Fin (2^31)) honestCoordLaw honestCoordLaw_sum T nearBucket
  simpa only [honestLaw,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] using h

 theorem near_finite_row (r : Nat) (hr : r≤80) :
    (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      feeCoefficient*(SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit h:ENNReal)) =
        feeCoefficient*(forestNearMoment r:ENNReal) := by
  rw [←Finset.mul_sum,←Nat.cast_sum]
  have h := SharedCoverage.forest_near_data ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563)
    WCTEnvelope.w1Table_wordDigit WCTEnvelope.wfTable_wordDigit rows_checked r (by omega)
  exact congrArg (fun n : Nat => feeCoefficient*(n:ENNReal)) h

 theorem law_nearPrice_mean_bound : Law.lawAvg honestLaw (2^32) nearPrice ≤ 378 := by
  rw [law_nearPrice_coordAverage]
  apply coordAverage_history_bound (2^32) 54 1 (by norm_num) (by norm_num)
    nearBucket (fun _ h => feeCoefficient*(SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit h:ENNReal))
    forestNearMoment 378 (fun L b R => nearBucket_insert L R b)
  · intro r _ h
    exact nearBucket_ofFn_le h
  · intro r hr
    simpa only [Nat.cast_one,div_one] using (near_finite_row r hr).le
  · intro W
    simpa only [Nat.cast_one,Nat.cast_ofNat,div_one] using nearBucket_bound W
  · intro g hp ht
    have h := near_bound_of_rows (2^32) _ kappa_mul_rate_le_one (thin_window _ le_rfl)
      1 le_rfl thin_lambda g hp ht
    simpa only [Nat.cast_one,div_one] using h

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleComp.EvalDist ENNReal Finset ClaudeWCT.Numerics
open SigGolfCandidate.T3 SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

 def NearCovered (X : List HashOutput) (N : HashOutput) : Prop :=
  ∃ hole,NearCoveredAtP (X.map proposal) N hole
noncomputable def nearScore (X : List HashOutput) (N : HashOutput) : ENNReal :=
  nearScoreP (X.map proposal) N

 theorem nearCoveredAtP_source (X : List HashOutput) (N : HashOutput) (hole : Fin 9 × Fin 6) :
    NearCoveredAtP (X.map proposal) N hole ↔
      ∀ k t,(k,t)≠hole → ∃ output∈X,ClaudeWCT.WCT9.digestIndex output=ClaudeWCT.WCT9.digestIndex N ∧
        SharedForest.rawChildFromOutput output k=SharedForest.rawChildFromOutput N k ∧
        ClaudeWCT.WCT9.wordDigit (SharedForest.forestRank N k.val) t≤
          ClaudeWCT.WCT9.wordDigit (SharedForest.forestRank output k.val) t := by
  unfold NearCoveredAtP
  exact forall_congr' fun k => forall_congr' fun t => imp_congr_right fun _ => slotCoveredP_source X N k t

 theorem nearCoveredAtP_append (W V : List Proposal) (N : HashOutput) (hole : Fin 9 × Fin 6)
    (h : NearCoveredAtP W N hole) : NearCoveredAtP (W++V) N hole := by
  intro k t hne
  obtain ⟨p,hp,h1,h2,h3⟩ := h k t hne
  exact ⟨p,List.mem_append_left V hp,h1,h2,h3⟩

 theorem nearScore_append_mono (X Y : List HashOutput) (N : HashOutput) :
    nearScore X N≤nearScore (X++Y) N := by
  unfold nearScore nearScoreP
  rw [List.map_append]
  split_ifs with ha
  · apply sum_le_sum
    intro hole _
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (nearCoveredAtP_append _ _ N hole h1) h2
    · exact zero_le_one
    · exact le_rfl
  · exact le_rfl

 theorem one_le_nearScore (X : List HashOutput) (N : HashOutput)
    (ha : admissible N=true) (h : NearCovered X N) : 1≤nearScore X N := by
  obtain ⟨hole,hh⟩ := h
  unfold nearScore nearScoreP
  rw [if_pos ha]
  have hs := Finset.single_le_sum (s:=Finset.univ) (a:=hole)
    (f:=fun h => if NearCoveredAtP (X.map proposal) N h then (1:ENNReal) else 0)
    (fun _ _ => zero_le) (mem_univ hole)
  simpa only [if_pos hh] using hs

 theorem average_nearScore (X : List HashOutput) :
    BPORS.finiteAverage (nearScore X) = nearPrice (X.map proposal)/2^128 := by
  unfold nearPrice nearScore
  rw [mul_comm,ENNReal.mul_div_cancel_right (by positivity) (by finiteness)]

noncomputable def withCoverage {P : Type} [Fintype P] [SampleableType P]
    (S : FtsBankSpec P) (score : List HashOutput → HashOutput → ENNReal)
    (covered : List HashOutput → HashOutput → Prop)
    (hscore : ∀ X N,S.admissible N=true → covered X N → 1 ≤ score X N)
    (hmono : ∀ X Y N,score X N ≤ score (X++Y) N)
    (price : List P → ENNReal)
    (havg : ∀ X,BPORS.finiteAverage (score X)=price (X.map S.proposal)/2^128)
    (rate : ENNReal)
    (hrate : Law.lawAvg S.law S.horizon (fun W => price W-S.specTheta)≤rate) : FtsBankSpec P :=
  { S with
    score := score
    covered := covered
    one_le_score := hscore
    score_append_mono := hmono
    price := price
    average_score := havg
    excessRate := rate
    excess_le := hrate }

noncomputable def nearLawSpec : FtsBankSpec Proposal :=
  withCoverage lawSpec nearScore NearCovered one_le_nearScore nearScore_append_mono
    nearPrice average_nearScore 378
    ((Law.lawAvg_mono honestLaw (2^32) (fun _ => tsub_le_self)).trans law_nearPrice_mean_bound)

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial
open ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.WCTEnvelope
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

theorem wordDigit_coordinate_coeff (K : Nat) (hK : K ∈ [64,128])
    (r : Nat) (hr : r ≤ 20) (c : Nat) :
    (coordinatePoly K r).coeff c ≤
      (univ.filter fun E : Fin r → Fin K × Fin 563 =>
        coordinateCoverage ClaudeWCT.WCT9.wordDigit E=c).card := by
  have hpoly (j : Nat) (hj1 : 1 ≤ j) (hj8 : j ≤ 8) :
      lawPoly coverageLaw 563 j = naturalDataPoly (coverageHData j) :=
    lawPoly_eq_data coverageLaw 563 j
      (coverageLaw_eq_packed ClaudeWCT.WCT9.wordDigit wordsOf_wordDigit
        ClaudeWCT.WCT9.wordDigit_le_four (Fintype.card_fin 563)
        coverageH_packed j hj1 hj8)
      (coverageHData_bounds ⟨j, by omega⟩)
  exact coordinatePoly_coeff_below ClaudeWCT.WCT9.wordDigit coverageLaw
    (coverageLaw_correct ClaudeWCT.WCT9.wordDigit wordsOf_wordDigit
      ClaudeWCT.WCT9.wordDigit_le_four)
    (Fintype.card_fin 563) K hK ⟨r, by omega⟩ coverageLaw_zero_poly
    ((hpoly 1 (by decide) (by decide)).trans coverageH1_poly)
    (fun j hj1 hj8 => hpoly j (by omega) hj8) c

end ClaudeWCT.Numerics.SharedCoverage

namespace ClaudeWCT.Numerics.SharedFees
open Finset
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.WCTEnvelope
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.SharedPathForest
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

theorem wordDigit_rowDots_convolution (r : Nat) (hr : r≤20) :
    rowDots r=convolutionDots r (SharedPathPacked.forest r) := by
  have hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K × Fin 563 =>
        coordinateCoverage ClaudeWCT.WCT9.wordDigit E=j).card :=
    fun K hK u hu j => wordDigit_coordinate_coeff K hK u (by omega) j
  exact rowDots_convolution r hr (actualPoly r)
    (actual_encoding ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r hr hp)
    (actual_coeff_small ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r hr hp)
    ((actual_mass_le ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r hr hp).trans
      (forest_mass_3072 r hr))

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem smallRows_checked (r : Nat) (hr : r≤4) : rowDots r=certifiedPayoff r := by
  interval_cases r
  · exact row_0
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4

theorem wordDigit_rows_of_convolutions
    (hconv : ∀ r, 5≤r → r≤18 →
      convolutionDots r (SharedPathPacked.forest r)=certifiedPayoff r)
    (r : Nat) (hlo : 1≤r) (hhi : r≤18) : rowDots r=certifiedPayoff r := by
  by_cases hs : r≤4
  · exact smallRows_checked r hs
  · exact (wordDigit_rowDots_convolution r (by omega)).trans (hconv r (by omega) hhi)

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Bank.Paired
open ClaudeWCT.Numerics

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

end ClaudeWCT.Bank.Paired
end
-- ==== merged from ClaudeWCT_Numerics_WCTPrice ====
section

/-! Route C for the FTS bank on #938's cap-777 law (RC938; R6 campaign stream RC, sec-rc/RC_SPEC.txt): binned
row bounds, thinned envelope moments, and the route-C excess theorems that replace the winsorized-Chernoff
certificate (removed). Every route-C moment is an insertion-monotone payoff, so #938's binomial thinning
(`Law.coordAverage_thin`: honest at rate `p` ≤ uniform at rate `kappa * p`) applies to all of them; the Scarf
payment of the one-large-bucket term is bounded by its monotone majorant `costOf 5`. The route-C split is
at rows `≤ 80`, so the long-row term is the `poissonCheckQ` tail only. The theorems
`excess_{middle,high,low,large,tiny}_certified` keep their installed names; their fee premise is gone. -/

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

/-- Thinned envelope bound for a coordinate average at a general rate and horizon (the conditional law
uses rate `(2^31-1)⁻¹` and horizon `2^32 - r`): the honest law at rate `p` is bounded by the uniform law at
rate `kappa * p` (cap-777 thinning), whose rows are checked by `poissonCheckQ` with `u = 13283369e-8` and
`λ = 2018833e-6`. -/
theorem rc_envelope_thin (rate : ENNReal) (hrate : kappa * rate ≤ 1) (T : ℕ)
    (hlam : (T : ENNReal) * (kappa * rate) * 1 ≤ ((2018833 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal))
    (hu : (1 - kappa * rate) ^ (T - 80) ≤ ((13283369 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal))
    (G : ℕ) (hG0 : 0 < G) (row : ℕ → ℕ) (f : List Alphabet → ENNReal)
    (hmono : ∀ L b R, f (L ++ R) ≤ f (L ++ b :: R))
    (g : (r : ℕ) → ForestHistory (Fin 563) r → ENNReal)
    (hfg : ∀ r ≤ 80, ∀ h : Fin r → Alphabet, f (List.ofFn h) ≤ g r (splitHistory h))
    (hfees : ∀ r ≤ 80, (∑ h, g r h) ≤ feeCoefficient / (feeScale : ENNReal) * (row r : ENNReal))
    (hpoint : ∀ W, f W ≤ (G : ENNReal) * feeCoefficient * alphabetSize / (feeScale : ENNReal))
    (Mn Md : ℕ) (hMd : 0 < Md)
    (hcheck : N600.poissonCheckQ fieldSize 13283369 100000000 2018833 1000000 (fun r => 16 ^ r * row r)
      (G * alphabetSize) (G * priceScaleTotal) feeScale Mn Md 80 = true) :
    (2 ^ 31 : ENNReal) * Law.coordAverage rate honestCoordLaw T f ≤ (Mn : ENNReal) / Md := by
  have hS : 0 < feeScale := by norm_num [feeScale]
  refine (mul_le_mul' le_rfl (Law.coordAverage_thin rate kappa honestCoordLaw uniformCoordLaw
    honestCoordLaw_sum uniformCoordLaw_sum honestCoordLaw_density kappa_one_le hrate T f hmono)).trans ?_
  let C : ENNReal := (G : ENNReal) * feeCoefficient * alphabetSize / (feeScale : ENNReal)
  have hC0 : C ≠ 0 := by
    have hMc : (G : ENNReal) ≠ 0 := by exact_mod_cast hG0.ne'
    have hfc : feeCoefficient ≠ 0 := by norm_num [feeCoefficient]
    have hDc : (alphabetSize : ENNReal) ≠ 0 := by norm_num [alphabetSize]
    exact ENNReal.div_ne_zero.mpr ⟨mul_ne_zero (mul_ne_zero hMc hfc) hDc, ENNReal.natCast_ne_top _⟩
  have hCt : C ≠ ⊤ := by dsimp [C, feeCoefficient]; finiteness
  let v : ℕ → ENNReal := fun r => Law.lawAvg uniformCoordLaw r (fun W => f W / C)
  have hv1 : ∀ r ≤ 80, v r ≤ 1 ^ r * (((16 ^ r * row r : ℕ) : ENNReal) /
      ((G * alphabetSize * fieldSize ^ (9 * r) : ℕ) : ENNReal)) := by
    intro r hr
    have h := uniform_normalized_history_row r G feeScale (row r) hG0 hS f (g r) (hfg r hr) (hfees r hr)
    exact h.trans_eq (mul_div_assoc _ _ _)
  have hv2 : ∀ r, 80 < r → v r ≤ 1 := fun r _ => uniform_normalized_le_one r f C hC0 hCt hpoint
  have hkey := N600.poissonCheckQ_sound_tilt hcheck (by norm_num [fieldSize]) (by norm_num) (by norm_num)
    (Nat.mul_pos hG0 (by norm_num [alphabetSize])) (by norm_num [feeScale]) hMd hrate 1 le_rfl hlam hu v
    hv1 hv2
  calc (2 ^ 31 : ENNReal) * Law.coordAverage (kappa * rate) uniformCoordLaw T f =
      ((2 ^ 31 : ENNReal) * C) * Law.coordAverage (kappa * rate) uniformCoordLaw T (fun W => f W / C) :=
        (coordAverage_scaled uniformCoordLaw T f C (2 ^ 31) (kappa * rate) hC0 hCt).symm
    _ = ((G * priceScaleTotal : ℕ) : ENNReal) / (feeScale : ENNReal) *
        SphincsSecurity.Concrete.binomialAverage (kappa * rate) T v := by
      rw [show (2 ^ 31 : ENNReal) * C = ((G * priceScaleTotal : ℕ) : ENNReal) / (feeScale : ENNReal) from
        normalizer_scale G feeScale]
      rfl
    _ ≤ (Mn : ENNReal) / Md := hkey

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

/-- Route-C costs of the bucket price are insertion-monotone. -/
theorem rc_cost_insert (k : ℕ) (hP : ParFacts rcPar) (L R : List Alphabet) (b : Alphabet) :
    ENNReal.ofReal (costOf k rcPar (priceBucket (L ++ R)).toReal) ≤
      ENNReal.ofReal (costOf k rcPar (priceBucket (L ++ b :: R)).toReal) :=
  ENNReal.ofReal_le_ofReal (costOf_mono k rcPar hP ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (priceBucket_ne_top _) (priceBucket_insert L R b)))

/-- A route-C moment of kind `k` (0 mean, 1 second moment, 2 count, 3 over, 4 clipped mgf, 5 Scarf). -/
theorem rc_kind_all (k : ℕ) (runs : List (ℕ × ℕ × ℕ)) (G pack : ℕ) (hpack : packRuns runs = pack)
    (hP : ParFacts rcPar) (hidx : (runEntries runs).map Prod.fst = List.range 7210)
    (hruns : runsOk k runs G = true) (hglob : globOk k rcPar G = true) (hG : G ≤ 2 ^ 900) (hG0 : 0 < G)
    (rate : ENNReal) (hrate : kappa * rate ≤ 1) (T : ℕ)
    (hlam : (T : ENNReal) * (kappa * rate) * 1 ≤ ((2018833 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal))
    (hu : (1 - kappa * rate) ^ (T - 80) ≤ ((13283369 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal))
    (Mn Md : ℕ) (hMd : 0 < Md)
    (hcheck : N600.poissonCheckQ fieldSize 13283369 100000000 2018833 1000000 (fun r => 16 ^ r * rowAll pack G r)
      (G * alphabetSize) (G * pst) feeScale Mn Md 80 = true) :
    (2 ^ 31 : ENNReal) * Law.coordAverage rate honestCoordLaw T
      (fun L => ENNReal.ofReal (costOf k rcPar (priceBucket L).toReal)) ≤ (Mn : ENNReal) / Md := by
  apply rc_envelope_thin rate hrate T hlam hu G hG0 (rowAll pack G) _ (fun L b R => rc_cost_insert k hP L R b)
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

/-- The long-row first moment (bucket price on rows above 80: the `poissonCheckQ` tail term). -/
theorem rc_long (rate : ENNReal) (hrate : kappa * rate ≤ 1) (T : ℕ)
    (hlam : (T : ENNReal) * (kappa * rate) * 1 ≤ ((2018833 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal))
    (hu : (1 - kappa * rate) ^ (T - 80) ≤ ((13283369 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal))
    (Mn Md : ℕ) (hMd : 0 < Md)
    (hcheck : N600.poissonCheckQ fieldSize 13283369 100000000 2018833 1000000 (fun r => 16 ^ r * rowLong r)
      (feeScale * alphabetSize) (feeScale * pst) feeScale Mn Md 80 = true) :
    (2 ^ 31 : ENNReal) * Law.coordAverage rate honestCoordLaw T
      (fun L => if 80 < L.length then priceBucket L else 0) ≤ (Mn : ENNReal) / Md := by
  have hS : (0 : ENNReal) < feeScale := by norm_num [feeScale]
  have hSt : (feeScale : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  apply rc_envelope_thin rate hrate T hlam hu feeScale (by norm_num [feeScale]) rowLong _ _
    (fun r h => if 80 < r then feeCoefficient * (forestCoverage ClaudeWCT.WCT9.wordDigit h : ENNReal) else 0)
    _ _ _ Mn Md hMd (by rw [rc_pst]; exact hcheck)
  · intro L b R
    by_cases h : 80 < (L ++ R).length
    · have h' : 80 < (L ++ b :: R).length := by simp at h ⊢; omega
      rw [if_pos h, if_pos h']
      exact priceBucket_insert L R b
    · rw [if_neg h]; exact zero_le
  · intro r _ h
    simp only [List.length_ofFn, priceBucket_ofFn]
    exact le_rfl
  · intro r hr
    unfold rowLong
    split_ifs with h80
    · omega
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

/-! ### Thinned envelope rates (RC_SPEC E3 / L4): unconditional and one-index conditional laws -/

theorem rc_rate_uncond : kappa * (2 ^ 31 : ENNReal)⁻¹ ≤ 1 := kappa_mul_rate_le_one

theorem rc_lam_uncond : ((2 ^ 32 : ℕ) : ENNReal) * (kappa * (2 ^ 31 : ENNReal)⁻¹) * 1 ≤
    ((2018833 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal) := thin_lambda

theorem rc_u_uncond : (1 - kappa * (2 ^ 31 : ENNReal)⁻¹) ^ (2 ^ 32 - 80) ≤
    ((13283369 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal) := thin_window (2 ^ 32) le_rfl

theorem rc_rate_cond : kappa * ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹ ≤ 1 := by
  rw [kappa_exact]
  have hc : (ClaudeWCT.Numerics.SharedFtsCount.count : ENNReal) ≠ 0 := by
    norm_num [ClaudeWCT.Numerics.SharedFtsCount.count]
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hc)
    (by simp)) (by finiteness)).mp
  norm_num [ClaudeWCT.Numerics.SharedFtsCount.total, ClaudeWCT.Numerics.SharedFtsCount.count,
    ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]

theorem rc_lam_cond (r : ℕ) (hr : 1 ≤ r) :
    ((2 ^ 32 - r : ℕ) : ENNReal) * (kappa * ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹) * 1 ≤
      ((2018833 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal) := by
  have hle : ((2 ^ 32 - r : ℕ) : ENNReal) ≤ ((2 ^ 32 - 1 : ℕ) : ENNReal) := by
    exact_mod_cast Nat.sub_le_sub_left hr _
  refine le_trans (mul_le_mul' (mul_le_mul' hle le_rfl) le_rfl) ?_
  rw [mul_one, kappa_exact]
  have hc : (ClaudeWCT.Numerics.SharedFtsCount.count : ENNReal) ≠ 0 := by
    norm_num [ClaudeWCT.Numerics.SharedFtsCount.count]
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ENNReal.mul_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hc) (by simp))) (by finiteness)).mp
  norm_num [ClaudeWCT.Numerics.SharedFtsCount.total, ClaudeWCT.Numerics.SharedFtsCount.count,
    ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]

/-- Conditional thinned window: `(1 - kappa/(2^31-1))^(2^32 - r - 80) ≤ 13283369e-8` for `r ≤ 80`
(tangent line of `exp` at 2, as `thin_window`). -/
theorem rc_u_cond (r : ℕ) (hr : r ≤ 80) :
    (1 - kappa * ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹) ^ (2 ^ 32 - r - 80) ≤
      ((13283369 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal) := by
  have hq1 := rc_rate_cond
  have hmono : (1 - kappa * ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹) ^ (2 ^ 32 - r - 80) ≤
      (1 - kappa * ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹) ^ (2 ^ 32 - 160) :=
    pow_le_pow_right_of_le_one' tsub_le_self (by omega)
  refine hmono.trans ?_
  have hfin : (1 - kappa * ((2 ^ 31 - 1 : ℕ) : ENNReal)⁻¹) ^ (2 ^ 32 - 160) ≠ ⊤ :=
    ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  apply (ENNReal.toReal_le_toReal hfin (by finiteness)).mp
  rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hq1 ENNReal.one_ne_top, ENNReal.toReal_mul,
    kappa_toReal, ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  simp only [ENNReal.toReal_one]
  set k : ℝ := (ClaudeWCT.Numerics.SharedFtsCount.total : ℝ) / ClaudeWCT.Numerics.SharedFtsCount.count with hk
  have hkv : k = 52416169542617085727767971710947931910569984 / 51927206731424509281114869451843031004872704 := by
    rw [hk]; norm_num [ClaudeWCT.Numerics.SharedFtsCount.total, ClaudeWCT.Numerics.SharedFtsCount.count]
  set n := 2 ^ 32 - 160 with hn
  have hn0 : ((2 ^ 32 - 160 : ℕ) : ℝ) = (2 : ℝ) ^ 32 - 160 := by norm_num
  have hq : (((2 ^ 31 - 1 : ℕ) : ℝ))⁻¹ = ((2 : ℝ) ^ 31 - 1)⁻¹ := by norm_num
  rw [hq]
  have h0 : (0 : ℝ) ≤ 1 - k * ((2 : ℝ) ^ 31 - 1)⁻¹ := by rw [hkv]; norm_num
  have hp : (1 - k * ((2 : ℝ) ^ 31 - 1)⁻¹ : ℝ) ≤ Real.exp (-(k * ((2 : ℝ) ^ 31 - 1)⁻¹)) :=
    Real.one_sub_le_exp_neg _
  have hpow : (1 - k * ((2 : ℝ) ^ 31 - 1)⁻¹ : ℝ) ^ n ≤ Real.exp (-(n * (k * ((2 : ℝ) ^ 31 - 1)⁻¹))) := by
    calc (1 - k * ((2 : ℝ) ^ 31 - 1)⁻¹ : ℝ) ^ n ≤ Real.exp (-(k * ((2 : ℝ) ^ 31 - 1)⁻¹)) ^ n :=
          pow_le_pow_left₀ h0 hp n
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  set a0 : ℝ := ((2 : ℝ) ^ 32 - 160) * (k * ((2 : ℝ) ^ 31 - 1)⁻¹) with ha0
  have ha : a0 ≤ n * (k * ((2 : ℝ) ^ 31 - 1)⁻¹) := by rw [hn, hn0]
  have hlow : (100000000 : ℝ) / 13283369 ≤ (2.7182818283 : ℝ) ^ 2 * (a0 - 1) := by
    rw [ha0, hkv]; norm_num
  have hexp : (100000000 : ℝ) / 13283369 ≤ Real.exp (n * (k * ((2 : ℝ) ^ 31 - 1)⁻¹)) :=
    hlow.trans ((ClaudeWCT.Numerics.PoissonReflect.exp_lower a0).trans (Real.exp_le_exp.mpr ha))
  refine hpow.trans ?_
  rw [Real.exp_neg]
  have hpos : (0 : ℝ) < 100000000 / 13283369 := by norm_num
  calc (Real.exp (n * (k * ((2 : ℝ) ^ 31 - 1)⁻¹)))⁻¹ ≤ ((100000000 : ℝ) / 13283369)⁻¹ :=
        inv_anti₀ hpos hexp
    _ = ((13283369 : ℕ) : ℝ) / ((100000000 : ℕ) : ℝ) := by norm_num

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

theorem forestMoment_zero : forestMoment 0 = 0 := by decide +kernel

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

/-- The Scarf payment of a short-row large bucket is below its monotone majorant `costOf 5`. -/
theorem rc_scarf_major (L : List Alphabet) :
    (if L.length ≤ 80 ∧ ENNReal.ofReal rcPar.c0 < priceBucket L then
      ENNReal.ofReal (RouteC.scarf ((rcPar.θ : ℝ) - (priceBucket L).toReal) rcPar.m rcPar.vv) else 0) ≤
    ENNReal.ofReal (costOf 5 rcPar (priceBucket L).toReal) := by
  have hc : (0 : ℝ) ≤ rcPar.c0 := (parFacts_of_ok rcPar par_ok).c0.le
  have hiff : ENNReal.ofReal rcPar.c0 < priceBucket L ↔ (rcPar.c0 : ℝ) < (priceBucket L).toReal :=
    ENNReal.ofReal_lt_iff_lt_toReal hc (priceBucket_ne_top L)
  show _ ≤ ENNReal.ofReal (if (rcPar.c0 : ℝ) < (priceBucket L).toReal then
    RouteC.scarf (rcPar.θ - (priceBucket L).toReal) rcPar.m rcPar.vv else 0)
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (hiff.mp h1.2) h2
  · exact zero_le
  · exact zero_le

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

theorem rc_prefactor (X : ENNReal) :
    ((Fintype.card (Fin (2 ^ 31)) - 1 : ℕ) : ENNReal) * X ≤ (2 ^ 31 : ENNReal) * X := by
  rw [rc_cardm1]
  exact mul_le_mul' (by norm_num) le_rfl

/-- Route C bank excess at the middle threshold (thinned cap-777 envelope, `rcPar`). -/
theorem rc_excess_middle :
    Law.lawAvg honestLaw (2 ^ 32) (fun W => price W - ENNReal.ofReal ((99847 : ℝ) / 50000 - 1 / 1024)) ≤
      ENNReal.ofReal ((1153 : ℝ) / 1000000) := by
  have hP := parFacts_of_ok rcPar par_ok
  have he : (fun W : List Proposal => price W - ENNReal.ofReal ((99847 : ℝ) / 50000 - 1 / 1024)) =
      fun W => (∑ i : Fin (2 ^ 31), priceBucket (atIndex i W)) - ENNReal.ofReal (rcPar.θ : ℝ) := by
    funext W; rw [price_eq_sum, rc_θ]
  rw [he]
  have hcard : 1 < Fintype.card (Fin (2 ^ 31)) := by rw [Fintype.card_fin]; norm_num
  have hθ0 : (0 : ℝ) ≤ (rcPar.θ : ℝ) := by rw [rc_θ]; norm_num
  have ha0 : (0 : ℝ) < (rcPar.a : ℝ) := by rw [rc_a]; norm_num
  have hnil : priceBucket [] ≤ ENNReal.ofReal (rcPar.c0 : ℝ) := by rw [priceBucket_nil]; exact zero_le
  -- the seven envelope moments
  have hmgf : (∑ _i : Fin (2 ^ 31), Law.coordAverage (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹ honestCoordLaw
      (2 ^ 32) (fun L => ENNReal.ofReal (Real.exp (rcPar.a * (min (priceBucket L)
        (ENNReal.ofReal rcPar.c0)).toReal)) - 1)) ≤ ENNReal.ofReal ((mgfN : ℝ) / mgfD) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, rc_card]
    simp_rw [rc_conv_mgf]
    rw [rc_frac _ _ (by norm_num [mgfD])]
    exact rc_kind_all 4 runs4 glob4 Pack4 pack4_eq hP entries4 runs4_ok glob4_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ rc_rate_uncond (2 ^ 32) rc_lam_uncond rc_u_uncond _ _
      (by norm_num [mgfD]) env_mgf
  have hmean : ∀ r, 1 ≤ r → r ≤ 80 →
      ((Fintype.card (Fin (2 ^ 31)) - 1 : ℕ) : ENNReal) * Law.coordAverage
        ((Fintype.card (Fin (2 ^ 31)) - 1 : ℕ) : ENNReal)⁻¹ honestCoordLaw (2 ^ 32 - r)
        (fun L => min (priceBucket L) (ENNReal.ofReal rcPar.c0)) ≤ ENNReal.ofReal (rcPar.m : ℝ) := by
    intro r h1 h80
    simp_rw [rc_conv_mean]
    refine (rc_prefactor _).trans ?_
    rw [rc_m, rc_frac _ _ (by norm_num [meanD])]
    rw [rc_cardm1]
    exact rc_kind_all 0 runs0 glob0 Pack0 pack0_eq hP entries0 runs0_ok glob0_ok (by decide +kernel)
      (by decide +kernel) _ rc_rate_cond (2 ^ 32 - r) (rc_lam_cond r h1) (rc_u_cond r h80) _ _
      (by norm_num [meanD]) env_mean
  have hsecond : ∀ r, 1 ≤ r → r ≤ 80 →
      ((Fintype.card (Fin (2 ^ 31)) - 1 : ℕ) : ENNReal) * Law.coordAverage
        ((Fintype.card (Fin (2 ^ 31)) - 1 : ℕ) : ENNReal)⁻¹ honestCoordLaw (2 ^ 32 - r)
        (fun L => min (priceBucket L) (ENNReal.ofReal rcPar.c0) ^ 2) ≤ ENNReal.ofReal (rcPar.vv : ℝ) := by
    intro r h1 h80
    simp_rw [rc_conv_sec]
    refine (rc_prefactor _).trans ?_
    rw [rc_vv, rc_frac _ _ (by norm_num [secD])]
    rw [rc_cardm1]
    exact rc_kind_all 1 runs1 glob1 Pack1 pack1_eq hP entries1 runs1_ok glob1_ok (by decide +kernel)
      (by decide +kernel) _ rc_rate_cond (2 ^ 32 - r) (rc_lam_cond r h1) (rc_u_cond r h80) _ _
      (by norm_num [secD]) env_sec
  have hK1 : (Fintype.card (Fin (2 ^ 31)) : ENNReal) * Law.coordAverage (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹
      honestCoordLaw (2 ^ 32) (fun L => if L.length ≤ 80 ∧ ENNReal.ofReal rcPar.c0 < priceBucket L then
        ENNReal.ofReal (RouteC.scarf ((rcPar.θ : ℝ) - (priceBucket L).toReal) rcPar.m rcPar.vv) else 0) ≤
      ENNReal.ofReal ((scarfN : ℝ) / scarfD) := by
    rw [rc_card, rc_frac _ _ (by norm_num [scarfD])]
    refine (mul_le_mul' le_rfl (Law.coordAverage_mono _ _ _ rc_scarf_major)).trans ?_
    exact rc_kind_all 5 runs5 glob5 Pack5 pack5_eq hP entries5 runs5_ok glob5_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ rc_rate_uncond (2 ^ 32) rc_lam_uncond rc_u_uncond _ _
      (by norm_num [scarfD]) env_scarf
  have hover : (Fintype.card (Fin (2 ^ 31)) : ENNReal) * Law.coordAverage (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹
      honestCoordLaw (2 ^ 32) (fun L => priceBucket L - ENNReal.ofReal rcPar.c0) ≤
      ENNReal.ofReal ((overN : ℝ) / overD) := by
    simp_rw [rc_conv_over]
    rw [rc_card, rc_frac _ _ (by norm_num [overD])]
    exact rc_kind_all 3 runs3 glob3 Pack3 pack3_eq hP entries3 runs3_ok glob3_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ rc_rate_uncond (2 ^ 32) rc_lam_uncond rc_u_uncond _ _
      (by norm_num [overD]) env_over
  have hcount : (Fintype.card (Fin (2 ^ 31)) : ENNReal) * Law.coordAverage (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹
      honestCoordLaw (2 ^ 32) (fun L => if ENNReal.ofReal rcPar.c0 < priceBucket L then 1 else 0) ≤
      ENNReal.ofReal ((countN : ℝ) / countD) := by
    simp_rw [rc_conv_count]
    rw [rc_card, rc_frac _ _ (by norm_num [countD])]
    exact rc_kind_all 2 runs2 glob2 Pack2 pack2_eq hP entries2 runs2_ok glob2_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ rc_rate_uncond (2 ^ 32) rc_lam_uncond rc_u_uncond _ _
      (by norm_num [countD]) env_count
  have htail : (Fintype.card (Fin (2 ^ 31)) : ENNReal) * Law.coordAverage (Fintype.card (Fin (2 ^ 31)) : ENNReal)⁻¹
      honestCoordLaw (2 ^ 32) (fun L => if 80 < L.length then priceBucket L else 0) ≤
      ENNReal.ofReal ((longN : ℝ) / longD) := by
    rw [rc_card, rc_frac _ _ (by norm_num [longD])]
    exact rc_long (2 ^ 31 : ENNReal)⁻¹ rc_rate_uncond (2 ^ 32) rc_lam_uncond rc_u_uncond _ _
      (by norm_num [longD]) env_long
  have key := RouteC.excess_route_c honestCoordLaw honestCoordLaw_sum hcard (2 ^ 32) 80 priceBucket
    priceBucket_ne_top (fun L b R => priceBucket_insert L R b) (rcPar.c0 : ℝ) (rcPar.θ : ℝ) (rcPar.a : ℝ)
    ((mgfN : ℝ) / mgfD) (rcPar.m : ℝ) (rcPar.vv : ℝ) ((scarfN : ℝ) / scarfD)
    ((overN : ℝ) / overD) ((countN : ℝ) / countD) ((longN : ℝ) / longD)
    hθ0 ha0 (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hP.m hP.vv
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    hnil hmgf hmean hsecond hK1 hover hcount htail
  exact key.trans (ENNReal.ofReal_le_ofReal rc_total_mid)

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open ClaudeWCT.Numerics.RouteCFees ClaudeWCT.Numerics.RouteCData ClaudeWCT.Numerics.RouteCRows
open ClaudeWCT.Numerics.RouteCBank
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The low threshold through the clipped Chernoff bound plus the excess over the clip. -/
theorem rc_excess_low :
    Law.lawAvg honestLaw (2 ^ 32) (fun W => price W - ENNReal.ofReal ((1 : ℝ) - 1 / 1024)) ≤
      ENNReal.ofReal ((49 : ℝ) / 100) := by
  have hP := parFacts_of_ok rcPar par_ok
  apply price_excess_of_bucket_bounds (2 ^ 32) (ENNReal.ofReal rcPar.c0) ENNReal.ofReal_ne_top
    (1 - 1 / 1024) (rcPar.a : ℝ) ((mgfN : ℝ) / mgfD) ((overN : ℝ) / overD) (49 / 100)
    (by norm_num) (by rw [rc_a]; norm_num) (by positivity) (by positivity)
  · simp_rw [rc_conv_mgf]
    rw [rc_frac _ _ (by norm_num [mgfD])]
    exact rc_kind_all 4 runs4 glob4 Pack4 pack4_eq hP entries4 runs4_ok glob4_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ rc_rate_uncond (2 ^ 32) rc_lam_uncond rc_u_uncond _ _
      (by norm_num [mgfD]) env_mgf
  · simp_rw [rc_conv_over]
    rw [rc_frac _ _ (by norm_num [overD])]
    exact rc_kind_all 3 runs3 glob3 Pack3 pack3_eq hP entries3 runs3_ok glob3_ok (by decide +kernel)
      (by decide +kernel) (2 ^ 31 : ENNReal)⁻¹ rc_rate_uncond (2 ^ 32) rc_lam_uncond rc_u_uncond _ _
      (by norm_num [overD]) env_over
  · exact rc_total_low

/-! Installed names (now proved by route C). -/

theorem excess_middle_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((99847:ℝ)/50000-1/1024)) ≤
        ENNReal.ofReal ((1153 : ℝ) / 1000000) := rc_excess_middle

theorem excess_high_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((2:ℝ)-6/2500-1/1024)) ≤
        ENNReal.ofReal ((2979:ℝ)/2500000) :=
  (Law.lawAvg_mono _ _ (fun W => tsub_le_tsub_left
    (ENNReal.ofReal_le_ofReal (by norm_num : (99847 : ℝ) / 50000 - 1 / 1024 ≤ 2 - 6 / 2500 - 1 / 1024)) _)).trans
    (rc_excess_middle.trans (ENNReal.ofReal_le_ofReal (by norm_num)))

theorem excess_low_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((1:ℝ)-1/1024)) ≤
        ENNReal.ofReal ((49:ℝ)/100) := rc_excess_low

/-- Large queries: the cap-777 envelope `(993/1000) y` from the high and low endpoints (as in #938). -/
theorem excess_large_certified (y : ℝ)
    (hy0 : 3/2500 ≤ y) (hy1 : y ≤ 1/2) :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal (2-2*y-1/1024)) ≤
        ENNReal.ofReal ((993/1000)*y) := by
  let t : ℝ := (y-3/2500)/(1/2-3/2500)
  have ht0 : 0≤t := div_nonneg (sub_nonneg.mpr hy0) (by norm_num)
  have ht1 : t≤1 := (div_le_one (by norm_num : (0:ℝ)<1/2-3/2500)).2 (by linarith)
  have h := price_excess_affine (2^32) (2-6/2500-1/1024) (1-1/1024)
    (2979/2500000) (49/100) t (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ht0 ht1 excess_high_certified excess_low_certified
  have harg : (1-t)*(2-6/2500-1/1024)+t*(1-1/1024) = 2-2*y-1/1024 := by
    dsimp [t]; ring
  rw [harg] at h
  have hgap : (993/1000)*y-((1-t)*(2979/2500000)+t*(49/100)) = t*(13/2000) := by
    dsimp [t]; ring
  have hval : (1-t)*(2979/2500000)+t*(49/100) ≤ (993/1000)*y := by nlinarith
  exact h.trans (ENNReal.ofReal_le_ofReal hval)

/-- Tiny queries: affine interpolation between the middle and low endpoints. -/
theorem excess_tiny_certified :
    Law.lawAvg honestLaw (2^32)
      (fun W=>price W-ENNReal.ofReal ((249:ℝ)/125-1/1024)) ≤
        ENNReal.ofReal ((18:ℝ)/5000) := by
  have h:=price_excess_affine (2^32) (99847/50000-1/1024) (1-1/1024)
    ((1153 : ℝ) / 1000000) (49/100) (247/49847) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    excess_middle_certified excess_low_certified
  have ht:(1-(247:ℝ)/49847)*(99847/50000-1/1024)+(247/49847)*(1-1/1024)=249/125-1/1024:=by norm_num
  rw[ht] at h
  exact h.trans (ENNReal.ofReal_le_ofReal (by norm_num))

end ClaudeWCT.Bank.Paired


namespace ClaudeWCT.Numerics.WCTPrice
open Finset ENNReal
open ClaudeWCT.Numerics.Law (lawAvg marked)
open SphincsSecurity.Concrete (uniformWordAverage)
open ClaudeWCT.Bank.WCT (WProposal price ExcessBound)
open ClaudeWCT.WCT9 (wordDigit Coord Child Rank)
open ClaudeWCT.Numerics.WCTEnvelope
theorem theta_eq : SigGolfCandidate.T3.Security.CaseC.theta = 63 / 64 := rfl
theorem price_fun_eq : price = N600.priceN wordDigit := funext price_eq
section Window
variable {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32)
include hT1 hT2
theorem wct_price_mean_law {law : (Coord → Child × Rank) → ENNReal} {κ : ENNReal} (hlaw : N600.LawOK law κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) law) T price ≤ 675 / 1000 := by
  rw [price_fun_eq]
  exact N600.law_price_mean_le wordDigit hT1 hT2 card_rank card_child w1Table_wordDigit hlaw
theorem wct_price_excess_law {law : (Coord → Child × Rank) → ENNReal} {κ : ENNReal} (hlaw : N600.LawOK law κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) law) T (fun W : List WProposal => price W - 1023 / 1024) ≤
      247 / 100000 := by
  rw [price_fun_eq]
  exact N600.law_price_excess_le wordDigit hT1 hT2 card_rank card_child w1Table_wordDigit w2Table_wordDigit hlaw
theorem wct_near_law {law : (Coord → Child × Rank) → ENNReal} {κ : ENNReal} (hlaw : N600.LawOK law κ) :
    lawAvg (marked (α := Fin (2 ^ 31)) law) T (N600.nearPriceN (C := Child) wordDigit) ≤ 300 - 1 / 16 :=
  (N600.law_nearPrice_le wordDigit hT1 hT2 card_rank card_child w1Table_wordDigit wfTable_wordDigit hlaw).trans
    N600.near_le_sub
theorem wct_price_mean_bound_window : uniformWordAverage T price ≤ 675 / 1000 := by
  rw [price_fun_eq]
  exact N600.uniform_price_mean_le wordDigit hT1 hT2 card_rank card_child w1Table_wordDigit
theorem wct_price_mean_bound_window' : uniformWordAverage T price ≤ 94 / 100 := by
  refine (wct_price_mean_bound_window hT1 hT2).trans ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]
theorem wct_excessBound_window : ExcessBound T (247 / 100000) :=
  ClaudeWCT.Bank.WCT.excessBound_of_honest (wct_price_excess_law hT1 hT2 N600Cap.lawOK_honest)
end Window
abbrev wctHorizon : ℕ := 2 ^ 32
theorem wctHorizon_eq : wctHorizon = 2 ^ 32 := rfl
theorem wctHorizon_ge : 2 ^ 32 ≤ wctHorizon := wctHorizon_eq.ge
theorem wctHorizon_le : wctHorizon ≤ 2 ^ 32 := wctHorizon_eq.le
theorem wct_excessBound_forall :
    ∀ T : ℕ, 2 ^ 32 ≤ T → T ≤ 2 ^ 32 → ExcessBound T (247 / 100000) :=
  fun _ h1 h2 => wct_excessBound_window h1 h2
theorem wct_excessBound : ExcessBound wctHorizon (247 / 100000) :=
  wct_excessBound_window wctHorizon_ge wctHorizon_le
theorem wct_excessBound_2_32 : ExcessBound (2 ^ 32) (247 / 100000) :=
  wct_excessBound_window le_rfl (by norm_num)
theorem wct_excess_honest_2_32 :
    lawAvg (marked (α := Fin (2 ^ 31)) N600Cap.honestLaw) (2 ^ 32)
      (fun W : List WProposal => price W - 1023 / 1024) ≤ 247 / 100000 :=
  wct_price_excess_law le_rfl (by norm_num) N600Cap.lawOK_honest
theorem wct_excess_honest :
    lawAvg (marked (α := Fin (2 ^ 31)) N600Cap.honestLaw) wctHorizon
      (fun W : List WProposal => price W - 1023 / 1024) ≤ 247 / 100000 :=
  wct_price_excess_law wctHorizon_ge wctHorizon_le N600Cap.lawOK_honest
theorem wct_near_honest_2_32 :
    lawAvg (marked (α := Fin (2 ^ 31)) N600Cap.honestLaw) (2 ^ 32) (N600.nearPriceN (C := Child) wordDigit) ≤
      300 - 1 / 16 :=
  wct_near_law le_rfl (by norm_num) N600Cap.lawOK_honest
theorem wct_near_honest :
    lawAvg (marked (α := Fin (2 ^ 31)) N600Cap.honestLaw) wctHorizon (N600.nearPriceN (C := Child) wordDigit) ≤
      300 - 1 / 16 :=
  wct_near_law wctHorizon_ge wctHorizon_le N600Cap.lawOK_honest
end ClaudeWCT.Numerics.WCTPrice
end
-- ==== merged from ClaudeWCT_W9_T3_Proofs ====
section

namespace ClaudeWCT.W9.T3.Security
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)
abbrev Requests := Request →ₒ Option Signature
def signingOracle : QueryImpl Requests (WriterT (QueryLog Requests) M) :=
  QueryImpl.withLogging fun request => liftM (sign request.cache request.message)
end ClaudeWCT.W9.T3.Security
end
-- ==== merged from ClaudeWCT_W9_T3_FullCache_NativeGame ====
section

section
namespace ClaudeWCT.W9.T3.Security.LazyPrivate
open OracleComp OracleSpec
abbrev Interaction := SphincsSecurity.OracleWorld + Requests
end ClaudeWCT.W9.T3.Security.LazyPrivate
end
section
namespace ClaudeWCT.W9.T3.Security.RequestHop
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.RequestHop
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {State : Type}
abbrev Signer (State : Type) := Request → StateT State ProbComp (Option Signature)
noncomputable def run {α : Type} (world : Public State) (signer : Signer State)
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    ProbComp ((α × QueryLog Requests) × State) :=
  OracleComp.recOn program (fun value state => pure ((value,[]),state))
    (fun input _ ih state => match input with
      | .inl input => do
          let result ← (world input).run state
          ih result.1 result.2
      | .inr request => do
          let result ← (signer request).run state
          (fun tail => ((tail.1.1,⟨request,result.1⟩::tail.1.2),tail.2)) <$> ih result.1 result.2) state
theorem run_pure {α : Type} (world : Public State) (signer : Signer State)
    (value : α) (state : State) : run world signer (pure value) state=pure ((value,[]),state) := rfl
theorem run_public {α : Type} (world : Public State) (signer : Signer State)
    (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp LazyPrivate.Interaction α)
    (state : State) :
    run world signer (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next) state=
      (do let result ← (world input).run state; run world signer (next result.1) result.2) := rfl
theorem run_request {α : Type} (world : Public State) (signer : Signer State)
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α)
    (state : State) :
    run world signer (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) state=
      (do
        let result ← (signer request).run state
        (fun tail => ((tail.1.1,⟨request,result.1⟩::tail.1.2),tail.2)) <$>
          run world signer (next result.1) result.2) := rfl
theorem erasure {α : Type} (world : Public State) (signer : Signer State)
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    (fun result => (result.1.1,result.2)) <$> run world signer program state=
      (simulateQ (world+signer) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [run_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [run_public,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          rw [run_request,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          apply bind_congr
          intro result
          simpa only [Functor.map_map,Function.comp_def] using ih result.1 result.2
end ClaudeWCT.W9.T3.Security.RequestHop
end
section
namespace ClaudeWCT.W9.SiggolfT3Mac4.Source
open OracleComp OracleSpec ENNReal SphincsSecurity
open _root_.SiggolfT3Mac4 _root_.SiggolfT3Mac4.Source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev WSignature := ClaudeWCT.W9.T3.Security.Signature
noncomputable def sign (payload : Request T3Message → T3M (Option WSignature))
    (request : Request T3Message) : T3M (Option WSignature) := do
  let tag ← privateMac request.cache.region
  if tag = request.cache.tag then payload request else pure none
end ClaudeWCT.W9.SiggolfT3Mac4.Source
end
section
namespace ClaudeWCT.W9.SiggolfT3Mac4.Source
open OracleComp OracleSpec
open _root_.SiggolfT3Mac4 _root_.SiggolfT3Mac4.Source
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def corePayload (request : Request T3Message) : T3M (Option WSignature) :=
  ClaudeWCT.W9.T3.Security.signPayload (toCoreCache request.cache) request.message
theorem corePayload_nonMac (request : Request T3Message) :
    AllQueriesSatisfy (corePayload request) NonMac :=
  ClaudeWCT.W9.T3.Security.Signer.signPayload_nonMac _ _
theorem core_sign_eq (cache : _root_.SiggolfT3Mac4.Cache) (message : T3Message) :
    ClaudeWCT.W9.T3.Security.sign (toCoreCache cache) message = sign corePayload ⟨message,cache⟩ := by
  rw [ClaudeWCT.W9.T3.Security.sign_eq]
  unfold SigGolfCandidate.T3.privateMac sign _root_.SiggolfT3Mac4.Source.privateMac
  rw [privateMacKey_eq_core]
  simp only [bind_assoc,pure_bind,toCoreCache,tagRegion,regionBytes]
  apply congrArg (fun k => SigGolfCandidate.T3.privateMacKey >>= k)
  funext key
  by_cases h : macTag key (List.ofFn cache.region)=cache.tag
  · simp only [h,ne_eq,not_true_eq_false,ite_false,ite_true,corePayload,toCoreCache]
  · have he : encodeTag (macTag key (List.ofFn cache.region)) ≠ encodeTag cache.tag :=
      fun hx => h (encodeTag_injective hx)
    rw [if_pos he, if_neg h]
end ClaudeWCT.W9.SiggolfT3Mac4.Source
end
section
namespace ClaudeWCT.W9.SiggolfT3Mac4.Source
open OracleComp OracleSpec ENNReal
open _root_.SiggolfT3Mac4 _root_.SiggolfT3Mac4.Source
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev CoreRequests := ClaudeWCT.W9.T3.Security.Requests
abbrev CoreInteraction := ClaudeWCT.W9.T3.Security.LazyPrivate.Interaction
theorem entry_roundtrip (request : CoreRequest) (answer : Option WSignature) :
    (⟨toCoreRequest (fromCoreRequest request),answer⟩ :
      (input : CoreRequests.Domain) × CoreRequests.Range input)=⟨request,answer⟩ := by
  exact Sigma.ext (toCoreRequest_fromCoreRequest request) HEq.rfl
def toCoreLog (log : QueryLog (Requests T3Message WSignature)) : QueryLog CoreRequests :=
  log.map fun entry => ⟨toCoreRequest entry.1,entry.2⟩
theorem toCoreLog_length (log : QueryLog (Requests T3Message WSignature)) :
    (toCoreLog log).length=log.length := by simp [toCoreLog]
noncomputable def interactionMap : QueryImpl CoreInteraction
    (OracleComp (Interaction T3Message WSignature))
  | .inl input => liftM ((Interaction T3Message WSignature).query (.inl input))
  | .inr request => liftM ((Interaction T3Message WSignature).query (.inr (fromCoreRequest request)))
noncomputable def transport {α : Type} (program : OracleComp CoreInteraction α) :
    OracleComp (Interaction T3Message WSignature) α := simulateQ interactionMap program
def restore {α State : Type}
    (result : (α × QueryLog (Requests T3Message WSignature)) × State) :
    (α × QueryLog CoreRequests) × State := ((result.1.1,toCoreLog result.1.2),result.2)
theorem run_transport {α State : Type} (world : SigGolfCandidate.T3.Security.RequestHop.Public State)
    (signer : ClaudeWCT.W9.T3.Security.RequestHop.Signer State)
    (program : OracleComp CoreInteraction α) (state : State) :
    ClaudeWCT.W9.T3.Security.RequestHop.run world signer program state =
      restore <$> Adaptive.run world (fun request => signer (toCoreRequest request))
        (transport program) state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [transport,simulateQ_bind,simulateQ_spec_query,interactionMap]
          rw [ClaudeWCT.W9.T3.Security.RequestHop.run_public,Adaptive.run_public,map_bind]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          simp only [transport,simulateQ_bind,simulateQ_spec_query,interactionMap]
          rw [ClaudeWCT.W9.T3.Security.RequestHop.run_request,Adaptive.run_request,map_bind,
            toCoreRequest_fromCoreRequest]
          apply bind_congr
          intro head
          rw [ih]
          simp only [Functor.map_map,Function.comp_def,restore,toCoreLog,List.map_cons,
            toCoreRequest_fromCoreRequest,entry_roundtrip]
          rfl
theorem run_transport_bind {α β State : Type} (world : SigGolfCandidate.T3.Security.RequestHop.Public State)
    (signer : ClaudeWCT.W9.T3.Security.RequestHop.Signer State)
    (program : OracleComp CoreInteraction α) (state : State)
    (cont : ((α × QueryLog CoreRequests) × State) → ProbComp β) :
    ClaudeWCT.W9.T3.Security.RequestHop.run world signer program state >>= cont =
      Adaptive.run world (fun request => signer (toCoreRequest request))
        (transport program) state >>= fun result => cont (restore result) := by
  rw [run_transport,bind_map_left]
end ClaudeWCT.W9.SiggolfT3Mac4.Source
end
section
namespace ClaudeWCT.W9.T3.Security.MacGame
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.CacheAuthentication
open SigGolfCandidate.T3.Security.MacGame
open _root_.SiggolfT3Mac4 (MacKey encodeTag decodeTag tagRegion)
open _root_.SiggolfT3Mac4.Adaptive (retagRegion)
open _root_.SiggolfT3Mac4.Source (keyCoordinate toCoreCache fromCoreCache toCoreRequest fromCoreRequest)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
noncomputable local instance : SampleableType MacTable := macTableSampler
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
variable {State : Type}
theorem payload_no_mac (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    AllQueriesSatisfy (signPayload cache message) NonMac :=
  Signer.signPayload_nonMac cache message
noncomputable def realSigner (base : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp))
    (key : MacTable) : RequestHop.Signer State := fun request =>
  _root_.SiggolfT3Mac4.Adaptive.realSigner (fun _ => overhead base)
    (fun request => simulateQ base (ClaudeWCT.W9.SiggolfT3Mac4.Source.corePayload request)) key
    (fromCoreRequest request)
noncomputable def idealSigner (base : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp))
    (published : SigGolfCandidate.T3.Cache) : RequestHop.Signer State := fun request =>
  _root_.SiggolfT3Mac4.Adaptive.idealSigner (fun _ => overhead base)
    (fun request => simulateQ base (ClaudeWCT.W9.SiggolfT3Mac4.Source.corePayload request))
    (fromCoreCache published) (fromCoreRequest request)
theorem source_signer_eq (base : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp))
    (key : MacTable) (request : Request) :
    simulateQ (sourceHandler base key) (sign request.cache request.message)=realSigner base key request := by
  rw [← _root_.SiggolfT3Mac4.Source.toCoreCache_fromCoreCache request.cache,
    ClaudeWCT.W9.SiggolfT3Mac4.Source.core_sign_eq]
  unfold ClaudeWCT.W9.SiggolfT3Mac4.Source.sign _root_.SiggolfT3Mac4.Source.privateMac
  rw [_root_.SiggolfT3Mac4.Source.privateMacKey_eq_core]
  simp only [bind_assoc,pure_bind,simulateQ_bind,source_key_eq,bind_assoc,pure_bind]
  change (overhead base >>= fun _ => _)=_
  unfold realSigner _root_.SiggolfT3Mac4.Adaptive.realSigner
  apply congrArg (fun next => overhead base >>= next)
  funext ignored
  simp only [_root_.SiggolfT3Mac4.Source.toCoreCache_fromCoreCache,
    fromCoreRequest,fromCoreCache]
  split_ifs
  · exact simulate_no_mac base key _ (ClaudeWCT.W9.SiggolfT3Mac4.Source.corePayload_nonMac _)
  · rfl
theorem authentication_hop {α β : Type} (world : SigGolfCandidate.T3.Security.RequestHop.Public State)
    (base : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp)) (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp LazyPrivate.Interaction α) (limit : Nat) (state : State)
    (cont : ((α × QueryLog Requests) × State) → ProbComp β) (event : β → Prop)
    (hlong : ∀ result,limit < result.1.2.length → Pr[event | cont result]=0) :
    Pr[event | ($ᵗ MacTable : ProbComp _) >>= fun key =>
      RequestHop.run world (realSigner base (retag key published)) program state >>= cont] ≤
      Pr[event | RequestHop.run world (idealSigner base published) program state >>= cont]+
        limit*((2 : ENNReal)^184)⁻¹ := by
  have hr := @ClaudeWCT.W9.SiggolfT3Mac4.Source.run_transport_bind α β State
  simp only [hr]
  simp only [realSigner,idealSigner,retag,_root_.SiggolfT3Mac4.Source.fromCoreRequest_toCoreRequest]
  exact _root_.SiggolfT3Mac4.Adaptive.authentication_hop world (fun _ => overhead base)
    (fun request => simulateQ base (ClaudeWCT.W9.SiggolfT3Mac4.Source.corePayload request))
    (fromCoreCache published) (ClaudeWCT.W9.SiggolfT3Mac4.Source.transport program) limit state
    (fun result => cont (ClaudeWCT.W9.SiggolfT3Mac4.Source.restore result)) event
    (fun result hlong' => hlong _ (by simpa only [ClaudeWCT.W9.SiggolfT3Mac4.Source.restore,
      ClaudeWCT.W9.SiggolfT3Mac4.Source.toCoreLog_length] using hlong'))
end ClaudeWCT.W9.T3.Security.MacGame
end
section
namespace ClaudeWCT.W9.T3.Security.ProposalOverflow
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def logFragment : (input : LazyPrivate.Interaction.Domain) →
    LazyPrivate.Interaction.Range input → QueryLog Requests
  | .inl _, _ => []
  | .inr request, response => [⟨request,response⟩]
def logging : QueryImpl LazyPrivate.Interaction
    (WriterT (QueryLog Requests) (OracleComp LazyPrivate.Interaction)) :=
  QueryImpl.withTraceAppend (fun input => LazyPrivate.Interaction.query input) logFragment
def logged {Result : Type} (program : OracleComp LazyPrivate.Interaction Result) :
    OracleComp LazyPrivate.Interaction (Result × QueryLog Requests) :=
  (simulateQ logging program).run
theorem logged_pure {Result : Type} (value : Result) : logged (pure value) = pure (value,[]) := rfl
theorem logged_query_bind {Result : Type} (input : LazyPrivate.Interaction.Domain)
    (next : LazyPrivate.Interaction.Range input → OracleComp LazyPrivate.Interaction Result) :
    logged (LazyPrivate.Interaction.query input >>= next) = (do
      let response ← LazyPrivate.Interaction.query input
      let result ← logged (next response)
      pure (result.1, logFragment input response ++ result.2)) := by
  simp [logged, logging, QueryImpl.withTraceAppend_apply]
end ClaudeWCT.W9.T3.Security.ProposalOverflow
end
section
namespace ClaudeWCT.W9.T3.Security.FullGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.FullGame
open SphincsSecurity (OracleWorld romImpl)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq _root_.SiggolfT3Mac4.Cache := Classical.decEq _
noncomputable local instance : DecidableEq Region := Classical.decEq _
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : Fintype OtherCoordinate := otherFintype
noncomputable local instance : Fintype Region := CacheAuthentication.regionFintype
noncomputable local instance : SampleableType FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : SampleableType OtherTable := otherSampler
noncomputable local instance : SampleableType MacTable := CacheAuthentication.macTableSampler
noncomputable def authenticatedSign (published : SigGolfCandidate.T3.Cache) (request : Request) :
    M (Option Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache=published then signPayload request.cache request.message else pure none
noncomputable def loggedWith {α : Type} (signer : Request → M (Option Signature))
    (program : OracleComp LazyPrivate.Interaction α) : M (α × QueryLog Requests) :=
  (simulateQ ((fun input => liftM (forwardWorld input) :
      QueryImpl OracleWorld (WriterT (QueryLog Requests) M))+
      (QueryImpl.withLogging (fun request => signer request) :
        QueryImpl Requests (WriterT (QueryLog Requests) M))) program).run
theorem loggedWith_pure {α : Type} (signer : Request → M (Option Signature)) (value : α) :
    loggedWith signer (pure value)=pure (value,[]) := rfl
theorem loggedWith_world {α : Type} (signer : Request → M (Option Signature))
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp LazyPrivate.Interaction α) :
    loggedWith signer (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next)=
      (forwardWorld input >>= fun answer => loggedWith signer (next answer)) := by
  unfold loggedWith
  rw [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inl]
  simp only [WriterT.run_bind',WriterT.run_liftM,bind_map_left]
  apply bind_congr
  intro answer
  change id <$> _ = _
  rw [id_map]
theorem loggedWith_request {α : Type} (signer : Request → M (Option Signature))
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    loggedWith signer (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next)=
      (signer request >>= fun answer =>
        (fun result => (result.1,⟨request,answer⟩::result.2)) <$> loggedWith signer (next answer)) := by
  unfold loggedWith
  rw [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inr]
  simp
theorem loggedWith_interpretation {State α : Type}
    (handler : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp))
    (signer : Request → M (Option Signature))
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    (simulateQ handler (loggedWith signer program)).run state=
      RequestHop.run (fun input => handler (.inl input))
        (fun request => simulateQ handler (signer request)) program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [loggedWith_pure,RequestHop.run_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [loggedWith_world,RequestHop.run_public,simulateQ_bind,StateT.run_bind]
          simp only [forwardWorld,simulateQ_spec_query]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          rw [loggedWith_request,RequestHop.run_request,simulateQ_bind,StateT.run_bind]
          apply bind_congr
          intro result
          simp only [simulateQ_map,StateT.run_map,ih]
theorem authenticatedSign_interpretation (other : OtherTable) (mac : MacTable)
    (published : SigGolfCandidate.T3.Cache) (request : Request) :
    simulateQ (SigGolfCandidate.T3.Security.MacGame.sourceHandler (baseHandler other) mac)
      (authenticatedSign published request)=
      MacGame.idealSigner (baseHandler other) published request := by
  classical
  unfold authenticatedSign privateMac
  simp only [bind_assoc,pure_bind,simulateQ_bind,SigGolfCandidate.T3.Security.MacGame.source_key_eq,
    bind_assoc,pure_bind]
  unfold MacGame.idealSigner _root_.SiggolfT3Mac4.Adaptive.idealSigner
  apply congrArg (fun next => SigGolfCandidate.T3.Security.MacGame.overhead (baseHandler other) >>= next)
  funext ignored
  simp only [_root_.SiggolfT3Mac4.Source.fromCoreRequest]
  have he : _root_.SiggolfT3Mac4.Source.fromCoreCache request.cache =
      _root_.SiggolfT3Mac4.Source.fromCoreCache published ↔ request.cache=published :=
    _root_.SiggolfT3Mac4.Source.coreCacheEquiv.symm.injective.eq_iff
  simp only [he]
  split_ifs
  · simpa only [ClaudeWCT.W9.SiggolfT3Mac4.Source.corePayload,
      _root_.SiggolfT3Mac4.Source.toCoreCache_fromCoreCache] using
      SigGolfCandidate.T3.Security.MacGame.simulate_no_mac (baseHandler other) mac _
        (MacGame.payload_no_mac request.cache request.message)
  · rfl
end ClaudeWCT.W9.T3.Security.FullGame
end

namespace ClaudeWCT.W9.T3.Security.PairedOuter
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.Research.SharedForest ClaudeWCT.WCT9
open _root_.SiggolfT3Mac4.Source (NonMac non_mac_tweak)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem privatePair_nonMac (tag lay tree position index : Nat) (h : tag%256≠14) :
    AllQueriesSatisfy (privatePair tag lay tree position index) NonMac := by
  unfold privatePair
  apply SourceQueries.bind_allowed
  · exact (allQueriesSatisfy_query_iff _ _).mpr ⟨non_mac_tweak _ _ _ _ _ h 0,non_mac_tweak _ _ _ _ _ h 1⟩
  · intro _;exact SourceQueries.pure_allowed _ _

theorem tail_nonMac : SharedQueries.TailAllowed NonMac where
  chainStep := fun _ _ _ _ _ _=>SourceQueries.shortHash_allowed _ (fun _=>trivial) _
  chainStepW := fun _ _ _ _ _ _=>SourceQueries.shortHash_allowed _ (fun _=>trivial) _
  leaf := fun _ _ _ _=>SourceQueries.shortHash_allowed _ (fun _=>trivial) _
  node := fun _ _ _ _ _ _=>Signer.lowerNodeHash_allowed_of_public _ (fun _=>trivial) _ _ _ _ _
  seed := fun _ _ _=>privatePair_nonMac _ _ _ _ _ (by decide)
  encoding := fun lay _ _ msg _=>by
    cases msg <;> exact SourceQueries.shortHash_allowed _ (fun _=>trivial) _
  top := _root_.SiggolfT3Mac4.Source.Payload.signTop_allowed

theorem forest_nonMac : ClaudeWCT.Bank.Paired.ForestAllowed NonMac where
  coefs := fun _ _=>Signer.ftsCoefs_allowed _
    (fun lay tree position index=>⟨non_mac_tweak 8 lay tree position index (by decide) 0,
      non_mac_tweak 8 lay tree position index (by decide) 1⟩) _ _
  child := Signer.buildChildH_allowed _ (fun _=>trivial)
  node := Signer.sharedNode_allowed _ (fun _=>trivial)

theorem signFromOutput_nonMac (cache : SigGolfCandidate.T3.Cache) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) :
    AllQueriesSatisfy (signFromOutput cache rho counter output) NonMac :=
  SharedQueries.signFromOutput_allowed _ tail_nonMac
    (ClaudeWCT.Bank.Paired.forest_allowed _ forest_nonMac) _ _ _ _

theorem digestSearch_nonMac (rho : Digest) (message : Message) (counter fuel : Nat) :
    AllQueriesSatisfy (sharedDigestSearch rho message counter fuel) NonMac := by
  induction fuel generalizing counter with
  | zero=>exact SourceQueries.pure_allowed _ _
  | succ fuel ih=>
    unfold sharedDigestSearch
    apply SourceQueries.bind_allowed _ (SourceQueries.publicHash_allowed _ (fun _=>trivial) _)
    intro output
    split
    · exact SourceQueries.pure_allowed _ _
    · exact ih _

theorem signPayload_nonMac (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    AllQueriesSatisfy (SigGolfCandidate.Research.SharedForest.signPayload cache message) NonMac := by
  unfold SigGolfCandidate.Research.SharedForest.signPayload
  apply SourceQueries.bind_allowed _ (SourceQueries.privateNonce_allowed _ _root_.SiggolfT3Mac4.Source.nonce_coordinate_other _)
  intro rho
  apply SourceQueries.bind_allowed _ (digestSearch_nonMac ..)
  intro found
  rcases found with _|⟨counter,output⟩
  · exact SourceQueries.pure_allowed _ _
  · apply SourceQueries.bind_allowed _ (signFromOutput_nonMac ..)
    intro signed
    cases signed <;> exact SourceQueries.pure_allowed _ _
end ClaudeWCT.W9.T3.Security.PairedOuter

namespace ClaudeWCT.W9.T3.Security.PairedOuter
open OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
abbrev Signature := SigGolfCandidate.Research.SharedForest.Signature
abbrev Requests := Request →ₒ Option Signature
abbrev signPayload := SigGolfCandidate.Research.SharedForest.signPayload
abbrev sign := SigGolfCandidate.Research.SharedForest.sign
end ClaudeWCT.W9.T3.Security.PairedOuter
section
namespace ClaudeWCT.W9.T3.Security.PairedOuter.LazyPrivate
open OracleComp OracleSpec
abbrev Interaction := SphincsSecurity.OracleWorld + Requests
end ClaudeWCT.W9.T3.Security.PairedOuter.LazyPrivate
end
section
namespace ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.RequestHop
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {State : Type}
abbrev Signer (State : Type) := Request → StateT State ProbComp (Option Signature)
noncomputable def run {α : Type} (world : Public State) (signer : Signer State)
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    ProbComp ((α × QueryLog Requests) × State) :=
  OracleComp.recOn program (fun value state => pure ((value,[]),state))
    (fun input _ ih state => match input with
      | .inl input => do
          let result ← (world input).run state
          ih result.1 result.2
      | .inr request => do
          let result ← (signer request).run state
          (fun tail => ((tail.1.1,⟨request,result.1⟩::tail.1.2),tail.2)) <$> ih result.1 result.2) state
theorem run_pure {α : Type} (world : Public State) (signer : Signer State)
    (value : α) (state : State) : run world signer (pure value) state=pure ((value,[]),state) := rfl
theorem run_public {α : Type} (world : Public State) (signer : Signer State)
    (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp LazyPrivate.Interaction α)
    (state : State) :
    run world signer (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next) state=
      (do let result ← (world input).run state; run world signer (next result.1) result.2) := rfl
theorem run_request {α : Type} (world : Public State) (signer : Signer State)
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α)
    (state : State) :
    run world signer (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) state=
      (do
        let result ← (signer request).run state
        (fun tail => ((tail.1.1,⟨request,result.1⟩::tail.1.2),tail.2)) <$>
          run world signer (next result.1) result.2) := rfl
theorem erasure {α : Type} (world : Public State) (signer : Signer State)
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    (fun result => (result.1.1,result.2)) <$> run world signer program state=
      (simulateQ (world+signer) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [run_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [run_public,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          rw [run_request,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          apply bind_congr
          intro result
          simpa only [Functor.map_map,Function.comp_def] using ih result.1 result.2
end ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop
end
section
namespace ClaudeWCT.W9.PairedMac.Source
open OracleComp OracleSpec ENNReal SphincsSecurity
open _root_.SiggolfT3Mac4 _root_.SiggolfT3Mac4.Source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev WSignature := ClaudeWCT.W9.T3.Security.PairedOuter.Signature
noncomputable def sign (payload : Request T3Message → T3M (Option WSignature))
    (request : Request T3Message) : T3M (Option WSignature) := do
  let tag ← privateMac request.cache.region
  if tag = request.cache.tag then payload request else pure none
end ClaudeWCT.W9.PairedMac.Source
end
section
namespace ClaudeWCT.W9.PairedMac.Source
open OracleComp OracleSpec
open _root_.SiggolfT3Mac4 _root_.SiggolfT3Mac4.Source
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def corePayload (request : Request T3Message) : T3M (Option WSignature) :=
  SigGolfCandidate.Research.SharedForest.signPayload (toCoreCache request.cache) request.message
theorem corePayload_nonMac (request : Request T3Message) :
    AllQueriesSatisfy (corePayload request) NonMac :=
  ClaudeWCT.W9.T3.Security.PairedOuter.signPayload_nonMac _ _
theorem core_sign_eq (cache : _root_.SiggolfT3Mac4.Cache) (message : T3Message) :
    SigGolfCandidate.Research.SharedForest.sign (toCoreCache cache) message = sign corePayload ⟨message,cache⟩ := by
  unfold SigGolfCandidate.Research.SharedForest.sign
  unfold SigGolfCandidate.T3.privateMac sign _root_.SiggolfT3Mac4.Source.privateMac
  rw [privateMacKey_eq_core]
  simp only [bind_assoc,pure_bind,toCoreCache,tagRegion,regionBytes]
  apply congrArg (fun k => SigGolfCandidate.T3.privateMacKey >>= k)
  funext key
  by_cases h : macTag key (List.ofFn cache.region)=cache.tag
  · simp only [h,ne_eq,not_true_eq_false,ite_false,ite_true,corePayload,toCoreCache]
  · have he : encodeTag (macTag key (List.ofFn cache.region)) ≠ encodeTag cache.tag :=
      fun hx => h (encodeTag_injective hx)
    rw [if_pos he, if_neg h]
end ClaudeWCT.W9.PairedMac.Source
end
section
namespace ClaudeWCT.W9.PairedMac.Source
open OracleComp OracleSpec ENNReal
open _root_.SiggolfT3Mac4 _root_.SiggolfT3Mac4.Source
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev CoreRequests := ClaudeWCT.W9.T3.Security.PairedOuter.Requests
abbrev CoreInteraction := ClaudeWCT.W9.T3.Security.PairedOuter.LazyPrivate.Interaction
theorem entry_roundtrip (request : CoreRequest) (answer : Option WSignature) :
    (⟨toCoreRequest (fromCoreRequest request),answer⟩ :
      (input : CoreRequests.Domain) × CoreRequests.Range input)=⟨request,answer⟩ := by
  exact Sigma.ext (toCoreRequest_fromCoreRequest request) HEq.rfl
def toCoreLog (log : QueryLog (Requests T3Message WSignature)) : QueryLog CoreRequests :=
  log.map fun entry => ⟨toCoreRequest entry.1,entry.2⟩
theorem toCoreLog_length (log : QueryLog (Requests T3Message WSignature)) :
    (toCoreLog log).length=log.length := by simp [toCoreLog]
noncomputable def interactionMap : QueryImpl CoreInteraction
    (OracleComp (Interaction T3Message WSignature))
  | .inl input => liftM ((Interaction T3Message WSignature).query (.inl input))
  | .inr request => liftM ((Interaction T3Message WSignature).query (.inr (fromCoreRequest request)))
noncomputable def transport {α : Type} (program : OracleComp CoreInteraction α) :
    OracleComp (Interaction T3Message WSignature) α := simulateQ interactionMap program
def restore {α State : Type}
    (result : (α × QueryLog (Requests T3Message WSignature)) × State) :
    (α × QueryLog CoreRequests) × State := ((result.1.1,toCoreLog result.1.2),result.2)
theorem run_transport {α State : Type} (world : SigGolfCandidate.T3.Security.RequestHop.Public State)
    (signer : ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.Signer State)
    (program : OracleComp CoreInteraction α) (state : State) :
    ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run world signer program state =
      restore <$> Adaptive.run world (fun request => signer (toCoreRequest request))
        (transport program) state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [transport,simulateQ_bind,simulateQ_spec_query,interactionMap]
          rw [ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run_public,Adaptive.run_public,map_bind]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          simp only [transport,simulateQ_bind,simulateQ_spec_query,interactionMap]
          rw [ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run_request,Adaptive.run_request,map_bind,
            toCoreRequest_fromCoreRequest]
          apply bind_congr
          intro head
          rw [ih]
          simp only [Functor.map_map,Function.comp_def,restore,toCoreLog,List.map_cons,
            toCoreRequest_fromCoreRequest,entry_roundtrip]
          rfl
theorem run_transport_bind {α β State : Type} (world : SigGolfCandidate.T3.Security.RequestHop.Public State)
    (signer : ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.Signer State)
    (program : OracleComp CoreInteraction α) (state : State)
    (cont : ((α × QueryLog CoreRequests) × State) → ProbComp β) :
    ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run world signer program state >>= cont =
      Adaptive.run world (fun request => signer (toCoreRequest request))
        (transport program) state >>= fun result => cont (restore result) := by
  rw [run_transport,bind_map_left]
end ClaudeWCT.W9.PairedMac.Source
end
section
namespace ClaudeWCT.W9.T3.Security.PairedOuter.MacGame
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.CacheAuthentication
open SigGolfCandidate.T3.Security.MacGame
open _root_.SiggolfT3Mac4 (MacKey encodeTag decodeTag tagRegion)
open _root_.SiggolfT3Mac4.Adaptive (retagRegion)
open _root_.SiggolfT3Mac4.Source (keyCoordinate toCoreCache fromCoreCache toCoreRequest fromCoreRequest)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
noncomputable local instance : SampleableType MacTable := macTableSampler
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
variable {State : Type}
theorem payload_no_mac (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    AllQueriesSatisfy (signPayload cache message) NonMac :=
  ClaudeWCT.W9.T3.Security.PairedOuter.signPayload_nonMac cache message
noncomputable def realSigner (base : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp))
    (key : MacTable) : RequestHop.Signer State := fun request =>
  _root_.SiggolfT3Mac4.Adaptive.realSigner (fun _ => overhead base)
    (fun request => simulateQ base (ClaudeWCT.W9.PairedMac.Source.corePayload request)) key
    (fromCoreRequest request)
noncomputable def idealSigner (base : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp))
    (published : SigGolfCandidate.T3.Cache) : RequestHop.Signer State := fun request =>
  _root_.SiggolfT3Mac4.Adaptive.idealSigner (fun _ => overhead base)
    (fun request => simulateQ base (ClaudeWCT.W9.PairedMac.Source.corePayload request))
    (fromCoreCache published) (fromCoreRequest request)
theorem source_signer_eq (base : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp))
    (key : MacTable) (request : Request) :
    simulateQ (sourceHandler base key) (sign request.cache request.message)=realSigner base key request := by
  change simulateQ (sourceHandler base key) (SigGolfCandidate.Research.SharedForest.sign request.cache request.message)=_
  rw [← _root_.SiggolfT3Mac4.Source.toCoreCache_fromCoreCache request.cache,
    ClaudeWCT.W9.PairedMac.Source.core_sign_eq]
  unfold ClaudeWCT.W9.PairedMac.Source.sign _root_.SiggolfT3Mac4.Source.privateMac
  rw [_root_.SiggolfT3Mac4.Source.privateMacKey_eq_core]
  simp only [bind_assoc,pure_bind,simulateQ_bind,source_key_eq,bind_assoc,pure_bind]
  change (overhead base >>= fun _ => _)=_
  unfold realSigner _root_.SiggolfT3Mac4.Adaptive.realSigner
  apply congrArg (fun next => overhead base >>= next)
  funext ignored
  simp only [_root_.SiggolfT3Mac4.Source.toCoreCache_fromCoreCache,
    fromCoreRequest,fromCoreCache]
  split_ifs
  · exact simulate_no_mac base key _ (ClaudeWCT.W9.PairedMac.Source.corePayload_nonMac _)
  · rfl
theorem authentication_hop {α β : Type} (world : SigGolfCandidate.T3.Security.RequestHop.Public State)
    (base : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp)) (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp LazyPrivate.Interaction α) (limit : Nat) (state : State)
    (cont : ((α × QueryLog Requests) × State) → ProbComp β) (event : β → Prop)
    (hlong : ∀ result,limit < result.1.2.length → Pr[event | cont result]=0) :
    Pr[event | ($ᵗ MacTable : ProbComp _) >>= fun key =>
      RequestHop.run world (realSigner base (retag key published)) program state >>= cont] ≤
      Pr[event | RequestHop.run world (idealSigner base published) program state >>= cont]+
        limit*((2 : ENNReal)^184)⁻¹ := by
  have hr := @ClaudeWCT.W9.PairedMac.Source.run_transport_bind α β State
  simp only [hr]
  simp only [realSigner,idealSigner,retag,_root_.SiggolfT3Mac4.Source.fromCoreRequest_toCoreRequest]
  exact _root_.SiggolfT3Mac4.Adaptive.authentication_hop world (fun _ => overhead base)
    (fun request => simulateQ base (ClaudeWCT.W9.PairedMac.Source.corePayload request))
    (fromCoreCache published) (ClaudeWCT.W9.PairedMac.Source.transport program) limit state
    (fun result => cont (ClaudeWCT.W9.PairedMac.Source.restore result)) event
    (fun result hlong' => hlong _ (by simpa only [ClaudeWCT.W9.PairedMac.Source.restore,
      ClaudeWCT.W9.PairedMac.Source.toCoreLog_length] using hlong'))
end ClaudeWCT.W9.T3.Security.PairedOuter.MacGame
end
section
namespace ClaudeWCT.W9.T3.Security.PairedOuter.ProposalOverflow
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def logFragment : (input : LazyPrivate.Interaction.Domain) →
    LazyPrivate.Interaction.Range input → QueryLog Requests
  | .inl _, _ => []
  | .inr request, response => [⟨request,response⟩]
def logging : QueryImpl LazyPrivate.Interaction
    (WriterT (QueryLog Requests) (OracleComp LazyPrivate.Interaction)) :=
  QueryImpl.withTraceAppend (fun input => LazyPrivate.Interaction.query input) logFragment
def logged {Result : Type} (program : OracleComp LazyPrivate.Interaction Result) :
    OracleComp LazyPrivate.Interaction (Result × QueryLog Requests) :=
  (simulateQ logging program).run
theorem logged_pure {Result : Type} (value : Result) : logged (pure value) = pure (value,[]) := rfl
theorem logged_query_bind {Result : Type} (input : LazyPrivate.Interaction.Domain)
    (next : LazyPrivate.Interaction.Range input → OracleComp LazyPrivate.Interaction Result) :
    logged (LazyPrivate.Interaction.query input >>= next) = (do
      let response ← LazyPrivate.Interaction.query input
      let result ← logged (next response)
      pure (result.1, logFragment input response ++ result.2)) := by
  simp [logged, logging, QueryImpl.withTraceAppend_apply]
end ClaudeWCT.W9.T3.Security.PairedOuter.ProposalOverflow
end
section
namespace ClaudeWCT.W9.T3.Security.PairedOuter.FullGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.FullGame
open SphincsSecurity (OracleWorld romImpl)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq _root_.SiggolfT3Mac4.Cache := Classical.decEq _
noncomputable local instance : DecidableEq Region := Classical.decEq _
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : Fintype OtherCoordinate := otherFintype
noncomputable local instance : Fintype Region := CacheAuthentication.regionFintype
noncomputable local instance : SampleableType FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : SampleableType OtherTable := otherSampler
noncomputable local instance : SampleableType MacTable := CacheAuthentication.macTableSampler
noncomputable def authenticatedSign (published : SigGolfCandidate.T3.Cache) (request : Request) :
    M (Option Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache=published then signPayload request.cache request.message else pure none
noncomputable def loggedWith {α : Type} (signer : Request → M (Option Signature))
    (program : OracleComp LazyPrivate.Interaction α) : M (α × QueryLog Requests) :=
  (simulateQ ((fun input => liftM (forwardWorld input) :
      QueryImpl OracleWorld (WriterT (QueryLog Requests) M))+
      (QueryImpl.withLogging (fun request => signer request) :
        QueryImpl Requests (WriterT (QueryLog Requests) M))) program).run
theorem loggedWith_pure {α : Type} (signer : Request → M (Option Signature)) (value : α) :
    loggedWith signer (pure value)=pure (value,[]) := rfl
theorem loggedWith_world {α : Type} (signer : Request → M (Option Signature))
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp LazyPrivate.Interaction α) :
    loggedWith signer (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next)=
      (forwardWorld input >>= fun answer => loggedWith signer (next answer)) := by
  unfold loggedWith
  rw [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inl]
  simp only [WriterT.run_bind',WriterT.run_liftM,bind_map_left]
  apply bind_congr
  intro answer
  change id <$> _ = _
  rw [id_map]
theorem loggedWith_request {α : Type} (signer : Request → M (Option Signature))
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    loggedWith signer (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next)=
      (signer request >>= fun answer =>
        (fun result => (result.1,⟨request,answer⟩::result.2)) <$> loggedWith signer (next answer)) := by
  unfold loggedWith
  rw [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inr]
  simp
theorem loggedWith_interpretation {State α : Type}
    (handler : QueryImpl SigGolfCandidate.T3.Spec (StateT State ProbComp))
    (signer : Request → M (Option Signature))
    (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    (simulateQ handler (loggedWith signer program)).run state=
      RequestHop.run (fun input => handler (.inl input))
        (fun request => simulateQ handler (signer request)) program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [loggedWith_pure,RequestHop.run_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [loggedWith_world,RequestHop.run_public,simulateQ_bind,StateT.run_bind]
          simp only [forwardWorld,simulateQ_spec_query]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          rw [loggedWith_request,RequestHop.run_request,simulateQ_bind,StateT.run_bind]
          apply bind_congr
          intro result
          simp only [simulateQ_map,StateT.run_map,ih]
theorem authenticatedSign_interpretation (other : OtherTable) (mac : MacTable)
    (published : SigGolfCandidate.T3.Cache) (request : Request) :
    simulateQ (SigGolfCandidate.T3.Security.MacGame.sourceHandler (baseHandler other) mac)
      (authenticatedSign published request)=
      MacGame.idealSigner (baseHandler other) published request := by
  classical
  unfold authenticatedSign privateMac
  simp only [bind_assoc,pure_bind,simulateQ_bind,SigGolfCandidate.T3.Security.MacGame.source_key_eq,
    bind_assoc,pure_bind]
  unfold MacGame.idealSigner _root_.SiggolfT3Mac4.Adaptive.idealSigner
  apply congrArg (fun next => SigGolfCandidate.T3.Security.MacGame.overhead (baseHandler other) >>= next)
  funext ignored
  simp only [_root_.SiggolfT3Mac4.Source.fromCoreRequest]
  have he : _root_.SiggolfT3Mac4.Source.fromCoreCache request.cache =
      _root_.SiggolfT3Mac4.Source.fromCoreCache published ↔ request.cache=published :=
    _root_.SiggolfT3Mac4.Source.coreCacheEquiv.symm.injective.eq_iff
  simp only [he]
  split_ifs
  · simpa only [ClaudeWCT.W9.PairedMac.Source.corePayload,
      _root_.SiggolfT3Mac4.Source.toCoreCache_fromCoreCache] using
      SigGolfCandidate.T3.Security.MacGame.simulate_no_mac (baseHandler other) mac _
        (MacGame.payload_no_mac request.cache request.message)
  · rfl
end ClaudeWCT.W9.T3.Security.PairedOuter.FullGame
end
end
-- ==== merged from T3M_SigCodec ====
section

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length)
def digNat (ds : List Digest) : Nat := readLE (ds.flatMap (bytesLE 16))
theorem digNat_nil : digNat [] = 0 := rfl
theorem digNat_cons (d : Digest) (ds : List Digest) :
    digNat (d :: ds) = d.toNat + 2 ^ 128 * digNat ds := by
  unfold digNat
  rw [List.flatMap_cons, readLE_append, readLE_bytesLE, bytesLE_length]
  norm_num
theorem digNat_lt (ds : List Digest) : digNat ds < 2 ^ (128 * ds.length) := by
  induction ds with
  | nil => simp [digNat_nil]
  | cons d ds ih =>
    rw [digNat_cons, List.length_cons, show 128 * (ds.length + 1) = 128 + 128 * ds.length by ring,
      pow_add]
    have := d.isLt
    nlinarith
theorem digNat_digit (ds : List Digest) (k : Nat) :
    digNat ds / 2 ^ (128 * k) % 2 ^ 128 = (ds.getD k 0).toNat := by
  induction ds generalizing k with
  | nil => simp [digNat_nil]
  | cons d ds ih =>
    have hd := d.isLt
    rcases k with _ | k
    · rw [digNat_cons]; simp; omega
    · rw [digNat_cons, show 128 * (k + 1) = 128 + 128 * k by ring, pow_add, ← Nat.div_div_eq_div_mul,
        show (d.toNat + 2 ^ 128 * digNat ds) / 2 ^ 128 = digNat ds by
          rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hd, Nat.zero_add], ih]
      simp
theorem digNat_eq_of_digits : ∀ (ds : List Digest) (B : Nat), B < 2 ^ (128 * ds.length) →
    (∀ k < ds.length, (ds.getD k 0).toNat = B / 2 ^ (128 * k) % 2 ^ 128) → digNat ds = B
  | [], B, hB, _ => by simp at hB; simp [digNat_nil, hB]
  | d :: ds, B, hB, h => by
    rw [digNat_cons]
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero, Nat.mul_zero, pow_zero, Nat.div_one] at h0
    have hB' : B / 2 ^ 128 < 2 ^ (128 * ds.length) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      simpa [show 128 * (ds.length + 1) = 128 * ds.length + 128 by ring] using hB
    have hrest : ∀ k < ds.length, (ds.getD k 0).toNat = B / 2 ^ 128 / 2 ^ (128 * k) % 2 ^ 128 := by
      intro k hk
      have := h (k + 1) (by simp; omega)
      rw [List.getD_cons_succ] at this
      rw [this, show 128 * (k + 1) = 128 + 128 * k by ring, pow_add, Nat.div_div_eq_div_mul]
    rw [digNat_eq_of_digits ds (B / 2 ^ 128) hB' hrest]
    omega
def sigDigests (s : Signature) : List Digest :=
  [s.rho] ++ List.ofFn s.secrets ++ List.ofFn s.proof ++
    (List.ofFn fun lay : Layer => List.ofFn (s.layers lay).values ++ List.ofFn (s.layers lay).path).flatten
theorem ofFn_four {α : Type} (f : Fin 4 → α) : List.ofFn f = [f 0, f 1, f 2, f 3] := by
  simp [List.ofFn_succ]
theorem sigDigests_eq (s : Signature) : sigDigests s =
    [s.rho] ++ List.ofFn s.secrets ++ List.ofFn s.proof ++
      ((List.ofFn (s.layers 0).values ++ List.ofFn (s.layers 0).path) ++
      ((List.ofFn (s.layers 1).values ++ List.ofFn (s.layers 1).path) ++
      ((List.ofFn (s.layers 2).values ++ List.ofFn (s.layers 2).path) ++
      (List.ofFn (s.layers 3).values ++ List.ofFn (s.layers 3).path)))) := by
  unfold sigDigests
  rw [ofFn_four]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
theorem serialize_eq (s : Signature) : serialize s = (sigDigests s).flatMap (bytesLE 16) := by
  rw [sigDigests_eq]
  unfold serialize serializeLayer
  rw [ofFn_four]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil]

/-- Machine slot of layer `lay`'s first value (campaign T51: the 51 top values start at slot 140, so the top ends at
slot 190 as in #938; lower layers unchanged). -/
def layIdx (lay : Layer) : Nat := (![140, 203, 253, 302] : Layer → Nat) lay
section getD
theorem getD_append_left' {l₁ l₂ : List Digest} {k : Nat} (h : k < l₁.length) :
    (l₁ ++ l₂).getD k 0 = l₁.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem getD_append_right' {l₁ l₂ : List Digest} {k : Nat} (h : l₁.length ≤ k) :
    (l₁ ++ l₂).getD k 0 = l₂.getD (k - l₁.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]
theorem getD_ofFn' {n : Nat} (f : Fin n → Digest) (i : Nat) (hi : i < n) :
    (List.ofFn f).getD i 0 = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]
theorem chainCount_0 : chainCount 0 = 51 := rfl
theorem chainCount_1 : chainCount 1 = 43 := rfl
theorem chainCount_2 : chainCount 2 = 43 := rfl
theorem chainCount_3 : chainCount 3 = 43 := rfl
theorem height_0 : height 0 = 12 := rfl
theorem height_1 : height 1 = 7 := rfl
theorem height_2 : height 2 = 6 := rfl
theorem height_3 : height 3 = 6 := rfl
def layerList (s : Signature) (lay : Layer) : List Digest :=
  List.ofFn (s.layers lay).values ++ List.ofFn (s.layers lay).path
variable (s : Signature)
theorem length_layerList (lay : Layer) : (layerList s lay).length = chainCount lay + height lay := by
  simp only [layerList, List.length_append, List.length_ofFn]
theorem sigDigests_rho : (sigDigests s).getD 0 0 = s.rho := by
  rw [sigDigests_eq]; rfl
theorem sigDigests_secret (i : Nat) (hi : i < 21) : (sigDigests s).getD (1 + i) 0 = s.secrets ⟨i, hi⟩ := by
  have h1 : 1 + i < ([s.rho] ++ List.ofFn s.secrets ++ List.ofFn s.proof).length := by
    simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega
  have h2 : 1 + i < ([s.rho] ++ List.ofFn s.secrets).length := by
    simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega
  rw [sigDigests_eq, getD_append_left' h1, getD_append_left' h2,
    getD_append_right' (by simp only [List.length_singleton]; omega), List.length_singleton,
    Nat.add_sub_cancel_left, getD_ofFn']
theorem sigDigests_proof (j : Nat) (hj : j < 115) : (sigDigests s).getD (22 + j) 0 = s.proof ⟨j, hj⟩ := by
  have h1 : 22 + j < ([s.rho] ++ List.ofFn s.secrets ++ List.ofFn s.proof).length := by
    simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega
  have h2 : ([s.rho] ++ List.ofFn s.secrets).length ≤ 22 + j := by
    simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega
  rw [sigDigests_eq, getD_append_left' h1, getD_append_right' h2]
  simp only [List.length_append, List.length_singleton, List.length_ofFn]
  rw [show 22 + j - (1 + 21) = j by omega, getD_ofFn']
theorem sigDigests_tail (k : Nat) (hk : 137 ≤ k) : (sigDigests s).getD k 0 =
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3))).getD (k - 137) 0 := by
  have h1 : ([s.rho] ++ List.ofFn s.secrets ++ List.ofFn s.proof).length ≤ k := by
    simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega
  rw [sigDigests_eq, getD_append_right' h1]
  simp only [List.length_append, List.length_singleton, List.length_ofFn]
  rfl

end getD
def sigDig (b : Bytes 5616) (k : Nat) : Digest := b.extractLsb' (128 * k) 128
def sigDec (b : Bytes 5616) : Signature where
  rho := sigDig b 0
  secrets := fun i => sigDig b (1 + i.val)
  proof := fun j => sigDig b (22 + j.val)
  layers := fun lay => ⟨fun i => sigDig b (layIdx lay + i.val), fun j => sigDig b (layIdx lay + (chainCount lay + j.val))⟩
theorem pow_5728 : (2 : Nat) ^ (8 * 5616) = 2 ^ (128 * 351) := congrArg (fun n => 2 ^ n) rfl
def sigB (s : Signature) : Bytes 5616 := BitVec.ofNat _ (readLE (serialize s))
set_option exponentiation.threshold 50000 in
theorem sigDig_toNat (b : Bytes 5616) (k : Nat) : (sigDig b k).toNat = b.toNat / 2 ^ (128 * k) % 2 ^ 128 := by
  rw [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem layerList_sigDec (b : Bytes 5616) (lay : Layer) (i : Nat) (hi : i < chainCount lay + height lay) :
    (layerList (sigDec b) lay).getD i 0 = sigDig b (layIdx lay + i) := by
  unfold layerList
  by_cases hc : i < chainCount lay
  · rw [getD_append_left' (by simpa using hc), getD_ofFn' _ i hc]; rfl
  · rw [getD_append_right' (by simp; omega), List.length_ofFn, getD_ofFn' _ (i - chainCount lay) (by omega)]
    show sigDig b (layIdx lay + (chainCount lay + (i - chainCount lay))) = _
    rw [show chainCount lay + (i - chainCount lay) = i by omega]

set_option exponentiation.threshold 50000 in
theorem sigDig_lo (b : Bytes 5616) (k : Nat) : (sigDig b k).extractLsb' 0 64 = b.extractLsb' (64 * (2 * k)) 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
  rw [show 64 * (2 * k) = 128 * k by ring, Nat.mod_mod_of_dvd _ (by norm_num)]
theorem sigDig_hi (b : Bytes 5616) (k : Nat) :
    (sigDig b k).extractLsb' 64 64 = b.extractLsb' (64 * (2 * k + 1)) 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 64 * (2 * k + 1) = 128 * k + 64 by ring, pow_add, ← Nat.div_div_eq_div_mul]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod_of_dvd _ (by norm_num)]
end SigGolfCandidate.T3M
end
-- ==== merged from ClaudeWCT_W9_T3M_SigCodec ====
section

namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.T3M (digNat digNat_lt digNat_digit digNat_eq_of_digits getD_append_left' getD_append_right'
  getD_ofFn' ofFn_four chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)
open SphincsSecurity (bytesLE bytesLE_length)
def openingList (op : WCT9.Opening) : List Digest := List.ofFn op.values ++ List.ofFn op.path
def layerList (s : WCT9.Signature) (lay : Layer) : List Digest :=
  List.ofFn (s.layers lay).values ++ List.ofFn (s.layers lay).path
def sigDigests (s : WCT9.Signature) : List Digest :=
  [s.rho] ++ (List.ofFn s.openings).flatMap openingList ++
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3)))
theorem serializeOpening_eq (op : WCT9.Opening) :
    WCT9.serializeOpening op = (openingList op).flatMap (bytesLE 16) := by
  unfold WCT9.serializeOpening openingList
  rw [List.flatMap_append]
theorem serialize_eq (s : WCT9.Signature) : WCT9.serialize s = (sigDigests s).flatMap (bytesLE 16) := by
  unfold WCT9.serialize sigDigests
  rw [ofFn_four]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatten_cons,
    List.flatten_nil, layerList, serializeLayer, List.flatMap_assoc, ← serializeOpening_eq]
theorem length_openingList (op : WCT9.Opening) : (openingList op).length = 13 := by
  simp [openingList]
theorem length_layerList (s : WCT9.Signature) (lay : Layer) :
    (layerList s lay).length = chainCount lay + height lay := by
  simp only [layerList, List.length_append, List.length_ofFn]
theorem length_openings (s : WCT9.Signature) :
    ((List.ofFn s.openings).flatMap openingList).length = 117 := by
  rw [List.length_flatMap]
  simp only [List.map_ofFn, Function.comp_def, length_openingList]
  rfl

def layIdx (lay : Layer) : Nat := (![118, 184, 234, 283] : Layer → Nat) lay
section getD
theorem getD_flatMap_chunks {α β : Type} (f : α → List β) (n : Nat) (d : β) (hf : ∀ a, (f a).length = n) :
    ∀ (L : List α) k i (hk : k < L.length), i < n → (L.flatMap f).getD (n * k + i) d = (f L[k]).getD i d
  | [], k, _, hk, _ => by simp at hk
  | a :: L, k, i, hk, hi => by
      have hl : (f a).length = n := hf a
      rw [List.flatMap_cons]
      rcases k with _ | k
      · simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < (f a).length by omega)]
      · simp only [List.getElem_cons_succ]
        have := getD_flatMap_chunks f n d hf L k i (by simpa using hk) hi
        simp only [List.getD_eq_getElem?_getD] at this ⊢
        rw [List.getElem?_append_right (show (f a).length ≤ n * (k + 1) + i by rw [hl]; nlinarith),
          show n * (k + 1) + i - (f a).length = n * k + i by rw [hl]; ring_nf; omega, this]
variable (s : WCT9.Signature)
theorem sigDigests_rho : (sigDigests s).getD 0 0 = s.rho := by
  unfold sigDigests; rfl
theorem sigDigests_opening (k : WCT9.Coord) (i : Nat) (hi : i < 13) :
    (sigDigests s).getD (1 + 13 * k.val + i) 0 = (openingList (s.openings k)).getD i 0 := by
  have hk := k.isLt
  unfold sigDigests
  rw [getD_append_left' (by simp only [List.length_append, List.length_singleton, length_openings]; omega),
    getD_append_right' (by simp; omega), List.length_singleton,
    show 1 + 13 * k.val + i - 1 = 13 * k.val + i by omega,
    getD_flatMap_chunks openingList 13 0 length_openingList _ k.val i (by simp [hk]) hi, List.getElem_ofFn]
theorem sigDigests_value (k : WCT9.Coord) (t : Fin 6) :
    (sigDigests s).getD (1 + 13 * k.val + t.val) 0 = (s.openings k).values t := by
  rw [sigDigests_opening s k t.val (by omega), openingList, getD_append_left' (by simp), getD_ofFn']
theorem sigDigests_path (k : WCT9.Coord) (l : Fin 7) :
    (sigDigests s).getD (1 + 13 * k.val + 6 + l.val) 0 = (s.openings k).path l := by
  rw [show 1 + 13 * k.val + 6 + l.val = 1 + 13 * k.val + (6 + l.val) by omega,
    sigDigests_opening s k _ (by omega), openingList, getD_append_right' (by simp), List.length_ofFn,
    Nat.add_sub_cancel_left, getD_ofFn']
theorem sigDigests_tail (k : Nat) (hk : 118 ≤ k) : (sigDigests s).getD k 0 =
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3))).getD (k - 118) 0 := by
  unfold sigDigests
  rw [getD_append_right' (by simp only [List.length_append, List.length_singleton, length_openings]; omega)]
  simp only [List.length_append, List.length_singleton, length_openings]

end getD
def sigDig (b : Bytes 5312) (k : Nat) : Digest := b.extractLsb' (128 * k) 128
def sigDec (b : Bytes 5312) : WCT9.Signature where
  rho := sigDig b 0
  openings := fun k => ⟨fun t => sigDig b (1 + 13 * k.val + t.val), fun l => sigDig b (1 + 13 * k.val + 6 + l.val)⟩
  layers := fun lay => ⟨fun i => sigDig b (layIdx lay + i.val), fun j => sigDig b (layIdx lay + (chainCount lay + j.val))⟩
theorem pow_5312 : (2 : Nat) ^ (8 * 5312) = 2 ^ (128 * 332) := congrArg (fun n => 2 ^ n) rfl
def sigB (s : WCT9.Signature) : Bytes 5312 := BitVec.ofNat _ (readLE (WCT9.serialize s))
set_option exponentiation.threshold 50000 in
theorem sigDig_toNat (b : Bytes 5312) (k : Nat) : (sigDig b k).toNat = b.toNat / 2 ^ (128 * k) % 2 ^ 128 := by
  rw [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

set_option exponentiation.threshold 50000 in
theorem sigDig_lo (b : Bytes 5312) (k : Nat) : (sigDig b k).extractLsb' 0 64 = b.extractLsb' (64 * (2 * k)) 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
  rw [show 64 * (2 * k) = 128 * k by ring, Nat.mod_mod_of_dvd _ (by norm_num)]
theorem sigDig_hi (b : Bytes 5312) (k : Nat) :
    (sigDig b k).extractLsb' 64 64 = b.extractLsb' (64 * (2 * k + 1)) 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 64 * (2 * k + 1) = 128 * k + 64 by ring, pow_add, ← Nat.div_div_eq_div_mul]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod_of_dvd _ (by norm_num)]
end ClaudeWCT.W9.T3M
end
-- ==== merged from ClaudeWCT_W9_T3M_SigCodecC ====
section

/-! # The compact (H2) signature bytes

5,310 bytes: the 332 digests of `sigDigests` with digest 183 (the top layer's level-11 sibling) cut out, then that
digest's low 14 bytes. `sigBC` encodes, `sigDecC` decodes (the omitted 16 bits decode as zero), and
`sigDecC (sigBC σ) = proj σ`, `sigBC (sigDecC b) = b`, `sigBC (proj σ) = sigBC σ`. -/

namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.T3M (digNat digNat_lt digNat_digit digNat_eq_of_digits getD_append_left' getD_append_right'
  getD_ofFn' chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)
set_option maxRecDepth 10000

abbrev CBytes := Bytes 5310
def sibIdx : Nat := 183
def cDig (b : CBytes) (k : Nat) : Digest := b.extractLsb' (128 * k) 128
/-- The digest at full-layout index `k` of the compact bytes. -/
def digC (b : CBytes) (k : Nat) : Digest :=
  if k < 183 then cDig b k else if k = 183 then cDig b 331 else cDig b (k - 1)
def sigDecC (b : CBytes) : WCT9.Signature where
  rho := digC b 0
  openings := fun k => ⟨fun t => digC b (1 + 13 * k.val + t.val), fun l => digC b (1 + 13 * k.val + 6 + l.val)⟩
  layers := fun lay => ⟨fun i => digC b (layIdx lay + i.val), fun j => digC b (layIdx lay + (chainCount lay + j.val))⟩
def sigBC (s : WCT9.Signature) : CBytes :=
  BitVec.ofNat _ (digNat ((sigDigests s).eraseIdx 183) + 2 ^ (128 * 331) * (((sigDigests s).getD 183 0).toNat % 2 ^ 112))


theorem cDig_toNat (b : CBytes) (k : Nat) : (cDig b k).toNat = b.toNat / 2 ^ (128 * k) % 2 ^ 128 := by
  rw [cDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem cTail_lt (b : CBytes) : b.toNat / 2 ^ (128 * 331) < 2 ^ 112 := by
  have hb := b.isLt
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  exact lt_of_lt_of_eq hb (by norm_num)

theorem getD_eraseIdx {α : Type} (l : List α) (i j : Nat) (d : α) :
    (l.eraseIdx i).getD j d = if j < i then l.getD j d else l.getD (j + 1) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
  split <;> rfl


theorem mod_digit (B n k : Nat) (hk : k < n) :
    B % 2 ^ (128 * n) / 2 ^ (128 * k) % 2 ^ 128 = B / 2 ^ (128 * k) % 2 ^ 128 := by
  rw [show 2 ^ (128 * n) = 2 ^ (128 * k) * 2 ^ (128 * (n - k)) by rw [← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact pow_dvd_pow 2 (by omega)

theorem lt_split (X y A M : Nat) (hX : X < 2 ^ A) (hy : y < M) : X + 2 ^ A * y < 2 ^ A * M := by
  have : 2 ^ A * y + 2 ^ A ≤ 2 ^ A * M := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hy
  omega

theorem split_mod (D T A : Nat) (hD : D < 2 ^ A) : (D + 2 ^ A * T) % 2 ^ A = D := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hD]

theorem split_div (D T A : Nat) (hD : D < 2 ^ A) : (D + 2 ^ A * T) / 2 ^ A = T := by
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hD, Nat.zero_add]

theorem pow_5310 : (2 : Nat) ^ (8 * 5310) = 2 ^ (128 * 331) * 2 ^ 112 := by rw [← pow_add]

set_option exponentiation.threshold 50000 in



theorem digC_183 (b : CBytes) : digC b 183 = cDig b 331 := by
  unfold digC; rw [if_neg (by decide), if_pos rfl]

end ClaudeWCT.W9.T3M

namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.T3M (digNat digNat_lt digNat_cons digNat_nil)

/-- Full-layout digest index of compact digest slot `k` (slot 331 holds the top sibling). -/
def cIdx (k : Nat) : Nat := if k < 183 then k else if k < 331 then k + 1 else 183
def compactList (s : WCT9.Signature) : List Digest := (List.range 332).map fun k => (sigDigests s).getD (cIdx k) 0

theorem digNat_append (L1 L2 : List Digest) : digNat (L1 ++ L2) = digNat L1 + 2 ^ (128 * L1.length) * digNat L2 := by
  induction L1 with
  | nil => simp [digNat_nil]
  | cons d L ih =>
    rw [List.cons_append, digNat_cons, digNat_cons, ih, List.length_cons,
      show 128 * (L.length + 1) = 128 + 128 * L.length by ring, pow_add]
    ring


theorem mod_split (X y A M : Nat) (hX : X < 2 ^ A) (hM : 0 < M) :
    (X + 2 ^ A * y) % (2 ^ A * M) = X + 2 ^ A * (y % M) := by
  conv_lhs => rw [← Nat.div_add_mod y M]
  rw [show X + 2 ^ A * (M * (y / M) + y % M) = (X + 2 ^ A * (y % M)) + (2 ^ A * M) * (y / M) by ring,
    Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have hr : y % M < M := Nat.mod_lt _ hM
  have h1 : 2 ^ A * (y % M) + 2 ^ A ≤ 2 ^ A * M := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
  omega
end ClaudeWCT.W9.T3M

/-! Compact serialization for the shared forest. -/
namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
abbrev SharedSignature := SigGolfCandidate.Research.SharedForest.Signature
open SigGolfCandidate.T3M (digNat getD_append_left' getD_append_right' getD_ofFn'
  chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)

def pairList (p : PairOpening) : List Digest :=
  ((List.ofFn p.firstValues ++ List.ofFn p.firstPath) ++
    List.ofFn p.secondValues) ++ List.ofFn p.secondPath
def singletonList (p : SingletonOpening) : List Digest :=
  List.ofFn p.values ++ List.ofFn p.path
def layerList (s : SharedSignature) (lay : Layer) : List Digest :=
  List.ofFn (s.layers lay).values ++ List.ofFn (s.layers lay).path
def sigDigests (s : SharedSignature) : List Digest :=
  (([s.rho] ++ (List.ofFn s.forest.pairs).flatMap pairList) ++ singletonList s.forest.singleton) ++
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3)))
/-- T51: top values at 114..164, top path 165..176, L1 at 177, L2 at 227, L3 at 276 (325 digests). -/
def layIdx (lay : Layer) : Nat := (![114,177,227,276] : Layer → Nat) lay
theorem pairList_length (p : PairOpening) : (pairList p).length = 25 := by simp [pairList]
theorem singletonList_length (p : SingletonOpening) : (singletonList p).length = 13 := by
  simp [singletonList]
theorem pairs_length (s : SharedSignature) : ((List.ofFn s.forest.pairs).flatMap pairList).length = 100 := by
  rw [List.length_flatMap]
  simp only [List.map_ofFn, Function.comp_def, pairList_length]
  rfl
theorem layerList_length (s : SharedSignature) (lay : Layer) :
    (layerList s lay).length = chainCount lay + height lay := by
  simp only [layerList, List.length_append, List.length_ofFn]
theorem sigDigests_length (s : SharedSignature) : (sigDigests s).length = 325 := by
  simp only [sigDigests, List.length_append, List.length_singleton, pairs_length,
    singletonList_length, layerList_length]
  rfl

/-- T51: the 5,195-byte compact signature (324 digests + an 11-byte tail; #938 img-v6: 5,239 bytes). -/
abbrev CBytes := Bytes 5195
def cDig (b : CBytes) (k : Nat) : Digest := b.extractLsb' (128 * k) 128
/-- Offset of the X field in the top `b_j = topZeroBits j` bits of the path node at height `j` (`j = 1..10`):
`Σ_{h < j} b_h` = 0, 1, 2, 4, 7, 11, 16, 22 for `j = 3..10` (heights 1, 2 carry no bits). -/
def xOff (j : Nat) : Nat := ((List.range j).map topZeroBits).sum
def clearTop (j : Nat) (d : Digest) : Digest := BitVec.ofNat 128 (d.toNat % 2 ^ (128 - j))
def topBits (j : Nat) (d : Digest) : Nat := d.toNat / 2 ^ (128 - j)
/-- T51: the 29-bit X field read from the top `b_j` bits of the path nodes of heights 3..10 (digests 168..175). -/
def xOfB (b : CBytes) : Nat :=
  topBits 1 (cDig b 168) + topBits 1 (cDig b 169) * 2 ^ 1 + topBits 2 (cDig b 170) * 2 ^ 2 +
  topBits 3 (cDig b 171) * 2 ^ 4 + topBits 4 (cDig b 172) * 2 ^ 7 + topBits 5 (cDig b 173) * 2 ^ 11 +
  topBits 6 (cDig b 174) * 2 ^ 16 + topBits 7 (cDig b 175) * 2 ^ 22
/-- Decoded digest `k`: the path nodes of heights 1..10 (digests 166..175) lose their top `b_j` bits; index 176 (top
sibling) = tail 88 bits + X bits 0..15 (bits 88..103; bits 104..127 zero, 112..127 brute-forced by expand). -/
def digC (b : CBytes) (k : Nat) : Digest :=
  if k < 176 then (if 166 ≤ k then clearTop (topZeroBits (k - 165)) (cDig b k) else cDig b k)
  else if k = 176 then BitVec.ofNat 128 (b.toNat / 2 ^ (128 * 324) % 2 ^ 88 + xOfB b % 2 ^ 16 * 2 ^ 88)
  else cDig b (k - 1)
def sigDecC (b : CBytes) : SharedSignature where
  rho := digC b 0
  policyHints := BitVec.ofNat 16 (xOfB b / 2 ^ 16)
  forest := {
    pairs := fun p => {
      firstValues := fun i => digC b (1 + 25 * p.val + i.val)
      firstPath := fun i => digC b (1 + 25 * p.val + 6 + i.val)
      secondValues := fun i => digC b (1 + 25 * p.val + 12 + i.val)
      secondPath := fun i => digC b (1 + 25 * p.val + 18 + i.val) }
    singleton := {
      values := fun i => digC b (101 + i.val)
      path := fun i => digC b (107 + i.val) } }
  layers := fun lay => {
    values := fun i => digC b (layIdx lay + i.val)
    path := fun i => digC b (layIdx lay + chainCount lay + i.val) }
/-- T51: X = top sibling bits 88..103 (16) | hint (13 bits) << 16 (29 bits). -/
def xField (s : SharedSignature) : Nat :=
  ((sigDigests s).getD 176 0).toNat / 2 ^ 88 % 2 ^ 16 + s.policyHints.toNat % 2 ^ 13 * 2 ^ 16
/-- T51: the path node of height `j` with X bits `xOff j ..` in its top `b_j = topZeroBits j` bits. -/
def packD (j : Nat) (d : Digest) (x : Nat) : Digest :=
  BitVec.ofNat 128 (d.toNat % 2 ^ (128 - topZeroBits j) +
    x / 2 ^ xOff j % 2 ^ topZeroBits j * 2 ^ (128 - topZeroBits j))
def encList (s : SharedSignature) : List Digest :=
  (List.range 324).map fun k => if 166 ≤ k ∧ k ≤ 175 then packD (k - 165) (((sigDigests s).eraseIdx 176).getD k 0)
    (xField s) else ((sigDigests s).eraseIdx 176).getD k 0
def sigBC (s : SharedSignature) : CBytes :=
  BitVec.ofNat _ (digNat (encList s) + 2 ^ (128 * 324) * (((sigDigests s).getD 176 0).toNat % 2 ^ 88))
theorem compact_length : 324 * 16 + 11 = 5195 := by decide
/-- The normal form a decoded signature has (T51): path tops of heights 1..10 clear (`b_j` bits), top sibling below
bit 104, hint 13 bits. -/
def normD (k : Nat) (d : Digest) : Digest :=
  if 166 ≤ k ∧ k ≤ 175 then clearTop (topZeroBits (k - 165)) d
  else if k = 176 then BitVec.ofNat 128 (d.toNat % 2 ^ 104) else d
theorem normD_of_lt (k : Nat) (d : Digest) (hk : k < 166) : normD k d = d := by
  unfold normD; rw [if_neg (by omega), if_neg (by omega)]
theorem sigDigests_rho (s : SharedSignature) : (sigDigests s).getD 0 0 = s.rho := by rfl
theorem sigDigests_pair (s : SharedSignature) (p : Fin 4) (i : Nat) (hi : i < 25) :
    (sigDigests s).getD (1 + 25 * p.val + i) 0 = (pairList (s.forest.pairs p)).getD i 0 := by
  unfold sigDigests
  rw [getD_append_left' (by simp only [List.length_append, List.length_singleton,
        pairs_length, singletonList_length]; omega),
    getD_append_left' (by simp only [List.length_append, List.length_singleton, pairs_length]; omega),
    getD_append_right' (by simp; omega), List.length_singleton,
    show 1 + 25 * p.val + i - 1 = 25 * p.val + i by omega,
    ClaudeWCT.W9.T3M.getD_flatMap_chunks pairList 25 0 pairList_length _ p.val i (by simp) hi,
    List.getElem_ofFn]
theorem pairList_firstValue (p : PairOpening) (i : Fin 6) :
    (pairList p).getD i.val 0 = p.firstValues i := by
  unfold pairList
  rw [getD_append_left' (by simp; omega), getD_append_left' (by simp; omega),
    getD_append_left' (by simp), getD_ofFn']
theorem pairList_firstPath (p : PairOpening) (i : Fin 6) :
    (pairList p).getD (6 + i.val) 0 = p.firstPath i := by
  unfold pairList
  rw [getD_append_left' (by simp; omega), getD_append_left' (by simp; omega),
    getD_append_right' (by simp), List.length_ofFn, Nat.add_sub_cancel_left, getD_ofFn']
theorem pairList_secondValue (p : PairOpening) (i : Fin 6) :
    (pairList p).getD (12 + i.val) 0 = p.secondValues i := by
  unfold pairList
  rw [getD_append_left' (by simp; omega), getD_append_right' (by simp)]
  simp only [List.length_append, List.length_ofFn]
  rw [show 12 + i.val - (6 + 6) = i.val by omega, getD_ofFn']
theorem pairList_secondPath (p : PairOpening) (i : Fin 7) :
    (pairList p).getD (18 + i.val) 0 = p.secondPath i := by
  unfold pairList
  rw [getD_append_right' (by simp)]
  simp only [List.length_append, List.length_ofFn]
  rw [show 18 + i.val - (6 + 6 + 6) = i.val by omega, getD_ofFn']
theorem sigDigests_singleton (s : SharedSignature) (i : Nat) (hi : i < 13) :
    (sigDigests s).getD (101 + i) 0 = (singletonList s.forest.singleton).getD i 0 := by
  unfold sigDigests
  rw [getD_append_left' (by simp only [List.length_append, List.length_singleton,
      pairs_length, singletonList_length]; omega), getD_append_right' (by
      simp only [List.length_append, List.length_singleton, pairs_length]; omega)]
  simp only [List.length_append, List.length_singleton, pairs_length]
  rw [show 101 + i - (1 + 100) = i by omega]
theorem sigDigests_tail (s : SharedSignature) (k : Nat) (hk : 114 ≤ k) : (sigDigests s).getD k 0 =
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3))).getD (k - 114) 0 := by
  unfold sigDigests
  rw [getD_append_right' (by simp only [List.length_append, List.length_singleton, pairs_length, singletonList_length]; omega)]
  simp only [List.length_append, List.length_singleton, pairs_length, singletonList_length]
theorem sigDigests_layer (s : SharedSignature) (lay : Layer) (i : Nat) (hi : i < chainCount lay + height lay) :
    (sigDigests s).getD (layIdx lay + i) 0 = (layerList s lay).getD i 0 := by
  have l0 := layerList_length s 0
  have l1 := layerList_length s 1
  have l2 := layerList_length s 2
  rw [chainCount_0, height_0] at l0
  rw [chainCount_1, height_1] at l1
  rw [chainCount_2, height_2] at l2
  fin_cases lay
  · show (sigDigests s).getD (114 + i) 0 = (layerList s 0).getD i 0
    have hi' : i < 63 := hi
    rw [sigDigests_tail s _ (by omega), show 114 + i - 114 = i by omega, getD_append_left' (by omega)]
  · show (sigDigests s).getD (177 + i) 0 = (layerList s 1).getD i 0
    have hi' : i < 50 := hi
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_left' (by omega),
      show 177 + i - 114 - 63 = i by omega]
  · show (sigDigests s).getD (227 + i) 0 = (layerList s 2).getD i 0
    have hi' : i < 49 := hi
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_right' (by omega), l1,
      getD_append_left' (by omega), show 227 + i - 114 - 63 - 50 = i by omega]
  · show (sigDigests s).getD (276 + i) 0 = (layerList s 3).getD i 0
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_right' (by omega), l1,
      getD_append_right' (by omega), l2, show 276 + i - 114 - 63 - 50 - 49 = i by omega]
theorem sigDigests_layValue (s : SharedSignature) (lay : Layer) (i : Nat) (hi : i < chainCount lay) :
    (sigDigests s).getD (layIdx lay + i) 0 = (s.layers lay).values ⟨i, hi⟩ := by
  rw [sigDigests_layer s lay i (by omega), layerList, getD_append_left' (by simpa using hi), getD_ofFn']
theorem sigDigests_layPath (s : SharedSignature) (lay : Layer) (j : Nat) (hj : j < height lay) :
    (sigDigests s).getD (layIdx lay + (chainCount lay + j)) 0 = (s.layers lay).path ⟨j, hj⟩ := by
  rw [sigDigests_layer s lay _ (by omega), layerList, getD_append_right' (by simp), List.length_ofFn,
    Nat.add_sub_cancel_left, getD_ofFn']

end ClaudeWCT.W9.T3M.SharedCodec


namespace ClaudeWCT.W9.T3M.SharedCodec
/-- Internal expansion retains the four unused seventh A-path slots. T51: the expander's slot layout keeps #938's
lower-layer slots, so the top path follows the 51 top values (slots 169..180) and three unused slots 181..183 precede
L1 (slot 184): digest `k` sits at slot `k + 4` for `114 ≤ k ≤ 176`, `k + 7` for `k ≥ 177`. -/
def internalFullIndex (k : Nat) : Nat :=
  k + (if 13 ≤ k then 1 else 0) + (if 38 ≤ k then 1 else 0) +
    (if 63 ≤ k then 1 else 0) + (if 88 ≤ k then 1 else 0) + (if 177 ≤ k then 3 else 0)
def externalFullIndex (k : Nat) : Nat :=
  k - ((if 13 < k then 1 else 0) + (if 39 < k then 1 else 0) +
    (if 65 < k then 1 else 0) + (if 91 < k then 1 else 0) + (if 183 < k then 3 else 0))
def internalDummy (k : Nat) : Bool := decide (k = 13 ∨ k = 39 ∨ k = 65 ∨ k = 91 ∨ k = 181 ∨ k = 182 ∨ k = 183)
theorem internalFullIndex_spec (k : Nat) :
    internalFullIndex k = k + (([13,38,63,88].filter fun skip => decide (skip ≤ k)).length) +
      (if 177 ≤ k then 3 else 0) := by
  unfold internalFullIndex
  by_cases h13 : 13 ≤ k <;> by_cases h38 : 38 ≤ k <;> by_cases h63 : 63 ≤ k <;> by_cases h88 : 88 ≤ k <;>
    simp [h13, h38, h63, h88] <;> omega

theorem internalFullIndex_bound (k : Nat) (hk : k < 325) : internalFullIndex k < 332 := by
  unfold internalFullIndex
  split_ifs <;> omega
theorem internalFullIndex_dummy (k : Nat) : internalDummy (internalFullIndex k) = false := by
  simp only [internalDummy, decide_eq_false_iff_not]
  unfold internalFullIndex
  split_ifs <;> omega
theorem internalFullIndex_inverse (k : Nat) : externalFullIndex (internalFullIndex k) = k := by
  unfold externalFullIndex internalFullIndex
  split_ifs <;> omega
def inflatedRead {α : Type} (zero : α) (read : Nat → α) (k : Nat) : α :=
  if internalDummy k then zero else read (externalFullIndex k)
theorem inflatedRead_internal {α : Type} (zero : α) (read : Nat → α) (k : Nat) :
    inflatedRead zero read (internalFullIndex k) = read k := by
  simp only [inflatedRead, internalFullIndex_dummy, Bool.false_eq_true, ↓reduceIte,
    internalFullIndex_inverse]
theorem internalFullIndex_main (k : Nat) (hk : 114 ≤ k) (hk' : k ≤ 176) : internalFullIndex k = k + 4 := by
  unfold internalFullIndex
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)]
theorem internalFullIndex_lower (k : Nat) (hk : 177 ≤ k) : internalFullIndex k = k + 7 := by
  unfold internalFullIndex
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos hk]
theorem internalFullIndex_tail : internalFullIndex 176 = 180 := by rfl
end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.T3
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def serializedWord (read : Nat → BitVec 64) (k : Nat) : BitVec 64 :=
  if k < 26 then read k else if k < 28 then 0 else
  if k < 78 then read (k - 2) else if k < 80 then 0 else
  if k < 130 then read (k - 4) else if k < 132 then 0 else
  if k < 182 then read (k - 6) else if k < 184 then 0 else
  if k < 366 then read (k - 8) else if k = 366 then read 654 else
  if k = 367 then (read 655 <<< 16) >>> 16 else read (k - 10)

theorem externalFullIndex_tail_iff (k : Nat) : externalFullIndex k = 176 ↔ k = 180 := by
  unfold externalFullIndex
  split_ifs <;> omega

theorem extract_digest_word {n : Nat} (x : BitVec n) (a i : Nat) (hi : i < 2) :
    (x.extractLsb' a 128).extractLsb' (64*i) 64 = x.extractLsb' (a+64*i) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rw [show decide (64*i+j < 128) = true from decide_eq_true (by omega), Bool.true_and]
  congr 1
  omega

end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (digNat digNat_lt digNat_digit)
open ClaudeWCT.W9.T3M (getD_eraseIdx mod_digit lt_split split_mod split_div)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

theorem length_eraseIdx_sig (s : SharedSignature) :
    ((sigDigests s).eraseIdx 176).length = 324 := by
  rw [List.length_eraseIdx,sigDigests_length];decide

theorem encList_length (s : SharedSignature) : (encList s).length = 324 := by simp [encList]

theorem encList_getD (s : SharedSignature) (k : Nat) (hk : k < 324) :
    (encList s).getD k 0 = if 166 ≤ k ∧ k ≤ 175 then packD (k - 165) (((sigDigests s).eraseIdx 176).getD k 0)
      (xField s) else ((sigDigests s).eraseIdx 176).getD k 0 := by
  simp [encList, List.getD_eq_getElem?_getD, hk]

theorem sigBC_toNat (s : SharedSignature) :
    (sigBC s).toNat = digNat (encList s) + 2^(128*324)*(((sigDigests s).getD 176 0).toNat%2^88) := by
  unfold sigBC
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hD := digNat_lt (encList s)
  rw [encList_length] at hD
  have hT := lt_split _ _ _ _ hD (Nat.mod_lt ((sigDigests s).getD 176 0).toNat (show 0<2^88 by positivity))
  simpa only [←pow_add] using hT

theorem encoded_low (s : SharedSignature) : (sigBC s).toNat%2^(128*324)=digNat (encList s) := by
  have hD := digNat_lt (encList s)
  rw [encList_length] at hD
  rw [sigBC_toNat, split_mod _ _ _ hD]

theorem encoded_tail (s : SharedSignature) :
    (sigBC s).toNat/2^(128*324)%2^88=((sigDigests s).getD 176 0).toNat%2^88 := by
  have hD := digNat_lt (encList s)
  rw [encList_length] at hD
  rw [sigBC_toNat, split_div _ _ _ hD, Nat.mod_mod]

theorem cDig_sigBC (s : SharedSignature) (j : Nat) (hj : j<324) : cDig (sigBC s) j=(encList s).getD j 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [cDig,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,←digNat_digit]
  rw [←mod_digit _ 324 j hj,encoded_low]

theorem pack_gen (b : Nat) (hb : b ≤ 128) (d : Digest) (y : Nat) :
    clearTop b (BitVec.ofNat 128 (d.toNat % 2 ^ (128 - b) + y % 2 ^ b * 2 ^ (128 - b))) = clearTop b d ∧
      topBits b (BitVec.ofNat 128 (d.toNat % 2 ^ (128 - b) + y % 2 ^ b * 2 ^ (128 - b))) = y % 2 ^ b := by
  have hd : d.toNat % 2 ^ (128 - b) < 2 ^ (128 - b) := Nat.mod_lt _ (by positivity)
  have hf : y % 2 ^ b < 2 ^ b := Nat.mod_lt _ (by positivity)
  have hlt : d.toNat % 2 ^ (128 - b) + y % 2 ^ b * 2 ^ (128 - b) < 2 ^ 128 := by
    have : y % 2 ^ b * 2 ^ (128 - b) ≤ (2 ^ b - 1) * 2 ^ (128 - b) := Nat.mul_le_mul_right _ (by omega)
    have e : (2 ^ b - 1) * 2 ^ (128 - b) + 2 ^ (128 - b) = 2 ^ 128 := by
      rw [Nat.sub_mul, one_mul, ← pow_add, show b + (128 - b) = 128 by omega]
      have : 2 ^ (128 - b) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  unfold clearTop topBits
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_right, Nat.mod_mod]
  · rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hd, zero_add]

theorem topZeroBits_le_eight (j : Nat) (hj : j ≤ 11) : topZeroBits j ≤ 8 := by interval_cases j <;> decide

/-- T51: the X bits stored in the top `b_j = topZeroBits j` bits of a packed path node (`b` names `b_j`). -/
theorem pack_facts (j b : Nat) (hj : 1 ≤ j ∧ j ≤ 10) (hb : topZeroBits j = b) (d : Digest) (x : Nat) :
    clearTop b (packD j d x) = clearTop b d ∧ topBits b (packD j d x) = x / 2 ^ xOff j % 2 ^ b := by
  subst hb
  exact pack_gen (topZeroBits j) (by have := topZeroBits_le_eight j (by omega); omega) d (x / 2 ^ xOff j)

theorem xOff_vals : xOff 3 = 0 ∧ xOff 4 = 1 ∧ xOff 5 = 2 ∧ xOff 6 = 4 ∧ xOff 7 = 7 ∧ xOff 8 = 11 ∧ xOff 9 = 16 ∧
    xOff 10 = 22 := by decide

theorem xField_lt (s : SharedSignature) : xField s < 2 ^ 29 := by
  unfold xField
  have h1 := Nat.mod_lt (((sigDigests s).getD 176 0).toNat / 2 ^ 88) (show 0 < 2 ^ 16 by positivity)
  have h2 := Nat.mod_lt s.policyHints.toNat (show 0 < 2 ^ 13 by positivity)
  omega

theorem xOfB_sigBC (s : SharedSignature) : xOfB (sigBC s) = xField s := by
  have hx := xField_lt s
  obtain ⟨o3, o4, o5, o6, o7, o8, o9, o10⟩ := xOff_vals
  unfold xOfB
  simp only [cDig_sigBC s _ (by norm_num : (168:Nat) < 324), cDig_sigBC s _ (by norm_num : (169:Nat) < 324),
    cDig_sigBC s _ (by norm_num : (170:Nat) < 324), cDig_sigBC s _ (by norm_num : (171:Nat) < 324),
    cDig_sigBC s _ (by norm_num : (172:Nat) < 324), cDig_sigBC s _ (by norm_num : (173:Nat) < 324),
    cDig_sigBC s _ (by norm_num : (174:Nat) < 324), cDig_sigBC s _ (by norm_num : (175:Nat) < 324)]
  simp only [encList_getD s _ (by norm_num : (168:Nat) < 324), encList_getD s _ (by norm_num : (169:Nat) < 324),
    encList_getD s _ (by norm_num : (170:Nat) < 324), encList_getD s _ (by norm_num : (171:Nat) < 324),
    encList_getD s _ (by norm_num : (172:Nat) < 324), encList_getD s _ (by norm_num : (173:Nat) < 324),
    encList_getD s _ (by norm_num : (174:Nat) < 324), encList_getD s _ (by norm_num : (175:Nat) < 324)]
  norm_num only [if_true, and_self, ite_true]
  rw [(pack_facts 3 1 (by norm_num) rfl _ _).2, (pack_facts 4 1 (by norm_num) rfl _ _).2,
    (pack_facts 5 2 (by norm_num) rfl _ _).2, (pack_facts 6 3 (by norm_num) rfl _ _).2,
    (pack_facts 7 4 (by norm_num) rfl _ _).2, (pack_facts 8 5 (by norm_num) rfl _ _).2,
    (pack_facts 9 6 (by norm_num) rfl _ _).2, (pack_facts 10 7 (by norm_num) rfl _ _).2,
    o3, o4, o5, o6, o7, o8, o9, o10]
  norm_num
  omega

theorem digC_sigBC (s : SharedSignature) (k : Nat) (hk : k<325) :
    digC (sigBC s) k = normD k ((sigDigests s).getD k 0) := by
  by_cases hlt : k<176
  · rw [digC, if_pos hlt, cDig_sigBC s k (by omega), encList_getD s k (by omega), getD_eraseIdx, if_pos hlt]
    by_cases hp : 166 ≤ k
    · rw [if_pos hp, if_pos ⟨hp, by omega⟩, (pack_facts _ _ ⟨by omega, by omega⟩ rfl _ _).1, normD,
        if_pos ⟨hp, by omega⟩]
    · rw [if_neg hp, if_neg (by omega), normD_of_lt _ _ (by omega)]
  · by_cases he : k=176
    · subst he
      rw [digC, if_neg (by decide), if_pos rfl, encoded_tail, xOfB_sigBC, normD, if_neg (by decide), if_pos rfl]
      congr 1
      unfold xField
      have h88 := Nat.mod_lt (((sigDigests s).getD 176 0).toNat / 2 ^ 88) (show 0 < 2 ^ 16 by positivity)
      have hm : ((sigDigests s).getD 176 0).toNat % 2 ^ 104 =
          ((sigDigests s).getD 176 0).toNat % 2 ^ 88 + 2 ^ 88 * (((sigDigests s).getD 176 0).toNat / 2 ^ 88 % 2 ^ 16) := by
        rw [show (2:Nat) ^ 104 = 2 ^ 88 * 2 ^ 16 by norm_num, Nat.mod_mul]
      rw [hm]
      omega
    · rw [digC, if_neg hlt, if_neg he, cDig_sigBC s (k-1) (by omega), encList_getD s _ (by omega),
        if_neg (by omega), getD_eraseIdx, if_neg (by omega), show k-1+1=k by omega, normD, if_neg (by omega),
        if_neg he]

theorem policyHints_sigDecC_sigBC (s : SharedSignature) :
    (sigDecC (sigBC s)).policyHints = BitVec.ofNat 16 (s.policyHints.toNat % 2 ^ 13) := by
  change BitVec.ofNat 16 (xOfB (sigBC s) / 2 ^ 16) = _
  rw [xOfB_sigBC]
  unfold xField
  congr 1
  have h1 := Nat.mod_lt (((sigDigests s).getD 176 0).toNat / 2 ^ 88) (show 0 < 2 ^ 16 by positivity)
  omega

end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (getD_append_left' getD_append_right' getD_ofFn')
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem forest_sigDecC_sigBC (s : SharedSignature) :
    (sigDecC (sigBC s)).forest=s.forest := by
  have hp : (sigDecC (sigBC s)).forest.pairs=s.forest.pairs := by
    funext p
    have h1 : ((sigDecC (sigBC s)).forest.pairs p).firstValues=(s.forest.pairs p).firstValues := by
      funext i
      change digC (sigBC s) (1+25*p.val+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),sigDigests_pair s p i.val (by omega),pairList_firstValue]
    have h2 : ((sigDecC (sigBC s)).forest.pairs p).firstPath=(s.forest.pairs p).firstPath := by
      funext i
      change digC (sigBC s) (1+25*p.val+6+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),show 1+25*p.val+6+i.val=1+25*p.val+(6+i.val) by omega,
        sigDigests_pair s p (6+i.val) (by omega),pairList_firstPath]
    have h3 : ((sigDecC (sigBC s)).forest.pairs p).secondValues=(s.forest.pairs p).secondValues := by
      funext i
      change digC (sigBC s) (1+25*p.val+12+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),show 1+25*p.val+12+i.val=1+25*p.val+(12+i.val) by omega,
        sigDigests_pair s p (12+i.val) (by omega),pairList_secondValue]
    have h4 : ((sigDecC (sigBC s)).forest.pairs p).secondPath=(s.forest.pairs p).secondPath := by
      funext i
      change digC (sigBC s) (1+25*p.val+18+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),show 1+25*p.val+18+i.val=1+25*p.val+(18+i.val) by omega,
        sigDigests_pair s p (18+i.val) (by omega),pairList_secondPath]
    cases h : (sigDecC (sigBC s)).forest.pairs p
    cases h' : s.forest.pairs p
    simp only [h,h'] at h1 h2 h3 h4
    cases h1;cases h2;cases h3;cases h4;rfl
  have hs : (sigDecC (sigBC s)).forest.singleton=s.forest.singleton := by
    have h1 : (sigDecC (sigBC s)).forest.singleton.values=s.forest.singleton.values := by
      funext i
      change digC (sigBC s) (101+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),sigDigests_singleton s i.val (by omega),singletonList,
        getD_append_left' (by simp),getD_ofFn']
    have h2 : (sigDecC (sigBC s)).forest.singleton.path=s.forest.singleton.path := by
      funext i
      change digC (sigBC s) (107+i.val)=_
      rw [digC_sigBC s _ (by omega),normD_of_lt _ _ (by omega),show 107+i.val=101+(6+i.val) by omega,
        sigDigests_singleton s (6+i.val) (by omega),singletonList,getD_append_right' (by simp),
        List.length_ofFn,Nat.add_sub_cancel_left,getD_ofFn']
    cases h : (sigDecC (sigBC s)).forest.singleton
    cases h' : s.forest.singleton
    simp only [h,h'] at h1 h2
    cases h1;cases h2;rfl
  cases h : (sigDecC (sigBC s)).forest
  cases h' : s.forest
  simp only [h,h'] at hp hs
  cases hp;cases hs;rfl

/-- Normal form (what the compact codec keeps; T51: 5,195 bytes). -/
def normalizeV6 (s : SharedSignature) : SharedSignature :=
  { s with
    policyHints := BitVec.ofNat 16 (s.policyHints.toNat % 2 ^ 13)
    layers := fun lay => ⟨(s.layers lay).values,
      fun j => normD (layIdx lay + chainCount lay + j.val) ((s.layers lay).path j)⟩ }

theorem normD_of_out (k : Nat) (d : Digest) (hk : k < 166 ∨ 176 < k) : normD k d = d := by
  unfold normD; rw [if_neg (by omega), if_neg (by omega)]

theorem sigDecC_sigBC (s : SharedSignature) : sigDecC (sigBC s) = normalizeV6 s := by
  have hr : (sigDecC (sigBC s)).rho=s.rho := by
    change digC (sigBC s) 0=s.rho
    rw [digC_sigBC s 0 (by decide),normD_of_lt _ _ (by decide),sigDigests_rho]
  have hh := policyHints_sigDecC_sigBC s
  have hf := forest_sigDecC_sigBC s
  have hl : (sigDecC (sigBC s)).layers=(normalizeV6 s).layers := by
    funext lay
    have hc : layIdx lay+chainCount lay≤325 := by fin_cases lay <;> decide
    have hp : layIdx lay+chainCount lay+height lay≤325 := by fin_cases lay <;> decide
    have hv : ((sigDecC (sigBC s)).layers lay).values=((normalizeV6 s).layers lay).values := by
      funext i
      change digC (sigBC s) (layIdx lay+i.val)=(s.layers lay).values i
      have hn : layIdx lay+i.val < 166 ∨ 176 < layIdx lay+i.val := by
        fin_cases lay <;> simp [layIdx,chainCount] at * <;> omega
      rw [digC_sigBC s _ (by omega),normD_of_out _ _ hn,sigDigests_layValue]
    have hpath : ((sigDecC (sigBC s)).layers lay).path=((normalizeV6 s).layers lay).path := by
      funext i
      change digC (sigBC s) (layIdx lay+chainCount lay+i.val) =
        normD (layIdx lay + chainCount lay + i.val) ((s.layers lay).path i)
      rw [digC_sigBC s _ (by omega), show layIdx lay+chainCount lay+i.val=layIdx lay+(chainCount lay+i.val) by omega,
        sigDigests_layPath s lay i.val i.isLt]
    cases h : (sigDecC (sigBC s)).layers lay
    cases h' : (normalizeV6 s).layers lay
    simp only [h,h'] at hv hpath
    cases hv;cases hpath;rfl
  have hf' : (sigDecC (sigBC s)).forest=(normalizeV6 s).forest := hf
  have hr' : (sigDecC (sigBC s)).rho=(normalizeV6 s).rho := hr
  have hh' : (sigDecC (sigBC s)).policyHints=(normalizeV6 s).policyHints := hh
  cases h : sigDecC (sigBC s)
  cases h' : normalizeV6 s
  simp only [h,h'] at hr' hh' hf' hl
  cases hr';cases hh';cases hf';cases hl;rfl

end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M (digNat digNat_eq_of_digits getD_append_left' getD_append_right' getD_ofFn'
 chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)
open ClaudeWCT.W9.T3M (getD_eraseIdx mod_digit)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

theorem sigDigests_sigDecC (b : CBytes) (k : Nat) (hk : k<325) :
    (sigDigests (sigDecC b)).getD k 0=digC b k := by
  by_cases h0:k=0
  · subst h0;exact sigDigests_rho _
  by_cases hp:k<101
  · have hq:(k-1)/25<4:=by omega
    let p : Fin 4:=⟨(k-1)/25,hq⟩
    let j : Nat:=(k-1)%25
    have hj:j<25:=Nat.mod_lt _ (by decide)
    have he:k=1+25*p.val+j:=by dsimp [p,j];omega
    rw [he,sigDigests_pair _ p j hj]
    by_cases h1:j<6
    · rw [pairList_firstValue _ ⟨j,h1⟩]
      change digC b _=digC b _
      congr 1 <;> simp only [Fin.val_mk] <;> omega
    · by_cases h2:j<12
      · rw [show j=6+(j-6) by omega,pairList_firstPath _ ⟨j-6,by omega⟩]
        change digC b _=digC b _
        congr 1 <;> simp only [Fin.val_mk] <;> omega
      · by_cases h3:j<18
        · rw [show j=12+(j-12) by omega,pairList_secondValue _ ⟨j-12,by omega⟩]
          change digC b _=digC b _
          congr 1 <;> simp only [Fin.val_mk] <;> omega
        · rw [show j=18+(j-18) by omega,pairList_secondPath _ ⟨j-18,by omega⟩]
          change digC b _=digC b _
          congr 1 <;> simp only [Fin.val_mk] <;> omega
  by_cases hs:k<114
  · have he:k=101+(k-101):=by omega
    rw [he,sigDigests_singleton _ (k-101) (by omega)]
    by_cases h1:k-101<6
    · unfold singletonList
      rw [getD_append_left' (by simp;omega),getD_ofFn' _ (k-101) h1]
      change digC b _=digC b _
      congr 1 <;> simp only [Fin.val_mk] <;> omega
    · unfold singletonList
      rw [getD_append_right' (by simp;omega),List.length_ofFn,getD_ofFn' _ ((k-101)-6) (by omega)]
      change digC b _=digC b _
      congr 1 <;> simp only [Fin.val_mk] <;> omega
  have key:∀ (lay:Layer) (i:Nat),i<chainCount lay+height lay→layIdx lay+i=k→
      (sigDigests (sigDecC b)).getD k 0=digC b k := by
    intro lay i hi he
    subst he
    rw [sigDigests_layer _ lay i hi]
    unfold layerList
    by_cases hc:i<chainCount lay
    · rw [getD_append_left' (by simpa using hc),getD_ofFn' _ i hc];rfl
    · rw [getD_append_right' (by simp;omega),List.length_ofFn,getD_ofFn' _ (i-chainCount lay) (by omega)]
      change digC b (layIdx lay+chainCount lay+(i-chainCount lay))=_
      congr 1;omega
  by_cases h1:k<177
  · exact key 0 (k-114) (by rw [chainCount_0,height_0];omega) (by simp [layIdx];omega)
  by_cases h2:k<227
  · exact key 1 (k-177) (by rw [chainCount_1,height_1];omega) (by simp [layIdx];omega)
  by_cases h3:k<276
  · exact key 2 (k-227) (by rw [chainCount_2,height_2];omega) (by simp [layIdx];omega)
  · exact key 3 (k-276) (by rw [chainCount_3,height_3];omega) (by simp [layIdx];omega)

theorem topBits_lt (j : Nat) (hj : j ≤ 128) (d : Digest) : topBits j d < 2 ^ j := by
  unfold topBits
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show j + (128 - j) = 128 by omega]
  exact d.isLt

theorem topBits_zero (d : Digest) : topBits 0 d = 0 := by
  unfold topBits; exact Nat.div_eq_of_lt d.isLt

theorem xOfB_digit (b : CBytes) (j : Nat) (h1 : 1 ≤ j) (h10 : j ≤ 10) :
    xOfB b / 2 ^ xOff j % 2 ^ topZeroBits j = topBits (topZeroBits j) (cDig b (165 + j)) := by
  have t3 := topBits_lt 1 (by norm_num) (cDig b 168); have t4 := topBits_lt 1 (by norm_num) (cDig b 169)
  have t5 := topBits_lt 2 (by norm_num) (cDig b 170); have t6 := topBits_lt 3 (by norm_num) (cDig b 171)
  have t7 := topBits_lt 4 (by norm_num) (cDig b 172); have t8 := topBits_lt 5 (by norm_num) (cDig b 173)
  have t9 := topBits_lt 6 (by norm_num) (cDig b 174); have t10 := topBits_lt 7 (by norm_num) (cDig b 175)
  obtain ⟨o3, o4, o5, o6, o7, o8, o9, o10⟩ := xOff_vals
  unfold xOfB
  interval_cases j
  · rw [show topZeroBits 1 = 0 from rfl, topBits_zero]; exact Nat.mod_one _
  · rw [show topZeroBits 2 = 0 from rfl, topBits_zero]; exact Nat.mod_one _
  all_goals
    first
      | (rw [o3, show topZeroBits 3 = 1 from rfl]; norm_num at *; omega)
      | (rw [o4, show topZeroBits 4 = 1 from rfl]; norm_num at *; omega)
      | (rw [o5, show topZeroBits 5 = 2 from rfl]; norm_num at *; omega)
      | (rw [o6, show topZeroBits 6 = 3 from rfl]; norm_num at *; omega)
      | (rw [o7, show topZeroBits 7 = 4 from rfl]; norm_num at *; omega)
      | (rw [o8, show topZeroBits 8 = 5 from rfl]; norm_num at *; omega)
      | (rw [o9, show topZeroBits 9 = 6 from rfl]; norm_num at *; omega)
      | (rw [o10, show topZeroBits 10 = 7 from rfl]; norm_num at *; omega)

theorem xOfB_lt (b : CBytes) : xOfB b < 2 ^ 29 := by
  have t3 := topBits_lt 1 (by norm_num) (cDig b 168); have t4 := topBits_lt 1 (by norm_num) (cDig b 169)
  have t5 := topBits_lt 2 (by norm_num) (cDig b 170); have t6 := topBits_lt 3 (by norm_num) (cDig b 171)
  have t7 := topBits_lt 4 (by norm_num) (cDig b 172); have t8 := topBits_lt 5 (by norm_num) (cDig b 173)
  have t9 := topBits_lt 6 (by norm_num) (cDig b 174); have t10 := topBits_lt 7 (by norm_num) (cDig b 175)
  unfold xOfB
  norm_num at *
  omega

theorem xField_sigDecC (b : CBytes) : xField (sigDecC b) = xOfB b := by
  have hx := xOfB_lt b
  unfold xField
  rw [sigDigests_sigDecC b 176 (by decide)]
  change (digC b 176).toNat / 2 ^ 88 % 2 ^ 16 + (BitVec.ofNat 16 (xOfB b / 2 ^ 16)).toNat % 2 ^ 13 * 2 ^ 16 = _
  rw [digC, if_neg (by decide), if_pos rfl, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have ht := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 88 by positivity)
  have hlt : b.toNat / 2 ^ (128 * 324) % 2 ^ 88 + xOfB b % 2 ^ 16 * 2 ^ 88 < 2 ^ 128 := by
    have := Nat.mod_lt (xOfB b) (show 0 < 2 ^ 16 by positivity)
    norm_num at *
    omega
  rw [Nat.mod_eq_of_lt hlt]
  norm_num at *
  omega

theorem packD_clear (j : Nat) (hj : 1 ≤ j ∧ j ≤ 10) (c : Digest) (x : Nat)
    (hx : x / 2 ^ xOff j % 2 ^ topZeroBits j = topBits (topZeroBits j) c) :
    packD j (clearTop (topZeroBits j) c) x = c := by
  have hb := topZeroBits_le_eight j (by omega)
  apply BitVec.eq_of_toNat_eq
  unfold packD clearTop
  unfold topBits at hx
  rw [hx, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hm : c.toNat % 2 ^ (128 - topZeroBits j) < 2 ^ 128 :=
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.mod_eq_of_lt hm, Nat.mod_mod]
  have e := Nat.mod_add_div c.toNat (2 ^ (128 - topZeroBits j))
  rw [mul_comm] at e
  rw [e]
  exact Nat.mod_eq_of_lt c.isLt

theorem sigBC_sigDecC (b : CBytes) : sigBC (sigDecC b)=b := by
  apply BitVec.eq_of_toNat_eq
  rw [sigBC_toNat]
  have hD : digNat (encList (sigDecC b))=b.toNat%2^(128*324) := by
    apply digNat_eq_of_digits
    · rw [encList_length];exact Nat.mod_lt _ (by positivity)
    · intro k hk
      rw [encList_length] at hk
      rw [mod_digit _ 324 k hk, encList_getD _ k hk, getD_eraseIdx]
      by_cases hp : 166 ≤ k ∧ k ≤ 175
      · rw [if_pos hp, if_pos (by omega), sigDigests_sigDecC b k (by omega), xField_sigDecC]
        have hj : 1 ≤ k - 165 ∧ k - 165 ≤ 10 := by omega
        have hdig := xOfB_digit b (k - 165) hj.1 hj.2
        rw [show 165 + (k - 165) = k by omega] at hdig
        have hc : digC b k = clearTop (topZeroBits (k - 165)) (cDig b k) := by
          rw [digC, if_pos (by omega), if_pos (by omega)]
        rw [hc, packD_clear _ hj _ _ hdig, cDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
      · rw [if_neg hp]
        split
        · rename_i hlt
          rw [sigDigests_sigDecC b k (by omega),digC,if_pos hlt,if_neg (by omega),cDig,BitVec.extractLsb'_toNat,
            Nat.shiftRight_eq_div_pow]
        · rename_i hge
          rw [sigDigests_sigDecC b (k+1) (by omega),digC,if_neg (by omega),if_neg (by omega),
            show k+1-1=k by omega,cDig,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  have hT : ((sigDigests (sigDecC b)).getD 176 0).toNat%2^88=b.toNat/2^(128*324)%2^88 := by
    rw [sigDigests_sigDecC b 176 (by decide),digC,if_neg (by decide),if_pos rfl,BitVec.toNat_ofNat]
    have hlt : b.toNat / 2 ^ (128 * 324) % 2 ^ 88 + xOfB b % 2 ^ 16 * 2 ^ 88 < 2 ^ 128 := by
      have := Nat.mod_lt (xOfB b) (show 0 < 2 ^ 16 by positivity)
      have := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 88 by positivity)
      norm_num at *
      omega
    rw [Nat.mod_eq_of_lt hlt, Nat.add_mul_mod_self_right, Nat.mod_mod]
  rw [hD,hT]
  have hb : b.toNat / 2 ^ (128 * 324) < 2 ^ 88 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact b.isLt
  rw [Nat.mod_eq_of_lt hb]
  exact Nat.mod_add_div _ _
end ClaudeWCT.W9.T3M.SharedCodec

namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Research.SharedForest

theorem normalizeV6_fill (sig : SharedSignature) (c : Nat) :
    normalizeV6 (fillTopSignature sig c) = normalizeV6 sig := by
  unfold normalizeV6 fillTopSignature
  congr 1
  funext lay
  congr 1
  funext j
  simp only [ClaudeWCT.WCT9.fillLayer]
  split
  · rename_i h
    obtain ⟨hl, hj⟩ := h
    have : lay = 0 := Fin.ext hl
    subst this
    have hidx : layIdx 0 + SigGolfCandidate.T3.chainCount 0 + j.val = 176 := by
      simp [layIdx, SigGolfCandidate.T3.chainCount, hj]
    rw [hidx]
    unfold normD
    rw [if_neg (by decide), if_pos rfl, if_neg (by decide), if_pos rfl, ClaudeWCT.WCT9.setTop_toNat]
    congr 1
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 104 ≤ 112)),
      show c % 2 ^ 16 * 2 ^ 112 % 2 ^ 104 = 0 from
        Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by norm_num)) _), add_zero, Nat.mod_mod]
  · rfl

theorem sigBC_fillTopSignature (sig : SharedSignature) (c : Nat) :
    sigBC (fillTopSignature sig c) = sigBC sig := by
  calc
    sigBC (fillTopSignature sig c) = sigBC (sigDecC (sigBC (fillTopSignature sig c))) := (sigBC_sigDecC _).symm
    _ = sigBC (normalizeV6 (fillTopSignature sig c)) := by rw [sigDecC_sigBC]
    _ = sigBC (normalizeV6 sig) := by rw [normalizeV6_fill]
    _ = sigBC (sigDecC (sigBC sig)) := by rw [sigDecC_sigBC]
    _ = sigBC sig := sigBC_sigDecC _


theorem layIdx_ge (l : SigGolfCandidate.T3.Layer) (h : l.val ≠ 0) : 177 ≤ layIdx l := by
  revert h; revert l; decide

/-- The codec's normal form is the normal form `SharedForest.normTop` that `expand` applies first. -/
theorem normalizeV6_eq_normTop (s : SharedSignature) : normalizeV6 s = normTop s := by
  unfold normalizeV6 normTop
  congr 1
  funext lay
  unfold normLayer
  congr 1
  funext j
  by_cases h0 : lay.val = 0
  · have hl : lay = 0 := Fin.ext h0
    subst hl
    rw [if_pos (show ((0 : SigGolfCandidate.T3.Layer) : Nat) = 0 from rfl)]
    have hk : layIdx 0 + SigGolfCandidate.T3.chainCount 0 + j.val = 165 + j.val := rfl
    rw [hk]
    unfold normD normPathD clearTop
    rw [show 165 + j.val - 165 = j.val by omega]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [if_neg h0]
    apply normD_of_out
    right
    have := layIdx_ge lay h0
    omega

/-- img-v6 codec round trip in the form used by the final pipeline. -/
theorem sigDecC_sigBC_normTop (s : SharedSignature) : sigDecC (sigBC s) = normTop s :=
  (sigDecC_sigBC s).trans (normalizeV6_eq_normTop s)

end ClaudeWCT.W9.T3M.SharedCodec

/-! ## T51 decoded-signature facts (KEYCODEC, round 2)

The expander's decoder DEC (words 54569..54738) writes digest `k` of the 5,195-byte signature at slot
`internalFullIndex k` (16 bytes per slot from `0x7000`), zero at the dummy slots (`internalDummy`), and the hint
`xOfB b / 2^16` at `0x66000`. `fill_sigDecC`: the decoded signature has its brute-forced field (top sibling bits
112..127) clear. The `inflatedRead_*` lemmas read the slot layout back without letting the kernel unfold `digC` against
`inflatedRead` (that comparison blows up on T51's `digC`). -/
namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

/-- T51: the decoded top sibling (digest 176) is below `2^104` (bits 104..111 zero-test, 112..127 filled by expand). -/
theorem digC_176_lt (b : CBytes) : (digC b 176).toNat < 2 ^ 104 := by
  rw [digC, if_neg (by decide), if_pos rfl, BitVec.toNat_ofNat]
  have h1 := Nat.mod_lt (b.toNat / 2 ^ (128 * 324)) (show 0 < 2 ^ 88 by positivity)
  have h2 := Nat.mod_lt (xOfB b) (show 0 < 2 ^ 16 by positivity)
  have hlt : b.toNat / 2 ^ (128 * 324) % 2 ^ 88 + xOfB b % 2 ^ 16 * 2 ^ 88 < 2 ^ 104 := by
    norm_num at *
    omega
  rw [Nat.mod_eq_of_lt (lt_trans hlt (by norm_num))]
  exact hlt

/-- T51: the decoded signature has its brute-forced top-sibling field (bits 112..127) clear. -/
theorem fill_sigDecC (b : CBytes) : fillTopSignature (sigDecC b) 0 = sigDecC b := by
  have hl : (fun lay => ClaudeWCT.WCT9.fillLayer lay ((sigDecC b).layers lay) 0) = (sigDecC b).layers := by
    funext lay
    have hp : (fun j : Fin (height lay) => if lay.val = 0 ∧ j.val = 11 then
        ClaudeWCT.WCT9.setTop (((sigDecC b).layers lay).path j) 0 else ((sigDecC b).layers lay).path j) =
        ((sigDecC b).layers lay).path := by
      funext j
      split
      · rename_i h
        obtain ⟨hl0, hj⟩ := h
        have : lay = 0 := Fin.ext hl0
        subst this
        apply BitVec.eq_of_toNat_eq
        rw [ClaudeWCT.WCT9.setTop_toNat]
        change (digC b (layIdx 0 + chainCount 0 + j.val)).toNat % 2 ^ 112 + 0 % 2 ^ 16 * 2 ^ 112 =
          (digC b (layIdx 0 + chainCount 0 + j.val)).toNat
        have hidx : layIdx 0 + chainCount 0 + j.val = 176 := by
          simp [layIdx, chainCount, hj]
        rw [hidx, Nat.zero_mod, Nat.zero_mul, Nat.add_zero]
        exact Nat.mod_eq_of_lt (lt_trans (digC_176_lt b) (by norm_num))
      · rfl
    unfold ClaudeWCT.WCT9.fillLayer
    rw [hp]
  unfold fillTopSignature
  rw [hl]

/-- T51: the decoded policy hints are the top 13 bits of the 29-bit X field. -/
theorem policyHints_sigDecC_toNat (b : CBytes) : (sigDecC b).policyHints.toNat = xOfB b / 2 ^ 16 := by
  change (BitVec.ofNat 16 (xOfB b / 2 ^ 16)).toNat = _
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := xOfB_lt b
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  norm_num at *
  omega

theorem policyHints_sigDecC_lt (b : CBytes) : (sigDecC b).policyHints.toNat < 2 ^ 13 := by
  rw [policyHints_sigDecC_toNat]
  have := xOfB_lt b
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  norm_num at *
  omega

/-! ### The slot layout (`internalFullIndex`) read back through `inflatedRead` -/

theorem inflatedRead_main {α : Type} (z : α) (read : Nat → α) (k : Nat) (hk : 114 ≤ k) (hk' : k ≤ 176) :
    inflatedRead z read (k + 4) = read k := by
  rw [← internalFullIndex_main k hk hk', inflatedRead_internal]

theorem inflatedRead_lower {α : Type} (z : α) (read : Nat → α) (k : Nat) (hk : 177 ≤ k) :
    inflatedRead z read (k + 7) = read k := by
  rw [← internalFullIndex_lower k hk, inflatedRead_internal]

/-- Slot 0 is `rho` (stated through `inflatedRead_internal`, so the kernel never unfolds `digC` against `inflatedRead`). -/
theorem inflatedRead_rho (b : CBytes) : inflatedRead (0 : Digest) (digC b) 0 = (sigDecC b).rho :=
  inflatedRead_internal (0 : Digest) (digC b) 0

theorem inflatedRead_dummy {α : Type} (z : α) (read : Nat → α) (k : Nat) (hk : internalDummy k = true) :
    inflatedRead z read k = z := by
  unfold inflatedRead; rw [if_pos hk]

theorem externalFullIndex_lt (k : Nat) (hk : k < 332) (hd : internalDummy k = false) : externalFullIndex k < 325 := by
  simp only [internalDummy, decide_eq_false_iff_not] at hd
  unfold externalFullIndex
  split_ifs <;> omega

theorem internalFullIndex_external (k : Nat) (hd : internalDummy k = false) :
    internalFullIndex (externalFullIndex k) = k := by
  simp only [internalDummy, decide_eq_false_iff_not] at hd
  unfold internalFullIndex externalFullIndex
  split_ifs <;> omega

end ClaudeWCT.W9.T3M.SharedCodec
end
-- ==== merged from Rv_Tactic ====
section

namespace SigGolfCandidate.Rv
open Lean Meta Elab Tactic Command
unsafe def evalOptResultUnsafe (e : Expr) : MetaM (Option Result) :=
  evalExpr (Option Result) (mkApp (mkConst ``Option [0]) (mkConst ``Result)) e
@[implemented_by evalOptResultUnsafe]
opaque evalOptResult (e : Expr) : MetaM (Option Result)
unsafe def evalExprExprUnsafe (e : Expr) : MetaM Expr := evalExpr Expr (mkConst ``Expr) e
@[implemented_by evalExprExprUnsafe]
opaque evalExprExpr (e : Expr) : MetaM Expr
def evalToLiteral (lhs : Expr) : MetaM Expr := do
  let lhs ← instantiateMVars lhs
  if lhs.hasFVar || lhs.hasMVar then
    throwError "sym_eval: the left-hand side must be a closed term, got{indentExpr lhs}"
  let α ← inferType lhs
  let u ← getLevel α
  let some u' := u.dec | throwError "sym_eval: type must live in `Type u`"
  let inst ← synthInstance (mkApp (mkConst ``Lean.ToExpr [u']) α)
  evalExprExpr (mkApp3 (mkConst ``Lean.toExpr [u']) α inst lhs)
def kernelEq (lhs lit : Expr) : MetaM Expr := do
  let ty ← mkEq lhs lit
  let pf ← mkEqRefl lit
  let name ← mkAuxLemma [] ty pf
  return mkConst name
elab "sym_eval" : tactic => do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := t.eq? | throwError "sym_eval: goal is not an equation"
  let lit ← evalToLiteral lhs
  unless ← isDefEq rhs lit do
    throwError "sym_eval: result mismatch; the computation returned{indentExpr lit}"
  goal.assign (← kernelEq lhs lit)
  replaceMainGoal []
section Shared
open Std
abbrev ShareM := StateM (HashMap USize Expr)
unsafe def eToExprShared (e : E) : ShareM Expr := do
  let key := ptrAddrUnsafe e
  if let some x := (← get).get? key then return x
  let x ← match e with
    | .c _ | .reg _ => pure (toExpr e)
    | .ld a => do pure (mkApp (mkConst ``E.ld) (← eToExprShared a))
    | .un op a => do pure (mkApp2 (mkConst ``E.un) (toExpr op) (← eToExprShared a))
    | .bin op a b => do
      pure (mkApp3 (mkConst ``E.bin) (toExpr op) (← eToExprShared a) (← eToExprShared b))
    | .ite op x y a b => do
      pure (mkApp5 (mkConst ``E.ite) (toExpr op) (← eToExprShared x) (← eToExprShared y)
        (← eToExprShared a) (← eToExprShared b))
  modify (·.insert key x)
  return x
unsafe def addrToExprShared (a : Addr) : ShareM Expr := do
  let b ← match a.base with
    | none => pure (mkApp (mkConst ``Option.none [0]) (mkConst ``E))
    | some b => do
      let x ← eToExprShared b
      pure (mkApp2 (mkConst ``Option.some [0]) (mkConst ``E) x)
  return mkApp2 (mkConst ``Addr.mk) b (toExpr a.off)
unsafe def obligToExprShared : Oblig → ShareM Expr
  | .valid a w => return mkApp2 (mkConst ``Oblig.valid) (← addrToExprShared a) (toExpr w)
  | .align8 b => return mkApp (mkConst ``Oblig.align8) (← eToExprShared b)
  | .ne a b => return mkApp2 (mkConst ``Oblig.ne) (← addrToExprShared a) (← addrToExprShared b)
def listLit (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc)
    (mkApp (mkConst ``List.nil [0]) ty)
unsafe def resultToExprSharedM (r : Result) : ShareM Expr := do
  let regs ← r.st.regs.fields.mapM eToExprShared
  let regsE := mkAppN (mkConst ``RegFile.mk) regs.toArray
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Addr) (mkConst ``E)
  let mem ← r.st.mem.mapM fun (k, v) => do
    return mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Addr) (mkConst ``E)
      (← addrToExprShared k) (← eToExprShared v)
  let obl ← r.st.obl.mapM obligToExprShared
  let st := mkApp3 (mkConst ``SymState.mk) regsE (listLit pairTy mem)
    (listLit (mkConst ``Oblig) obl)
  return mkApp5 (mkConst ``Result.mk) st (← eToExprShared r.pc) (toExpr r.stop)
    (toExpr r.steps) (toExpr r.cycles)
unsafe def resultToExprSharedUnsafe (r : Result) : Expr :=
  (resultToExprSharedM r).run' {}
@[implemented_by resultToExprSharedUnsafe]
opaque resultToExprShared (r : Result) : Expr
end Shared
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := t.eq? | throwError "kernel_rfl: goal is not an equation"
  if t.hasFVar || t.hasMVar then throwError "kernel_rfl: goal must be closed"
  let pf ← mkEqRefl lhs
  let name ← mkAuxLemma [] t (← mkExpectedTypeHint pf t)
  let _ := rhs
  goal.assign (mkConst name)
  replaceMainGoal []
elab "sym_block " id:ident " := " t:term : command => do
  liftTermElabM do
    let e ← Term.elabTermEnsuringType t (mkApp (mkConst ``Option [0]) (mkConst ``Result))
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasFVar || e.hasMVar then
      throwError "sym_block: the executor call must be a closed term"
    let v ← evalOptResult e
    let some r := v | throwError "sym_block: symbolic execution returned `none`{indentExpr e}"
    let base := (← getCurrNamespace) ++ id.getId
    let resName := base ++ `res
    addDecl <| Declaration.defnDecl {
      name := resName, levelParams := [], type := mkConst ``Result, value := resultToExprShared r,
      hints := .abbrev, safety := .safe }
    enableRealizationsForConst resName
    compileDecls #[resName]
    let lit := mkApp2 (mkConst ``Option.some [0]) (mkConst ``Result) (mkConst resName)
    let ty ← mkEq e lit
    let pf ← mkEqRefl lit
    addDecl <| Declaration.thmDecl { name := base, levelParams := [], type := ty, value := pf }
    enableRealizationsForConst base
end SigGolfCandidate.Rv
end
