import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import SigGolfCandidate.Merge001
import SigGolfCandidate.Merge005
import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge015
import SigGolfCandidate.Merge026
import SigGolfCandidate.Merge028
import SigGolfCandidate.Merge029
import SigGolfCandidate.Merge030
import SigGolfCandidate.Merge031
import SigGolfCandidate.Merge032

-- ==== merged from ClaudeWCT_Bank_Spec ====
section

namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete (independentProposalWord uniformWordAverage)
open SphincsSecurity.Completeness (searchLoop failMass failMass_eq_probEvent)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
structure FtsBankSpec (P : Type) [Fintype P] [SampleableType P] where
  specTheta : ENNReal := CaseC.theta
  admBound : ENNReal := 1 / 64
  theta_add_admBound : specTheta + admBound = CaseC.theta + 1 / 64 := by rfl
  admissible : HashOutput → Bool
  producer : HashOutput → Bool
  exists_producer : ∃ x, producer x = true
  acceptance_le : Pr[fun x : HashOutput => producer x = true | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ admBound
  proposal : HashOutput → P
  law : P → ENNReal
  law_sum : ∑ p, law p = 1
  accepted_proposal : ∀ g : P → ENNReal,
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun x => if producer x = true then g (proposal x) else 0) =
      (∑ p, law p * g p) * Pr[fun x : HashOutput => producer x = true | ($ᵗ HashOutput : ProbComp HashOutput)]
  score : List HashOutput → HashOutput → ENNReal
  covered : List HashOutput → HashOutput → Prop
  one_le_score : ∀ X N, admissible N = true → covered X N → 1 ≤ score X N
  score_append_mono : ∀ X Y N, score X N ≤ score (X ++ Y) N
  price : List P → ENNReal
  average_score : ∀ X, BPORS.finiteAverage (fun N : HashOutput => score X N) = price (X.map proposal) / 2 ^ 128
  horizon : Nat
  excessRate : ENNReal
  excess_le : ClaudeWCT.Numerics.Law.lawAvg law horizon (fun W : List P => price W - specTheta) ≤ excessRate
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
def decode (x : HashOutput) : Option HashOutput := if S.producer x then some x else none
noncomputable def acceptance : ENNReal :=
  Pr[fun x : HashOutput => S.producer x = true | ($ᵗ HashOutput : ProbComp HashOutput)]
def proposals (X : List HashOutput) : List P := X.map S.proposal
theorem proposals_append (X Y : List HashOutput) : S.proposals (X ++ Y) = S.proposals X ++ S.proposals Y :=
  List.map_append
noncomputable def admissibleSet : Finset HashOutput := Finset.univ.filter fun x => S.producer x = true
theorem decode_elim (w : HashOutput → ENNReal) (x : HashOutput) :
    (S.decode x).elim 0 w = if S.producer x = true then w x else 0 := by
  unfold decode
  split <;> simp_all
theorem acceptedWeight_eq_sum (w : HashOutput → ENNReal) :
    Sampling.acceptedWeight S.decode w = (∑ x ∈ S.admissibleSet, w x) / (Fintype.card HashOutput : ENNReal) := by
  have h : Sampling.acceptedWeight S.decode w = BPORS.finiteAverage (fun x => (S.decode x).elim 0 w) := by
    unfold Sampling.acceptedWeight
    exact BPORS.expected_uniform_eq_finiteAverage _
  have hsum : (∑ x, (S.decode x).elim 0 w) = ∑ x ∈ S.admissibleSet, w x := by
    unfold admissibleSet
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    exact S.decode_elim w x
  rw [h, BPORS.finiteAverage, hsum]
theorem acceptedWeight_eq_expected (w : HashOutput → ENNReal) :
    Sampling.acceptedWeight S.decode w =
      expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun x => if S.producer x = true then w x else 0) := by
  unfold Sampling.acceptedWeight
  simp_rw [S.decode_elim]
theorem acceptedWeight_one : Sampling.acceptedWeight S.decode (fun _ => 1) = S.acceptance := by
  rw [acceptedWeight_eq_expected, expectedValue_ite_one]
  rfl
theorem acceptance_eq_card :
    S.acceptance = (S.admissibleSet.card : ENNReal) / (Fintype.card HashOutput : ENNReal) := by
  rw [← S.acceptedWeight_one, acceptedWeight_eq_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
theorem admissibleSet_nonempty : S.admissibleSet.Nonempty := by
  obtain ⟨x, hx⟩ := S.exists_producer
  exact ⟨x, by simp [admissibleSet, hx]⟩
theorem acceptance_ne_zero : S.acceptance ≠ 0 := by
  rw [acceptance_eq_card]
  apply ENNReal.div_ne_zero.mpr
  refine ⟨?_, ENNReal.natCast_ne_top _⟩
  exact_mod_cast (Finset.card_pos.mpr S.admissibleSet_nonempty).ne'
theorem acceptance_le_one : S.acceptance ≤ 1 := probEvent_le_one
theorem acceptance_ne_top : S.acceptance ≠ ⊤ := ne_top_of_le_ne_top (by simp) S.acceptance_le_one
theorem acceptance_le_sixtyfourth : S.acceptance ≤ S.admBound := S.acceptance_le
theorem failMass_decode : failMass S.decode = 1 - S.acceptance := by
  have hf : failMass S.decode = Pr[fun answer : HashOutput => S.decode answer = none |
      ($ᵗ HashOutput : ProbComp HashOutput)] := failMass_eq_probEvent S.decode
  rw [hf]
  have he (answer : HashOutput) : S.decode answer = none ↔ ¬S.producer answer = true := by
    by_cases h : S.producer answer = true
    · simp only [decode, h, ite_true, reduceCtorEq, not_true_eq_false]
    · simp only [decode, h, Bool.false_eq_true, ite_false, not_false_eq_true]
  simp_rw [he]
  rw [Sampling.probEvent_not]
  rfl
noncomputable def accepted : PMF HashOutput := PMF.uniformOfFinset S.admissibleSet S.admissibleSet_nonempty
noncomputable def freshPrice (w : HashOutput → ENNReal) : ENNReal :=
  Sampling.acceptedWeight S.decode w / S.acceptance
theorem freshPrice_step (w : HashOutput → ENNReal) :
    Sampling.acceptedWeight S.decode w + failMass S.decode * S.freshPrice w = S.freshPrice w := by
  have hcancel : S.acceptance * S.freshPrice w = Sampling.acceptedWeight S.decode w := by
    unfold freshPrice
    rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel S.acceptance_ne_zero S.acceptance_ne_top, mul_one]
  rw [failMass_decode, ← hcancel, ← add_mul, add_tsub_cancel_of_le S.acceptance_le_one, one_mul]
theorem expected_accepted (w : HashOutput → ENNReal) : expectedValue S.accepted w = S.freshPrice w := by
  unfold freshPrice
  rw [acceptedWeight_eq_sum, acceptance_eq_card]
  have hcard : (Fintype.card HashOutput : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard' : (Fintype.card HashOutput : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcancel : (∑ x ∈ S.admissibleSet, w x) / (Fintype.card HashOutput : ENNReal) /
      ((S.admissibleSet.card : ENNReal) / (Fintype.card HashOutput : ENNReal)) =
      (∑ x ∈ S.admissibleSet, w x) / (S.admissibleSet.card : ENNReal) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.mpr hcard)) (Or.inr (ENNReal.inv_ne_zero.mpr hcard')),
      inv_inv, mul_assoc, mul_comm (Fintype.card HashOutput : ENNReal)⁻¹, mul_assoc,
      ENNReal.mul_inv_cancel hcard hcard', mul_one]
  rw [hcancel]
  unfold expectedValue accepted
  simp only [PMF.probOutput_eq_apply, PMF.uniformOfFinset_apply, tsum_fintype]
  rw [div_eq_mul_inv, Finset.sum_mul]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => x ∈ S.admissibleSet)]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter fun x => x ∉ S.admissibleSet), add_zero]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [if_pos hx, mul_comm]
  · intro x hx
    rw [Finset.mem_filter] at hx
    rw [if_neg hx.2, zero_mul]
theorem expected_accepted_proposal (g : P → ENNReal) :
    expectedValue S.accepted (fun x => g (S.proposal x)) = ∑ p, S.law p * g p := by
  rw [expected_accepted]
  unfold freshPrice
  rw [acceptedWeight_eq_expected, S.accepted_proposal g]
  change (∑ p, S.law p * g p) * S.acceptance / S.acceptance = _
  rw [mul_div_assoc, ENNReal.div_self S.acceptance_ne_zero S.acceptance_ne_top, mul_one]
end FtsBankSpec
end ClaudeWCT.Bank
end
-- ==== merged from T3_Secc_SeccLaw ====
section

namespace SigGolfCandidate.T3.Security.SeccLaw
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def maxInputLength : Nat := 4096
noncomputable def publicUniverse : Finset HashInput :=
  (Finset.range (maxInputLength + 1)).biUnion fun k =>
    (Finset.univ : Finset (Fin k → UInt8)).image fun bytes => List.ofFn bytes
attribute [irreducible] publicUniverse
theorem mem_publicUniverse (input : HashInput) (h : input.length ≤ maxInputLength) : input ∈ publicUniverse := by
  rw [publicUniverse, Finset.mem_biUnion]
  refine ⟨input.length, Finset.mem_range.mpr (by omega), ?_⟩
  rw [Finset.mem_image]
  exact ⟨input.get, Finset.mem_univ _, List.ofFn_get input⟩
attribute [local instance] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_seccLaw : Fintype Coordinate := coordinateFintype
abbrev PublicTable := publicUniverse → HashOutput
abbrev CompletionTables := FullGame.FullTable × PublicTable
noncomputable instance instFintypeCompletionTables : Fintype CompletionTables := by
  unfold CompletionTables PublicTable FullGame.FullTable
  infer_instance
instance instNonemptyCompletionTables : Nonempty CompletionTables := ⟨(fun _ => 0, fun _ => 0)⟩
noncomputable def publicFill (table : PublicTable) (input : HashInput) : HashOutput :=
  if h : input ∈ publicUniverse then table ⟨input, h⟩ else 0
noncomputable def completeWith (state : LazyPrivate.State) (tables : CompletionTables) : Correctness.Answers
  | .inl (.inl n) => (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inl (.inr input) => (state.2 input).getD (publicFill tables.2 input)
  | .inr coordinate => (state.1 coordinate).getD (tables.1 coordinate)
theorem completeWith_agrees (state : LazyPrivate.State) (tables : CompletionTables)
    (input : T3.Spec.Domain) (answer : T3.Spec.Range input)
    (h : SourceReplay.known state input = some answer) : completeWith state tables input = answer := by
  cases input with
  | inl input =>
      cases input with
      | inl n => cases h
      | inr input =>
          change state.2 input = some answer at h
          simp only [completeWith, h, Option.getD_some]
  | inr coordinate =>
      change state.1 coordinate = some answer at h
      simp only [completeWith, h, Option.getD_some]
noncomputable def classCharge (cls : T3.Spec.Domain → Prop) : Nat → List FirstHit.QueryEvent → Nat
  | _, [] => 0
  | budget, event :: rest =>
      if FullGame.queryCharge event.input ≤ budget then
        (if cls event.input then FullGame.queryCharge event.input else 0) +
          classCharge cls (budget - FullGame.queryCharge event.input) rest
      else 0
theorem classCharge_or (P Q : T3.Spec.Domain → Prop) (hdisj : ∀ input, ¬(P input ∧ Q input))
    (budget : Nat) (events : List FirstHit.QueryEvent) :
    classCharge (fun input => P input ∨ Q input) budget events =
      classCharge P budget events + classCharge Q budget events := by
  induction events generalizing budget with
  | nil => simp [classCharge]
  | cons event rest ih =>
      simp only [classCharge]
      split_ifs with hc hpq hp hq hq' <;> first
        | omega
        | (rw [ih]; omega)
        | (exfalso; exact hdisj _ ⟨hp, hq⟩)
        | (simp_all)
theorem classCharge_le (cls : T3.Spec.Domain → Prop) (budget : Nat) (events : List FirstHit.QueryEvent) :
    classCharge cls budget events ≤ budget := by
  induction events generalizing budget with
  | nil => simp [classCharge]
  | cons event rest ih =>
      simp only [classCharge]
      split_ifs with hc hcls
      · have := ih (budget - FullGame.queryCharge event.input); omega
      · have := ih (budget - FullGame.queryCharge event.input); omega
      · omega
abbrev SampleClass := PaddedGame.TraceResult × Correctness.Answers → T3.Spec.Domain → Prop
end SigGolfCandidate.T3.Security.SeccLaw
end
-- ==== merged from T3_Secc_CreationSharedLaw ====
section

namespace SigGolfCandidate.T3.Security.CreationGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem prefixCount_eq_classCharge (cls : T3.Spec.Domain → Prop) (budget : Nat)
    (events : List FirstHit.QueryEvent) :
    prefixCount cls budget events = SeccLaw.classCharge cls budget events := by
  induction events generalizing budget with
  | nil => rfl
  | cons event rest ih => simp only [prefixCount, SeccLaw.classCharge, ih]
end SigGolfCandidate.T3.Security.CreationGame
end
-- ==== merged from T3_Secc_CaseCSearch ====
section

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
open SphincsSecurity.Completeness (searchLoop failMass)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem search_le_price {β γ : Type} (secret : BitVec 256) (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (result : Nat → β → γ) (payoff : γ → ENNReal) (weight : β → ENNReal)
    (hweight : ∀ counter value, payoff (result counter value) = weight value)
    (base price : ENNReal) (hbase : base ≤ price)
    (hstep : Sampling.acceptedWeight decoder weight + failMass decoder * price ≤ price) (bound : Nat)
    (hinj : ∀ left right, left < bound → right < bound → inputs left = inputs right → left = right) :
    ∀ fuel counter, counter + fuel ≤ bound → ∀ cache : Sampling.RCache,
      Sampling.CachedTrialsReject inputs decoder counter bound cache →
      expectedValue (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache)
        (fun output => output.1.elim base payoff) ≤ price := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter _ cache _
      simpa [searchLoop, Sampling.publicProgram] using hbase
  | succ fuel ih =>
      intro counter hlimit cache hcache
      rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, expectedValue_bind]
      cases hc : cache (inputs counter) with
      | some answer =>
          have hd := hcache counter le_rfl (by omega) answer hc
          rw [randomOracle.run_eq, hc]
          simp only [expectedValue_pure, hd]
          exact ih (counter + 1) (by omega) cache
            (fun c hstart hbound answer ha => hcache c (by omega) hbound answer ha)
      | none =>
          rw [Sampling.expectedValue_fresh _ _ hc]
          calc
            _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                (fun answer => (decoder answer).elim price weight) := by
              apply expectedValue_mono
              intro answer
              cases hd : decoder answer with
              | some value => simp [hweight]
              | none =>
                  apply ih (counter + 1) (by omega) _
                  intro c hstart hbound output ho
                  have hne : inputs c ≠ inputs counter := by
                    intro he
                    have hh := hinj c counter hbound (by omega) he
                    omega
                  have hh : cache (inputs c) = some output :=
                    (QueryCache.cacheQuery_of_ne cache answer hne).symm.trans ho
                  exact hcache c (by omega) hbound output hh
            _ = Sampling.acceptedWeight decoder weight + failMass decoder * price :=
              Sampling.uniform_decoder_weight decoder weight price
            _ ≤ price := hstep
def Reuse (cache : Sampling.RCache) (rho : Digest) (m : Message) : Prop :=
  ¬Sampling.CachedTrialsReject (Sampling.digestTrial rho m) Sampling.digestDecode 0 (2 ^ 32) cache
noncomputable def admissibleEntry (cache : Sampling.RCache) (input : HashInput) : ENNReal :=
  (cache input).elim 0 (fun answer => if digestAdmissible answer = true then 1 else 0)
noncomputable def reuseMass (cache : Sampling.RCache) (m : Message) : ENNReal :=
  (∑' p : Digest × Fin (2 ^ 32), admissibleEntry cache (Sampling.digestTrial p.1 m p.2.val)) / 2 ^ 128
def nonceOf (state : LazyPrivate.State) (m : Message) : Digest :=
  ((state.1 (.inr (.inl m))).getD 0).extractLsb' 0 128
theorem nonceOf_cacheQuery (state : LazyPrivate.State) (m : Message) (output : HashOutput)
    (after : LazyPrivate.State)
    (hext : SourceReplay.Extends (state.1.cacheQuery (.inr (.inl m)) output, state.2) after) :
    nonceOf after m = output.extractLsb' 0 128 := by
  have h : after.1 (.inr (.inl m)) = some output := hext.1 (QueryCache.cacheQuery_self _ _ _)
  simp only [nonceOf, h, Option.getD_some]
end SigGolfCandidate.T3.Security.CaseC
end
-- ==== merged from T3_Secc_CaseCExcess ====
section

section
namespace SigGolfCandidate.T3.BPORS.History
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
theorem theta_excess_le_square (value mean : ENNReal) (hvalue : value ≠ ⊤) (hmean : mean ≤ 37/64) :
    (13/8)*(value-63/64)+2*mean*value ≤ value^2+mean^2 :=
  SigGolfResearch.Gate6.Excess.theta_excess_le_square value mean hvalue hmean
theorem excess_three_quarters :
    uniformWordAverage BPORS.Numeric.proposalLength (fun W => BPORS.History.fullPrice W-63/64) ≤
      11324/100000000 :=
  fullPrice_excess_of_pointwise (63/64) theta_excess_le_square
end SigGolfCandidate.T3.BPORS.History
end
section
namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete (uniformWordAverage)
theorem theta_excess_le_square (value mean : ENNReal) (hvalue : value ≠ ⊤) (hmean : mean ≤ 37/64) :
    (13/8) * (value - 63/64) + 2 * mean * value ≤ value ^ 2 + mean ^ 2 :=
  BPORS.History.theta_excess_le_square value mean hvalue hmean
theorem excess_three_quarters :
    uniformWordAverage BPORS.Numeric.proposalLength (fun W => BPORS.History.fullPrice W - theta) ≤
      11324 / 100000000 := by
  simpa only [theta] using BPORS.History.excess_three_quarters
end SigGolfCandidate.T3.Security.CaseC
end
end
-- ==== merged from SphincsSecurity_Proof_Forced_SecretGuessObservation ====
section

namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal UniformTableCompletion
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value : Type} [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
def restrict (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value)
    (hit : Bool) : Coordinate → Finset Value :=
  Function.update allowed coordinate ((allowed coordinate).filter fun value => hit = decide (value = candidate))
omit [Fintype Coordinate] in
theorem restrict_subset (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value)
    (hit : Bool) (other : Coordinate) : restrict allowed coordinate candidate hit other ⊆ allowed other := by
  by_cases heq : other = coordinate
  · subst other
    rw [restrict, Function.update_self]
    exact Finset.filter_subset _ _
  · simp only [restrict, Function.update_of_ne heq, Finset.Subset.refl]
omit [Fintype Coordinate] in
theorem restrict_membership (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value)
    (hit : Bool) (labels : Coordinate → Value) :
    (∀ other, labels other ∈ restrict allowed coordinate candidate hit other) ↔
      (∀ other, labels other ∈ allowed other) ∧ hit = decide (labels coordinate = candidate) := by
  constructor
  · intro h
    refine ⟨fun other => restrict_subset allowed coordinate candidate hit other (h other), ?_⟩
    have hc := h coordinate
    rw [restrict, Function.update_self, Finset.mem_filter] at hc
    exact hc.2
  · rintro ⟨h, hh⟩ other
    by_cases heq : other = coordinate
    · subst other
      rw [restrict, Function.update_self]
      exact Finset.mem_filter.mpr ⟨h coordinate, hh⟩
    · simpa only [restrict, Function.update_of_ne heq] using h other
theorem restrict_mass (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value)
    (hit : Bool) (labels : Coordinate → Value) :
    (if hit = decide (labels coordinate = candidate) then complete allowed labels else 0) =
      restrictionWeight allowed (restrict allowed coordinate candidate hit) *
        complete (restrict allowed coordinate candidate hit) labels := by
  have h := restrict_guard allowed _ (restrict_subset allowed coordinate candidate hit) _
    (restrict_membership allowed coordinate candidate hit) labels
  by_cases hh : hit = decide (labels coordinate = candidate)
  · simpa only [if_pos hh] using h
  · simpa only [if_neg hh] using h
noncomputable def trial (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value) : SPMF Bool :=
  complete allowed >>= fun labels => pure (decide (labels coordinate = candidate))
theorem trial_apply (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value) (hit : Bool) :
    trial allowed coordinate candidate hit = restrictionWeight allowed (restrict allowed coordinate candidate hit) := by
  rw [trial, SPMF.bind_apply_eq_tsum]
  simp only [SPMF.pure_apply, mul_ite, mul_one, mul_zero, restrict_mass, ENNReal.tsum_mul_left,
    weight_tsum_complete]
theorem trial_mass (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value)
    (hit : Bool) (labels : Coordinate → Value) :
    trial allowed coordinate candidate hit * complete (restrict allowed coordinate candidate hit) labels =
      if hit = decide (labels coordinate = candidate) then complete allowed labels else 0 := by
  rw [trial_apply, restrict_mass]
theorem trial_nonempty (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value)
    (hit : Bool) (hhit : trial allowed coordinate candidate hit ≠ 0) :
    ∀ other, (restrict allowed coordinate candidate hit other).Nonempty := by
  by_contra hn
  rw [trial_apply, weight_of_empty _ _ hn] at hhit
  exact hhit rfl
theorem bind_trial {Result : Type} (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value)
    (next : Bool → (Coordinate → Value) → SPMF Result) :
    (complete allowed >>= fun labels => next (decide (labels coordinate = candidate)) labels) =
      (trial allowed coordinate candidate >>= fun hit =>
        complete (restrict allowed coordinate candidate hit) >>= next hit) := by
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, ← ENNReal.tsum_mul_left, ← mul_assoc, trial_mass, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  simp [Classical.em]
theorem trial_true (allowed : Coordinate → Finset Value) (ha : ∀ coordinate, (allowed coordinate).Nonempty)
    (coordinate : Coordinate) (candidate : Value) :
    trial allowed coordinate candidate true =
      if candidate ∈ allowed coordinate then ((allowed coordinate).card : ENNReal)⁻¹ else 0 := by
  rw [trial, SPMF.bind_apply_eq_tsum, complete_of_nonempty allowed ha]
  simpa only [SPMF.pure_apply, SPMF.liftM_apply, eq_comm (a := true), decide_eq_true_eq, mul_ite, mul_one, mul_zero,
    probEvent_eq_tsum_ite, PMF.probOutput_eq_apply] using probEvent_uniformTable_eq allowed ha coordinate candidate
structure State (Coordinate Value Memory : Type) where
  allowed : Coordinate → Finset Value
  retired : Finset Coordinate
  guesses : Finset Coordinate
  probes : Nat
  memory : Memory
def SecretSpec (Coordinate Value : Type) : OracleSpec ((Coordinate × Value) ⊕ Coordinate)
  | .inl _ => Bool
  | .inr _ => Value
abbrev World {AuxIndex : Type} (auxSpec : OracleSpec AuxIndex) (Coordinate Value : Type) :=
  auxSpec + SecretSpec Coordinate Value
structure Environment {AuxIndex : Type} (auxSpec : OracleSpec AuxIndex) (Coordinate Value Memory : Type) where
  auxiliary : State Coordinate Value Memory → (input : auxSpec.Domain) → PMF (auxSpec.Range input × Memory)
  trial : Memory → Coordinate → Value → Bool → Memory
  disclosure : Memory → Coordinate → Value → Memory
variable {Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
def afterTrial (environment : Environment auxSpec Coordinate Value Memory) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value) (hit : Bool) : State Coordinate Value Memory :=
  { allowed := restrict state.allowed coordinate candidate hit
    retired := if hit then insert coordinate state.retired else state.retired
    guesses := if hit = true ∧ coordinate ∉ state.retired then insert coordinate state.guesses else state.guesses
    probes := state.probes + 1
    memory := environment.trial state.memory coordinate candidate hit }
def afterDisclosure (environment : Environment auxSpec Coordinate Value Memory) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (value : Value) : State Coordinate Value Memory :=
  { state with
    allowed := discloseTableValue state.allowed coordinate value
    retired := insert coordinate state.retired
    memory := environment.disclosure state.memory coordinate value }
noncomputable def fixedImpl (environment : Environment auxSpec Coordinate Value Memory) (labels : Coordinate → Value) :
    QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF)
  | .inl input => StateT.mk fun state =>
      (fun result => (result.1, { state with memory := result.2 })) <$> (liftM (environment.auxiliary state input) : SPMF _)
  | .inr (.inl (coordinate, candidate)) => StateT.mk fun state =>
      let hit := decide (labels coordinate = candidate)
      pure (hit, afterTrial environment state coordinate candidate hit)
  | .inr (.inr coordinate) => StateT.mk fun state =>
      pure (labels coordinate, afterDisclosure environment state coordinate (labels coordinate))
noncomputable def lazyImpl (environment : Environment auxSpec Coordinate Value Memory) :
    QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF)
  | .inl input => StateT.mk fun state =>
      (fun result => (result.1, { state with memory := result.2 })) <$> (liftM (environment.auxiliary state input) : SPMF _)
  | .inr (.inl (coordinate, candidate)) => StateT.mk fun state =>
      (fun hit => (hit, afterTrial environment state coordinate candidate hit)) <$> trial state.allowed coordinate candidate
  | .inr (.inr coordinate) => StateT.mk fun state =>
      (fun value => (value, afterDisclosure environment state coordinate value)) <$> cell (state.allowed coordinate)
noncomputable def runWith {Result : Type}
    (implementation : QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF))
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory) :
    SPMF (Result × State Coordinate Value Memory) :=
  (simulateQ implementation computation).run state
noncomputable def fixedRun {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (labels : Coordinate → Value) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) := runWith (fixedImpl environment labels) computation state
noncomputable def lazyRun {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory) :=
  runWith (lazyImpl environment) computation state
def probeStep : (World auxSpec Coordinate Value).Domain → Nat
  | .inr (.inl _) => 1
  | _ => 0
theorem lazyImpl_probes (environment : Environment auxSpec Coordinate Value Memory)
    (state : State Coordinate Value Memory) (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (lazyImpl environment input).run state result ≠ 0) :
    result.2.probes = state.probes + probeStep input := by
  cases input with
  | inl input =>
      simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
        Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      obtain ⟨answer, _, rfl⟩ := hr
      exact (Nat.add_zero _).symm
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
            Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
          obtain ⟨hit, _, rfl⟩ := hr
          rfl
      | inr coordinate =>
          simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
            Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
          obtain ⟨value, _, rfl⟩ := hr
          exact (Nat.add_zero _).symm
omit [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] in
theorem runWith_pure {Result : Type}
    (implementation : QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF))
    (result : Result) (state : State Coordinate Value Memory) :
    runWith implementation (pure result) state = pure (result, state) := by
  simp only [runWith, simulateQ_pure, StateT.run_pure]
omit [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] in
theorem runWith_query_bind {Result : Type}
    (implementation : QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF))
    (input : (World auxSpec Coordinate Value).Domain)
    (next : (World auxSpec Coordinate Value).Range input → OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) :
    runWith implementation (liftM ((World auxSpec Coordinate Value).query input) >>= next) state =
      ((implementation input).run state >>= fun result => runWith implementation (next result.1) result.2) := by
  simp only [runWith, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
theorem run_posterior {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory) :
    (complete state.allowed >>= fun labels => (fun result => (labels, result)) <$> fixedRun environment labels computation state) =
      (lazyRun environment computation state >>= fun result =>
        (fun labels => (labels, result)) <$> complete result.2.allowed) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result => simp only [fixedRun, lazyRun, runWith_pure, pure_bind, ← bind_pure_comp]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [fixedRun, lazyRun, runWith_query_bind, fixedImpl, lazyImpl,
            StateT.run_mk, bind_map_left, map_bind, bind_assoc]
          rw [RetainedObservation.bind_comm]
          exact congrArg ((liftM (environment.auxiliary state input) : SPMF _) >>= ·)
            (funext fun answer => ih answer.1 { state with memory := answer.2 })
      | inr input =>
          cases input with
          | inl probe =>
              rcases probe with ⟨coordinate, candidate⟩
              simp only [fixedRun, lazyRun, runWith_query_bind, fixedImpl, lazyImpl,
                StateT.run_mk, pure_bind, bind_map_left, bind_assoc]
              rw [bind_trial state.allowed coordinate candidate (fun hit labels =>
                (fun result => (labels, result)) <$> runWith (fixedImpl environment labels) (next hit)
                  (afterTrial environment state coordinate candidate hit))]
              exact congrArg (trial state.allowed coordinate candidate >>= ·)
                (funext fun hit => ih hit (afterTrial environment state coordinate candidate hit))
          | inr coordinate =>
              simp only [fixedRun, lazyRun, runWith_query_bind, fixedImpl, lazyImpl,
                StateT.run_mk, pure_bind, bind_map_left, bind_assoc]
              rw [bind_disclose state.allowed coordinate (fun value labels =>
                (fun result => (labels, result)) <$> runWith (fixedImpl environment labels) (next value)
                  (afterDisclosure environment state coordinate value))]
              exact congrArg (cell (state.allowed coordinate) >>= ·)
                (funext fun value => ih value (afterDisclosure environment state coordinate value))
theorem lazyRun_preserves {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (invariant : State Coordinate Value Memory → Prop)
    (hstep : ∀ state, invariant state → ∀ input result,
      (lazyImpl environment input).run state result ≠ 0 → invariant result.2)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hinvariant : invariant state) (result : Result × State Coordinate Value Memory)
    (hr : lazyRun environment computation state result ≠ 0) : invariant result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [lazyRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact hinvariant
  | query_bind input next ih =>
      rw [lazyRun, runWith_query_bind, RetainedObservation.bind_nonzero] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      exact ih middle.1 middle.2 (hstep state hinvariant input middle hm) result hr
theorem lazyRun_nonempty {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) (result : Result × State Coordinate Value Memory)
    (hr : lazyRun environment computation state result ≠ 0) : ∀ coordinate, (result.2.allowed coordinate).Nonempty := by
  apply lazyRun_preserves environment (fun state => ∀ coordinate, (state.allowed coordinate).Nonempty) _ computation state ha result hr
  intro state hs input result hr
  cases input with
  | inl input =>
      simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
        Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      obtain ⟨answer, _, rfl⟩ := hr
      exact hs
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
        Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
          obtain ⟨hit, hh, rfl⟩ := hr
          exact trial_nonempty state.allowed coordinate candidate hit hh
      | inr coordinate =>
          simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
        Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
          obtain ⟨value, _, rfl⟩ := hr
          exact discloseTableValue_nonempty state.allowed hs coordinate value
theorem run_erasure {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) :
    (complete state.allowed >>= fun labels => fixedRun environment labels computation state) =
      lazyRun environment computation state := by
  have h := congrArg (Functor.map Prod.snd) (run_posterior environment computation state)
  simp only [map_bind, Functor.map_map, id_map'] at h
  calc
    _ = lazyRun environment computation state >>= fun result =>
        (fun _ => result) <$> complete result.2.allowed := h
    _ = lazyRun environment computation state >>= pure := by
      apply RetainedObservation.bind_congr
      intro result hr
      rw [complete_of_nonempty result.2.allowed (lazyRun_nonempty environment computation state ha result hr),
        map_eq_bind_pure_comp]
      exact RetainedObservation.lift_bind_const _ _
    _ = _ := bind_pure _
omit [Fintype Coordinate] in
theorem restrict_false (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value) :
    restrict allowed coordinate candidate false = eraseTableValue allowed coordinate candidate := by
  funext other
  by_cases heq : other = coordinate
  · subst other
    rw [restrict, eraseTableValue, Function.update_self, Function.update_self]
    ext value
    by_cases hv : value = candidate
    · simp [hv]
    · simp [hv]
  · simp only [restrict, eraseTableValue, Function.update_of_ne heq]
omit [Fintype Coordinate] in
theorem restrict_false_card (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value)
    (other : Coordinate) : (allowed other).card ≤ (restrict allowed coordinate candidate false other).card + 1 := by
  rw [restrict_false]
  by_cases heq : other = coordinate
  · subst other
    rw [eraseTableValue, Function.update_self]
    have h := Finset.pred_card_le_card_erase (s := allowed coordinate) (a := candidate)
    omega
  · rw [eraseTableValue, Function.update_of_ne heq]
    omega
def Invariant (size : Nat) (state : State Coordinate Value Memory) : Prop :=
  (∀ coordinate, coordinate ∉ state.retired → size ≤ (state.allowed coordinate).card + state.probes) ∧
    state.guesses ⊆ state.retired
omit [Fintype Coordinate] in
theorem afterTrial_invariant (environment : Environment auxSpec Coordinate Value Memory)
    (size : Nat) (state : State Coordinate Value Memory) (hs : Invariant size state)
    (coordinate : Coordinate) (candidate : Value) (hit : Bool) :
    Invariant size (afterTrial environment state coordinate candidate hit) := by
  cases hit with
  | false =>
      constructor
      · intro other ho
        have hb := hs.1 other ho
        have hc := restrict_false_card state.allowed coordinate candidate other
        change size ≤ (restrict state.allowed coordinate candidate false other).card + (state.probes + 1)
        omega
      · simpa only [afterTrial, Bool.false_eq_true, false_and, if_false] using hs.2
  | true =>
      constructor
      · intro other ho
        have hn : other ≠ coordinate ∧ other ∉ state.retired := by
          simpa only [afterTrial, if_true, Finset.mem_insert, not_or] using ho
        have hb := hs.1 other hn.2
        change size ≤ (restrict state.allowed coordinate candidate true other).card + (state.probes + 1)
        rw [restrict, Function.update_of_ne hn.1]
        omega
      · simp only [afterTrial, if_true, true_and]
        split
        · exact Finset.insert_subset_insert coordinate hs.2
        · exact hs.2.trans (Finset.subset_insert _ _)
omit [Fintype Coordinate] [DecidableEq Value] in
theorem afterDisclosure_invariant (environment : Environment auxSpec Coordinate Value Memory)
    (size : Nat) (state : State Coordinate Value Memory) (hs : Invariant size state)
    (coordinate : Coordinate) (value : Value) : Invariant size (afterDisclosure environment state coordinate value) := by
  constructor
  · intro other ho
    have hn : other ≠ coordinate ∧ other ∉ state.retired := by
      simpa only [afterDisclosure, Finset.mem_insert, not_or] using ho
    change size ≤ (discloseTableValue state.allowed coordinate value other).card + state.probes
    rw [discloseTableValue, Function.update_of_ne hn.1]
    exact hs.1 other hn.2
  · exact hs.2.trans (Finset.subset_insert _ _)
theorem lazyRun_invariant {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (size : Nat) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Invariant size state) (result : Result × State Coordinate Value Memory)
    (hr : lazyRun environment computation state result ≠ 0) : Invariant size result.2 := by
  apply lazyRun_preserves environment (Invariant size) _ computation state hs result hr
  intro state hs input result hr
  cases input with
  | inl input =>
      simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
        Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      obtain ⟨answer, _, rfl⟩ := hr
      exact hs
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
            Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
          obtain ⟨hit, _, rfl⟩ := hr
          exact afterTrial_invariant environment size state hs coordinate candidate hit
      | inr coordinate =>
          simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
            Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
          obtain ⟨value, _, rfl⟩ := hr
          exact afterDisclosure_invariant environment size state hs coordinate value
omit [Fintype Coordinate] in
theorem afterTrial_guesses_card (environment : Environment auxSpec Coordinate Value Memory)
    (state : State Coordinate Value Memory) (hs : state.guesses ⊆ state.retired)
    (coordinate : Coordinate) (candidate : Value) (hit : Bool) :
    (afterTrial environment state coordinate candidate hit).guesses.card =
      state.guesses.card + if hit = true ∧ coordinate ∉ state.retired then 1 else 0 := by
  by_cases hh : hit = true ∧ coordinate ∉ state.retired
  · simp only [afterTrial, if_pos hh]
    exact Finset.card_insert_of_notMem (fun hm => hh.2 (hs hm))
  · simp only [afterTrial, if_neg hh, Nat.add_zero]
theorem trial_true_le (size q : Nat) (state : State Coordinate Value Memory)
    (hs : Invariant size state) (ha : ∀ coordinate, (state.allowed coordinate).Nonempty)
    (hq : state.probes ≤ q) (coordinate : Coordinate) (hc : coordinate ∉ state.retired) (candidate : Value) :
    trial state.allowed coordinate candidate true ≤ ((size - q : Nat) : ENNReal)⁻¹ := by
  rw [trial_true state.allowed ha]
  split
  · apply ENNReal.inv_le_inv.mpr
    have h := hs.1 coordinate hc
    exact_mod_cast (show size - q ≤ (state.allowed coordinate).card by omega)
  · exact bot_le
def initialState [Fintype Value] (memory : Memory) : State Coordinate Value Memory :=
  ⟨fun _ => Finset.univ, ∅, ∅, 0, memory⟩
omit [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] in
theorem initialState_invariant [Fintype Value] (memory : Memory) :
    Invariant (Fintype.card Value) (initialState (Coordinate := Coordinate) (Value := Value) memory) := by
  simp [Invariant, initialState]
def disclosure (coordinate : Coordinate) : OracleComp (World auxSpec Coordinate Value) Value :=
  liftM ((World auxSpec Coordinate Value).query (.inr (.inr coordinate)))
def disclosureSequenceState (environment : Environment auxSpec Coordinate Value Memory) (labels : Coordinate → Value)
    {n : Nat} (coordinates : Fin n → Coordinate) (state : State Coordinate Value Memory) : State Coordinate Value Memory :=
  (List.ofFn coordinates).foldl (fun state coordinate => afterDisclosure environment state coordinate (labels coordinate)) state
omit [Fintype Coordinate] [DecidableEq Value] in
theorem disclosureSequenceState_counts (environment : Environment auxSpec Coordinate Value Memory) (labels : Coordinate → Value)
    {n : Nat} (coordinates : Fin n → Coordinate) (state : State Coordinate Value Memory) :
    ((disclosureSequenceState environment labels coordinates state).guesses,
      (disclosureSequenceState environment labels coordinates state).probes) = (state.guesses, state.probes) := by
  unfold disclosureSequenceState
  generalize List.ofFn coordinates = entries
  induction entries generalizing state with
  | nil => rfl
  | cons coordinate entries ih => exact ih (afterDisclosure environment state coordinate (labels coordinate))
omit [Fintype Coordinate] in
theorem fixedRun_disclosureSequence_bind {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (labels : Coordinate → Value) {n : Nat} (coordinates : Fin n → Coordinate)
    (next : (Fin n → Value) → OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory) :
    fixedRun environment labels ((sequenceFin fun index => disclosure (coordinates index)) >>= next) state =
      fixedRun environment labels (next (fun index => labels (coordinates index)))
        (disclosureSequenceState environment labels coordinates state) := by
  induction n generalizing state with
  | zero =>
      have hv : (Fin.elim0 : Fin 0 → Value) = (fun index => labels (coordinates index)) := by
        funext index
        exact Fin.elim0 index
      simp only [sequenceFin, pure_bind, hv, disclosureSequenceState, List.ofFn_zero, List.foldl_nil]
  | succ n ih =>
      rw [sequenceFin, bind_assoc]
      change runWith (fixedImpl environment labels)
        (liftM ((World auxSpec Coordinate Value).query (.inr (.inr (coordinates 0)))) >>= _) state = _
      rw [runWith_query_bind]
      simp only [fixedImpl, StateT.run_mk, pure_bind, bind_assoc]
      change fixedRun environment labels
        ((sequenceFin fun index => disclosure (coordinates index.succ)) >>=
          fun tail => next (Fin.cons (labels (coordinates 0)) tail))
        (afterDisclosure environment state (coordinates 0) (labels (coordinates 0))) = _
      rw [ih]
      have hv : Fin.cons (labels (coordinates 0)) (fun index => labels (coordinates index.succ)) =
          (fun index => labels (coordinates index)) := by
        funext index
        cases index using Fin.cases <;> rfl
      rw [hv]
      simp only [disclosureSequenceState, List.ofFn_succ, List.foldl_cons]
end SphincsSecurity.Concrete.SecretGuessObservation
end
-- ==== merged from SphincsSecurity_Proof_Forced_SecretGuessForced ====
section

namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
def EligibleAt (slot : Nat) (state : State Coordinate Value Memory) (coordinate : Coordinate) (candidate : Value) : Prop :=
  state.probes = slot ∧ coordinate ∉ state.retired ∧ trial state.allowed coordinate candidate true ≠ 0
noncomputable def forcedTrial (slot : Nat) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value) : SPMF Bool :=
  if EligibleAt slot state coordinate candidate then pure true else trial state.allowed coordinate candidate
theorem forcedTrial_nonzero (slot : Nat) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value) (hit : Bool)
    (hhit : forcedTrial slot state coordinate candidate hit ≠ 0) : trial state.allowed coordinate candidate hit ≠ 0 := by
  by_cases he : EligibleAt slot state coordinate candidate
  · simp only [forcedTrial, if_pos he, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hhit
    subst hit
    exact he.2.2
  · simpa only [forcedTrial, if_neg he] using hhit
noncomputable def forcedImpl (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat) :
    QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF)
  | .inl input => lazyImpl environment (.inl input)
  | .inr (.inl (coordinate, candidate)) => StateT.mk fun state =>
      (fun hit => (hit, afterTrial environment state coordinate candidate hit)) <$> forcedTrial slot state coordinate candidate
  | .inr (.inr coordinate) => lazyImpl environment (.inr (.inr coordinate))
noncomputable def forcedRun {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory) :=
  runWith (forcedImpl environment slot) computation state
theorem forcedImpl_nonzero (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (state : State Coordinate Value Memory) (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (forcedImpl environment slot input).run state result ≠ 0) :
    (lazyImpl environment input).run state result ≠ 0 := by
  cases input with
  | inl input => exact hr
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [forcedImpl, lazyImpl, StateT.run_mk, map_eq_bind_pure_comp,
            RetainedObservation.bind_nonzero] at hr ⊢
          obtain ⟨hit, hh, hr⟩ := hr
          exact ⟨hit, forcedTrial_nonzero slot state coordinate candidate hit hh, hr⟩
      | inr coordinate => exact hr
theorem forcedRun_nonzero {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (result : Result × State Coordinate Value Memory) (hr : forcedRun environment slot computation state result ≠ 0) :
    lazyRun environment computation state result ≠ 0 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value => exact hr
  | query_bind input next ih =>
      simp only [forcedRun, lazyRun, runWith_query_bind, RetainedObservation.bind_nonzero] at hr ⊢
      obtain ⟨middle, hm, hr⟩ := hr
      exact ⟨middle, forcedImpl_nonzero environment slot state input middle hm, ih middle.1 middle.2 result hr⟩
theorem forcedImpl_probes (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (state : State Coordinate Value Memory) (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (forcedImpl environment slot input).run state result ≠ 0) :
    result.2.probes = state.probes + probeStep input :=
  lazyImpl_probes environment state input result (forcedImpl_nonzero environment slot state input result hr)
theorem forcedRun_nonempty {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) (result : Result × State Coordinate Value Memory)
    (hr : forcedRun environment slot computation state result ≠ 0) : ∀ coordinate, (result.2.allowed coordinate).Nonempty :=
  lazyRun_nonempty environment computation state ha result (forcedRun_nonzero environment slot computation state result hr)
end SphincsSecurity.Concrete.SecretGuessObservation
end
-- ==== merged from T3_Secc_WotsEvents ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
structure LeafAddr where
  lay : Layer
  tree : Nat
  leaf : Nat
  deriving DecidableEq
structure ChainAddr where
  key : LeafAddr
  chain : Nat
  deriving DecidableEq
noncomputable def leafMsg (answers : Answers) (L : LeafAddr) : Digest :=
  if h : L.lay.val < 3 then Extract.honestRoot answers ⟨L.lay.val + 1, by omega⟩ (L.tree * 2 ^ height L.lay + L.leaf)
  else Extract.honestForest answers (L.tree * 2 ^ height L.lay + L.leaf)
noncomputable def referenceSearch (answers : Answers) (L : LeafAddr) : Option (BitVec 32 × List Nat) :=
  evalWithAnswerFn answers (counterSearch L.lay L.tree L.leaf (leafMsg answers L) 0 counterLimit)
def dummyDigits (lay : Layer) : List Nat :=
  if lay.val = 0 then dummyTop
  else List.replicate 10 6 ++ List.replicate 12 5 ++ List.replicate 20 4 ++ [target lay - 200]
noncomputable def referenceDigits (answers : Answers) (L : LeafAddr) : List Nat :=
  ((referenceSearch answers L).map Prod.snd).getD (dummyDigits L.lay)
noncomputable def depth (answers : Answers) (a : ChainAddr) : Nat :=
  (referenceDigits answers a.key).getD a.chain 0
noncomputable def frontierValue (answers : Answers) (a : ChainAddr) : Digest :=
  honestChainValue answers a.key.lay a.key.tree a.key.leaf a.chain
    (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (depth answers a)
def chainRow (a : ChainAddr) (step : Nat) (value : Digest) : HashInput :=
  chainInput a.key.lay a.key.tree a.key.leaf a.chain step value
abbrev Entry := HashInput × HashOutput
def low (output : HashOutput) : Digest := output.extractLsb' 0 128
def SeenRow (trace : List Entry) (a : ChainAddr) (step : Nat) (value out : Digest) : Prop :=
  ∃ answer, (chainRow a step value, answer) ∈ trace ∧ low answer = out
def ContactAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  1 ≤ depth answers a ∧ ∃ value, SeenRow trace a (depth answers a - 1) value (frontierValue answers a)
def TwoEdgeAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  2 ≤ depth answers a ∧ ∃ start middle, SeenRow trace a (depth answers a - 2) start middle ∧
    SeenRow trace a (depth answers a - 1) middle (frontierValue answers a)
def encodingRow (L : LeafAddr) (message : Digest) (counter : BitVec 32) : HashInput :=
  pad64 (encodingInput L.lay L.tree L.leaf message counter)
noncomputable def referenceInput (answers : Answers) (L : LeafAddr) : Option HashInput :=
  (referenceSearch answers L).map fun selected => encodingRow L (leafMsg answers L) selected.1
def EncodingMatchAt (answers : Answers) (trace : List Entry) (L : LeafAddr) : Prop :=
  ∃ message counter answer, (encodingRow L message counter, answer) ∈ trace ∧
    referenceInput answers L ≠ some (encodingRow L message counter) ∧
    decode L.lay (low answer) = some (referenceDigits answers L)
def MarkerAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ message counter answer digits, (encodingRow a.key message counter, answer) ∈ trace ∧
    referenceInput answers a.key ≠ some (encodingRow a.key message counter) ∧
    decode a.key.lay (low answer) = some digits ∧
    digits.getD a.chain 0 + 1 = (referenceDigits answers a.key).getD a.chain 0 ∧
    ∀ i, i ≠ a.chain → (referenceDigits answers a.key).getD i 0 ≤ digits.getD i 0
def entriesOf (answers : Answers) (qs : List Spec.Domain) : List Entry :=
  qs.filterMap fun q => match q with
    | .inl (.inr input) => some (input, answers (.inl (.inr input)))
    | _ => none
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from T3_Secc_CanonGraph ====
section

namespace SigGolfCandidate.T3.Security.CanonGraph
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete FiniteGraphSampling
open SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafRoot)
open ChainGraph (Address Point Seeds)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
structure LeafPos where
  lay : Layer
  tree : Fin (2^31)
  leaf : Fin 4096
  deriving DecidableEq, Fintype
structure TreeNodeRaw where
  lay : Layer
  tree : Fin (2^31)
  level : Fin 12
  idx : Fin 2048
  deriving DecidableEq, Fintype
def TreeNodeRaw.Valid (n : TreeNodeRaw) : Prop :=
  n.level.val < height n.lay ∧ n.idx.val < 2 ^ (height n.lay - n.level.val - 1)
instance instDecidablePredTreeNodeRawValid : DecidablePred TreeNodeRaw.Valid := fun n => by unfold TreeNodeRaw.Valid; infer_instance
abbrev TreeNode := {n : TreeNodeRaw // n.Valid}
structure FtsLeafPos where
  index : Fin (2^31)
  coord : Fin 7
  leaf : Fin 2048
  deriving DecidableEq, Fintype
structure FtsNodeRaw where
  index : Fin (2^31)
  coord : Fin 7
  level : Fin 11
  idx : Fin 1024
  deriving DecidableEq, Fintype
def FtsNodeRaw.Valid (n : FtsNodeRaw) : Prop := n.idx.val < 2 ^ (11 - n.level.val - 1)
instance instDecidablePredFtsNodeRawValid : DecidablePred FtsNodeRaw.Valid := fun n => by unfold FtsNodeRaw.Valid; infer_instance
abbrev FtsNodePos := {n : FtsNodeRaw // n.Valid}
inductive Node where
  | chain (point : Point)
  | leaf (pos : LeafPos)
  | node (pos : TreeNode)
  | ftsLeaf (pos : FtsLeafPos)
  | ftsNode (pos : FtsNodePos)
  | forest (index : Fin (2^31))
  deriving DecidableEq, Fintype
attribute [local irreducible] ChainGraph.instFintypeAddress
def Node.depth : Node → Nat
  | .chain p => p.2.val
  | .leaf _ => 7
  | .node n => 8 + n.1.level.val
  | .ftsLeaf _ => 0
  | .ftsNode n => 1 + n.1.level.val
  | .forest _ => 12
abbrev SecretIndex := Address ⊕ FtsLeafPos
abbrev Secrets := SecretIndex → Digest
abbrev Labels := Node → HashOutput
def seedsOf (secrets : Secrets) : Seeds := fun address => secrets (.inl address)
def ftsOf (secrets : Secrets) : FtsLeafPos → Digest := fun leaf => secrets (.inr leaf)
def chainLabels (labels : Labels) : ChainGraph.Labels := fun point => labels (.chain point)
def fin58 (i : Nat) : Fin 58 := ⟨i % 58, Nat.mod_lt _ (by decide)⟩
def fin7 (i : Nat) : Fin 7 := ⟨i % 7, Nat.mod_lt _ (by decide)⟩
def endLabel (secrets : Secrets) (labels : Labels) (L : LeafPos) (i : Nat) : Digest :=
  ChainGraph.value (seedsOf secrets) (chainLabels labels) ⟨L.lay, L.tree, L.leaf, fin58 i⟩ (maxDigit L.lay i)
def treeNodeAt (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Option TreeNode :=
  if h : level < height lay ∧ c < 2 ^ (height lay - level - 1) then
    some ⟨⟨lay, tree, ⟨level, lt_of_lt_of_le h.1 (Extract.height_le lay)⟩,
      ⟨c, lt_of_lt_of_le h.2 (by
        calc 2 ^ (height lay - level - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by
              have := Extract.height_le lay; omega)
          _ = 2048 := by norm_num)⟩⟩, h⟩
  else none
def treeLabel (labels : Labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Digest :=
  if level = 0 then
    (if h : c < 4096 then (labels (.leaf ⟨lay, tree, ⟨c, h⟩⟩)).extractLsb' 0 128 else 0)
  else
    match treeNodeAt lay tree (level - 1) c with
    | some n => (labels (.node n)).extractLsb' 0 128
    | none => 0
def ftsNodeAt (index : Fin (2^31)) (coord : Fin 7) (level c : Nat) : Option FtsNodePos :=
  if h : level < 11 ∧ c < 2 ^ (11 - level - 1) then
    some ⟨⟨index, coord, ⟨level, h.1⟩, ⟨c, lt_of_lt_of_le h.2 (by
      calc 2 ^ (11 - level - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 1024 := by norm_num)⟩⟩, h.2⟩
  else none
def ftsLabel (labels : Labels) (index : Fin (2^31)) (coord : Fin 7) (level c : Nat) : Digest :=
  if level = 0 then
    (if h : c < 2048 then (labels (.ftsLeaf ⟨index, coord, ⟨c, h⟩⟩)).extractLsb' 0 128 else 0)
  else
    match ftsNodeAt index coord (level - 1) c with
    | some n => (labels (.ftsNode n)).extractLsb' 0 128
    | none => 0
def cell (secrets : Secrets) : Node → Labels → HashInput
  | .chain p, labels => ChainGraph.input (seedsOf secrets) p (chainLabels labels)
  | .leaf L, labels => pad64 (Extract.leafInput L.lay L.tree.val L.leaf.val
      ((List.range (chainCount L.lay)).map (endLabel secrets labels L)))
  | .node n, labels => pad64 (nodeInputP 3 n.1.lay.val n.1.tree.val
      (2 ^ (height n.1.lay - n.1.level.val - 1) + n.1.idx.val)
      (treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)) 0
      (treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)))
  | .ftsLeaf f, _ => pad64 (ftsLeafInputP f.index.val f.coord.val f.leaf.val 0 (ftsOf secrets f) 0)
  | .ftsNode n, labels => pad64 (nodeInputP 10 n.1.coord.val n.1.index.val
      (2 ^ (11 - n.1.level.val - 1) + n.1.idx.val)
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)) 0
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)))
  | .forest index, labels => pad64 (Extract.forestInput index.val
      ((List.range 7).map fun coord => ftsLabel labels index (fin7 coord) 11 0))
def treeBits (lay : Layer) : Nat := ![0, 12, 19, 25] lay
def LeafPos.Source (L : LeafPos) : Prop := L.tree.val < 2 ^ treeBits L.lay ∧ L.leaf.val < 2 ^ height L.lay
instance instDecidablePredLeafPosSource : DecidablePred LeafPos.Source := fun L => by unfold LeafPos.Source; infer_instance
def Node.toPos : Node → Extract.Pos
  | .chain p => .chain p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val p.2.val
  | .leaf L => .leaf L.lay L.tree.val L.leaf.val
  | .node n => .node n.1.lay n.1.tree.val n.1.level.val n.1.idx.val
  | .ftsLeaf f => .ftsLeaf f.index.val f.coord.val f.leaf.val
  | .ftsNode n => .ftsNode n.1.index.val n.1.coord.val n.1.level.val n.1.idx.val
  | .forest index => .forest index.val
theorem height_pos (lay : Layer) : 0 < height lay := by fin_cases lay <;> decide
def rootNode (lay : Layer) (tree : Fin (2^31)) : TreeNode :=
  ⟨⟨lay, tree, ⟨height lay - 1, by have := Extract.height_le lay; omega⟩, ⟨0, by decide⟩⟩,
    ⟨Nat.sub_lt (height_pos lay) Nat.one_pos, pow_pos (by decide : 0 < 2) _⟩⟩
def ftsRootNode (index : Fin (2^31)) (coord : Fin 7) : FtsNodePos :=
  ⟨⟨index, coord, ⟨10, by decide⟩, ⟨0, by decide⟩⟩, show 0 < 2 ^ (11 - 10 - 1) by decide⟩
theorem treeLabel_root (labels : Labels) (lay : Layer) (tree : Fin (2^31)) :
    treeLabel labels lay tree (height lay) 0 = (labels (.node (rootNode lay tree))).extractLsb' 0 128 := by
  have hpos := height_pos lay
  unfold treeLabel
  rw [if_neg (by omega)]
  have hv : height lay - 1 < height lay ∧ 0 < 2 ^ (height lay - (height lay - 1) - 1) :=
    ⟨by omega, pow_pos (by decide) _⟩
  unfold treeNodeAt
  rw [dif_pos hv]
  rfl
noncomputable def canonInputs : Finset HashInput :=
  (Finset.univ : Finset (Secrets × Labels × Node)).image fun x => cell x.1 x.2.2 x.2.1
attribute [irreducible] canonInputs
theorem cell_mem (secrets : Secrets) (node : Node) (labels : Labels) : cell secrets node labels ∈ canonInputs := by
  rw [canonInputs]
  exact Finset.mem_image.mpr ⟨(secrets, labels, node), Finset.mem_univ _, rfl⟩
noncomputable def cellIn (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (node : Node) (labels : Labels) : U :=
  ⟨cell secrets node labels, hU (cell_mem secrets node labels)⟩
noncomputable def order : List Node :=
  (Finset.univ : Finset Node).toList.mergeSort (fun left right => decide (left.depth ≤ right.depth))
attribute [irreducible] order
def advance (node : Node) (output : HashOutput) (labels : Labels) : Labels := Function.update labels node output
noncomputable def programmed (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (labels : Labels) (residual : U → HashOutput) : U → HashOutput :=
  patch (fun node => cellIn U hU secrets node labels) labels residual order
def ftsCoordinate (f : FtsLeafPos) : ChainGraph.HalfCoordinate :=
  (.inl (header 8 f.coord.val f.index.val 0 (f.leaf.val / 2)), ⟨f.leaf.val % 2, Nat.mod_lt _ (by decide)⟩)
def secretCoordinate : SecretIndex → ChainGraph.HalfCoordinate := Sum.elim ChainGraph.seedCoordinate ftsCoordinate
theorem ftsCoordinate_injective : Function.Injective ftsCoordinate := by
  intro left right heq
  have hp := congrArg Prod.fst heq
  have hh := congrArg (fun coordinate : ChainGraph.HalfCoordinate => coordinate.2.val) heq
  change Sum.inl (header 8 left.coord.val left.index.val 0 (left.leaf.val / 2)) =
    (Sum.inl (header 8 right.coord.val right.index.val 0 (right.leaf.val / 2)) : Coordinate) at hp
  change left.leaf.val % 2 = right.leaf.val % 2 at hh
  have hl := left.coord.isLt
  have hr := right.coord.isLt
  have hlt := left.index.isLt
  have hrt := right.index.isLt
  have hli := left.leaf.isLt
  have hri := right.leaf.isLt
  have fields := header_injective (by decide : 8 < 256) (by omega) (by omega) (by omega) (by omega)
    (by decide : 8 < 256) (by omega) (by omega) (by omega) (by omega) (Sum.inl.inj hp)
  obtain ⟨index, coord, leaf⟩ := left
  obtain ⟨index', coord', leaf'⟩ := right
  simp only at fields hh
  have e1 : index = index' := Fin.ext fields.2.2.1
  have e2 : coord = coord' := Fin.ext fields.2.1
  have e3 : leaf = leaf' := Fin.ext (by have := fields.2.2.2.2; omega)
  rw [e1, e2, e3]
theorem secretCoordinate_injective : Function.Injective secretCoordinate := by
  intro left right heq
  cases left with
  | inl a =>
      cases right with
      | inl b => exact congrArg Sum.inl (ChainGraph.seedCoordinate_injective heq)
      | inr g =>
          exfalso
          have hp := congrArg Prod.fst heq
          change Sum.inl (header 0 a.layer.val a.tree.val (a.chain.val / 2) a.leaf.val) =
            (Sum.inl (header 8 g.coord.val g.index.val 0 (g.leaf.val / 2)) : Coordinate) at hp
          exact QuerySpace.header_ne_of_tag (by decide) (Sum.inl.inj hp)
  | inr f =>
      cases right with
      | inl b =>
          exfalso
          have hp := congrArg Prod.fst heq
          change Sum.inl (header 8 f.coord.val f.index.val 0 (f.leaf.val / 2)) =
            (Sum.inl (header 0 b.layer.val b.tree.val (b.chain.val / 2) b.leaf.val) : Coordinate) at hp
          exact QuerySpace.header_ne_of_tag (by decide) (Sum.inl.inj hp)
      | inr g => exact congrArg Sum.inr (ftsCoordinate_injective heq)
abbrev OtherHalf := {coordinate : ChainGraph.HalfCoordinate // coordinate ∉ Set.range secretCoordinate}
abbrev OtherHalves := OtherHalf → Digest
noncomputable def splitEquiv : ChainGraph.HalfTable ≃ Secrets × OtherHalves :=
  (Equiv.arrowCongr ((Equiv.Set.sumCompl (Set.range secretCoordinate)).symm.trans
    ((Equiv.ofInjective secretCoordinate secretCoordinate_injective).symm.sumCongr (Equiv.refl OtherHalf)))
    (Equiv.refl Digest)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
noncomputable def privateEquiv : FullGame.FullTable ≃ Secrets × OtherHalves :=
  ChainGraph.halvesEquiv.trans splitEquiv
set_option warn.classDefReducibility false in
noncomputable def encodingKeyFintype : Fintype QuerySpace.EncodingKey := inferInstance
attribute [irreducible] encodingKeyFintype
noncomputable def encInputs : Finset HashInput :=
  (@Finset.univ _ encodingKeyFintype).image QuerySpace.encodingQuery
attribute [irreducible] encInputs
noncomputable def canonUniverse {α : Type} (program : M α) : Finset HashInput :=
  canonInputs ∪ encInputs ∪ ChainGraph.recordedInputs program
attribute [irreducible] canonUniverse
section PrivateLaws
noncomputable local instance instFintypeCoordinate_canonGraph : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_canonGraph : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance instSampleableTypeHashOutput_canonGraph_1 : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeLabels_1 : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeSecrets : SampleableType Secrets := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeOtherHalves : SampleableType OtherHalves := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeProdSecretsOtherHalves : SampleableType (Secrets × OtherHalves) := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 (U : Finset HashInput) : SampleableType (U → HashOutput) := SampleableType.ofFintype _
abbrev LowLabels := Node → Digest
noncomputable def joinLabels (low high : LowLabels) : Labels :=
  fun node => ChainGraph.joinOutput (low node) (high node)
theorem joinLabels_low (low high : LowLabels) (node : Node) :
    (joinLabels low high node).extractLsb' 0 128 = low node := ChainGraph.joinOutput_low _ _
noncomputable local instance instSampleableTypeLowLabels : SampleableType LowLabels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeProdLowLabels : SampleableType (LowLabels × LowLabels) := SampleableType.ofFintype _
end PrivateLaws
noncomputable def eagerAnswers (privateTable : FullGame.FullTable) (U : Finset HashInput)
    (publicTable : U → HashOutput) : Answers
  | .inl (.inl n) => (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inl (.inr input) => finiteHashAnswer ∅ U publicTable input
  | .inr coordinate => privateTable coordinate
def ftsSecretOf (answers : Answers) (f : FtsLeafPos) : Digest :=
  let pair := evalWithAnswerFn answers (privatePair 8 f.coord.val f.index.val 0 (f.leaf.val / 2))
  if f.leaf.val % 2 = 0 then pair.1 else pair.2
def secretsOf (answers : Answers) : Secrets
  | .inl a => leafSeed answers a.layer a.tree.val a.leaf.val a.chain.val
  | .inr f => ftsSecretOf answers f
def Agrees (answers : Answers) (labels : Labels) : Prop :=
  ∀ node, answers (.inl (.inr (cell (secretsOf answers) node labels))) = labels node
theorem agrees_chain {answers : Answers} {labels : Labels} (h : Agrees answers labels) :
    ChainGraph.Agrees answers (ChainGraph.sourceSeeds answers) (chainLabels labels) :=
  fun point => h (.chain point)
end SigGolfCandidate.T3.Security.CanonGraph
end
-- ==== merged from SphincsSecurity_Proof_Reference_QueryAllocation ====
section

namespace SphincsSecurity.QueryCap
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {Index : Type} {spec : OracleSpec Index} {Result : Type}
noncomputable def recorded (computation : OracleComp spec Result) : OracleComp spec (Result × List Index) :=
  OracleComp.construct (fun result => pure (result, []))
    (fun input _ next => do
      let answer ← liftM (spec.query input)
      let result ← next answer
      pure (result.1, input :: result.2)) computation
theorem recorded_pure (result : Result) : recorded (pure result : OracleComp spec Result) = pure (result, []) := rfl
theorem recorded_query_bind (input : spec.Domain) (next : spec.Range input → OracleComp spec Result) :
    recorded (liftM (spec.query input) >>= next) = (do
      let answer ← liftM (spec.query input)
      let result ← recorded (next answer)
      pure (result.1, input :: result.2)) := rfl
def calls (selected : Index → Prop) [DecidablePred selected] (inputs : List Index) : Nat :=
  inputs.countP (fun input => decide (selected input))
theorem calls_nil (selected : Index → Prop) [DecidablePred selected] : calls selected [] = 0 := rfl
theorem calls_cons (selected : Index → Prop) [DecidablePred selected] (input : Index) (inputs : List Index) :
    calls selected (input :: inputs) = (if selected input then 1 else 0) + calls selected inputs := by
  simp [calls, List.countP_cons, Nat.add_comm]
theorem recorded_counted (selected : Index → Prop) [DecidablePred selected] (computation : OracleComp spec Result) :
    (fun result => (result.1, calls selected result.2)) <$> recorded computation = counted selected computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [recorded_pure, counted_pure, map_pure, calls_nil]
  | query_bind input next ih =>
      simp only [recorded_query_bind, counted_query_bind, map_bind, map_pure, calls_cons]
      congr 1
      funext answer
      rw [← ih answer]
      simp only [bind_map_left]
theorem recorded_forget (computation : OracleComp spec Result) : Prod.fst <$> recorded computation = computation := by
  have h := congrArg (Functor.map Prod.fst) (recorded_counted (fun _ => True) computation)
  simpa only [Functor.map_map, counted_forget] using h
theorem calls_sum_le {Address : Type} (addresses : Finset Address)
    (selected : Address → Index → Prop) [∀ address, DecidablePred (selected address)]
    (total : Index → Prop) [DecidablePred total]
    (hdisjoint : ∀ input, (∑ address ∈ addresses, if selected address input then 1 else 0) ≤ if total input then 1 else 0)
    (inputs : List Index) : (∑ address ∈ addresses, calls (selected address) inputs) ≤ calls total inputs := by
  induction inputs with
  | nil => simp only [calls_nil, Finset.sum_const_zero, le_refl]
  | cons input inputs ih =>
      simp only [calls_cons, Finset.sum_add_distrib]
      exact Nat.add_le_add (hdisjoint input) ih
theorem recorded_calls_le (selected : Index → Prop) [DecidablePred selected]
    (computation : OracleComp spec Result) (cost : Result → Nat)
    (hcounted : ∀ result ∈ support (counted selected computation), result.2 ≤ cost result.1)
    (result : Result × List Index) (hresult : result ∈ support (recorded computation)) :
    calls selected result.2 ≤ cost result.1 := by
  apply hcounted (result.1, calls selected result.2)
  rw [← recorded_counted, support_map]
  exact ⟨result, hresult, rfl⟩
theorem counted_query (selected : Index → Prop) [DecidablePred selected] (input : spec.Domain) :
    counted selected (liftM (spec.query input) : OracleComp spec _) =
      (fun answer => (answer, if selected input then 1 else 0)) <$> (liftM (spec.query input) : OracleComp spec _) := by
  have h := counted_query_bind selected input (fun answer => pure answer)
  simpa only [bind_pure, counted_pure, pure_bind, Nat.add_zero, bind_pure_comp, map_pure] using h
theorem simulate_counted {Target : Type} {target : OracleSpec Target} {m : Type → Type} [Monad m] [LawfulMonad m]
    (selected : Index → Prop) [DecidablePred selected] (selectedTarget : Target → Prop) [DecidablePred selectedTarget]
    (handler : QueryImpl spec (OracleComp target)) (targetImpl : QueryImpl target m) (sourceImpl : QueryImpl spec m)
    (hhandler : ∀ input, simulateQ targetImpl (counted selectedTarget (handler input)) =
      (fun answer => (answer, if selected input then 1 else 0)) <$> sourceImpl input)
    (computation : OracleComp spec Result) :
    simulateQ targetImpl (counted selectedTarget (simulateQ handler computation)) =
      simulateQ sourceImpl (counted selected computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, counted_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, counted_bind, counted_query, simulateQ_pure,
        hhandler, bind_map_left, ih]
theorem simulate_oracle_mem_support {Target : Type} {target : OracleSpec Target}
    (handler : QueryImpl spec (OracleComp target)) (computation : OracleComp spec Result)
    (result : Result) (hresult : result ∈ support (simulateQ handler computation)) : result ∈ support computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure, mem_support_pure_iff] using hresult
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      rw [mem_support_bind_iff]
      exact ⟨answer, by simp only [support_query, Set.mem_univ], ih answer hresult⟩
end SphincsSecurity.QueryCap
end
-- ==== merged from T3_Secc_WotsReference ====
section

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_wotsReference : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsReference : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
abbrev TickSpec : OracleSpec Unit := Unit →ₒ Unit
abbrev RefWorld := OracleWorld + TickSpec
def RefCharged : RefWorld.Domain → Prop
  | .inl (.inl _) => False
  | .inl (.inr _) => True
  | .inr _ => True
instance instDecidablePredDomainSumNatHashInputUnitRefWorldRefCharged : DecidablePred RefCharged := fun input => by
  rcases input with (n | x) | u <;> unfold RefCharged <;> infer_instance
def tick : OracleComp RefWorld Unit := liftM (RefWorld.query (.inr ()))
def ticks : Nat → OracleComp RefWorld Unit
  | 0 => pure ()
  | n + 1 => tick >>= fun _ => ticks n
noncomputable def keygenCharge (T : Answers) : Nat := (SourceReplay.queried T keygen).length
noncomputable def signCharge (T : Answers) (published : T3.Cache) (request : Request) : Nat :=
  (SourceReplay.queried T (FullGame.authenticatedSign published request)).length
noncomputable def offlineSign (T : Answers) (published : T3.Cache) (request : Request) :
    OracleComp RefWorld (Option Signature) :=
  ticks (signCharge T published request) >>= fun _ =>
    pure (evalWithAnswerFn T (FullGame.authenticatedSign published request))
noncomputable def offlineImpl (T : Answers) (published : T3.Cache) :
    QueryImpl (OracleWorld + Requests) (WriterT (QueryLog Requests) (OracleComp RefWorld)) :=
  (fun input => (liftM (liftM (RefWorld.query (.inl input)) : OracleComp RefWorld (OracleWorld.Range input)) :
      WriterT (QueryLog Requests) (OracleComp RefWorld) (OracleWorld.Range input))) +
    QueryImpl.withLogging (offlineSign T published)
noncomputable def verdictImpl : QueryImpl T3.Spec (OracleComp RefWorld)
  | .inl input => liftM (RefWorld.query (.inl input))
  | .inr _ => pure (0 : HashOutput)
noncomputable def offlineInteraction (T : Answers) (published : T3.Cache) {α : Type}
    (program : OracleComp (OracleWorld + Requests) α) : OracleComp RefWorld (α × QueryLog Requests) :=
  (simulateQ (offlineImpl T published) program).run
noncomputable def offlineGame (T : Answers) (adversary : AdversaryP) : OracleComp RefWorld Bool :=
  ticks (keygenCharge T) >>= fun _ =>
    offlineInteraction T (evalWithAnswerFn T keygen).2
      (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2) >>= fun result =>
    simulateQ verdictImpl (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 result)
noncomputable def referenceGame (T : Answers) (adversary : AdversaryP) (q : Nat) :
    OracleComp RefWorld (Option (Bool × Nat)) :=
  SphincsSecurity.QueryCap.run RefCharged (offlineGame T adversary) q
noncomputable def refImpl (T : Answers) : QueryImpl RefWorld ProbComp
  | .inl (.inl n) => liftM (unifSpec.query n)
  | .inl (.inr input) => pure (T (.inl (.inr input)))
  | .inr _ => pure ()
def traceOf (T : Answers) (queries : List RefWorld.Domain) : List Entry :=
  queries.filterMap fun query => match query with
    | .inl (.inr input) => some (input, T (.inl (.inr input)))
    | _ => none
noncomputable def referenceInputs (adversary : AdversaryP) : Finset HashInput :=
  SeccLaw.publicUniverse ∪ ChainGraph.recordedInputs (GameWith.idealGame PaddedGame.checker adversary)
noncomputable def eagerAnswers (inputs : Finset HashInput) (privateTable : FullGame.FullTable)
    (publicTable : inputs → HashOutput) : Answers
  | .inl (.inl n) => (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inl (.inr input) => SphincsSecurity.Concrete.finiteHashAnswer ∅ inputs publicTable input
  | .inr coordinate => privateTable coordinate
structure RefSample where
  answers : Answers
  publicKey : Digest
  trace : List Entry
end SigGolfCandidate.T3.Security.Wots
end
-- ==== merged from SphincsSecurity_Proof_Forced_SecretGuessErasure ====
section

namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
noncomputable def fixedAnswers (auxiliary : QueryImpl auxSpec ProbComp) (labels : Coordinate → Value) :
    QueryImpl (World auxSpec Coordinate Value) ProbComp
  | .inl input => auxiliary input
  | .inr (.inl (coordinate, candidate)) => pure (decide (labels coordinate = candidate))
  | .inr (.inr coordinate) => pure (labels coordinate)
noncomputable def environment (auxiliary : QueryImpl auxSpec ProbComp) : Environment auxSpec Coordinate Value PUnit where
  auxiliary _ input := (fun answer => (answer, PUnit.unit)) <$> (liftM (auxiliary input) : PMF _)
  trial _ _ _ _ := PUnit.unit
  disclosure _ _ _ := PUnit.unit
omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem fixedAnswers_disclosureSequence (auxiliary : QueryImpl auxSpec ProbComp) (labels : Coordinate → Value)
    {n : Nat} (coordinates : Fin n → Coordinate) :
    simulateQ (fixedAnswers auxiliary labels) (sequenceFin fun position => disclosure (coordinates position)) =
      pure (fun position => labels (coordinates position)) := by
  induction n with
  | zero =>
      simp only [sequenceFin, simulateQ_pure]
      congr 1
      funext position
      exact Fin.elim0 position
  | succ n ih =>
      rw [sequenceFin, simulateQ_bind]
      change (pure (labels (coordinates 0)) >>= _) = _
      rw [pure_bind, simulateQ_bind, ih]
      simp only [pure_bind, simulateQ_pure]
      congr 1
      funext position
      exact Fin.cases rfl (fun _ => rfl) position
omit [Fintype Coordinate] in
theorem fixedImpl_projection (auxiliary : QueryImpl auxSpec ProbComp) (labels : Coordinate → Value)
    (input : (World auxSpec Coordinate Value).Domain) (state : State Coordinate Value PUnit) :
    Prod.fst <$> ((fixedImpl (environment auxiliary) labels input).run state) = 𝒮[fixedAnswers auxiliary labels input] := by
  cases input with
  | inl input =>
      change Prod.fst <$> ((fun result => (result.1, { state with memory := result.2 })) <$>
        𝒮[(fun answer => (answer, PUnit.unit)) <$> (liftM (auxiliary input) : PMF _)]) = 𝒮[auxiliary input]
      simp only [evalSPMF_map, Functor.map_map, id_map']
      rfl
  | inr input =>
      cases input <;> simp only [fixedImpl, fixedAnswers, StateT.run_mk, map_pure, evalSPMF_pure]
omit [Fintype Coordinate] in
theorem fixedRun_projection {Result : Type} (auxiliary : QueryImpl auxSpec ProbComp) (labels : Coordinate → Value)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value PUnit) :
    Prod.fst <$> fixedRun (environment auxiliary) labels computation state =
      𝒮[simulateQ (fixedAnswers auxiliary labels) computation] := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result => simp only [fixedRun, runWith_pure, map_pure, simulateQ_pure, evalSPMF_pure]
  | query_bind input next ih =>
      simp only [fixedRun, runWith_query_bind, map_bind, simulateQ_bind, simulateQ_spec_query, evalSPMF_bind]
      change ((fixedImpl (environment auxiliary) labels input).run state >>= fun middle =>
        Prod.fst <$> fixedRun (environment auxiliary) labels (next middle.1) middle.2) = _
      simp only [ih]
      have h := congrArg (· >>= fun answer => 𝒮[simulateQ (fixedAnswers auxiliary labels) (next answer)])
        (fixedImpl_projection auxiliary labels input state)
      rw [bind_map_left] at h
      exact h
end SphincsSecurity.Concrete.SecretGuessObservation
end
-- ==== merged from T3_Secc_PairGuessWorld ====
section

section


section
namespace SphincsSecurity.Concrete.WeightedQuery
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
variable {Index State : Type} {spec : OracleSpec Index}
noncomputable def implementation (base : QueryImpl spec (StateT State SPMF))
    (factor : State → spec.Domain → ENNReal) : QueryImpl spec (StateT (State × ENNReal) SPMF) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1, (result.2, state.2 * factor state.1 input))) <$> (base input).run state.1
noncomputable def run {Result : Type} (base : QueryImpl spec (StateT State SPMF))
    (factor : State → spec.Domain → ENNReal) (computation : OracleComp spec Result) (state : State × ENNReal) :=
  (simulateQ (implementation base factor) computation).run state
theorem run_forget {Result : Type} (base : QueryImpl spec (StateT State SPMF))
    (factor : State → spec.Domain → ENNReal) (computation : OracleComp spec Result) (state : State × ENNReal) :
    (fun result => (result.1, result.2.1)) <$> run base factor computation state =
      (simulateQ base computation).run state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [run, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind input next ih =>
      simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, implementation,
        StateT.run_mk, bind_map_left, map_bind]
      exact congrArg ((base input).run state.1 >>= ·) (funext fun result => ih result.1 _)
theorem run_payoff {Result : Type} (left right : QueryImpl spec (StateT State SPMF))
    (factor : State → spec.Domain → ENNReal)
    (hstep : ∀ state input result, (left input).run state result = factor state input * (right input).run state result)
    (computation : OracleComp spec Result) (state : State) (weight : ENNReal) (payoff : Result × State → ENNReal) :
    weight * (∑' result, Pr[= result | (simulateQ left computation).run state] * payoff result) =
      ∑' result, Pr[= result | run right factor computation (state, weight)] *
        (result.2.2 * payoff (result.1, result.2.1)) := by
  induction computation using OracleComp.inductionOn generalizing state weight with
  | pure value => simp only [run, simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
  | query_bind input next ih =>
      simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, implementation,
        StateT.run_mk, bind_map_left, tsum_probOutput_bind_mul]
      simp only [run] at ih
      simp_rw [← ih]
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro result
      simp only [SPMF.probOutput_eq_apply, hstep]
      ring
theorem run_preserves {Result : Type} (base : QueryImpl spec (StateT State SPMF))
    (factor : State → spec.Domain → ENNReal) (invariant : State × ENNReal → Prop)
    (hstep : ∀ state, invariant state → ∀ input result, (base input).run state.1 result ≠ 0 →
      invariant (result.2, state.2 * factor state.1 input))
    (computation : OracleComp spec Result) (state : State × ENNReal) (hs : invariant state)
    (result : Result × State × ENNReal) (hr : run base factor computation state result ≠ 0) : invariant result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [run, simulateQ_pure, StateT.run_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact hs
  | query_bind input next ih =>
      simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, implementation, StateT.run_mk,
        bind_map_left, RetainedObservation.bind_nonzero] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      exact ih middle.1 (middle.2, state.2 * factor state.1 input) (hstep state hs input middle hm) result hr
end SphincsSecurity.Concrete.WeightedQuery
end
section
namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
noncomputable def forceWeight (slot : Nat) (state : State Coordinate Value Memory × ENNReal) : ENNReal :=
  if slot < state.1.probes then state.2 else 0
end SphincsSecurity.Concrete.SecretGuessObservation
end
section
namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
end SphincsSecurity.Concrete.SecretGuessObservation
end
section
namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
end SphincsSecurity.Concrete.SecretGuessObservation
end
section
namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
end SphincsSecurity.Concrete.SecretGuessObservation
end
section
namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] [Fintype Value] [Nonempty Value]
end SphincsSecurity.Concrete.SecretGuessObservation
end
end

section





section
namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable def pairValue (rate : ENNReal) (remaining : Nat) : Nat → ENNReal
  | 0 => remaining.choose 2 * rate ^ 2
  | 1 => remaining * rate
  | _ + 2 => 1
theorem pairValue_mono (rate : ENNReal) (hits : Nat) {first second : Nat} (h : first ≤ second) :
    pairValue rate first hits ≤ pairValue rate second hits := by
  cases hits with
  | zero => exact mul_le_mul' (by exact_mod_cast Nat.choose_le_choose 2 h) le_rfl
  | succ hits =>
      cases hits with
      | zero => exact mul_le_mul' (by exact_mod_cast h) le_rfl
      | succ hits => exact le_rfl
private theorem expectation_const_le {Result : Type} (law : SPMF Result) (value : ENNReal) :
    (∑' result, Pr[= result | law] * value) ≤ value := by
  rw [ENNReal.tsum_mul_right]
  exact mul_le_of_le_one_left' tsum_probOutput_le_one
theorem pairValue_trial (law : SPMF Bool) (rate : ENNReal) (hrate : law true ≤ rate) (remaining hits : Nat) :
    (∑' hit, Pr[= hit | law] * pairValue rate remaining (hits + if hit then 1 else 0)) ≤
      pairValue rate (remaining + 1) hits := by
  have hfalse : law false ≤ 1 := by
    simpa only [SPMF.probOutput_eq_apply] using (show Pr[= false | law] ≤ 1 from probOutput_le_one)
  cases hits with
  | zero =>
      simp only [tsum_fintype, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, Nat.zero_add,
        pairValue, SPMF.probOutput_eq_apply]
      calc
        _ ≤ rate * (remaining * rate) + ((remaining.choose 2 : Nat) : ENNReal) * rate ^ 2 :=
          add_le_add (mul_le_mul' hrate le_rfl) (mul_le_of_le_one_left' hfalse)
        _ = _ := by
          rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
          ring
  | succ hits =>
      cases hits with
      | zero =>
          simp only [tsum_fintype, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, Nat.add_zero,
            pairValue, SPMF.probOutput_eq_apply, mul_one]
          calc
            _ ≤ rate + (remaining : ENNReal) * rate := add_le_add hrate (mul_le_of_le_one_left' hfalse)
            _ = _ := by rw [Nat.cast_add, Nat.cast_one]; ring
      | succ hits =>
          calc
            _ = ∑' hit, Pr[= hit | law] * 1 := by
              apply tsum_congr
              intro hit
              cases hit <;> rfl
            _ ≤ 1 := expectation_const_le law 1
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
noncomputable def pairPotential (size budget : Nat) (state : State Coordinate Value Memory) : ENNReal :=
  if state.probes ≤ budget then pairValue ((size - budget : Nat) : ENNReal)⁻¹ (budget - state.probes) state.guesses.card else 0
omit [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] in
theorem pairPotential_two (size budget : Nat) (state : State Coordinate Value Memory)
    (hbudget : state.probes ≤ budget) (hhits : 2 ≤ state.guesses.card) : 1 ≤ pairPotential size budget state := by
  rw [pairPotential, if_pos hbudget]
  obtain ⟨hits, heq⟩ := Nat.exists_eq_add_of_le hhits
  rw [heq, Nat.add_comm]
  exact le_rfl
end SphincsSecurity.Concrete.SecretGuessObservation
end
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
abbrev FtsCoord := Fin (2^31) × Fin 7 × Fin 2048
def toLeafPos (f : FtsCoord) : CanonGraph.FtsLeafPos := ⟨f.1, f.2.1, f.2.2⟩
def ofLeafPos (p : CanonGraph.FtsLeafPos) : FtsCoord := (p.index, p.coord, p.leaf)
@[simp] theorem ofLeafPos_toLeafPos (f : FtsCoord) : ofLeafPos (toLeafPos f) = f := rfl
@[simp] theorem toLeafPos_ofLeafPos (p : CanonGraph.FtsLeafPos) : toLeafPos (ofLeafPos p) = p := rfl
abbrev WState := SecretGuessObservation.State FtsCoord Digest PUnit
def init : WState := SecretGuessObservation.initialState PUnit.unit
theorem card_digest : Fintype.card Digest = 2 ^ 128 := by simp
def probeInput (f : FtsCoord) (c : Digest) : HashInput :=
  pad64 (ftsLeafInputP f.1.val f.2.1.val f.2.2.val 0 c 0)
theorem probeInput_eq (f : FtsCoord) (c : Digest) :
    probeInput f c = block4 0 (header 9 f.2.1.val f.1.val 0 f.2.2.val) c 0 := by
  unfold probeInput ftsLeafInputP
  exact pad64_block4 _ _ _ _
@[simp] theorem probeInput_length (f : FtsCoord) (c : Digest) : (probeInput f c).length = 64 := by
  rw [probeInput_eq]; exact block4_length _ _ _ _
noncomputable def decodeProbe (x : HashInput) : Option (FtsCoord × Digest) :=
  haveI := Classical.propDecidable (∃ p : FtsCoord × Digest, x = probeInput p.1 p.2)
  if h : ∃ p : FtsCoord × Digest, x = probeInput p.1 p.2 then some (Classical.choose h) else none
def secretAt (answers : Answers) (f : FtsCoord) : Digest := CanonGraph.ftsSecretOf answers (toLeafPos f)
def secretNat (answers : Answers) (index coord leaf : Nat) : Digest :=
  let pair := evalWithAnswerFn answers (privatePair 8 coord index 0 (leaf / 2))
  if leaf % 2 = 0 then pair.1 else pair.2
section Rows
attribute [local irreducible] SigGolfCandidate.T3.buildFts SigGolfCandidate.T3.buildLevels Correctness.ftsRows
theorem eval_ftsRows_secrets (answers : Answers) (index coord : Nat) :
    (evalWithAnswerFn answers (Correctness.ftsRows index coord)).2.length = 2048 ∧
      ∀ leaf, leaf < 2048 →
        (evalWithAnswerFn answers (Correctness.ftsRows index coord)).2.getD leaf 0 =
          secretNat answers index coord leaf := by
  unfold Correctness.ftsRows
  refine Correctness.eval_foldlM_range_inv answers 1024 _
    (fun pairs (rows : List Digest × List Digest) => rows.2.length = 2 * pairs ∧
      ∀ leaf, leaf < 2 * pairs → rows.2.getD leaf 0 = secretNat answers index coord leaf)
    ([], []) ⟨rfl, fun leaf h => by omega⟩ (fun pair _ rows hrows => ?_)
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  obtain ⟨hlen, hget⟩ := hrows
  refine ⟨by simp [hlen]; omega, ?_⟩
  intro leaf hleaf
  by_cases hold : leaf < 2 * pair
  · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hold)]
    exact hget leaf hold
  · rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
    have he : leaf = 2 * pair ∨ leaf = 2 * pair + 1 := by omega
    rcases he with rfl | rfl
    · simp only [Nat.sub_self, List.getD_cons_zero, secretNat]
      rw [show 2 * pair / 2 = pair by omega, if_pos (by omega)]
    · simp only [show 2 * pair + 1 - 2 * pair = 1 by omega, secretNat]
      rw [show (2 * pair + 1) / 2 = pair by omega, if_neg (by omega)]
      rfl
theorem buildFts_secret (answers : Answers) (index coord leaf : Nat) (hleaf : leaf < 2048) :
    (evalWithAnswerFn answers (buildFts index coord)).2.getD leaf 0 = secretNat answers index coord leaf := by
  rw [Correctness.buildFts_eq]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact (eval_ftsRows_secrets answers index coord).2 leaf hleaf
end Rows
theorem honestInput_ftsLeaf (answers : Answers) (f : FtsCoord) :
    Extract.honestInput answers (.ftsLeaf f.1.val f.2.1.val f.2.2.val) = probeInput f (secretAt answers f) := by
  simp only [Extract.honestInput]
  have h := buildFts_secret answers f.1.val f.2.1.val f.2.2.val f.2.2.isLt
  unfold Extract.ftsSecret
  rw [h]
  rfl
def leafIndex (bucket leaf : Nat) : Fin 2048 := ⟨(bucket * 128 + leaf) % 2048, Nat.mod_lt _ (by decide)⟩
def outputIndex (output : HashOutput) : Fin (2^31) := ⟨output.toNat % 2 ^ 31, Nat.mod_lt _ (by positivity)⟩
def openedPositions (output : HashOutput) : List FtsCoord :=
  (List.finRange 7).flatMap fun c =>
    ((selections output).getD c.val ⟨0, []⟩).leaves.map fun leaf =>
      (outputIndex output, c, leafIndex ((selections output).getD c.val ⟨0, []⟩).bucket leaf)
noncomputable def signedOutput (answers : Answers) (message : Message) (signature : Signature) :
    Option HashOutput :=
  (evalWithAnswerFn answers (digestSearch signature.rho message 0 attemptLimit)).map Prod.snd
def Disclosed (answers : Answers) (log : QueryLog Requests) (f : FtsCoord) : Prop :=
  ∃ entry ∈ log, ∃ signature output, entry.2 = some signature ∧
    signedOutput answers entry.1.message signature = some output ∧ f ∈ openedPositions output
noncomputable def pairTerm (q : Nat) : ENNReal := (q.choose 2 : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ ^ 2
noncomputable def guessTerm (q : Nat) : ENNReal := (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹
section World
variable (U : Finset HashInput) (hU : CanonGraph.canonInputs ⊆ U)
structure Omega where
  seeds : ChainGraph.Seeds
  other : CanonGraph.OtherHalves
  labels : CanonGraph.Labels
  residual : U → HashOutput
variable {U}
def Omega.secrets (ω : Omega U) (fts : FtsCoord → Digest) : CanonGraph.Secrets
  | .inl a => ω.seeds a
  | .inr p => fts (ofLeafPos p)
noncomputable def Omega.answers (ω : Omega U) (fts : FtsCoord → Digest) : Answers :=
  CanonGraph.eagerAnswers (CanonGraph.privateEquiv.symm (ω.secrets fts, ω.other)) U
    (CanonGraph.programmed U hU (ω.secrets fts) ω.labels ω.residual)
def overwrite (positions : List FtsCoord) (values : List Digest) (f : FtsCoord) : Digest :=
  ((positions.zip values).find? (fun pv => decide (pv.1 = f))).elim 0 Prod.snd
end World
end SigGolfCandidate.T3.Security.BPair
end
end
end
-- ==== merged from T3_Secc_CaseCCover ====
section

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem selection_getD (x : HashOutput) (c : Fin 7) :
    (selections x).getD c.val ⟨0, []⟩ =
      ⟨(outBucket x c).val, (List.ofFn fun j : Fin 3 => (outLeaves x c j).val).mergeSort (· ≤ ·)⟩ := by
  rw [← rawSelections_eq_selections, rawSelections, List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_ofFn]
  rfl
theorem mem_selection_leaves (x : HashOutput) (c : Fin 7) (leaf : Nat) :
    leaf ∈ ((selections x).getD c.val ⟨0, []⟩).leaves ↔ ∃ j, (outLeaves x c j).val = leaf := by
  rw [selection_getD]
  change leaf ∈ (List.ofFn fun j : Fin 3 => (outLeaves x c j).val).mergeSort (· ≤ ·) ↔ _
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_ofFn]
theorem outLeaves_injective (x : HashOutput) (h : admissible (selections x) = true) (c : Fin 7) :
    Function.Injective (outLeaves x c) := by
  unfold admissible at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hlen : c.val < (selections x).length := by simp [selections]
  have hc := h.1 ((selections x).getD c.val ⟨0, []⟩) (by
    rw [List.getD_eq_getElem _ _ hlen]; exact List.getElem_mem hlen)
  rw [decide_eq_true_eq, selection_getD] at hc
  change ((List.ofFn fun j : Fin 3 => (outLeaves x c j).val).mergeSort (· ≤ ·)).Nodup at hc
  rw [(List.mergeSort_perm _ _).nodup_iff, List.nodup_ofFn] at hc
  intro j j' hjj
  exact hc (congrArg Fin.val hjj)
theorem outputIndex_eq (x : HashOutput) : BPair.outputIndex x = outIdx x := by
  apply Fin.ext
  rw [show (BPair.outputIndex x).val = x.toNat % 2 ^ 31 from rfl, ← rawView_index]
  rfl
theorem leafIndex_val (b : Fin 16) (leaf : Fin 128) : (BPair.leafIndex b.val leaf.val).val = b.val * 128 + leaf.val := by
  unfold BPair.leafIndex
  simp only
  apply Nat.mod_eq_of_lt
  omega
theorem leafIndex_inj {b b' : Fin 16} {leaf leaf' : Fin 128}
    (h : BPair.leafIndex b.val leaf.val = BPair.leafIndex b'.val leaf'.val) : b = b' ∧ leaf = leaf' := by
  have hv := congrArg Fin.val h
  rw [leafIndex_val, leafIndex_val] at hv
  constructor
  · apply Fin.ext; omega
  · apply Fin.ext; omega
theorem mem_openedPositions (x : HashOutput) (f : BPair.FtsCoord) (h : f ∈ BPair.openedPositions x) :
    f.1 = outIdx x ∧ ∃ j, f.2.2 = BPair.leafIndex (outBucket x f.2.1).val (outLeaves x f.2.1 j).val := by
  unfold BPair.openedPositions at h
  rw [List.mem_flatMap] at h
  obtain ⟨c, -, hc⟩ := h
  rw [List.mem_map] at hc
  obtain ⟨leaf, hleaf, rfl⟩ := hc
  rw [mem_selection_leaves] at hleaf
  obtain ⟨j, rfl⟩ := hleaf
  refine ⟨outputIndex_eq x, j, ?_⟩
  rw [selection_getD]
theorem opened_mem (x : HashOutput) (c : Fin 7) (j : Fin 3) :
    ((outIdx x, c, BPair.leafIndex (outBucket x c).val (outLeaves x c j).val) : BPair.FtsCoord) ∈
      BPair.openedPositions x := by
  unfold BPair.openedPositions
  rw [List.mem_flatMap]
  refine ⟨c, List.mem_finRange c, ?_⟩
  rw [List.mem_map]
  refine ⟨(outLeaves x c j).val, (mem_selection_leaves x c _).mpr ⟨j, rfl⟩, ?_⟩
  rw [selection_getD, outputIndex_eq]
theorem coordCovered_of_opened (X : List HashOutput) (N : HashOutput) (c : Fin 7)
    (h : ∀ j : Fin 3, ∃ out ∈ X,
      ((outIdx N, c, BPair.leafIndex (outBucket N c).val (outLeaves N c j).val) : BPair.FtsCoord) ∈
        BPair.openedPositions out) : CoordCovered X N c := by
  intro j
  obtain ⟨out, hout, hopen⟩ := h j
  obtain ⟨hidx, j', hj'⟩ := mem_openedPositions out _ hopen
  obtain ⟨hb, hl⟩ := leafIndex_inj hj'
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hout
  refine ⟨⟨(k, j'), ?_, ?_⟩, ?_⟩
  · rw [hk]; exact hidx.symm
  · rw [hk]; exact hb.symm
  · simp only [slotValue]
    rw [hk]
    exact hl.symm
end SigGolfCandidate.T3.Security.CaseC
end
-- ==== merged from T3_Secc_CaseCCore ====
section

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem pmf_expectedValue_left_mul {α : Type} (law : PMF α) (factor : ENNReal) (payoff : α → ENNReal) :
    expectedValue law (fun result => factor * payoff result) = factor * expectedValue law payoff := by
  unfold expectedValue
  simp_rw [mul_left_comm _ factor]
  exact ENNReal.tsum_mul_left
noncomputable def ledger (R : Nat) (targets X : List HashOutput) (slack : Nat) : ENNReal :=
  (targets.map fun N => forecast R X N).sum + (slack : ENNReal) * excessForecast R X / 2 ^ 128
theorem expectedValue_list_sum' {α β : Type} (law : PMF α) (l : List β) (f : β → α → ENNReal) :
    expectedValue law (fun a => (l.map fun b => f b a).sum) = (l.map fun b => expectedValue law (f b)).sum := by
  induction l with
  | nil => simp [expectedValue]
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [expectedValue_add, ih]
theorem theta_add_sixteenth_le_one : theta + 1 / 64 ≤ 1 := by
  unfold theta
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num
noncomputable def admInd (a : HashOutput) : ENNReal := if digestAdmissible a = true then 1 else 0
def CoveredBy (X : List HashOutput) (N : HashOutput) : Prop :=
  ∀ f ∈ BPair.openedPositions N, ∃ out ∈ X, f ∈ BPair.openedPositions out
theorem expected_admInd_tight : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) admInd ≤ 1/64 := by
  have he : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) admInd=DigestSampling.acceptanceProbability := by
    rw [←Sampling.digest_acceptanceProbability,←expectedValue_ite_one]
    rfl
  rw [he]
  unfold DigestSampling.acceptanceProbability SigGolfResearch.Gate6.acceptance
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num
structure BankCore where
  targets : List HashOutput
  exposures : List HashOutput
  reused : Bool
  reuse : ENNReal
  slack : Nat
noncomputable def corePotential (b : BankCore) : ENNReal :=
  if BPORS.Numeric.proposalLength < b.exposures.length then 0
  else if b.reused = true then 1 + b.reuse
  else ledger (BPORS.Numeric.proposalLength - b.exposures.length) b.targets b.exposures b.slack + b.reuse
theorem expectedValue_add_const_le {α : Type} (p : ProbComp α) (f : α → ENNReal) (c : ENNReal) :
    expectedValue p (fun x => f x + c) ≤ expectedValue p f + c := by
  rw [expectedValue_add]
  exact add_le_add le_rfl (expectedValue_le_of_le p fun _ => le_rfl)
def BankCore.expose (b : BankCore) (C' : ENNReal) (o : Option HashOutput) : BankCore :=
  { b with exposures := b.exposures ++ o.toList, reuse := C' }
end SigGolfCandidate.T3.Security.CaseC
end
-- ==== merged from T3_Secc_SeccSufPayload ====
section

section
namespace SigGolfCandidate.T3.Security.BSuf
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] buildFts buildTree
abbrev S (answers : Answers) (index coord leaf : Nat) : Digest := Extract.ftsSecret answers index coord leaf
theorem hdrBlock_nodeInputP (tag lay tree heap : Nat) (l p r : Digest) :
    Extract.hdrBlock (nodeInputP tag lay tree heap l p r) = bytesLE 16 (nodeTweak tag lay tree heap) := by
  unfold nodeInputP; exact Extract.hdrBlock_block4 _ _ _ _
theorem hdrBlock_ftsLeafInputP (index coord leaf : Nat) (a s b : Digest) :
    Extract.hdrBlock (ftsLeafInputP index coord leaf a s b) = bytesLE 16 (header 9 coord index 0 leaf) := by
  unfold ftsLeafInputP; exact Extract.hdrBlock_block4 _ _ _ _
end SigGolfCandidate.T3.Security.BSuf
end
section
namespace SigGolfCandidate.T3.Security.BSuf
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] buildFts buildTree
end SigGolfCandidate.T3.Security.BSuf
end
end
-- ==== merged from T3_Secc_SeccSufSigned ====
section

namespace SigGolfCandidate.T3.Security.BPB
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_seccSufSigned : DecidableEq T3.Cache := Classical.decEq _
attribute [local irreducible] buildFts buildTree
end SigGolfCandidate.T3.Security.BPB
end
-- ==== merged from T3_Secc_SeccSufRoute ====
section

namespace SigGolfCandidate.T3.Security.BPB
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final Correctness
open SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3M.SecurityExtraction (queried queried_bind queried_shortHash)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_seccSufRoute : DecidableEq T3.Cache := Classical.decEq _
attribute [local irreducible] buildFts buildTree
theorem digestInput_length (rho : Digest) (m : Message) (c : BitVec 32) : (digestInput rho m c).length = 64 := by
  simp [digestInput, SphincsSecurity.bytesLE_length]
theorem pad64_digestInput (rho : Digest) (m : Message) (c : BitVec 32) :
    pad64 (digestInput rho m c) = digestInput rho m c := by
  simp [pad64, digestInput_length]
theorem digestInput_injective {rho rho' : Digest} {m m' : Message} {c c' : BitVec 32}
    (h : pad64 (digestInput rho m c) = pad64 (digestInput rho' m' c')) : rho = rho' ∧ c = c' ∧ m = m' := by
  rw [pad64_digestInput, pad64_digestInput] at h
  obtain ⟨hr, hm, hc⟩ := SigGolfCandidate.T3.digestInput_injective h
  exact ⟨hr, hc, hm⟩
theorem queried_digest (answers : Correctness.Answers) (rho : Digest) (m : Message) (c : BitVec 32) :
    queried answers (digest rho m c) = [.inl (.inr (pad64 (digestInput rho m c)))] := rfl
def hdrTag (input : HashInput) : Nat :=
  if 128 ≤ ((Extract.hdrBlock input).getD 0 0).toNat then 1
  else ((Extract.hdrBlock input).getD 1 0).toNat
theorem hdrBlock_digestInput (rho : Digest) (m : Message) (c : BitVec 32) :
    Extract.hdrBlock (pad64 (digestInput rho m c)) = SphincsSecurity.bytesLE 16 (digestHeader c) := by
  rw [pad64_digestInput]
  exact Extract.hdrBlock_prefix _ _ _
/-- First header byte (the pre-C4 digest marker). -/
def hdrByte0 (input : HashInput) : Nat := ((Extract.hdrBlock input).getD 0 0).toNat
/-- C4 (adapted from b3cc11b): the low header word (bytes 16..24 of the input). The digest is the only query whose low
header word is zero (`digestHeader_lowNat`, `nodeTweak_low_ne_zero`); byte0 alone no longer separates it, because a
top fold label `topNodeWord heap` has byte0 = 0 at the heaps `256 k`. -/
def hdrMarker (input : HashInput) : Nat := readLE ((Extract.hdrBlock input).take 8)
theorem hdrMarker_eq {input : HashInput} {hdr : Digest}
    (h : Extract.hdrBlock input = SphincsSecurity.bytesLE 16 hdr) : hdrMarker input = tweakLow hdr := by
  unfold hdrMarker tweakLow
  rw [h]
  have hs := T3M.readLE_append ((SphincsSecurity.bytesLE 16 hdr).take 8) ((SphincsSecurity.bytesLE 16 hdr).drop 8)
  rw [List.take_append_drop, T3M.readLE_bytesLE 16 hdr] at hs
  have hl : ((SphincsSecurity.bytesLE 16 hdr).take 8).length = 8 := by simp [SphincsSecurity.bytesLE_length]
  have hlt := T3M.readLE_lt ((SphincsSecurity.bytesLE 16 hdr).take 8)
  rw [hl] at hs hlt
  omega
theorem hdrMarker_ne_zero_of_byte0 {input : HashInput} (h : hdrByte0 input ≠ 0) : hdrMarker input ≠ 0 := by
  unfold hdrMarker
  intro h0
  have hd := T3M.readLE_div_mod ((Extract.hdrBlock input).take 8) 0
  rw [h0] at hd
  apply h
  unfold hdrByte0
  have : ((Extract.hdrBlock input).take 8).getD 0 0 = (Extract.hdrBlock input).getD 0 0 := by
    cases Extract.hdrBlock input <;> rfl
  rw [← this, ← hd]
  rfl
theorem hdrMarker_ne_zero {input : HashInput} {hdr : Digest}
    (h : Extract.hdrBlock input = SphincsSecurity.bytesLE 16 hdr) (hm : tweakMarker hdr ≠ 0) :
    hdrMarker input ≠ 0 := by
  rw [hdrMarker_eq h]
  unfold tweakMarker at hm
  unfold tweakLow
  omega
theorem hdrMarker_digestInput (rho : Digest) (m : Message) (c : BitVec 32) :
    hdrMarker (pad64 (digestInput rho m c)) = 0 := by
  rw [hdrMarker_eq (hdrBlock_digestInput rho m c), digestHeader_lowNat]
def NotDigestQ : T3.Spec.Domain → Prop
  | .inl (.inr input) => hdrMarker input ≠ 0
  | _ => True
theorem projHash_ok_marker (high : Bool) {input : HashInput} {hdr : Digest}
    (h : Extract.hdrBlock (pad64 input) = SphincsSecurity.bytesLE 16 hdr) (hm : tweakLow hdr ≠ 0) :
    AllQueriesSatisfy (projHash high input) NotDigestQ := by
  unfold projHash publicHash
  apply SourceQueries.bind_allowed
  · exact (allQueriesSatisfy_query_iff _ _).mpr (show hdrMarker (pad64 input) ≠ 0 by rw [hdrMarker_eq h]; exact hm)
  · intro _; exact SourceQueries.pure_allowed _ _
theorem shortHash_ok_marker {input : HashInput} {hdr : Digest}
    (h : Extract.hdrBlock (pad64 input) = SphincsSecurity.bytesLE 16 hdr) (hm : tweakMarker hdr ≠ 0) :
    AllQueriesSatisfy (shortHash input) NotDigestQ := by
  unfold shortHash publicHash
  apply SourceQueries.bind_allowed
  · exact (allQueriesSatisfy_query_iff _ _).mpr (hdrMarker_ne_zero h hm)
  · intro _; exact SourceQueries.pure_allowed _ _
theorem shortHash_ok {input : HashInput} {tag lay tree position index : Nat}
    (h : Extract.hdrBlock (pad64 input) = SphincsSecurity.bytesLE 16 (header tag lay tree position index))
    (_ht : tag % 256 ≠ 0) : AllQueriesSatisfy (shortHash input) NotDigestQ :=
  shortHash_ok_marker h (by rw [header_marker]; decide)
theorem privatePair_ok (tag lay tree position index : Nat) :
    AllQueriesSatisfy (privatePair tag lay tree position index) NotDigestQ :=
  SourceQueries.privatePair_allowed NotDigestQ (fun _ => trivial) tag lay tree position index
theorem mask_ok (level index : Nat) : AllQueriesSatisfy (mask level index) NotDigestQ :=
  SourceQueries.mask_allowed NotDigestQ (fun _ => trivial) level index
theorem chain_ok (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count value) NotDigestQ := by
  unfold chain
  apply SourceQueries.foldlM_allowed NotDigestQ
  intro v step
  unfold shortHash publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    change hdrMarker (pad64 (chainInput lay tree leaf i step v)) ≠ 0
    rw [chainInput_padded]
    apply hdrMarker_ne_zero_of_byte0
    unfold hdrByte0 Extract.hdrBlock
    rw [chainInput_header, bytesLE16_first_toNat]
    have := chainHeader_firstByte lay tree leaf i step
    omega
  · intro _; exact SourceQueries.pure_allowed _ _
/-- Witness stack: top chain steps (G: `value | header | 0 | 0`, F: `chainInput`) have the chain header in bytes
`16..32`. -/
theorem topChain_ok (leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (topChain leaf i start count value) NotDigestQ := by
  unfold topChain
  apply SourceQueries.foldlM_allowed NotDigestQ
  intro v step
  unfold projHash publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    have hpad : pad64 (topChainInput leaf i step v) = topChainInput leaf i step v := by
      unfold topChainInput; split
      · simp [pad64, SphincsSecurity.bytesLE_length, zero16]
      · exact chainInput_padded _ _ _ _ _ _
    have hhdr : ((topChainInput leaf i step v).drop 16).take 16 = SphincsSecurity.bytesLE 16 (chainHeader 0 0 leaf i step) := by
      unfold topChainInput; split
      · simp [zero16, List.append_assoc, SphincsSecurity.bytesLE_length]
      · exact chainInput_header _ _ _ _ _ _
    change hdrMarker (pad64 (topChainInput leaf i step v)) ≠ 0
    rw [hpad]
    apply hdrMarker_ne_zero_of_byte0
    unfold hdrByte0 Extract.hdrBlock
    rw [hhdr, bytesLE16_first_toNat]
    have := chainHeader_firstByte 0 0 leaf i step
    omega
  · intro _; exact SourceQueries.pure_allowed _ _
theorem layChain_ok (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (layChain lay tree leaf i start count value) NotDigestQ := by
  unfold layChain; split
  · exact topChain_ok _ _ _ _ _
  · exact chain_ok _ _ _ _ _ _ _
theorem leafHash_ok (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) NotDigestQ :=
  projHash_ok_marker _ (Extract.hdrBlock_leafInput _ _ _ _) (by
    have h := leafTweak_marker lay tree leaf
    unfold tweakMarker at h; unfold tweakLow; omega)
theorem nodeHash_ok (tag lay tree heap : Nat) (left right : Digest) (_ht : tag % 256 ≠ 0) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) NotDigestQ := by
  rw [nodeHash_eq_projHash]
  exact projHash_ok_marker _ (by rw [pad64_nodeInputP]; exact BSuf.hdrBlock_nodeInputP _ _ _ _ _ _ _)
    (nodeTweak_low_ne_zero _ _ _ _)
theorem nodeHash3_ok (lay tree heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (nodeHash 3 lay tree heap left right) NotDigestQ :=
  nodeHash_ok 3 lay tree heap left right (by decide)
theorem ftsLeaf_ok (index coord leaf : Nat) (secret : Digest) :
    AllQueriesSatisfy (ftsLeaf index coord leaf secret) NotDigestQ := by
  rw [ftsLeaf_eq_shortHash]
  exact shortHash_ok (tag := 9) (by rw [pad64_ftsLeafInputP]; exact BSuf.hdrBlock_ftsLeafInputP _ _ _ _ _ _)
    (by decide)
theorem forestPk_ok (index : Nat) (roots : List Digest) : AllQueriesSatisfy (forestPk index roots) NotDigestQ := by
  rw [Extract.forestPk_eq_shortHash]
  exact shortHash_ok (tag := 11) (Extract.hdrBlock_listInput _ _ _) (by decide)
theorem encoding_ok (lay : Layer) (tree leaf : Nat) (message : Digest) (counter : BitVec 32) :
    AllQueriesSatisfy (shortHash (encodingInput lay tree leaf message counter)) NotDigestQ :=
  shortHash_ok_marker (by
    rw [Extract.hdrBlock_pad64 _ (by simp [encodingInput, SphincsSecurity.bytesLE_length])]
    exact Extract.hdrBlock_prefix _ _ _) (by rw [rowTweak_marker]; decide)
theorem counterSearch_ok (lay : Layer) (tree leaf : Nat) (message : Digest) :
    ∀ fuel counter, AllQueriesSatisfy (counterSearch lay tree leaf message counter fuel) NotDigestQ := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact SourceQueries.pure_allowed _ _
  | succ fuel ih =>
      intro counter
      unfold counterSearch
      apply SourceQueries.bind_allowed _ (encoding_ok _ _ _ _ _)
      intro answer
      split
      · exact ih _
      · exact SourceQueries.pure_allowed _ _
theorem buildLevel_ok (tag lay tree h level : Nat) (nodes : List Digest) (ht : tag % 256 ≠ 0) :
    AllQueriesSatisfy (buildLevel tag lay tree h level nodes) NotDigestQ := by
  unfold buildLevel
  exact SourceQueries.mapM_allowed NotDigestQ _ _ fun _ => nodeHash_ok _ _ _ _ _ _ ht
theorem buildLevels_ok (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 0) :
    AllQueriesSatisfy (buildLevels tag lay tree h leaves) NotDigestQ := by
  unfold buildLevels
  exact SourceQueries.foldlM_allowed NotDigestQ _ _ (fun _ _ =>
    SourceQueries.bind_allowed _ (buildLevel_ok _ _ _ _ _ _ ht) fun _ => SourceQueries.pure_allowed _ _) _
theorem buildLevels3_ok (lay tree h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevels 3 lay tree h leaves) NotDigestQ := buildLevels_ok 3 lay tree h leaves (by decide)
theorem buildLevels10_ok (lay tree h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevels 10 lay tree h leaves) NotDigestQ := buildLevels_ok 10 lay tree h leaves (by decide)
section aesopShape
attribute [local aesop safe apply] SourceQueries.pure_allowed SourceQueries.bind_allowed SourceQueries.map_allowed
  SourceQueries.foldlM_allowed SourceQueries.mapM_allowed privatePair_ok mask_ok chain_ok topChain_ok layChain_ok leafHash_ok nodeHash3_ok
  ftsLeaf_ok forestPk_ok counterSearch_ok buildLevels3_ok buildLevels10_ok
theorem buildLeaf_ok (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeaf lay tree leaf digits signatureOnly) NotDigestQ := by
  unfold buildLeaf; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] buildLeaf_ok
theorem buildTree_ok (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (buildTree lay tree selected digits) NotDigestQ := by
  unfold buildTree; aesop (config := { maxRuleApplications := 1000 })
theorem buildFts_ok (index coord : Nat) : AllQueriesSatisfy (buildFts index coord) NotDigestQ := by
  unfold buildFts; aesop (config := { maxRuleApplications := 1000 })
theorem topPath_ok (cache : T3.Cache) (leaf : Nat) : AllQueriesSatisfy (topPath cache leaf) NotDigestQ := by
  unfold topPath; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] buildTree_ok buildFts_ok topPath_ok
/-- Witness stack: a top nonce trial is a projected node hash with the node tweak in bytes `16..32`. -/
theorem topNodeHashN_ok (heap n : Nat) (left right : Digest) :
    AllQueriesSatisfy (topNodeHashN heap n left right) NotDigestQ := by
  unfold topNodeHashN
  refine projHash_ok_marker _ (hdr := nodeTweak 3 0 0 heap) ?_ (nodeTweak_low_ne_zero _ _ _ _)
  rw [Extract.hdrBlock_pad64 _ (by simp [topNodeInput, nonceBytes, SphincsSecurity.bytesLE_length])]
  unfold topNodeInput
  rw [List.append_assoc]
  exact Extract.hdrBlock_prefix _ _ _
attribute [local aesop safe apply] topNodeHashN_ok
theorem topNonceSearch_ok (h heap : Nat) (left right : Digest) :
    ∀ fuel n, AllQueriesSatisfy (topNonceSearch h heap left right fuel n) NotDigestQ
  | 0, n => by unfold topNonceSearch; aesop (config := { maxRuleApplications := 1000 })
  | fuel + 1, n => by
      have ih := topNonceSearch_ok h heap left right fuel (n + 1)
      unfold topNonceSearch; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] topNonceSearch_ok
theorem topNodeAt_ok (h heap : Nat) (left right : Digest) : AllQueriesSatisfy (topNodeAt h heap left right) NotDigestQ := by
  unfold topNodeAt; exact topNonceSearch_ok h heap left right _ 0
attribute [local aesop safe apply] topNodeAt_ok
theorem buildTopLevel_ok (level : Nat) (nodes : List Digest) : AllQueriesSatisfy (buildTopLevel level nodes) NotDigestQ := by
  unfold buildTopLevel; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] buildTopLevel_ok
theorem buildTopLevels_ok (leaves : List Digest) : AllQueriesSatisfy (buildTopLevels leaves) NotDigestQ := by
  unfold buildTopLevels; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] buildTopLevels_ok
theorem topPairsFrom_ok (first start : Nat) (init : List Digest) :
    AllQueriesSatisfy (topPairsFrom first start init) NotDigestQ := by
  unfold topPairsFrom topSeedPair; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] topPairsFrom_ok
theorem topCoefs_ok (leaf : Nat) : AllQueriesSatisfy (topCoefs leaf) NotDigestQ := by
  unfold topCoefs; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] topCoefs_ok
theorem topCoefsK_ok (f : Nat) (carry : Digest) : AllQueriesSatisfy (topCoefsK f carry) NotDigestQ := by
  unfold topCoefsK; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] topCoefsK_ok
theorem buildLeafTopC_ok (leaf : Nat) (coefs : List Digest) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeafTopC leaf coefs digits signatureOnly) NotDigestQ := by
  unfold buildLeafTopC; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] buildLeafTopC_ok
theorem buildLeafTop_ok (leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeafTop leaf digits signatureOnly) NotDigestQ := by
  unfold buildLeafTop; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] buildLeafTop_ok
theorem topFamilyCoefs_ok (leaf : Nat) (cc : List Digest × Digest) :
    AllQueriesSatisfy (topFamilyCoefs leaf cc) NotDigestQ := by
  unfold topFamilyCoefs; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] topFamilyCoefs_ok
theorem topTreeStep_ok (st : List Digest × List Digest × Digest) (leaf : Nat) :
    AllQueriesSatisfy (topTreeStep st leaf) NotDigestQ := by
  unfold topTreeStep; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] topTreeStep_ok
theorem buildTopTree_ok : AllQueriesSatisfy buildTopTree NotDigestQ := by
  unfold buildTopTree; aesop (config := { maxRuleApplications := 1000 })
theorem signTop_ok (cache : T3.Cache) (leaf : Nat) (digits : List Nat) :
    AllQueriesSatisfy (signTop cache leaf digits) NotDigestQ := by
  unfold signTop; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] signTop_ok
theorem signLayers_ok (cache : T3.Cache) (index n : Nat) (message : Digest) :
    AllQueriesSatisfy (signLayers cache index n message) NotDigestQ := by
  induction n generalizing message with
  | zero => unfold signLayers; aesop (config := { maxRuleApplications := 1000 })
  | succ n ih => unfold signLayers; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] signLayers_ok
theorem forestRows_ok (index : Nat) (chosen : List Selection) :
    AllQueriesSatisfy (Correctness.forestRows index chosen) NotDigestQ := by
  unfold Correctness.forestRows; aesop (config := { maxRuleApplications := 1000 })
attribute [local aesop safe apply] forestRows_ok
theorem payloadAfterDigest_ok (cache : T3.Cache) (rho : Digest) (output : HashOutput) :
    AllQueriesSatisfy (payloadAfterDigest cache rho output) NotDigestQ := by
  rw [SigningRecords.payloadAfterDigest_forestRows]; aesop (config := { maxRuleApplications := 1000 })
end aesopShape
theorem allQ_queried {α : Type} (answers : Correctness.Answers) (P : T3.Spec.Domain → Prop) (program : M α)
    (h : AllQueriesSatisfy program P) : ∀ q ∈ queried answers program, P q := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      intro q hq
      rw [SecurityExtraction.queried_query_bind] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hi
      · exact ih _ (hn _) q hq
theorem queried_privateMac (answers : Correctness.Answers) (region : Region) :
    queried answers (privateMac region) =
      [.inr (.inl (header 14 0 0 0 0)), .inr (.inl (header 14 0 0 0 1))] := rfl
theorem queried_privateNonce (answers : Correctness.Answers) (m : Message) :
    queried answers (privateNonce m) = [.inr (.inr (.inl m))] := rfl
end SigGolfCandidate.T3.Security.BPB
end
-- ==== merged from T3_Secc_CaseCBankReuse ====
section

section
namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCBankDefs : DecidableEq T3.Cache := Classical.decEq _
def IsDigestInput (x : HashInput) : Prop :=
  ∃ (rho : Digest) (m : Message) (c : BitVec 32), x = pad64 (digestInput rho m c)
structure Ghost where
  targets : List HashOutput
  exposures : List HashOutput
  reused : Bool
  dead : Bool
  log : QueryLog Requests
def Ghost.empty : Ghost := ⟨[], [], false, false, []⟩
abbrev BankState := Ghost × QueryRecorded.State
def countOf (s : QueryRecorded.State) : Nat := s.base.source.1
def lazyOf (s : QueryRecorded.State) : LazyPrivate.State := s.base.source.2
def horizon : Nat := BPORS.Numeric.proposalLength
def Birth (budget : Nat) (x : HashInput) (before : QueryRecorded.State) : Prop :=
  IsDigestInput x ∧ (lazyOf before).2 x = none ∧ countOf before < budget
def FreshSigning (published : T3.Cache) (request : Request) (before : QueryRecorded.State) : Prop :=
  request.cache = published ∧ (lazyOf before).1 (.inr (.inl request.message)) = none
end SigGolfCandidate.T3.Security.CaseC
end
section
namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCBankReuse : DecidableEq T3.Cache := Classical.decEq _
theorem query_new_public (input : T3.Spec.Domain) (before : LazyPrivate.State)
    (result : T3.Spec.Range input × LazyPrivate.State)
    (h : result ∈ support (LazyPrivate.run (liftM (T3.Spec.query input)) before)) (x : HashInput)
    (hx : before.2 x = none) (hr : result.2.2 x ≠ none) : input = .inl (.inr x) := by
  rw [LazyPrivate.run_query] at h
  cases input with
  | inl input =>
      simp only [PrivateTable.lazyImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at h
      obtain ⟨step, hstep, rfl⟩ := h
      cases input with
      | inl n =>
          change step ∈ support ((fun answer => (answer, before.2)) <$>
            ($ᵗ (SphincsSecurity.OracleWorld.Range (.inl n)) : ProbComp _)) at hstep
          rw [support_map] at hstep
          obtain ⟨_, _, rfl⟩ := hstep
          exact absurd hx hr
      | inr y =>
          by_cases hxy : y = x
          · rw [hxy]
          · exfalso
            apply hr
            change step ∈ support ((randomOracle (spec := SphincsSecurity.HashSpec) y).run before.2) at hstep
            rw [OracleSpec.randomOracle] at hstep
            cases hc : before.2 y with
            | some u =>
                rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hstep
                subst step
                exact hx
            | none =>
                rw [QueryImpl.withCaching_run_none _ hc, support_map] at hstep
                obtain ⟨v, _, rfl⟩ := hstep
                change (before.2.cacheQuery y v) x = none
                rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hxy)]
                exact hx
  | inr coordinate =>
      simp only [PrivateTable.lazyImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at h
      obtain ⟨step, _, rfl⟩ := h
      exact absurd hx hr
theorem run_new_public {α : Type} (program : M α) (Q : HashInput → Prop)
    (hQ : AllQueriesSatisfy program (fun q => ∀ x, q = .inl (.inr x) → Q x))
    (before : LazyPrivate.State) (result : α × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run program before)) (x : HashInput)
    (hx : before.2 x = none) (hnew : result.2.2 x ≠ none) : Q x := by
  induction program using OracleComp.inductionOn generalizing before with
  | pure value =>
      rw [LazyPrivate.run_pure, mem_support_pure_iff] at hr
      subst result
      exact absurd hx hnew
  | query_bind input next ih =>
      obtain ⟨hinput, htail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hQ
      rw [LazyPrivate.run_bind, mem_support_bind_iff] at hr
      obtain ⟨step, hstep, htailResult⟩ := hr
      by_cases hs : step.2.2 x = none
      · exact ih step.1 (htail step.1) step.2 htailResult hs
      · exact hinput x (query_new_public input before step hstep x hx hs)
theorem allQueriesSatisfy_mono {α : Type} (program : M α) (P Q : T3.Spec.Domain → Prop)
    (hPQ : ∀ q, P q → Q q) (h : AllQueriesSatisfy program P) : AllQueriesSatisfy program Q := by
  induction program using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hPQ _ hi, fun u => ih u (hn u)⟩
def DigestRowOf (x : HashInput) (m : Message) : Prop :=
  ∃ p : Digest × Fin (2 ^ 32), x = Sampling.digestTrial p.1 m p.2.val
def SignerQ (m : Message) : T3.Spec.Domain → Prop :=
  fun q => ∀ x, q = .inl (.inr x) → IsDigestInput x → DigestRowOf x m
theorem notDigestQ_signerQ (m : Message) (q : T3.Spec.Domain) (h : BPB.NotDigestQ q) : SignerQ m q := by
  intro x hq ⟨rho, m', c, hx⟩
  subst hq
  exfalso
  have := BPB.hdrMarker_digestInput rho m' c
  rw [← hx] at this
  exact h this
theorem digestTrial_rowOf (rho : Digest) (m : Message) (c : Nat) (hc : c < 2 ^ 32) :
    DigestRowOf (Sampling.digestTrial rho m c) m := ⟨(rho, ⟨c, hc⟩), rfl⟩
theorem digestRowOf_unique {x : HashInput} {m m' : Message} (h : DigestRowOf x m) (h' : DigestRowOf x m') :
    m = m' := by
  obtain ⟨p, rfl⟩ := h
  obtain ⟨p', hp'⟩ := h'
  have he := Sampling.pad64_inj_of_length (by simp [digestInput, SphincsSecurity.bytesLE_length]) hp'
  exact (digestInput_injective he).2.1
theorem tsum_indicator_le_of_subsingleton {β : Type} (P : β → Prop) [DecidablePred P]
    (hP : ∀ a b, P a → P b → a = b)
    (c : ENNReal) : (∑' b, if P b then c else 0) ≤ c := by
  by_cases h : ∃ b, P b
  · obtain ⟨b0, hb0⟩ := h
    rw [tsum_eq_single b0 (fun b hb => if_neg (fun hP' => hb (hP b b0 hP' hb0)))]
    simp [hb0]
  · push Not at h
    simp [h]
noncomputable def reusePotential (s : LazyPrivate.State) : ENNReal :=
  ∑' m : Message, if s.1 (.inr (.inl m)) = none then reuseMass s.2 m else 0
end SigGolfCandidate.T3.Security.CaseC
end
end
-- ==== merged from T3_Secc_CaseCBankStep ====
section

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCBankStep : DecidableEq T3.Cache := Classical.decEq _
theorem lazy_of_recorded {α : Type} (program : M α) (s : QueryRecorded.State) :
    (fun r : α × QueryRecorded.State => (r.1, lazyOf r.2)) <$> QueryRecorded.run program s =
      LazyPrivate.run program (lazyOf s) := by
  calc
    (fun r : α × QueryRecorded.State => (r.1, lazyOf r.2)) <$> QueryRecorded.run program s =
        Prod.map id Prod.snd <$> (Prod.map id MonitoredPrivate.State.source <$>
          (Prod.map id QueryRecorded.State.base <$> QueryRecorded.run program s)) := by
      simp only [Functor.map_map]
      rfl
    _ = LazyPrivate.run program (lazyOf s) := by
      rw [QueryRecorded.run_erasure, MonitoredPrivate.run_erasure, CountedPrivate.run_erasure]
      rfl
theorem expected_recorded {α : Type} (program : M α) (s : QueryRecorded.State)
    (f : α × LazyPrivate.State → ENNReal) :
    expectedValue (QueryRecorded.run program s) (fun r => f (r.1, lazyOf r.2)) =
      expectedValue (LazyPrivate.run program (lazyOf s)) f := by
  rw [← lazy_of_recorded, expectedValue_map]
theorem recorded_lazy_support {α : Type} (program : M α) (s : QueryRecorded.State) (r : α × QueryRecorded.State)
    (hr : r ∈ support (QueryRecorded.run program s)) :
    (r.1, lazyOf r.2) ∈ support (LazyPrivate.run program (lazyOf s)) := by
  rw [← lazy_of_recorded, support_map]
  exact ⟨r, hr, rfl⟩
theorem recorded_count_le {α : Type} (program : M α) (s : QueryRecorded.State) (r : α × QueryRecorded.State)
    (hr : r ∈ support (QueryRecorded.run program s)) : countOf s ≤ countOf r.2 :=
  CreationGame.recorded_count_monotone program s r hr
noncomputable def bankValue (g : Ghost) : ENNReal :=
  (g.targets.map fun N => forecast (horizon - g.exposures.length) g.exposures N).sum
noncomputable def excessTerm (budget count : Nat) (g : Ghost) : ENNReal :=
  ((budget - count : Nat) : ENNReal) * excessForecast (horizon - g.exposures.length) g.exposures / 2 ^ 128
noncomputable def livePotential (budget count : Nat) (g : Ghost) (lazy : LazyPrivate.State) : ENNReal :=
  if g.dead = true ∨ budget < count then 0
  else if g.reused = true then 1 + reusePotential lazy
  else bankValue g + reusePotential lazy + excessTerm budget count g
noncomputable def potential (budget : Nat) (st : BankState) : ENNReal :=
  livePotential budget (countOf st.2) st.1 (lazyOf st.2)
theorem expectedValue_liftM {α : Type} (X : ProbComp α) (g : α → ENNReal) :
    expectedValue (liftM X : PMF α) g = expectedValue X g := by
  unfold expectedValue
  rfl
theorem expectedValue_pmf_map {α β : Type} (X : PMF α) (f : α → β) (g : β → ENNReal) :
    expectedValue (X.map f) g = expectedValue X (fun x => g (f x)) := by
  rw [← PMF.monad_map_eq_map, expectedValue_map]
theorem lazy_world_coin (n : Nat) (lazy : LazyPrivate.State)
    (r : SphincsSecurity.OracleWorld.Range (.inl n) × LazyPrivate.State)
    (hr : r ∈ support (LazyPrivate.run (forwardWorld (.inl n)) lazy)) : r.2 = lazy := by
  change r ∈ support (LazyPrivate.run (liftM (T3.Spec.query (.inl (.inl n)))) lazy) at hr
  rw [LazyPrivate.run_query] at hr
  simp only [PrivateTable.lazyImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hr
  obtain ⟨step, hstep, rfl⟩ := hr
  change step ∈ support ((fun answer => (answer, lazy.2)) <$>
    ($ᵗ (SphincsSecurity.OracleWorld.Range (.inl n)) : ProbComp _)) at hstep
  rw [support_map] at hstep
  obtain ⟨_, _, rfl⟩ := hstep
  rfl
theorem lazy_world_cached (x : HashInput) (lazy : LazyPrivate.State) (a0 : HashOutput) (hx : lazy.2 x = some a0) :
    LazyPrivate.run (forwardWorld (.inr x)) lazy = pure (a0, lazy) := by
  change LazyPrivate.run (Sampling.publicHandler x) lazy = _
  rw [LazyPrivate.run_publicQuery, randomOracle.run_eq, hx]
  simp
theorem lazy_world_fresh (x : HashInput) (lazy : LazyPrivate.State) (hx : lazy.2 x = none)
    (f : HashOutput × LazyPrivate.State → ENNReal) :
    expectedValue (LazyPrivate.run (forwardWorld (.inr x)) lazy) f =
      expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => f (a, (lazy.1, lazy.2.cacheQuery x a))) := by
  change expectedValue (LazyPrivate.run (Sampling.publicHandler x) lazy) f = _
  rw [LazyPrivate.run_publicQuery, expectedValue_bind]
  simp only [expectedValue_pure]
  exact Sampling.expectedValue_fresh x lazy.2 hx (fun result => f (result.1, (lazy.1, result.2)))
theorem digestRowOf_isDigest {x : HashInput} {m : Message} (h : DigestRowOf x m) : IsDigestInput x := by
  obtain ⟨p, rfl⟩ := h
  exact ⟨p.1, m, BitVec.ofNat 32 p.2.val, rfl⟩
theorem expectedValue_list_sum {α β : Type} (law : PMF α) (l : List β) (f : β → α → ENNReal) :
    expectedValue law (fun a => (l.map fun b => f b a).sum) = (l.map fun b => expectedValue law (f b)).sum := by
  induction l with
  | nil => simp [expectedValue]
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [expectedValue_add, ih]
end SigGolfCandidate.T3.Security.CaseC
end
-- ==== merged from ClaudeWCT_Bank_Kernel ====
section

section
namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete (independentProposalWord uniformWordAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
noncomputable def forecast (R : Nat) (X : List HashOutput) (N : HashOutput) : ENNReal :=
  expectedValue (independentProposalWord S.accepted R) (fun F => S.score (X ++ F) N)
theorem forecast_zero (X : List HashOutput) (N : HashOutput) : S.forecast 0 X N = S.score X N := by
  unfold forecast
  change expectedValue (pure [] : PMF (List HashOutput)) _ = _
  rw [expectedValue_pure, List.append_nil]
theorem forecast_step (R : Nat) (X : List HashOutput) (N : HashOutput) :
    expectedValue S.accepted (fun A => S.forecast R (X ++ [A]) N) = S.forecast (R + 1) X N := by
  unfold forecast
  rw [independentProposalWord, ← PMF.monad_bind_eq_bind, expectedValue_bind]
  apply congrArg
  funext A
  rw [← PMF.monad_map_eq_map, expectedValue_map]
  apply congrArg
  funext F
  simp only [List.append_assoc, List.singleton_append]
theorem score_le_forecast (R : Nat) (X : List HashOutput) (N : HashOutput) :
    S.score X N ≤ S.forecast R X N := by
  unfold forecast
  calc
    S.score X N = expectedValue (independentProposalWord S.accepted R) (fun _ => S.score X N) :=
      (expectedValue_const (by simp) _).symm
    _ ≤ _ := expectedValue_mono _ fun F => S.score_append_mono X F N
theorem expected_word_proposals (R : Nat) (g : List P → ENNReal) :
    expectedValue (independentProposalWord S.accepted R) (fun F => g (S.proposals F)) =
      ClaudeWCT.Numerics.Law.lawAvg S.law R g := by
  induction R generalizing g with
  | zero =>
      change expectedValue (pure [] : PMF (List HashOutput)) _ = _
      rw [expectedValue_pure]
      rfl
  | succ R ih =>
      rw [independentProposalWord, ← PMF.monad_bind_eq_bind, expectedValue_bind, ClaudeWCT.Numerics.Law.lawAvg_succ]
      have hstep (A : HashOutput) : expectedValue ((independentProposalWord S.accepted R).map (A :: ·))
          (fun F => g (S.proposals F)) = ClaudeWCT.Numerics.Law.lawAvg S.law R (fun W => g (S.proposal A :: W)) := by
        rw [← PMF.monad_map_eq_map, expectedValue_map]
        exact ih (fun W => g (S.proposal A :: W))
      simp_rw [hstep]
      exact S.expected_accepted_proposal (fun p => ClaudeWCT.Numerics.Law.lawAvg S.law R (fun W => g (p :: W)))
theorem average_forecast (R : Nat) (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => S.forecast R X N) =
      ClaudeWCT.Numerics.Law.lawAvg S.law R (fun W => S.price (S.proposals X ++ W)) / 2 ^ 128 := by
  unfold forecast
  rw [CaseC.finiteAverage_expectedValue]
  have hav : ∀ F : List HashOutput, BPORS.finiteAverage (fun N : HashOutput => S.score (X ++ F) N) =
      S.price (S.proposals X ++ S.proposals F) / 2 ^ 128 := by
    intro F
    rw [S.average_score, ← S.proposals_append]
    rfl
  simp_rw [hav]
  refine (S.expected_word_proposals R (fun W => S.price (S.proposals X ++ W) / 2 ^ 128)).trans ?_
  simp only [div_eq_mul_inv]
  rw [show (fun W => S.price (S.proposals X ++ W) * (2 ^ 128 : ENNReal)⁻¹) =
      fun W => (2 ^ 128 : ENNReal)⁻¹ * S.price (S.proposals X ++ W) by
    funext W; exact mul_comm _ _, ClaudeWCT.Numerics.Law.lawAvg_mul_left, mul_comm]
noncomputable def excessForecast (R : Nat) (X : List HashOutput) : ENNReal :=
  ClaudeWCT.Numerics.Law.lawAvg S.law R (fun W => S.price (S.proposals X ++ W) - S.specTheta)
theorem excessForecast_step (R : Nat) (X : List HashOutput) :
    expectedValue S.accepted (fun A => S.excessForecast R (X ++ [A])) = S.excessForecast (R + 1) X := by
  unfold excessForecast
  rw [ClaudeWCT.Numerics.Law.lawAvg_succ]
  have hA (A : HashOutput) : ClaudeWCT.Numerics.Law.lawAvg S.law R
      (fun W => S.price (S.proposals (X ++ [A]) ++ W) - S.specTheta) =
      (fun p : P => ClaudeWCT.Numerics.Law.lawAvg S.law R
        (fun W => S.price (S.proposals X ++ p :: W) - S.specTheta)) (S.proposal A) := by
    simp [proposals, List.map_append, List.append_assoc]
  simp_rw [hA]
  exact S.expected_accepted_proposal (fun p => ClaudeWCT.Numerics.Law.lawAvg S.law R
    (fun W => S.price (S.proposals X ++ p :: W) - S.specTheta))
theorem average_forecast_le (R : Nat) (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => S.forecast R X N) ≤
      (S.specTheta + S.excessForecast R X) / 2 ^ 128 := by
  rw [average_forecast]
  apply ENNReal.div_le_div_right
  unfold excessForecast
  calc
    _ ≤ ClaudeWCT.Numerics.Law.lawAvg S.law R
          (fun W => S.specTheta + (S.price (S.proposals X ++ W) - S.specTheta)) :=
      ClaudeWCT.Numerics.Law.lawAvg_mono S.law R fun W => le_add_tsub
    _ = _ := by
      rw [ClaudeWCT.Numerics.Law.lawAvg_add, ClaudeWCT.Numerics.Law.lawAvg_const S.law S.law_sum]
theorem excessForecast_initial : S.excessForecast S.horizon [] ≤ S.excessRate := by
  unfold excessForecast
  simpa [proposals] using S.excess_le
end FtsBankSpec
end ClaudeWCT.Bank
end
section
namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Completeness (searchLoop failMass)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
def search (rho : Digest) (message : Message) (counter fuel : Nat) : M (Option (BitVec 32 × HashOutput)) :=
  Sampling.publicProgram (searchLoop (Sampling.digestTrial rho message) S.decode
    (fun c output => pure (BitVec.ofNat 32 c, output)) fuel counter)
theorem step_le (w : HashOutput → ENNReal) (P' : ENNReal) (hP : S.freshPrice w ≤ P') :
    Sampling.acceptedWeight S.decode w + failMass S.decode * P' ≤ P' := by
  calc
    _ = S.acceptance * S.freshPrice w + (1 - S.acceptance) * P' := by
      have hw : Sampling.acceptedWeight S.decode w = S.acceptance * S.freshPrice w := by
        unfold freshPrice
        rw [div_eq_mul_inv, mul_comm, mul_assoc, ENNReal.inv_mul_cancel S.acceptance_ne_zero S.acceptance_ne_top,
          mul_one]
      rw [S.failMass_decode, hw]
    _ ≤ S.acceptance * P' + (1 - S.acceptance) * P' := add_le_add (mul_le_mul' le_rfl hP) le_rfl
    _ = P' := by rw [← add_mul, add_tsub_cancel_of_le S.acceptance_le_one, one_mul]
theorem search_le_price (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hreject : Sampling.CachedTrialsReject (Sampling.digestTrial rho message) S.decode 0 (2 ^ 32) cache)
    (w : HashOutput → ENNReal) (base P' : ENNReal) (hbase : base ≤ P') (hP : S.freshPrice w ≤ P') :
    expectedValue (Sampling.roRun secret (S.search rho message 0 fuel) cache)
      (fun result => result.1.elim base (fun found => w found.2)) ≤ P' := by
  exact CaseC.search_le_price secret (Sampling.digestTrial rho message) S.decode
    (fun c output => (BitVec.ofNat 32 c, output)) (fun found => w found.2) w (fun _ _ => rfl) base P' hbase
    (S.step_le w P' hP) (2 ^ 32)
    (fun _ _ hl hr he => Sampling.digestTrial_injective rho message hl hr he) fuel 0 (by omega) cache hreject
def Reuse (cache : Sampling.RCache) (rho : Digest) (m : Message) : Prop :=
  ¬Sampling.CachedTrialsReject (Sampling.digestTrial rho m) S.decode 0 (2 ^ 32) cache
noncomputable def admissibleEntry (cache : Sampling.RCache) (input : HashInput) : ENNReal :=
  (cache input).elim 0 (fun answer => if S.producer answer = true then 1 else 0)
noncomputable def reuseMass (cache : Sampling.RCache) (m : Message) : ENNReal :=
  (∑' p : Digest × Fin (2 ^ 32), S.admissibleEntry cache (Sampling.digestTrial p.1 m p.2.val)) / 2 ^ 128
theorem reuse_indicator_le (cache : Sampling.RCache) (rho : Digest) (m : Message) :
    (if S.Reuse cache rho m then (1 : ENNReal) else 0) ≤
      ∑ c : Fin (2 ^ 32), S.admissibleEntry cache (Sampling.digestTrial rho m c.val) := by
  split_ifs with h
  · unfold Reuse Sampling.CachedTrialsReject at h
    push Not at h
    obtain ⟨c, -, hc, answer, ha, hd⟩ := h
    have hadm : S.producer answer = true := by
      unfold decode at hd
      by_contra hn
      exact hd (by simp [hn])
    calc
      (1 : ENNReal) = S.admissibleEntry cache (Sampling.digestTrial rho m (⟨c, hc⟩ : Fin (2 ^ 32)).val) := by
        simp [admissibleEntry, ha, hadm]
      _ ≤ _ := Finset.single_le_sum (f := fun c : Fin (2 ^ 32) =>
          S.admissibleEntry cache (Sampling.digestTrial rho m c.val)) (fun _ _ => bot_le) (Finset.mem_univ _)
  · exact bot_le
theorem reuse_probability_le (cache : Sampling.RCache) (m : Message) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho => if S.Reuse cache rho m then 1 else 0) ≤
      S.reuseMass cache m := by
  rw [BPORS.expected_uniform_eq_finiteAverage]
  unfold BPORS.finiteAverage reuseMass
  simp only [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_div_right
  calc
    _ ≤ ∑ rho : Digest, ∑ c : Fin (2 ^ 32), S.admissibleEntry cache (Sampling.digestTrial rho m c.val) :=
      Finset.sum_le_sum fun rho _ => S.reuse_indicator_le cache rho m
    _ = ∑' p : Digest × Fin (2 ^ 32), S.admissibleEntry cache (Sampling.digestTrial p.1 m p.2.val) := by
      rw [tsum_fintype, Fintype.sum_prod_type]
noncomputable def admInd (a : HashOutput) : ENNReal := if S.producer a = true then 1 else 0
theorem expected_admInd : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) S.admInd = S.acceptance := by
  unfold admInd
  rw [expectedValue_ite_one]
  rfl
theorem expected_admInd_tight : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) S.admInd ≤ S.admBound := by
  rw [expected_admInd]
  exact S.acceptance_le
theorem admissibleEntry_cacheQuery (cache : Sampling.RCache) (x : HashInput) (a : HashOutput)
    (hx : cache x = none) (y : HashInput) :
    S.admissibleEntry (cache.cacheQuery x a) y = S.admissibleEntry cache y + if y = x then S.admInd a else 0 := by
  by_cases hy : y = x
  · subst hy
    simp [admissibleEntry, hx, admInd]
  · simp [admissibleEntry, hy]
theorem reuseMass_cacheQuery_le (cache : Sampling.RCache) (x : HashInput) (a : HashOutput)
    (hx : cache x = none) (m : Message) :
    S.reuseMass (cache.cacheQuery x a) m ≤
      S.reuseMass cache m + (if CaseC.DigestRowOf x m then S.admInd a else 0) / 2 ^ 128 := by
  unfold reuseMass
  rw [← ENNReal.add_div]
  apply ENNReal.div_le_div_right
  simp_rw [S.admissibleEntry_cacheQuery cache x a hx]
  rw [ENNReal.tsum_add]
  apply add_le_add le_rfl
  by_cases hrow : CaseC.DigestRowOf x m
  · rw [if_pos hrow]
    apply CaseC.tsum_indicator_le_of_subsingleton
    intro p q hp hq
    exact Sampling.WeightedSelection.digest_nonce_trials_injective m (2 ^ 32) le_rfl (hp.trans hq.symm)
  · rw [if_neg hrow]
    apply le_of_eq
    apply ENNReal.tsum_eq_zero.mpr
    intro p
    rw [if_neg]
    intro he
    exact hrow ⟨p, he.symm⟩
end FtsBankSpec
end ClaudeWCT.Bank
end
section
namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open CaseC (BankCore BankCore.expose theta)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
noncomputable def ledger (R : Nat) (targets X : List HashOutput) (slack : Nat) : ENNReal :=
  (targets.map fun N => S.forecast R X N).sum + (slack : ENNReal) * S.excessForecast R X / 2 ^ 128
theorem ledger_slack_succ (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    S.ledger R targets X (slack + 1) = S.ledger R targets X slack + S.excessForecast R X / 2 ^ 128 := by
  unfold ledger
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ENNReal.add_div, add_assoc]
theorem ledger_slack_mono (R : Nat) (targets X : List HashOutput) {slack slack' : Nat} (h : slack ≤ slack') :
    S.ledger R targets X slack ≤ S.ledger R targets X slack' := by
  unfold ledger
  apply add_le_add le_rfl
  apply ENNReal.div_le_div_right
  apply mul_le_mul' _ le_rfl
  exact_mod_cast h
theorem ledger_birth (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => S.ledger R (targets ++ [a]) X slack) ≤
      S.ledger R targets X (slack + 1) + S.specTheta / 2 ^ 128 := by
  have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => S.forecast R X a) ≤
      (S.specTheta + S.excessForecast R X) / 2 ^ 128 := by
    rw [BPORS.expected_uniform_eq_finiteAverage]
    exact S.average_forecast_le R X
  have hsplit : ∀ a, S.ledger R (targets ++ [a]) X slack = S.ledger R targets X slack + S.forecast R X a := by
    intro a
    simp only [ledger, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      add_zero]
    ring
  simp_rw [hsplit]
  rw [expectedValue_add, expectedValue_const (by simp : Pr[⊥ | ($ᵗ HashOutput : ProbComp HashOutput)] = 0),
    ledger_slack_succ, add_assoc]
  exact add_le_add le_rfl (hfa.trans (by rw [ENNReal.add_div, add_comm]))
theorem ledger_expose (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue S.accepted (fun A => S.ledger R targets (X ++ [A]) slack) = S.ledger (R + 1) targets X slack := by
  unfold ledger
  rw [expectedValue_add, CaseC.expectedValue_list_sum']
  congr 1
  · congr 1
    apply List.map_congr_left
    intro N _
    exact S.forecast_step R X N
  · simp only [div_eq_mul_inv]
    rw [show (fun A : HashOutput => (slack : ENNReal) * S.excessForecast R (X ++ [A]) * (2 ^ 128 : ENNReal)⁻¹) =
        fun A => (slack : ENNReal) * (2 ^ 128 : ENNReal)⁻¹ * S.excessForecast R (X ++ [A]) by
      funext A; ring]
    rw [CaseC.pmf_expectedValue_left_mul, S.excessForecast_step]
    ring
theorem ledger_freshPrice (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    S.freshPrice (fun A => S.ledger R targets (X ++ [A]) slack) = S.ledger (R + 1) targets X slack := by
  rw [← S.expected_accepted, ledger_expose]
theorem ledger_search (secret : BitVec 256) (rho : Digest) (message : Message) (fuel : Nat)
    (hlimit : fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hreject : Sampling.CachedTrialsReject (Sampling.digestTrial rho message) S.decode 0 (2 ^ 32) cache)
    (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue (Sampling.roRun secret (S.search rho message 0 fuel) cache)
      (fun result => result.1.elim (S.ledger (R + 1) targets X slack)
        (fun found => S.ledger R targets (X ++ [found.2]) slack)) ≤ S.ledger (R + 1) targets X slack :=
  S.search_le_price secret rho message fuel hlimit cache hreject _ _ _ le_rfl
    (S.ledger_freshPrice R targets X slack).le
theorem ledger_win (R : Nat) (targets X : List HashOutput) (slack : Nat) (N : HashOutput) (hN : N ∈ targets)
    (hadm : S.admissible N = true) (hcov : S.covered X N) : 1 ≤ S.ledger R targets X slack :=
  calc
    (1 : ENNReal) ≤ S.score X N := S.one_le_score X N hadm hcov
    _ ≤ S.forecast R X N := S.score_le_forecast R X N
    _ ≤ (targets.map fun N => S.forecast R X N).sum := List.le_sum_of_mem (List.mem_map_of_mem hN)
    _ ≤ _ := le_self_add
theorem ledger_initial (budget : Nat) :
    S.ledger S.horizon [] [] budget ≤ (budget : ENNReal) * S.excessRate / 2 ^ 128 := by
  unfold ledger
  simp only [List.map_nil, List.sum_nil, zero_add]
  apply ENNReal.div_le_div_right
  exact mul_le_mul' le_rfl S.excessForecast_initial
noncomputable def corePotential (b : BankCore) : ENNReal :=
  if S.horizon < b.exposures.length then 0
  else if b.reused = true then 1 + b.reuse
  else S.ledger (S.horizon - b.exposures.length) b.targets b.exposures b.slack + b.reuse
theorem corePotential_mono (b b' : BankCore) (ht : b'.targets = b.targets) (hx : b'.exposures = b.exposures)
    (hr : b'.reused = b.reused) (hC : b'.reuse ≤ b.reuse) (hs : b'.slack ≤ b.slack) :
    S.corePotential b' ≤ S.corePotential b := by
  unfold corePotential
  rw [ht, hx, hr]
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl hC
  · exact add_le_add (S.ledger_slack_mono _ _ _ hs) hC
theorem core_birth (b : BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + S.admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => S.corePotential { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      S.corePotential b + (theta + 1 / 64) / 2 ^ 128 := by
  have hadm : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun N => S.admInd N / 2 ^ 128) ≤
      S.admBound / 2 ^ 128 := by
    simp only [div_eq_mul_inv]
    rw [expectedValue_mul_const]
    exact mul_le_mul' (by simpa [div_eq_mul_inv] using S.expected_admInd_tight) le_rfl
  unfold corePotential
  simp only
  by_cases hd : S.horizon < b.exposures.length
  · simp only [hd, if_true]
    exact (expectedValue_le_of_le _ fun _ => le_rfl).trans bot_le
  simp only [hd, if_false]
  by_cases hr : b.reused = true
  · simp only [hr, if_true]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun N => S.admInd N / 2 ^ 128 + (1 + b.reuse)) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ S.admBound / 2 ^ 128 + (1 + b.reuse) :=
        (CaseC.expectedValue_add_const_le _ _ _).trans (add_le_add hadm le_rfl)
      _ ≤ _ := by
        rw [add_comm, ← S.theta_add_admBound]
        apply add_le_add le_rfl
        apply ENNReal.div_le_div_right
        exact le_add_self
  · simp only [hr, Bool.false_eq_true, if_false]
    set R := S.horizon - b.exposures.length
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => (S.ledger R (b.targets ++ [N]) b.exposures s + S.admInd N / 2 ^ 128) + b.reuse) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => S.ledger R (b.targets ++ [N]) b.exposures s + S.admInd N / 2 ^ 128) + b.reuse :=
        CaseC.expectedValue_add_const_le _ _ _
      _ ≤ (S.ledger R b.targets b.exposures (s + 1) + S.specTheta / 2 ^ 128 + S.admBound / 2 ^ 128) + b.reuse := by
        rw [expectedValue_add]
        exact add_le_add (add_le_add (S.ledger_birth R b.targets b.exposures s) hadm) le_rfl
      _ = _ := by
        rw [hs, ← S.theta_add_admBound, ENNReal.add_div]
        ring
theorem core_sign (b : BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + S.reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat) (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if S.Reuse cache rho m then S.corePotential { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (S.search rho m 0 fuel) cache)
        (fun result => S.corePotential (b.expose C' (result.1.map Prod.snd)))) ≤ S.corePotential b := by
  have hlenA : ∀ (o : Option HashOutput), b.exposures.length ≤ (b.exposures ++ o.toList).length := by
    intro o; simp
  by_cases hd : S.horizon < b.exposures.length
  · apply expectedValue_le_of_le
    intro rho
    have h0 : ∀ (o : Option HashOutput), S.corePotential (b.expose C' o) = 0 := by
      intro o
      unfold corePotential BankCore.expose
      simp only
      rw [if_pos (lt_of_lt_of_le hd (hlenA o))]
    split_ifs
    · unfold corePotential; simp only; rw [if_pos hd]; exact bot_le
    · exact (expectedValue_le_of_le _ fun result => (h0 _).le).trans bot_le
  by_cases hr : b.reused = true
  · have hb : S.corePotential b = 1 + b.reuse := by unfold corePotential; simp [hd, hr]
    rw [hb]
    apply expectedValue_le_of_le
    intro rho
    have hle : ∀ (o : Option HashOutput), S.corePotential (b.expose C' o) ≤ 1 + b.reuse := by
      intro o
      unfold corePotential BankCore.expose
      simp only [hr, if_true]
      split_ifs
      · exact bot_le
      · exact add_le_add le_rfl (le_of_add_le_left hC)
    split_ifs
    · unfold corePotential; simp only [hd, if_false, if_true]; exact add_le_add le_rfl (le_of_add_le_left hC)
    · exact expectedValue_le_of_le _ fun result => hle _
  have hr' : b.reused = false := by simpa using hr
  set R0 := S.horizon - b.exposures.length with hR0
  have hb : S.corePotential b = S.ledger R0 b.targets b.exposures b.slack + b.reuse := by
    unfold corePotential; simp only [hd, hr', if_false, Bool.false_eq_true]; rfl
  have hsearch : ∀ rho, ¬S.Reuse cache rho m →
      expectedValue (Sampling.roRun secret (S.search rho m 0 fuel) cache)
        (fun result => S.corePotential (b.expose C' (result.1.map Prod.snd))) ≤
          S.ledger R0 b.targets b.exposures b.slack + C' := by
    intro rho hnr
    have hrej : Sampling.CachedTrialsReject (Sampling.digestTrial rho m) S.decode 0 (2 ^ 32) cache := by
      unfold Reuse at hnr; push Not at hnr; exact hnr
    by_cases hlen : b.exposures.length < S.horizon
    · obtain ⟨R, hR⟩ : ∃ R, R0 = R + 1 := ⟨R0 - 1, by omega⟩
      calc
        _ ≤ expectedValue (Sampling.roRun secret (S.search rho m 0 fuel) cache)
            (fun result => result.1.elim (S.ledger (R + 1) b.targets b.exposures b.slack)
              (fun found => S.ledger R b.targets (b.exposures ++ [found.2]) b.slack) + C') := by
          apply expectedValue_mono
          intro result
          rcases result with ⟨_ | found, cache'⟩
          · unfold corePotential BankCore.expose
            simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr',
              Bool.false_eq_true, Option.elim_none]
            rw [← hR]
          · unfold corePotential BankCore.expose
            have hl1 : (b.exposures ++ [found.2]).length = b.exposures.length + 1 := by simp
            have hnd : ¬S.horizon < (b.exposures ++ [found.2]).length := by omega
            simp only [Option.map_some, Option.toList_some, hnd, if_false, hr', Bool.false_eq_true,
              Option.elim_some]
            rw [show S.horizon - (b.exposures ++ [found.2]).length = R by omega]
        _ ≤ S.ledger (R + 1) b.targets b.exposures b.slack + C' :=
          (CaseC.expectedValue_add_const_le _ _ _).trans
            (add_le_add (S.ledger_search secret rho m fuel hfuel cache hrej R b.targets b.exposures b.slack) le_rfl)
        _ = _ := by rw [hR]
    · apply expectedValue_le_of_le
      intro result
      rcases result with ⟨_ | found, cache'⟩
      · unfold corePotential BankCore.expose
        simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr', Bool.false_eq_true]
        exact le_rfl
      · unfold corePotential BankCore.expose
        have hnd : S.horizon < (b.exposures ++ [found.2]).length := by simp; omega
        simp only [Option.map_some, Option.toList_some, hnd, if_true]
        exact bot_le
  rw [hb]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest)
        (fun rho => (if S.Reuse cache rho m then 1 else 0) + (S.ledger R0 b.targets b.exposures b.slack + C')) := by
      apply expectedValue_mono
      intro rho
      by_cases hre : S.Reuse cache rho m
      · rw [if_pos hre, if_pos hre]
        unfold corePotential
        simp only [hd, if_false, if_true]
        exact add_le_add le_rfl le_add_self
      · rw [if_neg hre, if_neg hre, zero_add]
        exact hsearch rho hre
    _ ≤ S.reuseMass cache m + (S.ledger R0 b.targets b.exposures b.slack + C') :=
      (CaseC.expectedValue_add_const_le _ _ _).trans (add_le_add (S.reuse_probability_le cache m) le_rfl)
    _ ≤ _ := by
      rw [add_comm (S.ledger _ _ _ _), ← add_assoc, add_comm (S.reuseMass cache m), add_comm _ (S.ledger _ _ _ _)]
      exact add_le_add le_rfl hC
theorem core_win (b : BankCore) (halive : ¬S.horizon < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, S.admissible N = true ∧ S.covered b.exposures N) :
    1 ≤ S.corePotential b := by
  unfold corePotential
  rw [if_neg halive]
  by_cases hr : b.reused = true
  · rw [if_pos hr]; exact le_self_add
  · rw [if_neg hr]
    obtain ⟨N, hN, hadm, hcov⟩ := h.resolve_left hr
    exact (S.ledger_win _ _ _ _ N hN hadm hcov).trans le_self_add
theorem core_initial (budget : Nat) :
    S.corePotential ⟨[], [], false, 0, budget⟩ ≤ (budget : ENNReal) * S.excessRate / 2 ^ 128 := by
  unfold corePotential
  simp only [List.length_nil, Nat.not_lt_zero, if_false, Bool.false_eq_true, Nat.sub_zero, add_zero]
  exact S.ledger_initial budget
end FtsBankSpec
end ClaudeWCT.Bank
end
section
namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Completeness (searchLoop failMass)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankKernel : DecidableEq T3.Cache := Classical.decEq _
def PayNotDigest {Sig : Type} (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) : Prop :=
  ∀ cache rho output, AllQueriesSatisfy (pay cache rho output) BPB.NotDigestQ
def PayAvoids {Sig : Type} (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) : Prop :=
  ∀ m cache rho output, NonceFreshness.Avoids m (pay cache rho output)
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
variable {Sig : Type}
def recordForNonce (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (cache : T3.Cache) (rho : Digest)
    (message : Message) : M (Option Sig × Option HashOutput) := do
  let found ← S.search rho message 0 attemptLimit
  match found with
  | none => pure (none, none)
  | some (_, output) => do
      let signature ← pay cache rho output
      pure (signature, some output)
def payloadRecord (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (cache : T3.Cache) (message : Message) :
    M (Option Sig × Option HashOutput) := do
  let rho ← privateNonce message
  S.recordForNonce pay cache rho message
noncomputable def authenticatedRecord (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (published : T3.Cache)
    (request : Request) : M (Option Sig × Option HashOutput) := do
  let _ ← privateMac request.cache.region
  if request.cache = published then S.payloadRecord pay request.cache request.message else pure (none, none)
theorem run_search (rho : Digest) (message : Message) (counter fuel : Nat) (state : LazyPrivate.State) :
    LazyPrivate.run (S.search rho message counter fuel) state =
      (fun result => (result.1, (state.1, result.2))) <$> Sampling.roRun 0 (S.search rho message counter fuel) state.2 := by
  rw [search, LazyPrivate.run_publicProgram, Sampling.roRun, Sampling.public_randomOracle]
theorem recordForNonce_le_search (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (cache : T3.Cache)
    (rho : Digest) (message : Message) (state : LazyPrivate.State) (w : HashOutput → ENNReal) (base : ENNReal) :
    expectedValue (LazyPrivate.run (S.recordForNonce pay cache rho message) state)
      (fun result => result.1.2.elim base w) ≤
    expectedValue (Sampling.roRun 0 (S.search rho message 0 attemptLimit) state.2)
      (fun result => result.1.elim base (fun found => w found.2)) := by
  rw [recordForNonce, LazyPrivate.run_bind, expectedValue_bind, run_search, expectedValue_map]
  apply expectedValue_mono
  intro result
  cases result.1 with
  | none => simp only [LazyPrivate.run_pure, expectedValue_pure, Option.elim_none, le_refl]
  | some found =>
      rcases found with ⟨counter, output⟩
      simp only [LazyPrivate.run_bind, expectedValue_bind, LazyPrivate.run_pure, expectedValue_pure,
        Option.elim_some]
      apply expectedValue_le_of_le
      intro signature
      exact le_rfl
theorem fresh_signing_kernel (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (published : T3.Cache)
    (m : Message) (state : LazyPrivate.State) (hfresh : state.1 (.inr (.inl m)) = none)
    (F : (Option Sig × Option HashOutput) × LazyPrivate.State → ENNReal)
    (w : HashOutput → ENNReal) (P' : ENNReal) (hP : S.freshPrice w ≤ P')
    (hF : ∀ result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩) state),
      F result ≤ if S.Reuse state.2 (CaseC.nonceOf result.2 m) m then 1 else result.1.2.elim P' w) :
    expectedValue (LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩) state) F ≤
      P' + S.reuseMass state.2 m := by
  have hrun : LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩) state =
      LazyPrivate.run (privateMac published.region) state >>= fun mac =>
        LazyPrivate.run (S.payloadRecord pay published m) mac.2 := by
    rw [authenticatedRecord, LazyPrivate.run_bind]
    simp only [if_true]
  rw [hrun, expectedValue_bind]
  have hmac : ∀ mac ∈ support (LazyPrivate.run (privateMac published.region) state),
      expectedValue (LazyPrivate.run (S.payloadRecord pay published m) mac.2) F ≤ P' + S.reuseMass state.2 m := by
    intro mac hmac
    have hp := LazyPrivate.privateMac_preserves_nonce published.region m state mac hmac
    have hfresh1 : mac.2.1 (.inr (.inl m)) = none := hp.1.trans hfresh
    rw [payloadRecord, LazyPrivate.run_bind, LazyPrivate.run_privateNonce_fresh m mac.2 hfresh1]
    simp only [bind_assoc, pure_bind, expectedValue_bind]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun output =>
          (if S.Reuse state.2 (output.extractLsb' 0 128) m then 1 else 0) + P') := by
        apply expectedValue_mono
        intro output
        set s2 : LazyPrivate.State := (mac.2.1.cacheQuery (.inr (.inl m)) output, mac.2.2) with hs2
        have hsupp : ∀ result ∈ support (LazyPrivate.run
            (S.recordForNonce pay published (output.extractLsb' 0 128) m) s2),
            F result ≤ if S.Reuse state.2 (output.extractLsb' 0 128) m then 1
              else result.1.2.elim P' w := by
          intro result hr
          have hmem : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩)
              state) := by
            rw [hrun, mem_support_bind_iff]
            refine ⟨mac, hmac, ?_⟩
            rw [payloadRecord, LazyPrivate.run_bind, LazyPrivate.run_privateNonce_fresh m mac.2 hfresh1]
            simp only [bind_assoc, pure_bind, mem_support_bind_iff]
            exact ⟨output, by simp, hr⟩
          have hn := CaseC.nonceOf_cacheQuery mac.2 m output result.2
            (SourceReplay.run_extends _ s2 result hr)
          have := hF result hmem
          rwa [hn] at this
        by_cases hreuse : S.Reuse state.2 (output.extractLsb' 0 128) m
        · refine le_trans (expectedValue_le_of_support (c := 1) ?_) ?_
          · intro result hr
            simpa [hreuse] using hsupp result hr
          · simp [hreuse]
        · refine le_trans (expectedValue_mono_of_support (h := fun result => result.1.2.elim P' w) ?_) ?_
          · intro result hr
            simpa [hreuse] using hsupp result hr
          calc
            expectedValue (LazyPrivate.run (S.recordForNonce pay published (output.extractLsb' 0 128) m) s2)
                (fun result => result.1.2.elim P' w) ≤
                expectedValue (Sampling.roRun 0 (S.search (output.extractLsb' 0 128) m 0 attemptLimit) s2.2)
                (fun result => result.1.elim P' (fun found => w found.2)) :=
              S.recordForNonce_le_search pay published _ m s2 w P'
            _ ≤ P' := by
              apply S.search_le_price 0 _ m attemptLimit (by decide) s2.2 _ w P' P' le_rfl hP
              have hc : s2.2 = state.2 := by rw [hs2]; exact hp.2
              rw [hc]
              exact not_not.mp hreuse
            _ ≤ _ := by simp [hreuse]
      _ = expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho => if S.Reuse state.2 rho m then 1 else 0) + P' := by
        rw [expectedValue_add, expectedValue_const (by simp)]
        congr 1
        exact LazyPrivate.uniform_hash_low_expectation (fun rho => if S.Reuse state.2 rho m then 1 else 0)
      _ ≤ S.reuseMass state.2 m + P' := add_le_add (S.reuse_probability_le state.2 m) le_rfl
      _ = P' + S.reuseMass state.2 m := add_comm _ _
  exact expectedValue_le_of_support hmac
theorem search_allowed (rho : Digest) (m : Message) (Q : T3.Spec.Domain → Prop)
    (hQ : ∀ c, c < 2 ^ 32 → Q (.inl (.inr (Sampling.digestTrial rho m c)))) :
    ∀ fuel counter, counter + fuel ≤ 2 ^ 32 → AllQueriesSatisfy (S.search rho m counter fuel) Q := by
  intro fuel
  induction fuel with
  | zero => intro counter _; exact SourceQueries.pure_allowed _ _
  | succ fuel ih =>
      intro counter hlimit
      rw [search, Sampling.publicSearch_succ]
      apply SourceQueries.bind_allowed
      · exact (allQueriesSatisfy_query_iff _ _).mpr (hQ counter (by omega))
      · intro answer
        split
        · exact ih (counter + 1) (by omega)
        · exact SourceQueries.pure_allowed _ _
theorem privateMac_avoids (region : Region) (m : Message) : NonceFreshness.Avoids m (privateMac region) :=
  SourceQueries.privateMac_allowed _ (fun tweak h => by cases h) region
theorem authenticatedRecord_signerQ (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayNotDigest pay)
    (published : T3.Cache) (request : Request) :
    AllQueriesSatisfy (S.authenticatedRecord pay published request) (CaseC.SignerQ request.message) := by
  unfold authenticatedRecord
  apply SourceQueries.bind_allowed
  · apply SourceQueries.privateMac_allowed (CaseC.SignerQ request.message)
    intro tweak x hx
    cases hx
  · intro tag
    split
    · unfold payloadRecord recordForNonce
      apply SourceQueries.bind_allowed
      · unfold privateNonce
        apply SourceQueries.bind_allowed
        · apply (allQueriesSatisfy_query_iff _ _).mpr
          intro x hx
          cases hx
        · intro _; exact SourceQueries.pure_allowed _ _
      · intro rho
        apply SourceQueries.bind_allowed _
          (S.search_allowed rho request.message _ (fun c hc x hx _ => by
            simp only [Sum.inl.injEq, Sum.inr.injEq] at hx
            rw [← hx]
            exact CaseC.digestTrial_rowOf rho request.message c hc) attemptLimit 0 (by decide))
        intro found
        split
        · exact SourceQueries.pure_allowed _ _
        · apply SourceQueries.bind_allowed
          · exact CaseC.allQueriesSatisfy_mono _ _ _ (CaseC.notDigestQ_signerQ request.message) (hpay _ _ _)
          · intro _; exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
theorem signer_new_rows (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayNotDigest pay)
    (published : T3.Cache) (request : Request) (before : LazyPrivate.State)
    (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published request) before))
    (x : HashInput) (hx : before.2 x = none) (hnew : result.2.2 x ≠ none) (hdig : CaseC.IsDigestInput x) :
    CaseC.DigestRowOf x request.message :=
  CaseC.run_new_public _ (fun x => CaseC.IsDigestInput x → CaseC.DigestRowOf x request.message)
    (CaseC.allQueriesSatisfy_mono _ _ _ (fun _ hq x hx => hq x hx)
      (S.authenticatedRecord_signerQ pay hpay published request))
    before result hr x hx hnew hdig
theorem authenticatedRecord_avoids (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayAvoids pay)
    (message : Message) (published : T3.Cache) (request : Request)
    (hrequest : request.cache ≠ published ∨ request.message ≠ message) :
    NonceFreshness.Avoids message (S.authenticatedRecord pay published request) := by
  unfold authenticatedRecord
  apply NonceFreshness.avoids_bind message (privateMac_avoids _ message)
  intro tag
  split
  · rename_i hc
    have hm : request.message ≠ message := hrequest.resolve_left (fun h => h hc)
    unfold payloadRecord recordForNonce
    apply NonceFreshness.avoids_bind message
    · unfold privateNonce
      apply NonceFreshness.avoids_bind message
      · apply (allQueriesSatisfy_query_iff _ _).mpr
        intro he
        apply hm
        unfold NonceFreshness.nonceQuery at he
        simp only [Sum.inr.injEq, Sum.inl.injEq] at he
        exact he
      · intro _; exact NonceFreshness.avoids_pure _ _
    · intro rho
      apply NonceFreshness.avoids_bind message
        (S.search_allowed rho request.message _ (fun c _ h => by cases h) attemptLimit 0 (by decide))
      intro found
      split
      · exact NonceFreshness.avoids_pure _ _
      · exact NonceFreshness.avoids_bind message (hpay _ _ _ _) fun _ => NonceFreshness.avoids_pure _ _
  · exact NonceFreshness.avoids_pure _ _
theorem sign_other_nonce (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayAvoids pay)
    (published : T3.Cache) (request : Request) (lz : LazyPrivate.State)
    (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published request) lz))
    (m' : Message) (hm' : m' ≠ request.message) :
    result.2.1 (.inr (.inl m')) = lz.1 (.inr (.inl m')) :=
  NonceFreshness.run_preserves m' _
    (S.authenticatedRecord_avoids pay hpay m' published request (Or.inr (Ne.symm hm'))) lz result hr
theorem sign_other_reuseMass (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayNotDigest pay)
    (published : T3.Cache) (request : Request) (lz : LazyPrivate.State)
    (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published request) lz))
    (m' : Message) (hm' : m' ≠ request.message) :
    S.reuseMass result.2.2 m' = S.reuseMass lz.2 m' := by
  have hext := SourceReplay.run_extends _ lz result hr
  unfold reuseMass
  congr 1
  apply tsum_congr
  intro p
  unfold admissibleEntry
  cases hc : lz.2 (Sampling.digestTrial p.1 m' p.2.val) with
  | some a =>
      rw [hext.2 hc]
  | none =>
      have hn : result.2.2 (Sampling.digestTrial p.1 m' p.2.val) = none := by
        by_contra hne
        have hrow := S.signer_new_rows pay hpay published request lz result hr _ hc hne
          (CaseC.digestRowOf_isDigest ⟨p, rfl⟩)
        exact hm' (CaseC.digestRowOf_unique ⟨p, rfl⟩ hrow)
      rw [hn]
theorem sign_published_nonce (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (published : T3.Cache)
    (m : Message) (lz : LazyPrivate.State) (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩) lz)) :
    result.2.1 (.inr (.inl m)) ≠ none := by
  rw [authenticatedRecord, LazyPrivate.run_bind, mem_support_bind_iff] at hr
  obtain ⟨mac, _, hr⟩ := hr
  simp only [if_true] at hr
  rw [payloadRecord, LazyPrivate.run_bind, mem_support_bind_iff] at hr
  obtain ⟨nonce, hnonce, hr⟩ := hr
  have hext := SourceReplay.run_extends _ nonce.2 result hr
  unfold privateNonce at hnonce
  rw [LazyPrivate.run_bind, mem_support_bind_iff] at hnonce
  obtain ⟨hashed, hhashed, hn⟩ := hnonce
  rw [LazyPrivate.run_pure, mem_support_pure_iff] at hn
  have hc := SourceReplay.hash_query_caches (.inr (.inr (.inl m))) trivial mac.2 hashed hhashed
  have hc' : nonce.2.1 (.inr (.inl m)) = some hashed.1 := by rw [hn]; exact hc
  rw [hext.1 hc']
  simp
theorem sign_unpublished (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (published : T3.Cache)
    (request : Request) (hc : request.cache ≠ published)
    (lz : LazyPrivate.State) (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published request) lz)) :
    result.2.1 (.inr (.inl request.message)) = lz.1 (.inr (.inl request.message)) ∧ result.2.2 = lz.2 := by
  rw [authenticatedRecord, LazyPrivate.run_bind, mem_support_bind_iff] at hr
  obtain ⟨mac, hmac, hr⟩ := hr
  simp only [hc, if_false, LazyPrivate.run_pure, mem_support_pure_iff] at hr
  subst hr
  exact LazyPrivate.privateMac_preserves_nonce request.cache.region request.message lz mac hmac
noncomputable def reusePotential (s : LazyPrivate.State) : ENNReal :=
  ∑' m : Message, if s.1 (.inr (.inl m)) = none then S.reuseMass s.2 m else 0
theorem reusePotential_public_le (s : LazyPrivate.State) (x : HashInput) (a : HashOutput) (hx : s.2 x = none) :
    S.reusePotential (s.1, s.2.cacheQuery x a) ≤ S.reusePotential s + S.admInd a / 2 ^ 128 := by
  unfold reusePotential
  calc
    (∑' m : Message, if s.1 (.inr (.inl m)) = none then S.reuseMass (s.2.cacheQuery x a) m else 0) ≤
        ∑' m : Message, ((if s.1 (.inr (.inl m)) = none then S.reuseMass s.2 m else 0) +
          (if CaseC.DigestRowOf x m then S.admInd a / 2 ^ 128 else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro m
      split_ifs with h1 h2
      · simpa [ENNReal.div_eq_inv_mul, h2] using S.reuseMass_cacheQuery_le s.2 x a hx m
      · simpa [h2] using S.reuseMass_cacheQuery_le s.2 x a hx m
      · exact bot_le
      · exact bot_le
    _ = _ + _ := ENNReal.tsum_add
    _ ≤ _ := add_le_add le_rfl
      (CaseC.tsum_indicator_le_of_subsingleton _ (fun _ _ h h' => CaseC.digestRowOf_unique h h') _)
theorem reusePotential_public_nondigest (s : LazyPrivate.State) (x : HashInput) (a : HashOutput)
    (hx : s.2 x = none) (hnd : ¬CaseC.IsDigestInput x) :
    S.reusePotential (s.1, s.2.cacheQuery x a) ≤ S.reusePotential s := by
  unfold reusePotential
  apply ENNReal.tsum_le_tsum
  intro m
  split_ifs with h
  · have h1 := S.reuseMass_cacheQuery_le s.2 x a hx m
    rw [if_neg (fun hr => hnd (CaseC.digestRowOf_isDigest hr)), ENNReal.zero_div, add_zero] at h1
    exact h1
  · exact le_rfl
theorem reusePotential_sign_le (s s' : LazyPrivate.State) (m : Message)
    (hm : s.1 (.inr (.inl m)) = none) (hm' : s'.1 (.inr (.inl m)) ≠ none)
    (hother : ∀ m', m' ≠ m → s'.1 (.inr (.inl m')) = s.1 (.inr (.inl m')))
    (hrows : ∀ m', m' ≠ m → S.reuseMass s'.2 m' = S.reuseMass s.2 m') :
    S.reusePotential s' + S.reuseMass s.2 m ≤ S.reusePotential s := by
  unfold reusePotential
  rw [ENNReal.tsum_eq_add_tsum_ite m, ENNReal.tsum_eq_add_tsum_ite m (f := fun m' =>
    if s.1 (.inr (.inl m')) = none then S.reuseMass s.2 m' else 0)]
  simp only [hm', if_false, zero_add, hm, if_true]
  rw [add_comm]
  apply add_le_add le_rfl
  apply le_of_eq
  apply tsum_congr
  intro m'
  by_cases he : m' = m
  · simp [he]
  · simp only [he, if_false, hother m' he, hrows m' he]
theorem reusePotential_sign_stale_le (s s' : LazyPrivate.State) (m : Message)
    (hm : s.1 (.inr (.inl m)) ≠ none → s'.1 (.inr (.inl m)) ≠ none)
    (hnone : s.1 (.inr (.inl m)) = none → s'.1 (.inr (.inl m)) = none ∧ S.reuseMass s'.2 m = S.reuseMass s.2 m)
    (hother : ∀ m', m' ≠ m → s'.1 (.inr (.inl m')) = s.1 (.inr (.inl m')))
    (hrows : ∀ m', m' ≠ m → S.reuseMass s'.2 m' = S.reuseMass s.2 m') :
    S.reusePotential s' ≤ S.reusePotential s := by
  unfold reusePotential
  apply ENNReal.tsum_le_tsum
  intro m'
  by_cases he : m' = m
  · subst he
    by_cases hc : s.1 (.inr (.inl m')) = none
    · obtain ⟨h1, h2⟩ := hnone hc
      simp [h1, h2, hc]
    · simp [hm hc, hc]
  · simp only [hother m' he, hrows m' he, le_refl]
theorem reuseMass_of_noDigest (cache : Sampling.RCache) (h : ∀ x, CaseC.IsDigestInput x → cache x = none)
    (m : Message) : S.reuseMass cache m = 0 := by
  unfold reuseMass
  rw [ENNReal.div_eq_zero_iff]
  left
  apply ENNReal.tsum_eq_zero.mpr
  intro p
  simp [admissibleEntry, h _ (CaseC.digestRowOf_isDigest ⟨p, rfl⟩)]
theorem reusePotential_of_noDigest (s : LazyPrivate.State) (h : ∀ x, CaseC.IsDigestInput x → s.2 x = none) :
    S.reusePotential s = 0 := by
  unfold reusePotential
  apply ENNReal.tsum_eq_zero.mpr
  intro m
  split_ifs
  · exact S.reuseMass_of_noDigest _ h m
  · rfl
end FtsBankSpec
end ClaudeWCT.Bank
end
end
-- ==== merged from T3_Secc_CaseCBankMain ====
section

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCBankMain : DecidableEq T3.Cache := Classical.decEq _
theorem pmf_expectedValue_mono {α : Type} (p : PMF α) {f g : α → ENNReal} (h : ∀ x ∈ p.support, f x ≤ g x) :
    expectedValue p f ≤ expectedValue p g := by
  unfold expectedValue
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ p.support
  · exact mul_le_mul' le_rfl (h x hx)
  · have hp : Pr[= x | p] = 0 := by
      rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
      exact hx
    rw [hp, zero_mul, zero_mul]
theorem keygen_notDigest : AllQueriesSatisfy keygen BPB.NotDigestQ := by
  unfold keygen keygenPayload
  apply SourceQueries.bind_allowed
  · apply SourceQueries.bind_allowed _ BPB.buildTopTree_ok
    intro levels
    apply SourceQueries.bind_allowed
    · apply SourceQueries.mapM_allowed
      intro level
      unfold maskedLevel pairedMask
      apply SourceQueries.bind_allowed
      · apply SourceQueries.mapM_allowed
        intro pair
        exact SourceQueries.bind_allowed _ (BPB.privatePair_ok 13 0 0 level pair)
          (fun _ => SourceQueries.pure_allowed _ _)
      · intro _; exact SourceQueries.pure_allowed _ _
    · intro _
      exact SourceQueries.pure_allowed _ _
  · intro generated
    rcases generated with ⟨publicKey, region⟩
    apply SourceQueries.bind_allowed
    · exact SourceQueries.privateMac_allowed BPB.NotDigestQ (fun _ => trivial) region
    · intro _
      exact SourceQueries.pure_allowed _ _
theorem reuseMass_of_noDigest (cache : Sampling.RCache) (h : ∀ x, IsDigestInput x → cache x = none) (m : Message) :
    reuseMass cache m = 0 := by
  unfold reuseMass
  rw [ENNReal.div_eq_zero_iff]
  left
  apply ENNReal.tsum_eq_zero.mpr
  intro p
  simp [admissibleEntry, h _ (digestRowOf_isDigest ⟨p, rfl⟩)]
theorem keygen_noDigest (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    ∀ x, IsDigestInput x → (lazyOf generated.2).2 x = none := by
  intro x hx
  by_contra hne
  have hl := recorded_lazy_support keygen QueryRecorded.initial generated hg
  have := run_new_public keygen (fun x => ¬IsDigestInput x)
    (allQueriesSatisfy_mono _ _ _ (fun q hq x hqx hd => by
      subst hqx
      obtain ⟨rho, m, c, rfl⟩ := hd
      exact hq (BPB.hdrMarker_digestInput rho m c)) keygen_notDigest)
    (lazyOf QueryRecorded.initial) (generated.1, lazyOf generated.2) hl x rfl hne
  exact this hx
theorem potential_initial_le (budget : Nat) (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    potential budget (Ghost.empty, generated.2) ≤ (budget : ENNReal) * (11324 / 100000000) / 2 ^ 128 := by
  have hreuse : reusePotential (lazyOf generated.2) = 0 := by
    unfold reusePotential
    apply ENNReal.tsum_eq_zero.mpr
    intro m
    split_ifs
    · exact reuseMass_of_noDigest _ (keygen_noDigest generated hg) m
    · rfl
  unfold potential livePotential
  split_ifs with h1 h2
  · exact bot_le
  · simp [Ghost.empty] at h2
  · simp only [hreuse, add_zero]
    have hbank : bankValue Ghost.empty = 0 := by simp [bankValue, Ghost.empty]
    rw [hbank, zero_add]
    unfold excessTerm
    apply ENNReal.div_le_div_right
    apply mul_le_mul'
    · exact_mod_cast Nat.sub_le budget _
    · have he := excess_three_quarters
      simpa [excessForecast, Ghost.empty, labels, horizon] using he
end SigGolfCandidate.T3.Security.CaseC
end
-- ==== merged from ClaudeWCT_Bank_GameBank ====
section

namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M.Final
open CaseC (theta IsDigestInput Birth FreshSigning countOf lazyOf)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankGame : DecidableEq T3.Cache := Classical.decEq _
abbrev Requests' (Sig : Type) := Request →ₒ Option Sig
abbrev Interaction' (Sig : Type) := SphincsSecurity.OracleWorld + Requests' Sig
structure Ghost (Sig : Type) where
  targets : List HashOutput
  exposures : List HashOutput
  reused : Bool
  dead : Bool
  log : QueryLog (Requests' Sig)
def Ghost.empty {Sig : Type} : Ghost Sig := ⟨[], [], false, false, []⟩
abbrev BankState (Sig : Type) := Ghost Sig × QueryRecorded.State
noncomputable def ghostWorld {Sig : Type} (budget : Nat) :
    (input : SphincsSecurity.OracleWorld.Domain) → Ghost Sig → QueryRecorded.State →
      SphincsSecurity.OracleWorld.Range input → Ghost Sig
  | .inl _, g, _, _ => g
  | .inr x, g, before, answer =>
      if Birth budget x before then { g with targets := g.targets ++ [show HashOutput from answer] } else g
noncomputable def birthCharge {Sig : Type} (budget : Nat) : (Interaction' Sig).Domain → BankState Sig → ENNReal
  | .inl (.inr x), st => if Birth budget x st.2 then (theta + 1 / 64) / 2 ^ 128 else 0
  | _, _ => 0
noncomputable def birthWeight {Sig : Type} (budget : Nat) : (Interaction' Sig).Domain → QueryRecorded.State → ENNReal
  | .inl (.inr x), s => if Birth budget x s then 1 else 0
  | _, _ => 0
theorem birthCharge_eq {Sig : Type} (budget : Nat) (input : (Interaction' Sig).Domain) (st : BankState Sig) :
    birthCharge budget input st = (theta + 1 / 64) / 2 ^ 128 * birthWeight budget input st.2 := by
  rcases input with (n | x) | request
  · simp [birthCharge, birthWeight]
  · simp only [birthCharge, birthWeight]
    split_ifs <;> simp
  · simp [birthCharge, birthWeight]
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
variable {Sig : Type} (pay : T3.Cache → Digest → HashOutput → M (Option Sig))
noncomputable def ghostSign (published : T3.Cache) (request : Request) (g : Ghost Sig) (before : QueryRecorded.State)
    (record : (Option Sig × Option HashOutput) × LazyPrivate.State) : Ghost Sig :=
  if FreshSigning published request before then
    if S.horizon ≤ g.exposures.length then
      { g with dead := true, log := g.log ++ [⟨request, record.1.1⟩] }
    else
      { g with exposures := g.exposures ++ record.1.2.toList,
               reused := g.reused || decide (S.Reuse (lazyOf before).2 (CaseC.nonceOf record.2 request.message)
                 request.message),
               log := g.log ++ [⟨request, record.1.1⟩] }
  else { g with log := g.log ++ [⟨request, record.1.1⟩] }
noncomputable def source (published : T3.Cache) : QueryImpl (Interaction' Sig) M
  | .inl input => forwardWorld input
  | .inr request => Prod.fst <$> S.authenticatedRecord pay published request
noncomputable def bankImpl (published : T3.Cache) (budget : Nat) :
    QueryImpl (Interaction' Sig) (StateT (BankState Sig) PMF)
  | .inl input => StateT.mk fun st =>
      (liftM (QueryRecorded.run (forwardWorld input) st.2) : PMF _).map fun r =>
        (r.1, (ghostWorld budget input st.1 st.2 r.1, r.2))
  | .inr request => StateT.mk fun st =>
      (liftM (QueryRecorded.run (S.authenticatedRecord pay published request) st.2) : PMF _).map fun r =>
        (r.1.1, (S.ghostSign published request st.1 st.2 (r.1, lazyOf r.2), r.2))
noncomputable def recordedImpl (published : T3.Cache) : QueryImpl (Interaction' Sig) (StateT QueryRecorded.State PMF) :=
  fun input => StateT.mk fun s => (liftM (QueryRecorded.run (S.source pay published input) s) : PMF _)
theorem bank_query_project (published : T3.Cache) (budget : Nat) (input : (Interaction' Sig).Domain)
    (st : BankState Sig) :
    Prod.map id Prod.snd <$> (S.bankImpl pay published budget input).run st =
      (liftM (QueryRecorded.run (S.source pay published input) st.2) : PMF _) := by
  cases input with
  | inl input =>
      change (PMF.map _ (PMF.map _ _)) = _
      rw [PMF.map_comp]
      change PMF.map id _ = _
      rw [PMF.map_id]
      rfl
  | inr request =>
      change (PMF.map _ (PMF.map _ _)) = _
      rw [PMF.map_comp]
      change _ = (liftM (QueryRecorded.run (Prod.fst <$> S.authenticatedRecord pay published request) st.2) : PMF _)
      rw [QueryRecorded.run_map, liftM_map, ← PMF.monad_map_eq_map]
      rfl
theorem bank_project {α : Type} (published : T3.Cache) (budget : Nat)
    (program : OracleComp (Interaction' Sig) α) (st : BankState Sig) :
    Prod.map id Prod.snd <$> (simulateQ (S.bankImpl pay published budget) program).run st =
      (liftM (QueryRecorded.run (simulateQ (S.source pay published) program) st.2) :
        PMF (α × QueryRecorded.State)) := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, QueryRecorded.run_pure, liftM_pure, map_pure]
      rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [simulateQ_bind, simulateQ_spec_query, QueryRecorded.run_bind, liftM_bind]
      rw [← S.bank_query_project pay published budget input st, bind_map_left]
      apply bind_congr
      intro result
      exact ih result.1 result.2
noncomputable def bankValue (g : Ghost Sig) : ENNReal :=
  (g.targets.map fun N => S.forecast (S.horizon - g.exposures.length) g.exposures N).sum
noncomputable def excessTerm (budget count : Nat) (g : Ghost Sig) : ENNReal :=
  ((budget - count : Nat) : ENNReal) * S.excessForecast (S.horizon - g.exposures.length) g.exposures / 2 ^ 128
noncomputable def livePotential (budget count : Nat) (g : Ghost Sig) (lazy : LazyPrivate.State) : ENNReal :=
  if g.dead = true ∨ budget < count then 0
  else if g.reused = true then 1 + S.reusePotential lazy
  else S.bankValue g + S.reusePotential lazy + S.excessTerm budget count g
noncomputable def potential (budget : Nat) (st : BankState Sig) : ENNReal :=
  S.livePotential budget (countOf st.2) st.1 (lazyOf st.2)
theorem livePotential_count_anti (budget : Nat) {count count' : Nat} (h : count ≤ count') (g : Ghost Sig)
    (lazy : LazyPrivate.State) : S.livePotential budget count' g lazy ≤ S.livePotential budget count g lazy := by
  unfold livePotential
  by_cases hd : g.dead = true
  · simp [hd]
  by_cases hb : budget < count'
  · simp [hd, hb]
  have hb0 : ¬budget < count := by omega
  have hd' : g.dead = false := by simpa using hd
  simp only [hd', hb, hb0, Bool.false_eq_true, false_or, if_false]
  by_cases hr : g.reused = true
  · simp only [hr, if_true, le_refl]
  · simp only [hr]
    apply add_le_add le_rfl
    unfold excessTerm
    apply ENNReal.div_le_div_right
    apply mul_le_mul' _ le_rfl
    exact_mod_cast Nat.sub_le_sub_left h budget
theorem bankValue_birth (g : Ghost Sig) (a : HashOutput) :
    S.bankValue { g with targets := g.targets ++ [a] } =
      S.bankValue g + S.forecast (S.horizon - g.exposures.length) g.exposures a := by
  simp [bankValue, List.map_append, List.sum_append]
theorem livePotential_alive (budget count : Nat) (g : Ghost Sig) (lazy : LazyPrivate.State)
    (hd : g.dead = false) (hb : ¬budget < count) (hr : g.reused = false) :
    S.livePotential budget count g lazy = S.bankValue g + S.reusePotential lazy + S.excessTerm budget count g := by
  simp [livePotential, hd, hb, hr]
theorem livePotential_reused (budget count : Nat) (g : Ghost Sig) (lazy : LazyPrivate.State)
    (hd : g.dead = false) (hb : ¬budget < count) (hr : g.reused = true) :
    S.livePotential budget count g lazy = 1 + S.reusePotential lazy := by
  simp [livePotential, hd, hb, hr]
theorem livePotential_reuse_mono (budget count : Nat) (g : Ghost Sig) {lazy lazy' : LazyPrivate.State}
    (h : S.reusePotential lazy' ≤ S.reusePotential lazy) :
    S.livePotential budget count g lazy' ≤ S.livePotential budget count g lazy := by
  unfold livePotential
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl h
  · exact add_le_add (add_le_add le_rfl h) le_rfl
theorem excessTerm_succ (budget count : Nat) (g : Ghost Sig) (hc : count < budget) :
    S.excessTerm budget count g = S.excessTerm budget (count + 1) g +
      S.excessForecast (S.horizon - g.exposures.length) g.exposures / 2 ^ 128 := by
  unfold excessTerm
  have hn : budget - count = (budget - (count + 1)) + 1 := by omega
  rw [hn, Nat.cast_add, Nat.cast_one, add_mul, one_mul, ENNReal.add_div]
theorem livePotential_log (budget count : Nat) (g : Ghost Sig) (l : QueryLog (Requests' Sig))
    (lazy : LazyPrivate.State) :
    S.livePotential budget count { g with log := l } lazy = S.livePotential budget count g lazy := rfl
theorem world_unfold (published : T3.Cache) (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain)
    (st : BankState Sig) (f : BankState Sig → ENNReal) :
    expectedValue ((S.bankImpl pay published budget (.inl input)).run st) (fun r => f r.2) =
      expectedValue (QueryRecorded.run (forwardWorld input) st.2)
        (fun r => f (ghostWorld budget input st.1 st.2 r.1, r.2)) := by
  change expectedValue (PMF.map _ (liftM _)) _ = _
  rw [CaseC.expectedValue_pmf_map, CaseC.expectedValue_liftM]
theorem world_step (published : T3.Cache) (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain)
    (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget (.inl input)).run st) (fun r => S.potential budget r.2) ≤
      S.potential budget st + birthCharge budget (.inl input) st := by
  rw [S.world_unfold pay published budget input st (S.potential budget)]
  cases input with
  | inl n =>
      have hb : birthCharge (Sig := Sig) budget (.inl (.inl n)) st = 0 := rfl
      rw [hb, add_zero]
      apply expectedValue_le_of_support
      intro r hr
      have hl := CaseC.lazy_world_coin n (lazyOf st.2) (r.1, lazyOf r.2) (CaseC.recorded_lazy_support _ _ r hr)
      have hc := CaseC.recorded_count_le _ _ r hr
      change S.livePotential budget (countOf r.2) st.1 (lazyOf r.2) ≤
        S.livePotential budget (countOf st.2) st.1 (lazyOf st.2)
      rw [show lazyOf r.2 = lazyOf st.2 from hl]
      exact S.livePotential_count_anti budget hc st.1 _
  | inr x =>
      have hcount : ∀ r ∈ support (QueryRecorded.run (forwardWorld (.inr x)) st.2),
          countOf r.2 = countOf st.2 + 1 :=
        fun r hr => CreationGame.recorded_world_hash_count x st.2 r hr
      set g := st.1 with hg
      set c := countOf st.2 with hc
      set lz := lazyOf st.2 with hlz
      calc
        _ ≤ expectedValue (QueryRecorded.run (forwardWorld (.inr x)) st.2)
            (fun r => S.livePotential budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) (lazyOf r.2)) := by
          apply expectedValue_mono_of_support
          intro r hr
          change S.livePotential budget (countOf r.2) _ _ ≤ _
          rw [hcount r hr]
        _ = expectedValue (LazyPrivate.run (forwardWorld (.inr x)) lz)
            (fun r => S.livePotential budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) r.2) :=
          CaseC.expected_recorded _ _
            (fun r => S.livePotential budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) r.2)
        _ ≤ _ := ?_
      cases hx : lz.2 x with
      | some a0 =>
          rw [CaseC.lazy_world_cached x lz a0 hx, expectedValue_pure]
          have hnb : ¬Birth budget x st.2 := fun h => by
            have h2 := h.2.1
            rw [← hlz, hx] at h2
            cases h2
          have hcb : birthCharge (Sig := Sig) budget (.inl (.inr x)) st = 0 := by simp [birthCharge, hnb]
          simp only [ghostWorld, hnb, if_false, hcb, add_zero]
          exact S.livePotential_count_anti budget (Nat.le_succ _) g _
      | none =>
          rw [CaseC.lazy_world_fresh x lz hx]
          by_cases hbirth : Birth budget x st.2
          · have hcb : birthCharge (Sig := Sig) budget (.inl (.inr x)) st = (theta + 1 / 64) / 2 ^ 128 := by
              simp [birthCharge, hbirth]
            rw [hcb]
            have hlt : c < budget := hbirth.2.2
            have hnot : ¬budget < c + 1 := by omega
            have hnot0 : ¬budget < c := by omega
            simp only [ghostWorld, hbirth, if_true]
            by_cases hd : g.dead = true
            · simp only [livePotential, hd, true_or, if_true, expectedValue_const (by simp : Pr[⊥ |
                ($ᵗ HashOutput : ProbComp HashOutput)] = 0), zero_le]
            have hd' : g.dead = false := by simpa using hd
            by_cases hr : g.reused = true
            · have hpt : S.potential budget st = 1 + S.reusePotential lz :=
                S.livePotential_reused budget c g lz hd' hnot0 hr
              rw [hpt]
              calc
                _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                    (fun a => 1 + S.reusePotential lz + S.admInd a / 2 ^ 128) := by
                  apply expectedValue_mono
                  intro a
                  rw [S.livePotential_reused budget (c + 1) { g with targets := g.targets ++ [a] } _ hd' hnot hr,
                    add_assoc]
                  exact add_le_add le_rfl (S.reusePotential_public_le lz x a hx)
                _ = 1 + S.reusePotential lz +
                    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) S.admInd / 2 ^ 128 := by
                  rw [expectedValue_add, expectedValue_const (by simp)]
                  congr 1
                  simp only [div_eq_mul_inv]
                  rw [expectedValue_mul_const]
                _ ≤ 1 + S.reusePotential lz + S.admBound / 2 ^ 128 :=
                  add_le_add le_rfl (ENNReal.div_le_div_right S.expected_admInd_tight _)
                _ ≤ _ := by
                  rw [← S.theta_add_admBound]
                  apply add_le_add le_rfl
                  apply ENNReal.div_le_div_right
                  exact le_add_self
            · have hr' : g.reused = false := by simpa using hr
              have hpt : S.potential budget st = S.bankValue g + S.reusePotential lz + S.excessTerm budget c g :=
                S.livePotential_alive budget c g lz hd' hnot0 hr'
              rw [hpt]
              set R := S.horizon - g.exposures.length
              have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                  (fun a => S.forecast R g.exposures a) ≤ (S.specTheta + S.excessForecast R g.exposures) / 2 ^ 128 := by
                rw [BPORS.expected_uniform_eq_finiteAverage]
                exact S.average_forecast_le R g.exposures
              calc
                _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a =>
                    S.bankValue g + S.forecast R g.exposures a + (S.reusePotential lz + S.admInd a / 2 ^ 128) +
                      S.excessTerm budget (c + 1) g) := by
                  apply expectedValue_mono
                  intro a
                  rw [S.livePotential_alive budget (c + 1) { g with targets := g.targets ++ [a] } _ hd' hnot hr',
                    S.bankValue_birth]
                  exact add_le_add (add_le_add le_rfl (S.reusePotential_public_le lz x a hx)) le_rfl
                _ = S.bankValue g + expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                      (fun a => S.forecast R g.exposures a) +
                    (S.reusePotential lz + expectedValue ($ᵗ HashOutput : ProbComp HashOutput) S.admInd / 2 ^ 128) +
                    S.excessTerm budget (c + 1) g := by
                  simp only [expectedValue_add, expectedValue_const (by simp : Pr[⊥ |
                    ($ᵗ HashOutput : ProbComp HashOutput)] = 0), div_eq_mul_inv, expectedValue_mul_const]
                _ ≤ S.bankValue g + (S.specTheta + S.excessForecast R g.exposures) / 2 ^ 128 +
                    (S.reusePotential lz + S.admBound / 2 ^ 128) + S.excessTerm budget (c + 1) g := by
                  gcongr
                  exact S.expected_admInd_tight
                _ = S.bankValue g + S.reusePotential lz +
                    (S.excessTerm budget (c + 1) g + S.excessForecast R g.exposures / 2 ^ 128) +
                    (theta + 1 / 64) / 2 ^ 128 := by
                  rw [← S.theta_add_admBound, ENNReal.add_div, ENNReal.add_div]
                  ring
                _ = _ := by rw [← S.excessTerm_succ budget c g hlt]
          · have hcb : birthCharge (Sig := Sig) budget (.inl (.inr x)) st = 0 := by simp [birthCharge, hbirth]
            simp only [ghostWorld, hbirth, if_false, hcb, add_zero]
            apply expectedValue_le_of_le
            intro a
            by_cases hlt : c < budget
            · have hnd : ¬IsDigestInput x := fun hd => hbirth ⟨hd, by rw [← hlz]; exact hx, hlt⟩
              calc
                _ ≤ S.livePotential budget (c + 1) g lz :=
                  S.livePotential_reuse_mono budget (c + 1) g (S.reusePotential_public_nondigest lz x a hx hnd)
                _ ≤ S.livePotential budget c g lz := S.livePotential_count_anti budget (Nat.le_succ _) g lz
                _ = _ := rfl
            · have hover : budget < c + 1 := by omega
              simp [livePotential, hover]
noncomputable def signWeight (budget count : Nat) (g : Ghost Sig) (A : HashOutput) : ENNReal :=
  S.bankValue { g with exposures := g.exposures ++ [A] } +
    S.excessTerm budget count { g with exposures := g.exposures ++ [A] }
theorem freshPrice_signWeight (budget count : Nat) (g : Ghost Sig) (hlen : g.exposures.length < S.horizon) :
    S.freshPrice (S.signWeight budget count g) = S.bankValue g + S.excessTerm budget count g := by
  rw [← S.expected_accepted]
  have hR' : ∀ A : HashOutput, S.horizon - (g.exposures ++ [A]).length = S.horizon - g.exposures.length - 1 := by
    intro A
    simp only [List.length_append, List.length_singleton]
    omega
  have hRR : S.horizon - g.exposures.length - 1 + 1 = S.horizon - g.exposures.length := by omega
  unfold signWeight bankValue excessTerm
  rw [expectedValue_add]
  simp only [hR']
  rw [CaseC.expectedValue_list_sum]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro N _
    rw [S.forecast_step, hRR]
  · simp only [div_eq_mul_inv]
    rw [show (fun A : HashOutput => ((budget - count : Nat) : ENNReal) *
        S.excessForecast (S.horizon - g.exposures.length - 1) (g.exposures ++ [A]) * (2 ^ 128 : ENNReal)⁻¹) =
        fun A => ((budget - count : Nat) : ENNReal) * (2 ^ 128 : ENNReal)⁻¹ *
          S.excessForecast (S.horizon - g.exposures.length - 1) (g.exposures ++ [A]) by
      funext A; ring]
    rw [CaseC.pmf_expectedValue_left_mul, S.excessForecast_step, hRR]
    ring
theorem sign_step (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache) (budget : Nat)
    (request : Request) (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget (.inr request)).run st) (fun r => S.potential budget r.2) ≤
      S.potential budget st := by
  set g := st.1 with hg
  set c := countOf st.2 with hc
  set lz := lazyOf st.2 with hlz
  have hunfold : expectedValue ((S.bankImpl pay published budget (.inr request)).run st)
      (fun r => S.potential budget r.2) =
      expectedValue (QueryRecorded.run (S.authenticatedRecord pay published request) st.2)
        (fun r => S.potential budget (S.ghostSign published request st.1 st.2 (r.1, lazyOf r.2), r.2)) := by
    change expectedValue (PMF.map _ (liftM _)) _ = _
    rw [CaseC.expectedValue_pmf_map, CaseC.expectedValue_liftM]
  rw [hunfold]
  calc
    _ ≤ expectedValue (QueryRecorded.run (S.authenticatedRecord pay published request) st.2)
        (fun r => S.livePotential budget c (S.ghostSign published request g st.2 (r.1, lazyOf r.2)) (lazyOf r.2)) := by
      apply expectedValue_mono_of_support
      intro r hr
      change S.livePotential budget (countOf r.2) (S.ghostSign published request st.1 st.2 (r.1, lazyOf r.2))
        (lazyOf r.2) ≤ _
      exact S.livePotential_count_anti budget (CaseC.recorded_count_le _ _ r hr) _ _
    _ = expectedValue (LazyPrivate.run (S.authenticatedRecord pay published request) lz)
        (fun r => S.livePotential budget c (S.ghostSign published request g st.2 r) r.2) :=
      CaseC.expected_recorded _ _ (fun r => S.livePotential budget c (S.ghostSign published request g st.2 r) r.2)
    _ ≤ S.potential budget st := ?_
  change _ ≤ S.livePotential budget c g lz
  by_cases hfresh : FreshSigning published request st.2
  swap
  ·
    apply expectedValue_le_of_support
    intro r hr
    simp only [ghostSign, hfresh, if_false, livePotential_log]
    apply S.livePotential_reuse_mono
    apply S.reusePotential_sign_stale_le lz r.2 request.message
    · intro hcached hnone
      apply hcached
      cases hcz : lz.1 (.inr (.inl request.message)) with
      | none => rfl
      | some a =>
          have := (SourceReplay.run_extends _ lz r hr).1 hcz
          rw [hnone] at this
          cases this
    · intro hnone
      have hcp : request.cache ≠ published := fun h => hfresh ⟨h, hnone⟩
      obtain ⟨h1, h2⟩ := S.sign_unpublished pay published request hcp lz r hr
      exact ⟨h1.trans hnone, by rw [h2]⟩
    · exact fun m' hm' => S.sign_other_nonce pay hAvoids published request lz r hr m' hm'
    · exact fun m' hm' => S.sign_other_reuseMass pay hNotDigest published request lz r hr m' hm'
  by_cases hhor : S.horizon ≤ g.exposures.length
  · apply expectedValue_le_of_le
    intro r
    simp [ghostSign, hfresh, hhor, livePotential]
  have hlen : g.exposures.length < S.horizon := by omega
  by_cases hd : g.dead = true
  · apply expectedValue_le_of_le
    intro r
    simp [ghostSign, hfresh, hhor, livePotential, hd]
  have hd' : g.dead = false := by simpa using hd
  by_cases hb : budget < c
  · apply expectedValue_le_of_le
    intro r
    simp [ghostSign, hfresh, hhor, livePotential, hb]
  obtain ⟨m, cache⟩ := request
  obtain ⟨hcache, hnonce⟩ := hfresh
  change cache = published at hcache
  subst hcache
  change lz.1 (.inr (.inl m)) = none at hnonce
  have hsign : ∀ r ∈ support (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz),
      S.reusePotential r.2 + S.reuseMass lz.2 m ≤ S.reusePotential lz := fun r hr =>
    S.reusePotential_sign_le lz r.2 m hnonce (S.sign_published_nonce pay cache m lz r hr)
      (fun m' hm' => S.sign_other_nonce pay hAvoids cache ⟨m, cache⟩ lz r hr m' hm')
      (fun m' hm' => S.sign_other_reuseMass pay hNotDigest cache ⟨m, cache⟩ lz r hr m' hm')
  have hfr : FreshSigning cache ⟨m, cache⟩ st.2 := ⟨rfl, hnonce⟩
  have hdead : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).dead = false := by
    intro r; simp [ghostSign, hfr, hhor, hd']
  have hreu : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused =
      (g.reused || decide (S.Reuse (lazyOf st.2).2 (CaseC.nonceOf r.2 m) m)) := by
    intro r; simp [ghostSign, hfr, hhor]
  have hexp : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).exposures = g.exposures ++ r.1.2.toList := by
    intro r; simp [ghostSign, hfr, hhor]
  have htar : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).targets = g.targets := by
    intro r; simp [ghostSign, hfr, hhor]
  by_cases hr : g.reused = true
  · apply expectedValue_le_of_support
    intro r hrs
    rw [S.livePotential_reused budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) r.2 (hdead r) hb
        (by rw [hreu r, hr, Bool.true_or]),
      S.livePotential_reused budget c g lz hd' hb hr]
    exact add_le_add le_rfl (le_trans le_self_add (hsign r hrs))
  have hr' : g.reused = false := by simpa using hr
  set P' := S.bankValue g + S.excessTerm budget c g with hP
  let Fmain : (Option Sig × Option HashOutput) × LazyPrivate.State → ENNReal := fun r =>
    if S.Reuse lz.2 (CaseC.nonceOf r.2 m) m then 1 else r.1.2.elim P' (S.signWeight budget c g)
  have hpoint : ∀ r, S.livePotential budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) r.2 ≤
      Fmain r + S.reusePotential r.2 := by
    intro r
    by_cases hre : S.Reuse lz.2 (CaseC.nonceOf r.2 m) m
    · have hru : (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused = true := by
        rw [hreu r, hr', Bool.false_or]
        exact decide_eq_true hre
      rw [S.livePotential_reused budget c _ r.2 (hdead r) hb hru]
      simp only [Fmain, hre, if_true, le_refl]
    · have hru : (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused = false := by
        rw [hreu r, hr', Bool.false_or]
        exact decide_eq_false hre
      rw [S.livePotential_alive budget c _ r.2 (hdead r) hb hru]
      simp only [Fmain, hre, if_false]
      have hbv : S.bankValue (S.ghostSign cache ⟨m, cache⟩ g st.2 r) =
          S.bankValue { g with exposures := g.exposures ++ r.1.2.toList } := by
        unfold bankValue; rw [htar r, hexp r]
      have het : S.excessTerm budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) =
          S.excessTerm budget c { g with exposures := g.exposures ++ r.1.2.toList } := by
        unfold excessTerm; rw [hexp r]
      rw [hbv, het]
      cases hsel : r.1.2 with
      | none =>
          simp only [Option.toList_none, List.append_nil, Option.elim_none, hP]
          apply le_of_eq
          ring
      | some A =>
          simp only [Option.toList_some, Option.elim_some, signWeight]
          apply le_of_eq
          ring
  calc
    _ ≤ expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
        (fun r => Fmain r + S.reusePotential r.2) := expectedValue_mono _ hpoint
    _ = expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz) Fmain +
        expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2) := expectedValue_add _ _ _
    _ ≤ (P' + S.reuseMass lz.2 m) +
        expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2) := by
      apply add_le_add _ le_rfl
      apply S.fresh_signing_kernel pay cache m lz hnonce Fmain (S.signWeight budget c g) P'
        (le_of_eq (S.freshPrice_signWeight budget c g hlen))
      intro r _
      exact le_rfl
    _ = P' + (expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2 + S.reuseMass lz.2 m)) := by
      rw [expectedValue_add, expectedValue_const (by simp)]
      ring
    _ ≤ P' + S.reusePotential lz := add_le_add le_rfl (expectedValue_le_of_support hsign)
    _ = S.livePotential budget c g lz := by
      rw [S.livePotential_alive budget c g lz hd' hb hr', hP]
      ring
theorem potential_step (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache)
    (budget : Nat) (input : (Interaction' Sig).Domain) (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget input).run st) (fun r => S.potential budget r.2) ≤
      S.potential budget st + birthCharge budget input st := by
  cases input with
  | inl input => exact S.world_step pay published budget input st
  | inr request => exact (S.sign_step pay hNotDigest hAvoids published budget request st).trans le_self_add
theorem potential_run {α : Type} (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache)
    (budget : Nat) (program : OracleComp (Interaction' Sig) α) (st : BankState Sig) :
    expectedValue ((simulateQ (S.bankImpl pay published budget) program).run st)
        (fun r => S.potential budget r.2) ≤
      S.potential budget st + BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
        (birthCharge budget) program st := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, BPORS.Adaptive.Creation.expectedCharges_pure, add_zero]
      rw [expectedValue_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, expectedValue_bind,
        BPORS.Adaptive.Creation.expectedCharges_query_bind]
      calc
        _ ≤ expectedValue ((S.bankImpl pay published budget input).run st) (fun result =>
            S.potential budget result.2 + BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
              (birthCharge budget) (next result.1) result.2) :=
          expectedValue_mono _ fun result => ih result.1 result.2
        _ = expectedValue ((S.bankImpl pay published budget input).run st)
              (fun result => S.potential budget result.2) +
            expectedValue ((S.bankImpl pay published budget input).run st) (fun result =>
              BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
                (birthCharge budget) (next result.1) result.2) := expectedValue_add _ _ _
        _ ≤ (S.potential budget st + birthCharge budget input st) + _ :=
          add_le_add (S.potential_step pay hNotDigest hAvoids published budget input st) le_rfl
        _ = _ := by ring
theorem bank_charges_eq_births {α : Type} (published : T3.Cache) (budget : Nat)
    (program : OracleComp (Interaction' Sig) α) (s : QueryRecorded.State) (g : Ghost Sig) :
    BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget) (birthCharge budget) program (g, s) =
      (theta + 1 / 64) / 2 ^ 128 * BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay published)
        (birthWeight budget) program s := by
  have h1 : BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget) (birthCharge budget)
      program (g, s) =
      BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
        (fun input st => (theta + 1 / 64) / 2 ^ 128 * birthWeight budget input st.2) program (g, s) := by
    congr 1
    funext input st
    exact birthCharge_eq budget input st
  rw [h1, BPORS.Adaptive.Creation.expectedCharges_scale]
  congr 1
  exact BPORS.Adaptive.Creation.expectedCharges_project (S.bankImpl pay published budget)
    (S.recordedImpl pay published) Prod.snd
    (fun input st => S.bank_query_project pay published budget input st)
    (birthWeight budget) program (g, s)
theorem potential_initial_le (budget : Nat) (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    S.potential budget ((Ghost.empty : Ghost Sig), generated.2) ≤
      (budget : ENNReal) * S.excessRate / 2 ^ 128 := by
  have hreuse : S.reusePotential (lazyOf generated.2) = 0 :=
    S.reusePotential_of_noDigest _ (CaseC.keygen_noDigest generated hg)
  unfold potential livePotential
  split_ifs with h1 h2
  · exact bot_le
  · simp [Ghost.empty] at h2
  · simp only [hreuse, add_zero]
    have hbank : S.bankValue (Ghost.empty : Ghost Sig) = 0 := by simp [bankValue, Ghost.empty]
    rw [hbank, zero_add]
    unfold excessTerm
    apply ENNReal.div_le_div_right
    apply mul_le_mul'
    · exact_mod_cast Nat.sub_le budget _
    · have he := S.excessForecast_initial
      simpa [Ghost.empty] using he
noncomputable def bankExperiment (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) :
    PMF (Bool × BankState Sig) := do
  let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
  (simulateQ (S.bankImpl pay generated.1.2 budget) (rest generated.1.1 generated.1.2)).run (Ghost.empty, generated.2)
noncomputable def recordedExperiment (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) :
    PMF (Bool × QueryRecorded.State) := do
  let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
  (liftM (QueryRecorded.run (simulateQ (S.source pay generated.1.2) (rest generated.1.1 generated.1.2))
    generated.2) : PMF _)
theorem bank_experiment_project (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) :
    (fun r : Bool × BankState Sig => (r.1, r.2.2)) <$> S.bankExperiment pay rest budget =
      S.recordedExperiment pay rest := by
  unfold bankExperiment recordedExperiment
  rw [map_bind]
  apply bind_congr
  intro generated
  exact S.bank_project pay generated.1.2 budget (rest generated.1.1 generated.1.2) (Ghost.empty, generated.2)
noncomputable def expectedBirths (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) :
    ENNReal :=
  expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _) (fun generated =>
    BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay generated.1.2) (birthWeight budget)
      (rest generated.1.1 generated.1.2) generated.2)
theorem bank_potential_le (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) :
    expectedValue (S.bankExperiment pay rest budget) (fun r => S.potential budget r.2) ≤
      (theta + 1 / 64) / 2 ^ 128 * S.expectedBirths pay rest budget +
        (budget : ENNReal) * S.excessRate / 2 ^ 128 := by
  unfold bankExperiment
  rw [expectedValue_bind]
  calc
    _ ≤ expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _) (fun generated =>
        (budget : ENNReal) * S.excessRate / 2 ^ 128 +
          (theta + 1 / 64) / 2 ^ 128 * BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay generated.1.2)
            (birthWeight budget) (rest generated.1.1 generated.1.2) generated.2) := by
      apply CaseC.pmf_expectedValue_mono
      intro generated hg
      rw [MonitoredPrivate.pmf_support] at hg
      refine (S.potential_run pay hNotDigest hAvoids generated.1.2 budget _ _).trans ?_
      rw [S.bank_charges_eq_births pay generated.1.2 budget]
      exact add_le_add (S.potential_initial_le budget generated hg) le_rfl
    _ = _ := by
      rw [expectedValue_add, expectedValue_const (by simp), CaseC.pmf_expectedValue_left_mul]
      unfold expectedBirths
      ring
theorem potential_win (budget : Nat) (st : BankState Sig) (halive : st.1.dead = false)
    (hcount : countOf st.2 ≤ budget)
    (h : st.1.reused = true ∨ ∃ N ∈ st.1.targets, S.admissible N = true ∧ S.covered st.1.exposures N) :
    1 ≤ S.potential budget st := by
  have hnot : ¬budget < countOf st.2 := by omega
  unfold potential
  by_cases hr : st.1.reused = true
  · rw [S.livePotential_reused budget _ st.1 _ halive hnot hr]
    exact le_add_right le_rfl
  · have hr' : st.1.reused = false := by simpa using hr
    obtain ⟨N, hN, hadm, hcov⟩ := h.resolve_left hr
    rw [S.livePotential_alive budget _ st.1 _ halive hnot hr']
    calc
      (1 : ENNReal) ≤ S.score st.1.exposures N := S.one_le_score _ N hadm hcov
      _ ≤ S.forecast (S.horizon - st.1.exposures.length) st.1.exposures N := S.score_le_forecast _ _ _
      _ ≤ S.bankValue st.1 := List.le_sum_of_mem (List.mem_map_of_mem hN)
      _ ≤ _ := le_self_add.trans le_self_add
theorem bank_event_le (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat)
    (weight : Bool × QueryRecorded.State → ENNReal) (hle : ∀ y, weight y ≤ 1)
    (hwin : ∀ b ∈ (S.bankExperiment pay rest budget).support, weight (b.1, b.2.2) ≠ 0 → 1 ≤ S.potential budget b.2) :
    expectedValue (S.recordedExperiment pay rest) weight ≤
      (theta + 1 / 64) / 2 ^ 128 * S.expectedBirths pay rest budget +
        (budget : ENNReal) * S.excessRate / 2 ^ 128 := by
  rw [← S.bank_experiment_project pay rest budget, PMF.monad_map_eq_map, CaseC.expectedValue_pmf_map]
  refine le_trans ?_ (S.bank_potential_le pay hNotDigest hAvoids rest budget)
  apply CaseC.pmf_expectedValue_mono
  intro b hb
  by_cases h0 : weight (b.1, b.2.2) = 0
  · rw [h0]; exact bot_le
  · exact (hle _).trans (hwin b hb h0)
end FtsBankSpec
end ClaudeWCT.Bank
end
-- ==== merged from ClaudeWCT_Bank_GameBankL ====
section

section
namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Completeness (searchLoop failMass)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankKernelL : DecidableEq T3.Cache := Classical.decEq _
structure FtsBankSpecL (P : Type) [Fintype P] [SampleableType P] extends FtsBankSpec P where
  limit : Nat
  limit_le : limit ≤ 2 ^ 32
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P]
def atLimit (S : FtsBankSpec P) (limit : Nat) (h : limit ≤ 2 ^ 32) : FtsBankSpecL P :=
  { toFtsBankSpec := S, limit := limit, limit_le := h }
def toL (S : FtsBankSpec P) : FtsBankSpecL P := S.atLimit attemptLimit (by decide)
@[simp] theorem atLimit_toFtsBankSpec (S : FtsBankSpec P) (limit : Nat) (h : limit ≤ 2 ^ 32) :
    (S.atLimit limit h).toFtsBankSpec = S := rfl
@[simp] theorem atLimit_limit (S : FtsBankSpec P) (limit : Nat) (h : limit ≤ 2 ^ 32) :
    (S.atLimit limit h).limit = limit := rfl
end FtsBankSpec
namespace FtsBankSpecL
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P)
variable {Sig : Type}
def recordForNonce (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (cache : T3.Cache) (rho : Digest)
    (message : Message) : M (Option Sig × Option HashOutput) := do
  let found ← S.search rho message 0 S.limit
  match found with
  | none => pure (none, none)
  | some (_, output) => do
      let signature ← pay cache rho output
      pure (signature, some output)
def payloadRecord (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (cache : T3.Cache) (message : Message) :
    M (Option Sig × Option HashOutput) := do
  let rho ← privateNonce message
  S.recordForNonce pay cache rho message
noncomputable def authenticatedRecord (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (published : T3.Cache)
    (request : Request) : M (Option Sig × Option HashOutput) := do
  let _ ← privateMac request.cache.region
  if request.cache = published then S.payloadRecord pay request.cache request.message else pure (none, none)
theorem recordForNonce_le_search (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (cache : T3.Cache)
    (rho : Digest) (message : Message) (state : LazyPrivate.State) (w : HashOutput → ENNReal) (base : ENNReal) :
    expectedValue (LazyPrivate.run (S.recordForNonce pay cache rho message) state)
      (fun result => result.1.2.elim base w) ≤
    expectedValue (Sampling.roRun 0 (S.search rho message 0 S.limit) state.2)
      (fun result => result.1.elim base (fun found => w found.2)) := by
  rw [recordForNonce, LazyPrivate.run_bind, expectedValue_bind, S.run_search, expectedValue_map]
  apply expectedValue_mono
  intro result
  cases result.1 with
  | none => simp only [LazyPrivate.run_pure, expectedValue_pure, Option.elim_none, le_refl]
  | some found =>
      rcases found with ⟨counter, output⟩
      simp only [LazyPrivate.run_bind, expectedValue_bind, LazyPrivate.run_pure, expectedValue_pure,
        Option.elim_some]
      apply expectedValue_le_of_le
      intro signature
      exact le_rfl
theorem fresh_signing_kernel (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (published : T3.Cache)
    (m : Message) (state : LazyPrivate.State) (hfresh : state.1 (.inr (.inl m)) = none)
    (F : (Option Sig × Option HashOutput) × LazyPrivate.State → ENNReal)
    (w : HashOutput → ENNReal) (P' : ENNReal) (hP : S.freshPrice w ≤ P')
    (hF : ∀ result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩) state),
      F result ≤ if S.Reuse state.2 (CaseC.nonceOf result.2 m) m then 1 else result.1.2.elim P' w) :
    expectedValue (LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩) state) F ≤
      P' + S.reuseMass state.2 m := by
  have hrun : LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩) state =
      LazyPrivate.run (privateMac published.region) state >>= fun mac =>
        LazyPrivate.run (S.payloadRecord pay published m) mac.2 := by
    rw [authenticatedRecord, LazyPrivate.run_bind]
    simp only [if_true]
  rw [hrun, expectedValue_bind]
  have hmac : ∀ mac ∈ support (LazyPrivate.run (privateMac published.region) state),
      expectedValue (LazyPrivate.run (S.payloadRecord pay published m) mac.2) F ≤ P' + S.reuseMass state.2 m := by
    intro mac hmac
    have hp := LazyPrivate.privateMac_preserves_nonce published.region m state mac hmac
    have hfresh1 : mac.2.1 (.inr (.inl m)) = none := hp.1.trans hfresh
    rw [payloadRecord, LazyPrivate.run_bind, LazyPrivate.run_privateNonce_fresh m mac.2 hfresh1]
    simp only [bind_assoc, pure_bind, expectedValue_bind]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun output =>
          (if S.Reuse state.2 (output.extractLsb' 0 128) m then 1 else 0) + P') := by
        apply expectedValue_mono
        intro output
        set s2 : LazyPrivate.State := (mac.2.1.cacheQuery (.inr (.inl m)) output, mac.2.2) with hs2
        have hsupp : ∀ result ∈ support (LazyPrivate.run
            (S.recordForNonce pay published (output.extractLsb' 0 128) m) s2),
            F result ≤ if S.Reuse state.2 (output.extractLsb' 0 128) m then 1
              else result.1.2.elim P' w := by
          intro result hr
          have hmem : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩)
              state) := by
            rw [hrun, mem_support_bind_iff]
            refine ⟨mac, hmac, ?_⟩
            rw [payloadRecord, LazyPrivate.run_bind, LazyPrivate.run_privateNonce_fresh m mac.2 hfresh1]
            simp only [bind_assoc, pure_bind, mem_support_bind_iff]
            exact ⟨output, by simp, hr⟩
          have hn := CaseC.nonceOf_cacheQuery mac.2 m output result.2
            (SourceReplay.run_extends _ s2 result hr)
          have := hF result hmem
          rwa [hn] at this
        by_cases hreuse : S.Reuse state.2 (output.extractLsb' 0 128) m
        · refine le_trans (expectedValue_le_of_support (c := 1) ?_) ?_
          · intro result hr
            simpa [hreuse] using hsupp result hr
          · simp [hreuse]
        · refine le_trans (expectedValue_mono_of_support (h := fun result => result.1.2.elim P' w) ?_) ?_
          · intro result hr
            simpa [hreuse] using hsupp result hr
          calc
            expectedValue (LazyPrivate.run (S.recordForNonce pay published (output.extractLsb' 0 128) m) s2)
                (fun result => result.1.2.elim P' w) ≤
                expectedValue (Sampling.roRun 0 (S.search (output.extractLsb' 0 128) m 0 S.limit) s2.2)
                (fun result => result.1.elim P' (fun found => w found.2)) :=
              S.recordForNonce_le_search pay published _ m s2 w P'
            _ ≤ P' := by
              apply S.search_le_price 0 _ m S.limit S.limit_le s2.2 _ w P' P' le_rfl hP
              have hc : s2.2 = state.2 := by rw [hs2]; exact hp.2
              rw [hc]
              exact not_not.mp hreuse
            _ ≤ _ := by simp [hreuse]
      _ = expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho => if S.Reuse state.2 rho m then 1 else 0) + P' := by
        rw [expectedValue_add, expectedValue_const (by simp)]
        congr 1
        exact LazyPrivate.uniform_hash_low_expectation (fun rho => if S.Reuse state.2 rho m then 1 else 0)
      _ ≤ S.reuseMass state.2 m + P' := add_le_add (S.reuse_probability_le state.2 m) le_rfl
      _ = P' + S.reuseMass state.2 m := add_comm _ _
  exact expectedValue_le_of_support hmac
theorem authenticatedRecord_signerQ (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayNotDigest pay)
    (published : T3.Cache) (request : Request) :
    AllQueriesSatisfy (S.authenticatedRecord pay published request) (CaseC.SignerQ request.message) := by
  unfold authenticatedRecord
  apply SourceQueries.bind_allowed
  · apply SourceQueries.privateMac_allowed (CaseC.SignerQ request.message)
    intro tweak x hx
    cases hx
  · intro tag
    split
    · unfold payloadRecord recordForNonce
      apply SourceQueries.bind_allowed
      · unfold privateNonce
        apply SourceQueries.bind_allowed
        · apply (allQueriesSatisfy_query_iff _ _).mpr
          intro x hx
          cases hx
        · intro _; exact SourceQueries.pure_allowed _ _
      · intro rho
        apply SourceQueries.bind_allowed _
          (S.search_allowed rho request.message _ (fun c hc x hx _ => by
            simp only [Sum.inl.injEq, Sum.inr.injEq] at hx
            rw [← hx]
            exact CaseC.digestTrial_rowOf rho request.message c hc) S.limit 0 (by simpa using S.limit_le))
        intro found
        split
        · exact SourceQueries.pure_allowed _ _
        · apply SourceQueries.bind_allowed
          · exact CaseC.allQueriesSatisfy_mono _ _ _ (CaseC.notDigestQ_signerQ request.message) (hpay _ _ _)
          · intro _; exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
theorem signer_new_rows (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayNotDigest pay)
    (published : T3.Cache) (request : Request) (before : LazyPrivate.State)
    (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published request) before))
    (x : HashInput) (hx : before.2 x = none) (hnew : result.2.2 x ≠ none) (hdig : CaseC.IsDigestInput x) :
    CaseC.DigestRowOf x request.message :=
  CaseC.run_new_public _ (fun x => CaseC.IsDigestInput x → CaseC.DigestRowOf x request.message)
    (CaseC.allQueriesSatisfy_mono _ _ _ (fun _ hq x hx => hq x hx)
      (S.authenticatedRecord_signerQ pay hpay published request))
    before result hr x hx hnew hdig
theorem authenticatedRecord_avoids (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayAvoids pay)
    (message : Message) (published : T3.Cache) (request : Request)
    (hrequest : request.cache ≠ published ∨ request.message ≠ message) :
    NonceFreshness.Avoids message (S.authenticatedRecord pay published request) := by
  unfold authenticatedRecord
  apply NonceFreshness.avoids_bind message (FtsBankSpec.privateMac_avoids _ message)
  intro tag
  split
  · rename_i hc
    have hm : request.message ≠ message := hrequest.resolve_left (fun h => h hc)
    unfold payloadRecord recordForNonce
    apply NonceFreshness.avoids_bind message
    · unfold privateNonce
      apply NonceFreshness.avoids_bind message
      · apply (allQueriesSatisfy_query_iff _ _).mpr
        intro he
        apply hm
        unfold NonceFreshness.nonceQuery at he
        simp only [Sum.inr.injEq, Sum.inl.injEq] at he
        exact he
      · intro _; exact NonceFreshness.avoids_pure _ _
    · intro rho
      apply NonceFreshness.avoids_bind message
        (S.search_allowed rho request.message _ (fun c _ h => by cases h) S.limit 0 (by simpa using S.limit_le))
      intro found
      split
      · exact NonceFreshness.avoids_pure _ _
      · exact NonceFreshness.avoids_bind message (hpay _ _ _ _) fun _ => NonceFreshness.avoids_pure _ _
  · exact NonceFreshness.avoids_pure _ _
theorem sign_other_nonce (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayAvoids pay)
    (published : T3.Cache) (request : Request) (lz : LazyPrivate.State)
    (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published request) lz))
    (m' : Message) (hm' : m' ≠ request.message) :
    result.2.1 (.inr (.inl m')) = lz.1 (.inr (.inl m')) :=
  NonceFreshness.run_preserves m' _
    (S.authenticatedRecord_avoids pay hpay m' published request (Or.inr (Ne.symm hm'))) lz result hr
theorem sign_other_reuseMass (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayNotDigest pay)
    (published : T3.Cache) (request : Request) (lz : LazyPrivate.State)
    (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published request) lz))
    (m' : Message) (hm' : m' ≠ request.message) :
    S.reuseMass result.2.2 m' = S.reuseMass lz.2 m' := by
  have hext := SourceReplay.run_extends _ lz result hr
  unfold FtsBankSpec.reuseMass
  congr 1
  apply tsum_congr
  intro p
  unfold FtsBankSpec.admissibleEntry
  cases hc : lz.2 (Sampling.digestTrial p.1 m' p.2.val) with
  | some a =>
      rw [hext.2 hc]
  | none =>
      have hn : result.2.2 (Sampling.digestTrial p.1 m' p.2.val) = none := by
        by_contra hne
        have hrow := S.signer_new_rows pay hpay published request lz result hr _ hc hne
          (CaseC.digestRowOf_isDigest ⟨p, rfl⟩)
        exact hm' (CaseC.digestRowOf_unique ⟨p, rfl⟩ hrow)
      rw [hn]
theorem sign_published_nonce (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (published : T3.Cache)
    (m : Message) (lz : LazyPrivate.State) (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩) lz)) :
    result.2.1 (.inr (.inl m)) ≠ none := by
  rw [authenticatedRecord, LazyPrivate.run_bind, mem_support_bind_iff] at hr
  obtain ⟨mac, _, hr⟩ := hr
  simp only [if_true] at hr
  rw [payloadRecord, LazyPrivate.run_bind, mem_support_bind_iff] at hr
  obtain ⟨nonce, hnonce, hr⟩ := hr
  have hext := SourceReplay.run_extends _ nonce.2 result hr
  unfold privateNonce at hnonce
  rw [LazyPrivate.run_bind, mem_support_bind_iff] at hnonce
  obtain ⟨hashed, hhashed, hn⟩ := hnonce
  rw [LazyPrivate.run_pure, mem_support_pure_iff] at hn
  have hc := SourceReplay.hash_query_caches (.inr (.inr (.inl m))) trivial mac.2 hashed hhashed
  have hc' : nonce.2.1 (.inr (.inl m)) = some hashed.1 := by rw [hn]; exact hc
  rw [hext.1 hc']
  simp
theorem sign_unpublished (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (published : T3.Cache)
    (request : Request) (hc : request.cache ≠ published)
    (lz : LazyPrivate.State) (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published request) lz)) :
    result.2.1 (.inr (.inl request.message)) = lz.1 (.inr (.inl request.message)) ∧ result.2.2 = lz.2 := by
  rw [authenticatedRecord, LazyPrivate.run_bind, mem_support_bind_iff] at hr
  obtain ⟨mac, hmac, hr⟩ := hr
  simp only [hc, if_false, LazyPrivate.run_pure, mem_support_pure_iff] at hr
  subst hr
  exact LazyPrivate.privateMac_preserves_nonce request.cache.region request.message lz mac hmac
end FtsBankSpecL
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P) {Sig : Type}
theorem toL_recordForNonce (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) :
    S.toL.recordForNonce pay = S.recordForNonce pay := rfl
theorem toL_payloadRecord (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) :
    S.toL.payloadRecord pay = S.payloadRecord pay := rfl
theorem toL_authenticatedRecord (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) :
    S.toL.authenticatedRecord pay = S.authenticatedRecord pay := rfl
end FtsBankSpec
end ClaudeWCT.Bank
end
section
namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M.Final
open SphincsSecurity.Concrete (uniformWordAverage)
open CaseC (theta IsDigestInput Birth FreshSigning countOf lazyOf)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankGameL : DecidableEq T3.Cache := Classical.decEq _
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P) {Sig : Type}
theorem potential_initial_le_rate (budget : Nat) (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law S.horizon (fun W : List P => S.price W - S.specTheta) ≤ rate)
    (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    S.potential budget ((Ghost.empty : Ghost Sig), generated.2) ≤ (budget : ENNReal) * rate / 2 ^ 128 := by
  have hreuse : S.reusePotential (lazyOf generated.2) = 0 :=
    S.reusePotential_of_noDigest _ (CaseC.keygen_noDigest generated hg)
  unfold potential livePotential
  split_ifs with h1 h2
  · exact bot_le
  · simp [Ghost.empty] at h2
  · simp only [hreuse, add_zero]
    have hbank : S.bankValue (Ghost.empty : Ghost Sig) = 0 := by simp [bankValue, Ghost.empty]
    rw [hbank, zero_add]
    unfold excessTerm
    apply ENNReal.div_le_div_right
    apply mul_le_mul'
    · exact_mod_cast Nat.sub_le budget _
    · have he : S.excessForecast S.horizon [] ≤ rate := by
        unfold excessForecast
        simpa [proposals] using hrate
      simpa [Ghost.empty] using he
end FtsBankSpec
namespace FtsBankSpecL
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P)
variable {Sig : Type} (pay : T3.Cache → Digest → HashOutput → M (Option Sig))
noncomputable def source (published : T3.Cache) : QueryImpl (Interaction' Sig) M
  | .inl input => forwardWorld input
  | .inr request => Prod.fst <$> S.authenticatedRecord pay published request
noncomputable def bankImpl (published : T3.Cache) (budget : Nat) :
    QueryImpl (Interaction' Sig) (StateT (BankState Sig) PMF)
  | .inl input => StateT.mk fun st =>
      (liftM (QueryRecorded.run (forwardWorld input) st.2) : PMF _).map fun r =>
        (r.1, (ghostWorld budget input st.1 st.2 r.1, r.2))
  | .inr request => StateT.mk fun st =>
      (liftM (QueryRecorded.run (S.authenticatedRecord pay published request) st.2) : PMF _).map fun r =>
        (r.1.1, (S.ghostSign published request st.1 st.2 (r.1, lazyOf r.2), r.2))
noncomputable def recordedImpl (published : T3.Cache) : QueryImpl (Interaction' Sig) (StateT QueryRecorded.State PMF) :=
  fun input => StateT.mk fun s => (liftM (QueryRecorded.run (S.source pay published input) s) : PMF _)
theorem bank_query_project (published : T3.Cache) (budget : Nat) (input : (Interaction' Sig).Domain)
    (st : BankState Sig) :
    Prod.map id Prod.snd <$> (S.bankImpl pay published budget input).run st =
      (liftM (QueryRecorded.run (S.source pay published input) st.2) : PMF _) := by
  cases input with
  | inl input =>
      change (PMF.map _ (PMF.map _ _)) = _
      rw [PMF.map_comp]
      change PMF.map id _ = _
      rw [PMF.map_id]
      rfl
  | inr request =>
      change (PMF.map _ (PMF.map _ _)) = _
      rw [PMF.map_comp]
      change _ = (liftM (QueryRecorded.run (Prod.fst <$> S.authenticatedRecord pay published request) st.2) : PMF _)
      rw [QueryRecorded.run_map, liftM_map, ← PMF.monad_map_eq_map]
      rfl
theorem bank_project {α : Type} (published : T3.Cache) (budget : Nat)
    (program : OracleComp (Interaction' Sig) α) (st : BankState Sig) :
    Prod.map id Prod.snd <$> (simulateQ (S.bankImpl pay published budget) program).run st =
      (liftM (QueryRecorded.run (simulateQ (S.source pay published) program) st.2) :
        PMF (α × QueryRecorded.State)) := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, QueryRecorded.run_pure, liftM_pure, map_pure]
      rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [simulateQ_bind, simulateQ_spec_query, QueryRecorded.run_bind, liftM_bind]
      rw [← S.bank_query_project pay published budget input st, bind_map_left]
      apply bind_congr
      intro result
      exact ih result.1 result.2
theorem world_unfold (published : T3.Cache) (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain)
    (st : BankState Sig) (f : BankState Sig → ENNReal) :
    expectedValue ((S.bankImpl pay published budget (.inl input)).run st) (fun r => f r.2) =
      expectedValue (QueryRecorded.run (forwardWorld input) st.2)
        (fun r => f (ghostWorld budget input st.1 st.2 r.1, r.2)) := by
  change expectedValue (PMF.map _ (liftM _)) _ = _
  rw [CaseC.expectedValue_pmf_map, CaseC.expectedValue_liftM]
theorem world_step (published : T3.Cache) (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain)
    (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget (.inl input)).run st) (fun r => S.potential budget r.2) ≤
      S.potential budget st + birthCharge budget (.inl input) st := by
  rw [S.world_unfold pay published budget input st (S.potential budget)]
  cases input with
  | inl n =>
      have hb : birthCharge (Sig := Sig) budget (.inl (.inl n)) st = 0 := rfl
      rw [hb, add_zero]
      apply expectedValue_le_of_support
      intro r hr
      have hl := CaseC.lazy_world_coin n (lazyOf st.2) (r.1, lazyOf r.2) (CaseC.recorded_lazy_support _ _ r hr)
      have hc := CaseC.recorded_count_le _ _ r hr
      change S.livePotential budget (countOf r.2) st.1 (lazyOf r.2) ≤
        S.livePotential budget (countOf st.2) st.1 (lazyOf st.2)
      rw [show lazyOf r.2 = lazyOf st.2 from hl]
      exact S.livePotential_count_anti budget hc st.1 _
  | inr x =>
      have hcount : ∀ r ∈ support (QueryRecorded.run (forwardWorld (.inr x)) st.2),
          countOf r.2 = countOf st.2 + 1 :=
        fun r hr => CreationGame.recorded_world_hash_count x st.2 r hr
      set g := st.1 with hg
      set c := countOf st.2 with hc
      set lz := lazyOf st.2 with hlz
      calc
        _ ≤ expectedValue (QueryRecorded.run (forwardWorld (.inr x)) st.2)
            (fun r => S.livePotential budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) (lazyOf r.2)) := by
          apply expectedValue_mono_of_support
          intro r hr
          change S.livePotential budget (countOf r.2) _ _ ≤ _
          rw [hcount r hr]
        _ = expectedValue (LazyPrivate.run (forwardWorld (.inr x)) lz)
            (fun r => S.livePotential budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) r.2) :=
          CaseC.expected_recorded _ _
            (fun r => S.livePotential budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) r.2)
        _ ≤ _ := ?_
      cases hx : lz.2 x with
      | some a0 =>
          rw [CaseC.lazy_world_cached x lz a0 hx, expectedValue_pure]
          have hnb : ¬Birth budget x st.2 := fun h => by
            have h2 := h.2.1
            rw [← hlz, hx] at h2
            cases h2
          have hcb : birthCharge (Sig := Sig) budget (.inl (.inr x)) st = 0 := by simp [birthCharge, hnb]
          simp only [ghostWorld, hnb, if_false, hcb, add_zero]
          exact S.livePotential_count_anti budget (Nat.le_succ _) g _
      | none =>
          rw [CaseC.lazy_world_fresh x lz hx]
          by_cases hbirth : Birth budget x st.2
          · have hcb : birthCharge (Sig := Sig) budget (.inl (.inr x)) st = (theta + 1 / 64) / 2 ^ 128 := by
              simp [birthCharge, hbirth]
            rw [hcb]
            have hlt : c < budget := hbirth.2.2
            have hnot : ¬budget < c + 1 := by omega
            have hnot0 : ¬budget < c := by omega
            simp only [ghostWorld, hbirth, if_true]
            by_cases hd : g.dead = true
            · simp only [FtsBankSpec.livePotential, hd, true_or, if_true, expectedValue_const (by simp : Pr[⊥ |
                ($ᵗ HashOutput : ProbComp HashOutput)] = 0), zero_le]
            have hd' : g.dead = false := by simpa using hd
            by_cases hr : g.reused = true
            · have hpt : S.potential budget st = 1 + S.reusePotential lz :=
                S.livePotential_reused budget c g lz hd' hnot0 hr
              rw [hpt]
              calc
                _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                    (fun a => 1 + S.reusePotential lz + S.admInd a / 2 ^ 128) := by
                  apply expectedValue_mono
                  intro a
                  rw [S.livePotential_reused budget (c + 1) { g with targets := g.targets ++ [a] } _ hd' hnot hr,
                    add_assoc]
                  exact add_le_add le_rfl (S.reusePotential_public_le lz x a hx)
                _ = 1 + S.reusePotential lz +
                    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) S.admInd / 2 ^ 128 := by
                  rw [expectedValue_add, expectedValue_const (by simp)]
                  congr 1
                  simp only [div_eq_mul_inv]
                  rw [expectedValue_mul_const]
                _ ≤ 1 + S.reusePotential lz + S.admBound / 2 ^ 128 :=
                  add_le_add le_rfl (ENNReal.div_le_div_right S.expected_admInd_tight _)
                _ ≤ _ := by
                  rw [← S.theta_add_admBound]
                  apply add_le_add le_rfl
                  apply ENNReal.div_le_div_right
                  exact le_add_self
            · have hr' : g.reused = false := by simpa using hr
              have hpt : S.potential budget st = S.bankValue g + S.reusePotential lz + S.excessTerm budget c g :=
                S.livePotential_alive budget c g lz hd' hnot0 hr'
              rw [hpt]
              set R := S.horizon - g.exposures.length
              have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                  (fun a => S.forecast R g.exposures a) ≤ (S.specTheta + S.excessForecast R g.exposures) / 2 ^ 128 := by
                rw [BPORS.expected_uniform_eq_finiteAverage]
                exact S.average_forecast_le R g.exposures
              calc
                _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a =>
                    S.bankValue g + S.forecast R g.exposures a + (S.reusePotential lz + S.admInd a / 2 ^ 128) +
                      S.excessTerm budget (c + 1) g) := by
                  apply expectedValue_mono
                  intro a
                  rw [S.livePotential_alive budget (c + 1) { g with targets := g.targets ++ [a] } _ hd' hnot hr',
                    S.bankValue_birth]
                  exact add_le_add (add_le_add le_rfl (S.reusePotential_public_le lz x a hx)) le_rfl
                _ = S.bankValue g + expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                      (fun a => S.forecast R g.exposures a) +
                    (S.reusePotential lz + expectedValue ($ᵗ HashOutput : ProbComp HashOutput) S.admInd / 2 ^ 128) +
                    S.excessTerm budget (c + 1) g := by
                  simp only [expectedValue_add, expectedValue_const (by simp : Pr[⊥ |
                    ($ᵗ HashOutput : ProbComp HashOutput)] = 0), div_eq_mul_inv, expectedValue_mul_const]
                _ ≤ S.bankValue g + (S.specTheta + S.excessForecast R g.exposures) / 2 ^ 128 +
                    (S.reusePotential lz + S.admBound / 2 ^ 128) + S.excessTerm budget (c + 1) g := by
                  gcongr
                  exact S.expected_admInd_tight
                _ = S.bankValue g + S.reusePotential lz +
                    (S.excessTerm budget (c + 1) g + S.excessForecast R g.exposures / 2 ^ 128) +
                    (theta + 1 / 64) / 2 ^ 128 := by
                  rw [← S.theta_add_admBound, ENNReal.add_div, ENNReal.add_div]
                  ring
                _ = _ := by rw [← S.excessTerm_succ budget c g hlt]
          · have hcb : birthCharge (Sig := Sig) budget (.inl (.inr x)) st = 0 := by simp [birthCharge, hbirth]
            simp only [ghostWorld, hbirth, if_false, hcb, add_zero]
            apply expectedValue_le_of_le
            intro a
            by_cases hlt : c < budget
            · have hnd : ¬IsDigestInput x := fun hd => hbirth ⟨hd, by rw [← hlz]; exact hx, hlt⟩
              calc
                _ ≤ S.livePotential budget (c + 1) g lz :=
                  S.livePotential_reuse_mono budget (c + 1) g (S.reusePotential_public_nondigest lz x a hx hnd)
                _ ≤ S.livePotential budget c g lz := S.livePotential_count_anti budget (Nat.le_succ _) g lz
                _ = _ := rfl
            · have hover : budget < c + 1 := by omega
              simp [FtsBankSpec.livePotential, hover]
theorem sign_step (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache) (budget : Nat)
    (request : Request) (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget (.inr request)).run st) (fun r => S.potential budget r.2) ≤
      S.potential budget st := by
  set g := st.1 with hg
  set c := countOf st.2 with hc
  set lz := lazyOf st.2 with hlz
  have hunfold : expectedValue ((S.bankImpl pay published budget (.inr request)).run st)
      (fun r => S.potential budget r.2) =
      expectedValue (QueryRecorded.run (S.authenticatedRecord pay published request) st.2)
        (fun r => S.potential budget (S.ghostSign published request st.1 st.2 (r.1, lazyOf r.2), r.2)) := by
    change expectedValue (PMF.map _ (liftM _)) _ = _
    rw [CaseC.expectedValue_pmf_map, CaseC.expectedValue_liftM]
  rw [hunfold]
  calc
    _ ≤ expectedValue (QueryRecorded.run (S.authenticatedRecord pay published request) st.2)
        (fun r => S.livePotential budget c (S.ghostSign published request g st.2 (r.1, lazyOf r.2)) (lazyOf r.2)) := by
      apply expectedValue_mono_of_support
      intro r hr
      change S.livePotential budget (countOf r.2) (S.ghostSign published request st.1 st.2 (r.1, lazyOf r.2))
        (lazyOf r.2) ≤ _
      exact S.livePotential_count_anti budget (CaseC.recorded_count_le _ _ r hr) _ _
    _ = expectedValue (LazyPrivate.run (S.authenticatedRecord pay published request) lz)
        (fun r => S.livePotential budget c (S.ghostSign published request g st.2 r) r.2) :=
      CaseC.expected_recorded _ _ (fun r => S.livePotential budget c (S.ghostSign published request g st.2 r) r.2)
    _ ≤ S.potential budget st := ?_
  change _ ≤ S.livePotential budget c g lz
  by_cases hfresh : FreshSigning published request st.2
  swap
  ·
    apply expectedValue_le_of_support
    intro r hr
    simp only [FtsBankSpec.ghostSign, hfresh, if_false, FtsBankSpec.livePotential_log]
    apply S.livePotential_reuse_mono
    apply S.reusePotential_sign_stale_le lz r.2 request.message
    · intro hcached hnone
      apply hcached
      cases hcz : lz.1 (.inr (.inl request.message)) with
      | none => rfl
      | some a =>
          have := (SourceReplay.run_extends _ lz r hr).1 hcz
          rw [hnone] at this
          cases this
    · intro hnone
      have hcp : request.cache ≠ published := fun h => hfresh ⟨h, hnone⟩
      obtain ⟨h1, h2⟩ := S.sign_unpublished pay published request hcp lz r hr
      exact ⟨h1.trans hnone, by rw [h2]⟩
    · exact fun m' hm' => S.sign_other_nonce pay hAvoids published request lz r hr m' hm'
    · exact fun m' hm' => S.sign_other_reuseMass pay hNotDigest published request lz r hr m' hm'
  by_cases hhor : S.horizon ≤ g.exposures.length
  · apply expectedValue_le_of_le
    intro r
    simp [FtsBankSpec.ghostSign, hfresh, hhor, FtsBankSpec.livePotential]
  have hlen : g.exposures.length < S.horizon := by omega
  by_cases hd : g.dead = true
  · apply expectedValue_le_of_le
    intro r
    simp [FtsBankSpec.ghostSign, hfresh, hhor, FtsBankSpec.livePotential, hd]
  have hd' : g.dead = false := by simpa using hd
  by_cases hb : budget < c
  · apply expectedValue_le_of_le
    intro r
    simp [FtsBankSpec.ghostSign, hfresh, hhor, FtsBankSpec.livePotential, hb]
  obtain ⟨m, cache⟩ := request
  obtain ⟨hcache, hnonce⟩ := hfresh
  change cache = published at hcache
  subst hcache
  change lz.1 (.inr (.inl m)) = none at hnonce
  have hsign : ∀ r ∈ support (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz),
      S.reusePotential r.2 + S.reuseMass lz.2 m ≤ S.reusePotential lz := fun r hr =>
    S.reusePotential_sign_le lz r.2 m hnonce (S.sign_published_nonce pay cache m lz r hr)
      (fun m' hm' => S.sign_other_nonce pay hAvoids cache ⟨m, cache⟩ lz r hr m' hm')
      (fun m' hm' => S.sign_other_reuseMass pay hNotDigest cache ⟨m, cache⟩ lz r hr m' hm')
  have hfr : FreshSigning cache ⟨m, cache⟩ st.2 := ⟨rfl, hnonce⟩
  have hdead : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).dead = false := by
    intro r; simp [FtsBankSpec.ghostSign, hfr, hhor, hd']
  have hreu : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused =
      (g.reused || decide (S.Reuse (lazyOf st.2).2 (CaseC.nonceOf r.2 m) m)) := by
    intro r; simp [FtsBankSpec.ghostSign, hfr, hhor]
  have hexp : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).exposures = g.exposures ++ r.1.2.toList := by
    intro r; simp [FtsBankSpec.ghostSign, hfr, hhor]
  have htar : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).targets = g.targets := by
    intro r; simp [FtsBankSpec.ghostSign, hfr, hhor]
  by_cases hr : g.reused = true
  · apply expectedValue_le_of_support
    intro r hrs
    rw [S.livePotential_reused budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) r.2 (hdead r) hb
        (by rw [hreu r, hr, Bool.true_or]),
      S.livePotential_reused budget c g lz hd' hb hr]
    exact add_le_add le_rfl (le_trans le_self_add (hsign r hrs))
  have hr' : g.reused = false := by simpa using hr
  set P' := S.bankValue g + S.excessTerm budget c g with hP
  let Fmain : (Option Sig × Option HashOutput) × LazyPrivate.State → ENNReal := fun r =>
    if S.Reuse lz.2 (CaseC.nonceOf r.2 m) m then 1 else r.1.2.elim P' (S.signWeight budget c g)
  have hpoint : ∀ r, S.livePotential budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) r.2 ≤
      Fmain r + S.reusePotential r.2 := by
    intro r
    by_cases hre : S.Reuse lz.2 (CaseC.nonceOf r.2 m) m
    · have hru : (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused = true := by
        rw [hreu r, hr', Bool.false_or]
        exact decide_eq_true hre
      rw [S.livePotential_reused budget c _ r.2 (hdead r) hb hru]
      simp only [Fmain, hre, if_true, le_refl]
    · have hru : (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused = false := by
        rw [hreu r, hr', Bool.false_or]
        exact decide_eq_false hre
      rw [S.livePotential_alive budget c _ r.2 (hdead r) hb hru]
      simp only [Fmain, hre, if_false]
      have hbv : S.bankValue (S.ghostSign cache ⟨m, cache⟩ g st.2 r) =
          S.bankValue { g with exposures := g.exposures ++ r.1.2.toList } := by
        unfold FtsBankSpec.bankValue; rw [htar r, hexp r]
      have het : S.excessTerm budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) =
          S.excessTerm budget c { g with exposures := g.exposures ++ r.1.2.toList } := by
        unfold FtsBankSpec.excessTerm; rw [hexp r]
      rw [hbv, het]
      cases hsel : r.1.2 with
      | none =>
          simp only [Option.toList_none, List.append_nil, Option.elim_none, hP]
          apply le_of_eq
          ring
      | some A =>
          simp only [Option.toList_some, Option.elim_some, FtsBankSpec.signWeight]
          apply le_of_eq
          ring
  calc
    _ ≤ expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
        (fun r => Fmain r + S.reusePotential r.2) := expectedValue_mono _ hpoint
    _ = expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz) Fmain +
        expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2) := expectedValue_add _ _ _
    _ ≤ (P' + S.reuseMass lz.2 m) +
        expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2) := by
      apply add_le_add _ le_rfl
      apply S.fresh_signing_kernel pay cache m lz hnonce Fmain (S.signWeight budget c g) P'
        (le_of_eq (S.freshPrice_signWeight budget c g hlen))
      intro r _
      exact le_rfl
    _ = P' + (expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2 + S.reuseMass lz.2 m)) := by
      rw [expectedValue_add, expectedValue_const (by simp)]
      ring
    _ ≤ P' + S.reusePotential lz := add_le_add le_rfl (expectedValue_le_of_support hsign)
    _ = S.livePotential budget c g lz := by
      rw [S.livePotential_alive budget c g lz hd' hb hr', hP]
      ring
theorem potential_step (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache)
    (budget : Nat) (input : (Interaction' Sig).Domain) (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget input).run st) (fun r => S.potential budget r.2) ≤
      S.potential budget st + birthCharge budget input st := by
  cases input with
  | inl input => exact S.world_step pay published budget input st
  | inr request => exact (S.sign_step pay hNotDigest hAvoids published budget request st).trans le_self_add
theorem potential_run {α : Type} (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache)
    (budget : Nat) (program : OracleComp (Interaction' Sig) α) (st : BankState Sig) :
    expectedValue ((simulateQ (S.bankImpl pay published budget) program).run st)
        (fun r => S.potential budget r.2) ≤
      S.potential budget st + BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
        (birthCharge budget) program st := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, BPORS.Adaptive.Creation.expectedCharges_pure, add_zero]
      rw [expectedValue_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, expectedValue_bind,
        BPORS.Adaptive.Creation.expectedCharges_query_bind]
      calc
        _ ≤ expectedValue ((S.bankImpl pay published budget input).run st) (fun result =>
            S.potential budget result.2 + BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
              (birthCharge budget) (next result.1) result.2) :=
          expectedValue_mono _ fun result => ih result.1 result.2
        _ = expectedValue ((S.bankImpl pay published budget input).run st)
              (fun result => S.potential budget result.2) +
            expectedValue ((S.bankImpl pay published budget input).run st) (fun result =>
              BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
                (birthCharge budget) (next result.1) result.2) := expectedValue_add _ _ _
        _ ≤ (S.potential budget st + birthCharge budget input st) + _ :=
          add_le_add (S.potential_step pay hNotDigest hAvoids published budget input st) le_rfl
        _ = _ := by ring
theorem bank_charges_eq_births {α : Type} (published : T3.Cache) (budget : Nat)
    (program : OracleComp (Interaction' Sig) α) (s : QueryRecorded.State) (g : Ghost Sig) :
    BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget) (birthCharge budget) program (g, s) =
      (theta + 1 / 64) / 2 ^ 128 * BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay published)
        (birthWeight budget) program s := by
  have h1 : BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget) (birthCharge budget)
      program (g, s) =
      BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
        (fun input st => (theta + 1 / 64) / 2 ^ 128 * birthWeight budget input st.2) program (g, s) := by
    congr 1
    funext input st
    exact birthCharge_eq budget input st
  rw [h1, BPORS.Adaptive.Creation.expectedCharges_scale]
  congr 1
  exact BPORS.Adaptive.Creation.expectedCharges_project (S.bankImpl pay published budget)
    (S.recordedImpl pay published) Prod.snd
    (fun input st => S.bank_query_project pay published budget input st)
    (birthWeight budget) program (g, s)
noncomputable def bankExperiment (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) :
    PMF (Bool × BankState Sig) := do
  let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
  (simulateQ (S.bankImpl pay generated.1.2 budget) (rest generated.1.1 generated.1.2)).run (Ghost.empty, generated.2)
noncomputable def recordedExperiment (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) :
    PMF (Bool × QueryRecorded.State) := do
  let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
  (liftM (QueryRecorded.run (simulateQ (S.source pay generated.1.2) (rest generated.1.1 generated.1.2))
    generated.2) : PMF _)
theorem bank_experiment_project (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) :
    (fun r : Bool × BankState Sig => (r.1, r.2.2)) <$> S.bankExperiment pay rest budget =
      S.recordedExperiment pay rest := by
  unfold bankExperiment recordedExperiment
  rw [map_bind]
  apply bind_congr
  intro generated
  exact S.bank_project pay generated.1.2 budget (rest generated.1.1 generated.1.2) (Ghost.empty, generated.2)
noncomputable def expectedBirths (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) :
    ENNReal :=
  expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _) (fun generated =>
    BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay generated.1.2) (birthWeight budget)
      (rest generated.1.1 generated.1.2) generated.2)
theorem bank_potential_le (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) :
    expectedValue (S.bankExperiment pay rest budget) (fun r => S.potential budget r.2) ≤
      (theta + 1 / 64) / 2 ^ 128 * S.expectedBirths pay rest budget +
        (budget : ENNReal) * S.excessRate / 2 ^ 128 := by
  unfold bankExperiment
  rw [expectedValue_bind]
  calc
    _ ≤ expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _) (fun generated =>
        (budget : ENNReal) * S.excessRate / 2 ^ 128 +
          (theta + 1 / 64) / 2 ^ 128 * BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay generated.1.2)
            (birthWeight budget) (rest generated.1.1 generated.1.2) generated.2) := by
      apply CaseC.pmf_expectedValue_mono
      intro generated hg
      rw [MonitoredPrivate.pmf_support] at hg
      refine (S.potential_run pay hNotDigest hAvoids generated.1.2 budget _ _).trans ?_
      rw [S.bank_charges_eq_births pay generated.1.2 budget]
      exact add_le_add (S.potential_initial_le budget generated hg) le_rfl
    _ = _ := by
      rw [expectedValue_add, expectedValue_const (by simp), CaseC.pmf_expectedValue_left_mul]
      unfold expectedBirths
      ring
theorem bank_event_le (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat)
    (weight : Bool × QueryRecorded.State → ENNReal) (hle : ∀ y, weight y ≤ 1)
    (hwin : ∀ b ∈ (S.bankExperiment pay rest budget).support, weight (b.1, b.2.2) ≠ 0 → 1 ≤ S.potential budget b.2) :
    expectedValue (S.recordedExperiment pay rest) weight ≤
      (theta + 1 / 64) / 2 ^ 128 * S.expectedBirths pay rest budget +
        (budget : ENNReal) * S.excessRate / 2 ^ 128 := by
  rw [← S.bank_experiment_project pay rest budget, PMF.monad_map_eq_map, CaseC.expectedValue_pmf_map]
  refine le_trans ?_ (S.bank_potential_le pay hNotDigest hAvoids rest budget)
  apply CaseC.pmf_expectedValue_mono
  intro b hb
  by_cases h0 : weight (b.1, b.2.2) = 0
  · rw [h0]; exact bot_le
  · exact (hle _).trans (hwin b hb h0)
theorem bank_potential_le_rate (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law S.horizon (fun W : List P => S.price W - S.specTheta) ≤ rate) :
    expectedValue (S.bankExperiment pay rest budget) (fun r => S.potential budget r.2) ≤
      (theta + 1 / 64) / 2 ^ 128 * S.expectedBirths pay rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 := by
  unfold bankExperiment
  rw [expectedValue_bind]
  calc
    _ ≤ expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _) (fun generated =>
        (budget : ENNReal) * rate / 2 ^ 128 +
          (theta + 1 / 64) / 2 ^ 128 * BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay generated.1.2)
            (birthWeight budget) (rest generated.1.1 generated.1.2) generated.2) := by
      apply CaseC.pmf_expectedValue_mono
      intro generated hg
      rw [MonitoredPrivate.pmf_support] at hg
      refine (S.potential_run pay hNotDigest hAvoids generated.1.2 budget _ _).trans ?_
      rw [S.bank_charges_eq_births pay generated.1.2 budget]
      exact add_le_add (S.toFtsBankSpec.potential_initial_le_rate budget rate hrate generated hg) le_rfl
    _ = _ := by
      rw [expectedValue_add, expectedValue_const (by simp), CaseC.pmf_expectedValue_left_mul]
      unfold expectedBirths
      ring
theorem bank_event_le_rate (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law S.horizon (fun W : List P => S.price W - S.specTheta) ≤ rate)
    (weight : Bool × QueryRecorded.State → ENNReal) (hle : ∀ y, weight y ≤ 1)
    (hwin : ∀ b ∈ (S.bankExperiment pay rest budget).support, weight (b.1, b.2.2) ≠ 0 → 1 ≤ S.potential budget b.2) :
    expectedValue (S.recordedExperiment pay rest) weight ≤
      (theta + 1 / 64) / 2 ^ 128 * S.expectedBirths pay rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 := by
  rw [← S.bank_experiment_project pay rest budget, PMF.monad_map_eq_map, CaseC.expectedValue_pmf_map]
  refine le_trans ?_ (S.bank_potential_le_rate pay hNotDigest hAvoids rest budget rate hrate)
  apply CaseC.pmf_expectedValue_mono
  intro b hb
  by_cases h0 : weight (b.1, b.2.2) = 0
  · rw [h0]; exact bot_le
  · exact (hle _).trans (hwin b hb h0)
end FtsBankSpecL
end ClaudeWCT.Bank
end
end
-- ==== merged from T3_Secc_CaseCLinkInv ====
section

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityExtraction (queried)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCLinkInv : DecidableEq T3.Cache := Classical.decEq _
def Agrees (A : Correctness.Answers) (lazy : LazyPrivate.State) : Prop :=
  ∀ input answer, SourceReplay.known lazy input = some answer → A input = answer
theorem Agrees.mono {A : Correctness.Answers} {lazy lazy' : LazyPrivate.State} (h : Agrees A lazy')
    (hext : SourceReplay.Extends lazy lazy') : Agrees A lazy :=
  fun input answer hk => h input answer (SourceReplay.known_mono lazy lazy' hext hk)
def eventPublic : FirstHit.QueryEvent → Option (HashInput × HashOutput)
  | ⟨_, .inl (.inr x), a⟩ => some (x, a)
  | _ => none
def SignerQueried (published : T3.Cache) (log : QueryLog Requests) (lazy : LazyPrivate.State) (x : HashInput) :
    Prop :=
  ∃ entry ∈ log, ∀ A, Agrees A lazy →
    (.inl (.inr x) : T3.Spec.Domain) ∈ queried A (FullGame.authenticatedSign published entry.1)
structure BankInv (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent) (st : BankState) : Prop where
  len : st.1.exposures.length ≤ st.1.log.length
  dead : st.1.dead = true → horizon < st.1.log.length
  events : ∀ e ∈ st.2.events, e ∈ kg ∨ ∀ x a, eventPublic e = some (x, a) → IsDigestInput x →
    e.before.2 x = none → a ∈ st.1.targets ∨ budget < countOf st.2 ∨ SignerQueried published st.1.log (lazyOf st.2) x
  exposed : st.1.dead = false → ∀ m, (lazyOf st.2).1 (.inr (.inl m)) ≠ none → ∀ A, Agrees A (lazyOf st.2) →
    ∀ c out, evalWithAnswerFn A (digestSearch (nonceOf (lazyOf st.2) m) m 0 attemptLimit) = some (c, out) →
      out ∈ st.1.exposures
  logged : ∀ entry ∈ st.1.log, ∀ σ, entry.2 = some σ → entry.1.cache = published ∧
    (lazyOf st.2).1 (.inr (.inl entry.1.message)) ≠ none ∧ σ.rho = nonceOf (lazyOf st.2) entry.1.message
theorem nonceOf_extends {lazy lazy' : LazyPrivate.State} (hext : SourceReplay.Extends lazy lazy') (m : Message)
    (h : lazy.1 (.inr (.inl m)) ≠ none) : nonceOf lazy' m = nonceOf lazy m ∧ lazy'.1 (.inr (.inl m)) ≠ none := by
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp h
  have h' := hext.1 ho
  simp [nonceOf, ho, h']
theorem eval_privateNonce (A : Correctness.Answers) (lazy : LazyPrivate.State) (hA : Agrees A lazy) (m : Message)
    (h : lazy.1 (.inr (.inl m)) ≠ none) : evalWithAnswerFn A (privateNonce m) = nonceOf lazy m := by
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp h
  have hk : A (.inr (.inr (.inl m))) = o := hA (.inr (.inr (.inl m))) o ho
  unfold privateNonce privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, nonceOf, ho, Option.getD_some]
  rw [← hk]
  rfl
theorem eval_payloadAfterDigest_rho (A : Correctness.Answers) (cache : T3.Cache) (rho : Digest)
    (output : HashOutput) (σ : Signature) (h : evalWithAnswerFn A (payloadAfterDigest cache rho output) = some σ) :
    σ.rho = rho := by
  unfold payloadAfterDigest at h
  simp only [evalWithAnswerFn_bind] at h
  split at h
  all_goals (rw [evalWithAnswerFn_pure] at h; cases h)
  all_goals rfl
theorem recorded_new_events {α : Type} (program : M α) (s : QueryRecorded.State) (r : α × QueryRecorded.State)
    (hr : r ∈ support (QueryRecorded.run program s)) :
    ∃ rec ∈ support (FirstHit.record program (lazyOf s)),
      r.2.events = s.events ++ rec.events ∧ rec.state = lazyOf r.2 ∧ rec.value = r.1 := by
  have hm : QueryRecorded.recorded r ∈ support (QueryRecorded.recorded <$> QueryRecorded.run program s) := by
    rw [support_map]; exact ⟨r, hr, rfl⟩
  rw [QueryRecorded.run_recorded, support_map] at hm
  obtain ⟨rec, hrec, he⟩ := hm
  refine ⟨rec, hrec, ?_, ?_, ?_⟩
  · have := congrArg FirstHit.Recorded.events he
    exact this.symm
  · have := congrArg FirstHit.Recorded.state he
    exact this
  · have := congrArg FirstHit.Recorded.value he
    exact this
theorem world_query_support (input : SphincsSecurity.OracleWorld.Domain) (s : QueryRecorded.State)
    (q : SphincsSecurity.OracleWorld.Range input × QueryRecorded.State)
    (hq : q ∈ support (QueryRecorded.run (forwardWorld input) s)) :
    q.2.events = s.events ++ [⟨lazyOf s, .inl input, q.1⟩] ∧
      countOf q.2 = countOf s + FullGame.queryCharge (.inl input) ∧
      (q.1, lazyOf q.2) ∈ support (LazyPrivate.run (forwardWorld input) (lazyOf s)) := by
  change q ∈ support (QueryRecorded.run (liftM (T3.Spec.query (.inl input))) s) at hq
  rw [QueryRecorded.run_query_explicit, support_map] at hq
  obtain ⟨res, hres, rfl⟩ := hq
  exact ⟨rfl, rfl, hres⟩
theorem world_private_eq (input : SphincsSecurity.OracleWorld.Domain) (lazy : LazyPrivate.State)
    (res : SphincsSecurity.OracleWorld.Range input × LazyPrivate.State)
    (hres : res ∈ support (LazyPrivate.run (forwardWorld input) lazy)) : res.2.1 = lazy.1 := by
  cases input with
  | inl n => rw [lazy_world_coin n lazy res hres]
  | inr x =>
      change res ∈ support (LazyPrivate.run (Sampling.publicHandler x) lazy) at hres
      rw [LazyPrivate.run_publicQuery, mem_support_bind_iff] at hres
      obtain ⟨step, _, hres⟩ := hres
      rw [mem_support_pure_iff] at hres
      subst hres
      rfl
end SigGolfCandidate.T3.Security.CaseC
end
-- ==== merged from ClaudeWCT_Bank_GameInv ====
section

namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open CaseC (Agrees Birth FreshSigning countOf lazyOf IsDigestInput eventPublic nonceOf)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankInv : DecidableEq T3.Cache := Classical.decEq _
def PayHashOnly {Sig : Type} (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) : Prop :=
  ∀ cache rho output, Security.SourceReplay.HashOnly (pay cache rho output)
def PayRho {Sig : Type} (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (sigRho : Sig → Digest) : Prop :=
  ∀ (A : Correctness.Answers) cache rho output σ, evalWithAnswerFn A (pay cache rho output) = some σ → sigRho σ = rho
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
variable {Sig : Type} (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (sigRho : Sig → Digest)
theorem eval_recordForNonce_selected (A : Correctness.Answers) (cache : T3.Cache) (rho : Digest) (m : Message) :
    (evalWithAnswerFn A (S.recordForNonce pay cache rho m)).2 =
      (evalWithAnswerFn A (S.search rho m 0 attemptLimit)).map Prod.snd := by
  unfold recordForNonce
  simp only [evalWithAnswerFn_bind]
  cases evalWithAnswerFn A (S.search rho m 0 attemptLimit) with
  | none => simp
  | some found =>
      rcases found with ⟨c, out⟩
      simp
theorem eval_recordForNonce_rho (hrho : PayRho pay sigRho) (A : Correctness.Answers) (cache : T3.Cache)
    (rho : Digest) (m : Message) (σ : Sig) (h : (evalWithAnswerFn A (S.recordForNonce pay cache rho m)).1 = some σ) :
    sigRho σ = rho := by
  unfold recordForNonce at h
  simp only [evalWithAnswerFn_bind] at h
  cases hd : evalWithAnswerFn A (S.search rho m 0 attemptLimit) with
  | none => simp [hd] at h
  | some found =>
      rcases found with ⟨c, out⟩
      simp only [hd, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at h
      exact hrho A cache rho out σ h
theorem eval_authenticatedRecord (A : Correctness.Answers) (published : T3.Cache) (request : Request) :
    evalWithAnswerFn A (S.authenticatedRecord pay published request) =
      if request.cache = published then
        evalWithAnswerFn A (S.recordForNonce pay published (evalWithAnswerFn A (privateNonce request.message))
          request.message)
      else (none, none) := by
  unfold authenticatedRecord
  simp only [evalWithAnswerFn_bind]
  by_cases hc : request.cache = published
  · rw [if_pos hc, if_pos hc]
    unfold payloadRecord
    rw [evalWithAnswerFn_bind, hc]
  · rw [if_neg hc, if_neg hc]
    rfl
theorem eval_source_sign (A : Correctness.Answers) (published : T3.Cache) (request : Request) :
    evalWithAnswerFn A (S.source pay published (.inr request)) =
      (evalWithAnswerFn A (S.authenticatedRecord pay published request)).1 := by
  change evalWithAnswerFn A (Prod.fst <$> S.authenticatedRecord pay published request) = _
  rw [SigGolfCandidate.T3M.eval_map]
theorem queried_record_sign (A : Correctness.Answers) (published : T3.Cache) (request : Request) :
    SourceReplay.queried A (S.authenticatedRecord pay published request) =
      queried A (S.source pay published (.inr request)) := by
  change _ = queried A (Prod.fst <$> S.authenticatedRecord pay published request)
  rw [SigGolfCandidate.T3M.Extract.queried_map]
  rfl
theorem authenticatedRecord_hashOnly (hhash : PayHashOnly pay) (published : T3.Cache) (request : Request) :
    Security.SourceReplay.HashOnly (S.authenticatedRecord pay published request) := by
  unfold authenticatedRecord
  apply SourceQueries.bind_allowed
  · exact SourceQueries.privateMac_allowed Security.SourceReplay.IsHash (fun _ => trivial) _
  · intro tag
    split
    · unfold payloadRecord recordForNonce
      apply SourceQueries.bind_allowed
      · exact SourceQueries.privateNonce_allowed Security.SourceReplay.IsHash (fun _ => trivial) _
      · intro rho
        apply SourceQueries.bind_allowed _
          (S.search_allowed rho request.message _ (fun _ _ => trivial) attemptLimit 0 (by decide))
        intro found
        split
        · exact SourceQueries.pure_allowed _ _
        · exact SourceQueries.bind_allowed _ (hhash _ _ _) fun _ => SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
def SignerQueried (published : T3.Cache) (log : QueryLog (Requests' Sig)) (lazy : LazyPrivate.State)
    (x : HashInput) : Prop :=
  ∃ entry ∈ log, ∀ A, Agrees A lazy →
    (.inl (.inr x) : T3.Spec.Domain) ∈ queried A (S.source pay published (.inr entry.1))
structure BankInv (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent) (st : BankState Sig) :
    Prop where
  len : st.1.exposures.length ≤ st.1.log.length
  dead : st.1.dead = true → S.horizon < st.1.log.length
  events : ∀ e ∈ st.2.events, e ∈ kg ∨ ∀ x a, eventPublic e = some (x, a) → IsDigestInput x →
    e.before.2 x = none → a ∈ st.1.targets ∨ budget < countOf st.2 ∨ S.SignerQueried pay published st.1.log (lazyOf st.2) x
  exposed : st.1.dead = false → ∀ m, (lazyOf st.2).1 (.inr (.inl m)) ≠ none → ∀ A, Agrees A (lazyOf st.2) →
    ∀ c out, evalWithAnswerFn A (S.search (nonceOf (lazyOf st.2) m) m 0 attemptLimit) = some (c, out) →
      out ∈ st.1.exposures
  logged : ∀ entry ∈ st.1.log, ∀ σ, entry.2 = some σ → entry.1.cache = published ∧
    (lazyOf st.2).1 (.inr (.inl entry.1.message)) ≠ none ∧ sigRho σ = nonceOf (lazyOf st.2) entry.1.message
theorem bank_support_world (published : T3.Cache) (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain)
    (st : BankState Sig) (r : SphincsSecurity.OracleWorld.Range input × BankState Sig)
    (hr : r ∈ ((S.bankImpl pay published budget (.inl input)).run st).support) :
    ∃ q ∈ support (QueryRecorded.run (forwardWorld input) st.2),
      r = (q.1, (ghostWorld budget input st.1 st.2 q.1, q.2)) := by
  change r ∈ (PMF.map _ (liftM (QueryRecorded.run (forwardWorld input) st.2))).support at hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  refine ⟨q, ?_, rfl⟩
  rw [MonitoredPrivate.pmf_support] at hq
  exact hq
theorem bank_support_sign (published : T3.Cache) (budget : Nat) (request : Request)
    (st : BankState Sig) (r : Option Sig × BankState Sig)
    (hr : r ∈ ((S.bankImpl pay published budget (.inr request)).run st).support) :
    ∃ q ∈ support (QueryRecorded.run (S.authenticatedRecord pay published request) st.2),
      r = (q.1.1, (S.ghostSign published request st.1 st.2 (q.1, lazyOf q.2), q.2)) := by
  change r ∈ (PMF.map _ (liftM (QueryRecorded.run (S.authenticatedRecord pay published request) st.2))).support
    at hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  refine ⟨q, ?_, rfl⟩
  rw [MonitoredPrivate.pmf_support] at hq
  exact hq
omit [Fintype P] [SampleableType P] S pay sigRho in
theorem ghostWorld_fields (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain) (g : Ghost Sig)
    (s : QueryRecorded.State) (a : SphincsSecurity.OracleWorld.Range input) :
    (ghostWorld budget input g s a).exposures = g.exposures ∧ (ghostWorld budget input g s a).log = g.log ∧
      (ghostWorld budget input g s a).dead = g.dead ∧ (ghostWorld budget input g s a).reused = g.reused ∧
      ∀ N ∈ g.targets, N ∈ (ghostWorld budget input g s a).targets := by
  cases input with
  | inl n => exact ⟨rfl, rfl, rfl, rfl, fun _ h => h⟩
  | inr x =>
      by_cases hb : Birth budget x s
      · simp only [ghostWorld, hb, if_true, true_and]
        exact fun _ h => List.mem_append_left _ h
      · simp only [ghostWorld, hb, if_false, true_and]
        exact fun _ h => h
theorem bankInv_world (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (input : SphincsSecurity.OracleWorld.Domain) (st : BankState Sig) (hinv : S.BankInv pay sigRho published budget kg st)
    (r : SphincsSecurity.OracleWorld.Range input × BankState Sig)
    (hr : r ∈ ((S.bankImpl pay published budget (.inl input)).run st).support) :
    S.BankInv pay sigRho published budget kg r.2 := by
  obtain ⟨q, hq, rfl⟩ := S.bank_support_world pay published budget input st r hr
  obtain ⟨hev, hcount, hlazy⟩ := CaseC.world_query_support input st.2 q hq
  have hext : SourceReplay.Extends (lazyOf st.2) (lazyOf q.2) :=
    SourceReplay.run_extends _ (lazyOf st.2) (q.1, lazyOf q.2) hlazy
  have hpriv : (lazyOf q.2).1 = (lazyOf st.2).1 :=
    CaseC.world_private_eq input (lazyOf st.2) (q.1, lazyOf q.2) hlazy
  obtain ⟨hX, hL, hD, hR, hT⟩ := ghostWorld_fields budget input st.1 st.2 q.1
  have hcle : countOf st.2 ≤ countOf q.2 := by rw [hcount]; exact Nat.le_add_right _ _
  constructor
  · simp only [hX, hL]; exact hinv.len
  · simp only [hD, hL]; exact hinv.dead
  · intro e he
    rw [hev, List.mem_append] at he
    rcases he with he | he
    · rcases hinv.events e he with hk | hp
      · exact Or.inl hk
      · right
        intro x a hxa hdig hfresh
        rcases hp x a hxa hdig hfresh with ht | hb | hs
        · exact Or.inl (hT _ ht)
        · exact Or.inr (Or.inl (lt_of_lt_of_le hb hcle))
        · right; right
          obtain ⟨entry, hentry, hq'⟩ := hs
          exact ⟨entry, by rw [hL]; exact hentry, fun A hA => hq' A (hA.mono hext)⟩
    · rw [List.mem_singleton] at he
      subst he
      right
      intro x a hxa hdig hfresh
      cases input with
      | inl n => simp [eventPublic] at hxa
      | inr y =>
          simp only [eventPublic, Option.some.injEq, Prod.mk.injEq] at hxa
          obtain ⟨hy, ha⟩ := hxa
          subst hy
          by_cases hlt : countOf st.2 < budget
          · left
            have hbirth : Birth budget y st.2 := ⟨hdig, hfresh, hlt⟩
            simp only [ghostWorld, hbirth, if_true]
            rw [← ha]
            exact List.mem_append_right _ (List.mem_singleton_self _)
          · right; left
            rw [hcount]
            change budget < countOf st.2 + 1
            omega
  · intro hdead m hm A hA c out hs
    rw [hD] at hdead
    have hm0 : (lazyOf st.2).1 (.inr (.inl m)) ≠ none := by rwa [← hpriv]
    have hn : nonceOf (lazyOf q.2) m = nonceOf (lazyOf st.2) m := by simp [nonceOf, hpriv]
    rw [hn] at hs
    rw [hX]
    exact hinv.exposed hdead m hm0 A (hA.mono hext) c out hs
  · intro entry he σ hσ
    rw [hL] at he
    obtain ⟨h1, h2, h3⟩ := hinv.logged entry he σ hσ
    refine ⟨h1, by rwa [hpriv], ?_⟩
    rw [h3]
    simp [nonceOf, hpriv]
theorem ghostSign_log (published : T3.Cache) (request : Request) (g : Ghost Sig) (s : QueryRecorded.State)
    (q : (Option Sig × Option HashOutput) × LazyPrivate.State) :
    (S.ghostSign published request g s q).log = g.log ++ [⟨request, q.1.1⟩] := by
  unfold ghostSign; split_ifs <;> rfl
theorem ghostSign_targets (published : T3.Cache) (request : Request) (g : Ghost Sig) (s : QueryRecorded.State)
    (q : (Option Sig × Option HashOutput) × LazyPrivate.State) :
    (S.ghostSign published request g s q).targets = g.targets := by
  unfold ghostSign; split_ifs <;> rfl
theorem ghostSign_exposures_len (published : T3.Cache) (request : Request) (g : Ghost Sig) (s : QueryRecorded.State)
    (q : (Option Sig × Option HashOutput) × LazyPrivate.State) :
    (S.ghostSign published request g s q).exposures.length ≤ g.exposures.length + 1 := by
  unfold ghostSign
  split_ifs
  · simp
  · cases q.1.2 <;> simp
  · simp
theorem bankInv_sign (hhash : PayHashOnly pay) (hrho : PayRho pay sigRho) (hAvoids : PayAvoids pay)
    (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (request : Request) (st : BankState Sig) (hinv : S.BankInv pay sigRho published budget kg st)
    (r : Option Sig × BankState Sig)
    (hr : r ∈ ((S.bankImpl pay published budget (.inr request)).run st).support) :
    S.BankInv pay sigRho published budget kg r.2 := by
  obtain ⟨q, hq, rfl⟩ := S.bank_support_sign pay published budget request st r hr
  obtain ⟨rec, hrec, hev, hstate, hvalue⟩ := CaseC.recorded_new_events _ st.2 q hq
  have hlazy := CaseC.recorded_lazy_support _ st.2 q hq
  have hext : SourceReplay.Extends (lazyOf st.2) (lazyOf q.2) :=
    SourceReplay.run_extends _ (lazyOf st.2) (q.1, lazyOf q.2) hlazy
  have hres : SourceReplay.Resolves (lazyOf q.2) (S.authenticatedRecord pay published request) q.1 :=
    SourceReplay.resolves_of_run _ (S.authenticatedRecord_hashOnly pay hhash published request) _ _ hlazy
  have hcle := CaseC.recorded_count_le _ st.2 q hq
  have hlog := S.ghostSign_log published request st.1 st.2 (q.1, lazyOf q.2)
  have htar := S.ghostSign_targets published request st.1 st.2 (q.1, lazyOf q.2)
  have h1 := S.ghostSign_exposures_len published request st.1 st.2 (q.1, lazyOf q.2)
  set g' := S.ghostSign published request st.1 st.2 (q.1, lazyOf q.2) with hg'
  show S.BankInv pay sigRho published budget kg (g', q.2)
  constructor
  ·
    show g'.exposures.length ≤ g'.log.length
    rw [hlog, List.length_append, List.length_singleton]
    have := hinv.len
    omega
  ·
    intro hd
    rw [hlog, List.length_append, List.length_singleton]
    by_cases hf : FreshSigning published request st.2
    · by_cases hh : S.horizon ≤ st.1.exposures.length
      · have := hinv.len
        omega
      · have hd0 : st.1.dead = true := by
          simpa [hg', ghostSign, hf, hh] using hd
        have := hinv.dead hd0
        omega
    · have hd0 : st.1.dead = true := by
        simpa [hg', ghostSign, hf] using hd
      have := hinv.dead hd0
      omega
  ·
    intro e he
    rw [hev, List.mem_append] at he
    rcases he with he | he
    · rcases hinv.events e he with hk | hp
      · exact Or.inl hk
      · right
        intro x a hxa hdig hfresh
        rcases hp x a hxa hdig hfresh with ht | hb | hs
        · left; rw [htar]; exact ht
        · exact Or.inr (Or.inl (lt_of_lt_of_le hb hcle))
        · right; right
          obtain ⟨entry, hentry, hq'⟩ := hs
          exact ⟨entry, by rw [hlog]; exact List.mem_append_left _ hentry, fun A hA => hq' A (hA.mono hext)⟩
    · right
      intro x a hxa _ _
      right; right
      refine ⟨⟨request, q.1.1⟩, by rw [hlog]; exact List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      intro A hA
      have hinputs := FirstHit.recorded_inputs _ (S.authenticatedRecord_hashOnly pay hhash published request)
        (lazyOf st.2) rec hrec A (by rw [hstate]; exact hA)
      have hmem : e.input ∈ rec.events.map FirstHit.QueryEvent.input := List.mem_map_of_mem he
      rw [hinputs, S.queried_record_sign pay] at hmem
      have hin : e.input = .inl (.inr x) := by
        rcases e with ⟨before, input, answer⟩
        rcases input with (n | y) | coordinate
        · simp [eventPublic] at hxa
        · simp only [eventPublic, Option.some.injEq, Prod.mk.injEq] at hxa
          rw [hxa.1]
        · simp [eventPublic] at hxa
      rw [hin] at hmem
      exact hmem
  ·
    intro hdead m hm A hA c out hs
    by_cases hf : FreshSigning published request st.2
    · by_cases hh : S.horizon ≤ st.1.exposures.length
      · simp [hg', ghostSign, hf, hh] at hdead
      · have hdead0 : st.1.dead = false := by simpa [hg', ghostSign, hf, hh] using hdead
        have hX : g'.exposures = st.1.exposures ++ q.1.2.toList := by simp [hg', ghostSign, hf, hh]
        rw [hX]
        by_cases hmm : m = request.message
        · subst hmm
          obtain ⟨hcache, hnonce⟩ := hf
          have heval := hres.eval A hA
          rw [S.eval_authenticatedRecord pay, if_pos hcache,
            CaseC.eval_privateNonce A (lazyOf q.2) hA request.message hm] at heval
          have hsel := S.eval_recordForNonce_selected pay A published (nonceOf (lazyOf q.2) request.message)
            request.message
          rw [heval, hs] at hsel
          apply List.mem_append_right
          rw [hsel]
          simp
        · have hn := S.sign_other_nonce pay hAvoids published request (lazyOf st.2) (q.1, lazyOf q.2) hlazy m hmm
          have hm0 : (lazyOf st.2).1 (.inr (.inl m)) ≠ none := by rwa [← hn]
          obtain ⟨hno, _⟩ := CaseC.nonceOf_extends hext m hm0
          rw [hno] at hs
          exact List.mem_append_left _ (hinv.exposed hdead0 m hm0 A (hA.mono hext) c out hs)
    · have hdead0 : st.1.dead = false := by simpa [hg', ghostSign, hf] using hdead
      have hX : g'.exposures = st.1.exposures := by simp [hg', ghostSign, hf]
      rw [hX]
      have hm0 : (lazyOf st.2).1 (.inr (.inl m)) ≠ none := by
        by_cases hmm : m = request.message
        · subst hmm
          by_cases hc : request.cache = published
          · intro hnone
            exact hf ⟨hc, hnone⟩
          · have := (S.sign_unpublished pay published request hc (lazyOf st.2) (q.1, lazyOf q.2) hlazy).1
            rwa [← this]
        · have hn := S.sign_other_nonce pay hAvoids published request (lazyOf st.2) (q.1, lazyOf q.2) hlazy m hmm
          rwa [← hn]
      obtain ⟨hno, _⟩ := CaseC.nonceOf_extends hext m hm0
      rw [hno] at hs
      exact hinv.exposed hdead0 m hm0 A (hA.mono hext) c out hs
  ·
    intro entry he σ hσ
    rw [hlog, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨h1, h2, h3⟩ := hinv.logged entry he σ hσ
      obtain ⟨hno, hc'⟩ := CaseC.nonceOf_extends hext entry.1.message h2
      exact ⟨h1, hc', by rw [hno]; exact h3⟩
    · rw [List.mem_singleton] at he
      subst he
      change q.1.1 = some σ at hσ
      have hA : Agrees (SourceReplay.answers (lazyOf q.2)) (lazyOf q.2) :=
        fun input answer hk => SourceReplay.answers_known _ input answer hk
      have heval := hres.eval _ hA
      rw [S.eval_authenticatedRecord pay] at heval
      by_cases hc : request.cache = published
      · rw [if_pos hc] at heval
        have hreq : request = ⟨request.message, published⟩ := by cases request; simp_all
        have hcached : (lazyOf q.2).1 (.inr (.inl request.message)) ≠ none := by
          have := S.sign_published_nonce pay published request.message (lazyOf st.2) (q.1, lazyOf q.2)
            (by rw [← hreq]; exact hlazy)
          exact this
        refine ⟨hc, hcached, ?_⟩
        have hsig : (evalWithAnswerFn (SourceReplay.answers (lazyOf q.2)) (S.recordForNonce pay published
            (evalWithAnswerFn (SourceReplay.answers (lazyOf q.2)) (privateNonce request.message))
            request.message)).1 = some σ := by rw [heval]; exact hσ
        have hrho' := S.eval_recordForNonce_rho pay sigRho hrho _ published _ request.message σ hsig
        rw [hrho', CaseC.eval_privateNonce _ (lazyOf q.2) hA request.message hcached]
      · rw [if_neg hc] at heval
        rw [← heval] at hσ
        cases hσ
theorem bankInv_step (hhash : PayHashOnly pay) (hrho : PayRho pay sigRho) (hAvoids : PayAvoids pay)
    (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (input : (Interaction' Sig).Domain) (st : BankState Sig) (hinv : S.BankInv pay sigRho published budget kg st)
    (r : (Interaction' Sig).Range input × BankState Sig)
    (hr : r ∈ ((S.bankImpl pay published budget input).run st).support) :
    S.BankInv pay sigRho published budget kg r.2 := by
  cases input with
  | inl input => exact S.bankInv_world pay sigRho published budget kg input st hinv r hr
  | inr request => exact S.bankInv_sign pay sigRho hhash hrho hAvoids published budget kg request st hinv r hr
theorem bankInv_run {α : Type} (hhash : PayHashOnly pay) (hrho : PayRho pay sigRho) (hAvoids : PayAvoids pay)
    (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (program : OracleComp (Interaction' Sig) α) (st : BankState Sig)
    (hinv : S.BankInv pay sigRho published budget kg st)
    (r : α × BankState Sig) (hr : r ∈ ((simulateQ (S.bankImpl pay published budget) program).run st).support) :
    S.BankInv pay sigRho published budget kg r.2 := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure] at hr
      change r ∈ (PMF.pure (value, st)).support at hr
      rw [PMF.support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact hinv
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hr
      change r ∈ (PMF.bind _ _).support at hr
      rw [PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      exact ih middle.1 middle.2
        (S.bankInv_step pay sigRho hhash hrho hAvoids published budget kg input st hinv middle hm) hr
theorem bankInv_initial (published : T3.Cache) (budget : Nat)
    (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    S.BankInv pay sigRho published budget generated.2.events ((Ghost.empty : Ghost Sig), generated.2) := by
  have hl := CaseC.recorded_lazy_support keygen QueryRecorded.initial generated hg
  constructor
  · simp [Ghost.empty]
  · simp [Ghost.empty]
  · intro e he
    exact Or.inl he
  · intro _ m hm
    exfalso
    apply hm
    exact NonceFreshness.keygen_nonce_fresh m (generated.1, lazyOf generated.2) hl
  · intro entry he
    simp [Ghost.empty] at he
theorem bankInv_experiment (hhash : PayHashOnly pay) (hrho : PayRho pay sigRho) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) (b : Bool × BankState Sig)
    (hb : b ∈ (S.bankExperiment pay rest budget).support) :
    ∃ generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial),
      S.BankInv pay sigRho generated.1.2 budget generated.2.events b.2 := by
  unfold bankExperiment at hb
  change b ∈ (PMF.bind _ _).support at hb
  rw [PMF.mem_support_bind_iff] at hb
  obtain ⟨generated, hg, hb⟩ := hb
  rw [MonitoredPrivate.pmf_support] at hg
  exact ⟨generated, hg, S.bankInv_run pay sigRho hhash hrho hAvoids generated.1.2 budget generated.2.events _
    (Ghost.empty, generated.2) (S.bankInv_initial pay sigRho generated.1.2 budget generated hg) b hb⟩
theorem BankInv.alive {published : T3.Cache} {budget : Nat} {kg : List FirstHit.QueryEvent} {st : BankState Sig}
    (hinv : S.BankInv pay sigRho published budget kg st) (hlog : st.1.log.length ≤ S.horizon) :
    st.1.dead = false := by
  cases hd : st.1.dead
  · rfl
  · have := hinv.dead hd
    omega
theorem BankInv.logged_exposed {published : T3.Cache} {budget : Nat} {kg : List FirstHit.QueryEvent}
    {st : BankState Sig} (hinv : S.BankInv pay sigRho published budget kg st) (halive : st.1.dead = false)
    (entry : (_ : Request) × Option Sig) (he : entry ∈ st.1.log) (σ : Sig) (hσ : entry.2 = some σ)
    (A : Correctness.Answers) (hA : Agrees A (lazyOf st.2)) (c : BitVec 32) (out : HashOutput)
    (hs : evalWithAnswerFn A (S.search (sigRho σ) entry.1.message 0 attemptLimit) = some (c, out)) :
    out ∈ st.1.exposures := by
  obtain ⟨-, hcached, hrho⟩ := hinv.logged entry he σ hσ
  rw [hrho] at hs
  exact hinv.exposed halive entry.1.message hcached A hA c out hs
end FtsBankSpec
end ClaudeWCT.Bank
end
-- ==== merged from ClaudeWCT_Bank_GameInvL ====
section

namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open CaseC (Agrees Birth FreshSigning countOf lazyOf IsDigestInput eventPublic nonceOf)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankInvL : DecidableEq T3.Cache := Classical.decEq _
namespace FtsBankSpecL
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P)
variable {Sig : Type} (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (sigRho : Sig → Digest)
theorem eval_recordForNonce_selected (A : Correctness.Answers) (cache : T3.Cache) (rho : Digest) (m : Message) :
    (evalWithAnswerFn A (S.recordForNonce pay cache rho m)).2 =
      (evalWithAnswerFn A (S.search rho m 0 S.limit)).map Prod.snd := by
  unfold recordForNonce
  simp only [evalWithAnswerFn_bind]
  cases evalWithAnswerFn A (S.search rho m 0 S.limit) with
  | none => simp
  | some found =>
      rcases found with ⟨c, out⟩
      simp
theorem eval_recordForNonce_rho (hrho : PayRho pay sigRho) (A : Correctness.Answers) (cache : T3.Cache)
    (rho : Digest) (m : Message) (σ : Sig) (h : (evalWithAnswerFn A (S.recordForNonce pay cache rho m)).1 = some σ) :
    sigRho σ = rho := by
  unfold recordForNonce at h
  simp only [evalWithAnswerFn_bind] at h
  cases hd : evalWithAnswerFn A (S.search rho m 0 S.limit) with
  | none => simp [hd] at h
  | some found =>
      rcases found with ⟨c, out⟩
      simp only [hd, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at h
      exact hrho A cache rho out σ h
theorem eval_authenticatedRecord (A : Correctness.Answers) (published : T3.Cache) (request : Request) :
    evalWithAnswerFn A (S.authenticatedRecord pay published request) =
      if request.cache = published then
        evalWithAnswerFn A (S.recordForNonce pay published (evalWithAnswerFn A (privateNonce request.message))
          request.message)
      else (none, none) := by
  unfold authenticatedRecord
  simp only [evalWithAnswerFn_bind]
  by_cases hc : request.cache = published
  · rw [if_pos hc, if_pos hc]
    unfold payloadRecord
    rw [evalWithAnswerFn_bind, hc]
  · rw [if_neg hc, if_neg hc]
    rfl
theorem eval_source_sign (A : Correctness.Answers) (published : T3.Cache) (request : Request) :
    evalWithAnswerFn A (S.source pay published (.inr request)) =
      (evalWithAnswerFn A (S.authenticatedRecord pay published request)).1 := by
  change evalWithAnswerFn A (Prod.fst <$> S.authenticatedRecord pay published request) = _
  rw [SigGolfCandidate.T3M.eval_map]
theorem queried_record_sign (A : Correctness.Answers) (published : T3.Cache) (request : Request) :
    SourceReplay.queried A (S.authenticatedRecord pay published request) =
      queried A (S.source pay published (.inr request)) := by
  change _ = queried A (Prod.fst <$> S.authenticatedRecord pay published request)
  rw [SigGolfCandidate.T3M.Extract.queried_map]
  rfl
theorem authenticatedRecord_hashOnly (hhash : PayHashOnly pay) (published : T3.Cache) (request : Request) :
    Security.SourceReplay.HashOnly (S.authenticatedRecord pay published request) := by
  unfold authenticatedRecord
  apply SourceQueries.bind_allowed
  · exact SourceQueries.privateMac_allowed Security.SourceReplay.IsHash (fun _ => trivial) _
  · intro tag
    split
    · unfold payloadRecord recordForNonce
      apply SourceQueries.bind_allowed
      · exact SourceQueries.privateNonce_allowed Security.SourceReplay.IsHash (fun _ => trivial) _
      · intro rho
        apply SourceQueries.bind_allowed _
          (S.search_allowed rho request.message _ (fun _ _ => trivial) S.limit 0 (by simpa using S.limit_le))
        intro found
        split
        · exact SourceQueries.pure_allowed _ _
        · exact SourceQueries.bind_allowed _ (hhash _ _ _) fun _ => SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
def SignerQueried (published : T3.Cache) (log : QueryLog (Requests' Sig)) (lazy : LazyPrivate.State)
    (x : HashInput) : Prop :=
  ∃ entry ∈ log, ∀ A, Agrees A lazy →
    (.inl (.inr x) : T3.Spec.Domain) ∈ queried A (S.source pay published (.inr entry.1))
structure BankInv (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent) (st : BankState Sig) :
    Prop where
  len : st.1.exposures.length ≤ st.1.log.length
  dead : st.1.dead = true → S.horizon < st.1.log.length
  events : ∀ e ∈ st.2.events, e ∈ kg ∨ ∀ x a, eventPublic e = some (x, a) → IsDigestInput x →
    e.before.2 x = none → a ∈ st.1.targets ∨ budget < countOf st.2 ∨ S.SignerQueried pay published st.1.log (lazyOf st.2) x
  exposed : st.1.dead = false → ∀ m, (lazyOf st.2).1 (.inr (.inl m)) ≠ none → ∀ A, Agrees A (lazyOf st.2) →
    ∀ c out, evalWithAnswerFn A (S.search (nonceOf (lazyOf st.2) m) m 0 S.limit) = some (c, out) →
      out ∈ st.1.exposures
  logged : ∀ entry ∈ st.1.log, ∀ σ, entry.2 = some σ → entry.1.cache = published ∧
    (lazyOf st.2).1 (.inr (.inl entry.1.message)) ≠ none ∧ sigRho σ = nonceOf (lazyOf st.2) entry.1.message
theorem bank_support_world (published : T3.Cache) (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain)
    (st : BankState Sig) (r : SphincsSecurity.OracleWorld.Range input × BankState Sig)
    (hr : r ∈ ((S.bankImpl pay published budget (.inl input)).run st).support) :
    ∃ q ∈ support (QueryRecorded.run (forwardWorld input) st.2),
      r = (q.1, (ghostWorld budget input st.1 st.2 q.1, q.2)) := by
  change r ∈ (PMF.map _ (liftM (QueryRecorded.run (forwardWorld input) st.2))).support at hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  refine ⟨q, ?_, rfl⟩
  rw [MonitoredPrivate.pmf_support] at hq
  exact hq
theorem bank_support_sign (published : T3.Cache) (budget : Nat) (request : Request)
    (st : BankState Sig) (r : Option Sig × BankState Sig)
    (hr : r ∈ ((S.bankImpl pay published budget (.inr request)).run st).support) :
    ∃ q ∈ support (QueryRecorded.run (S.authenticatedRecord pay published request) st.2),
      r = (q.1.1, (S.ghostSign published request st.1 st.2 (q.1, lazyOf q.2), q.2)) := by
  change r ∈ (PMF.map _ (liftM (QueryRecorded.run (S.authenticatedRecord pay published request) st.2))).support
    at hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  refine ⟨q, ?_, rfl⟩
  rw [MonitoredPrivate.pmf_support] at hq
  exact hq
theorem bankInv_world (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (input : SphincsSecurity.OracleWorld.Domain) (st : BankState Sig) (hinv : S.BankInv pay sigRho published budget kg st)
    (r : SphincsSecurity.OracleWorld.Range input × BankState Sig)
    (hr : r ∈ ((S.bankImpl pay published budget (.inl input)).run st).support) :
    S.BankInv pay sigRho published budget kg r.2 := by
  obtain ⟨q, hq, rfl⟩ := S.bank_support_world pay published budget input st r hr
  obtain ⟨hev, hcount, hlazy⟩ := CaseC.world_query_support input st.2 q hq
  have hext : SourceReplay.Extends (lazyOf st.2) (lazyOf q.2) :=
    SourceReplay.run_extends _ (lazyOf st.2) (q.1, lazyOf q.2) hlazy
  have hpriv : (lazyOf q.2).1 = (lazyOf st.2).1 :=
    CaseC.world_private_eq input (lazyOf st.2) (q.1, lazyOf q.2) hlazy
  obtain ⟨hX, hL, hD, hR, hT⟩ := FtsBankSpec.ghostWorld_fields budget input st.1 st.2 q.1
  have hcle : countOf st.2 ≤ countOf q.2 := by rw [hcount]; exact Nat.le_add_right _ _
  constructor
  · simp only [hX, hL]; exact hinv.len
  · simp only [hD, hL]; exact hinv.dead
  · intro e he
    rw [hev, List.mem_append] at he
    rcases he with he | he
    · rcases hinv.events e he with hk | hp
      · exact Or.inl hk
      · right
        intro x a hxa hdig hfresh
        rcases hp x a hxa hdig hfresh with ht | hb | hs
        · exact Or.inl (hT _ ht)
        · exact Or.inr (Or.inl (lt_of_lt_of_le hb hcle))
        · right; right
          obtain ⟨entry, hentry, hq'⟩ := hs
          exact ⟨entry, by rw [hL]; exact hentry, fun A hA => hq' A (hA.mono hext)⟩
    · rw [List.mem_singleton] at he
      subst he
      right
      intro x a hxa hdig hfresh
      cases input with
      | inl n => simp [eventPublic] at hxa
      | inr y =>
          simp only [eventPublic, Option.some.injEq, Prod.mk.injEq] at hxa
          obtain ⟨hy, ha⟩ := hxa
          subst hy
          by_cases hlt : countOf st.2 < budget
          · left
            have hbirth : Birth budget y st.2 := ⟨hdig, hfresh, hlt⟩
            simp only [ghostWorld, hbirth, if_true]
            rw [← ha]
            exact List.mem_append_right _ (List.mem_singleton_self _)
          · right; left
            rw [hcount]
            change budget < countOf st.2 + 1
            omega
  · intro hdead m hm A hA c out hs
    rw [hD] at hdead
    have hm0 : (lazyOf st.2).1 (.inr (.inl m)) ≠ none := by rwa [← hpriv]
    have hn : nonceOf (lazyOf q.2) m = nonceOf (lazyOf st.2) m := by simp [nonceOf, hpriv]
    rw [hn] at hs
    rw [hX]
    exact hinv.exposed hdead m hm0 A (hA.mono hext) c out hs
  · intro entry he σ hσ
    rw [hL] at he
    obtain ⟨h1, h2, h3⟩ := hinv.logged entry he σ hσ
    refine ⟨h1, by rwa [hpriv], ?_⟩
    rw [h3]
    simp [nonceOf, hpriv]
theorem bankInv_sign (hhash : PayHashOnly pay) (hrho : PayRho pay sigRho) (hAvoids : PayAvoids pay)
    (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (request : Request) (st : BankState Sig) (hinv : S.BankInv pay sigRho published budget kg st)
    (r : Option Sig × BankState Sig)
    (hr : r ∈ ((S.bankImpl pay published budget (.inr request)).run st).support) :
    S.BankInv pay sigRho published budget kg r.2 := by
  obtain ⟨q, hq, rfl⟩ := S.bank_support_sign pay published budget request st r hr
  obtain ⟨rec, hrec, hev, hstate, hvalue⟩ := CaseC.recorded_new_events _ st.2 q hq
  have hlazy := CaseC.recorded_lazy_support _ st.2 q hq
  have hext : SourceReplay.Extends (lazyOf st.2) (lazyOf q.2) :=
    SourceReplay.run_extends _ (lazyOf st.2) (q.1, lazyOf q.2) hlazy
  have hres : SourceReplay.Resolves (lazyOf q.2) (S.authenticatedRecord pay published request) q.1 :=
    SourceReplay.resolves_of_run _ (S.authenticatedRecord_hashOnly pay hhash published request) _ _ hlazy
  have hcle := CaseC.recorded_count_le _ st.2 q hq
  have hlog := S.ghostSign_log published request st.1 st.2 (q.1, lazyOf q.2)
  have htar := S.ghostSign_targets published request st.1 st.2 (q.1, lazyOf q.2)
  have h1 := S.ghostSign_exposures_len published request st.1 st.2 (q.1, lazyOf q.2)
  set g' := S.ghostSign published request st.1 st.2 (q.1, lazyOf q.2) with hg'
  show S.BankInv pay sigRho published budget kg (g', q.2)
  constructor
  ·
    show g'.exposures.length ≤ g'.log.length
    rw [hlog, List.length_append, List.length_singleton]
    have := hinv.len
    omega
  ·
    intro hd
    rw [hlog, List.length_append, List.length_singleton]
    by_cases hf : FreshSigning published request st.2
    · by_cases hh : S.horizon ≤ st.1.exposures.length
      · have := hinv.len
        omega
      · have hd0 : st.1.dead = true := by
          simpa [hg', FtsBankSpec.ghostSign, hf, hh] using hd
        have := hinv.dead hd0
        omega
    · have hd0 : st.1.dead = true := by
        simpa [hg', FtsBankSpec.ghostSign, hf] using hd
      have := hinv.dead hd0
      omega
  ·
    intro e he
    rw [hev, List.mem_append] at he
    rcases he with he | he
    · rcases hinv.events e he with hk | hp
      · exact Or.inl hk
      · right
        intro x a hxa hdig hfresh
        rcases hp x a hxa hdig hfresh with ht | hb | hs
        · left; rw [htar]; exact ht
        · exact Or.inr (Or.inl (lt_of_lt_of_le hb hcle))
        · right; right
          obtain ⟨entry, hentry, hq'⟩ := hs
          exact ⟨entry, by rw [hlog]; exact List.mem_append_left _ hentry, fun A hA => hq' A (hA.mono hext)⟩
    · right
      intro x a hxa _ _
      right; right
      refine ⟨⟨request, q.1.1⟩, by rw [hlog]; exact List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      intro A hA
      have hinputs := FirstHit.recorded_inputs _ (S.authenticatedRecord_hashOnly pay hhash published request)
        (lazyOf st.2) rec hrec A (by rw [hstate]; exact hA)
      have hmem : e.input ∈ rec.events.map FirstHit.QueryEvent.input := List.mem_map_of_mem he
      rw [hinputs, S.queried_record_sign pay] at hmem
      have hin : e.input = .inl (.inr x) := by
        rcases e with ⟨before, input, answer⟩
        rcases input with (n | y) | coordinate
        · simp [eventPublic] at hxa
        · simp only [eventPublic, Option.some.injEq, Prod.mk.injEq] at hxa
          rw [hxa.1]
        · simp [eventPublic] at hxa
      rw [hin] at hmem
      exact hmem
  ·
    intro hdead m hm A hA c out hs
    by_cases hf : FreshSigning published request st.2
    · by_cases hh : S.horizon ≤ st.1.exposures.length
      · simp [hg', FtsBankSpec.ghostSign, hf, hh] at hdead
      · have hdead0 : st.1.dead = false := by simpa [hg', FtsBankSpec.ghostSign, hf, hh] using hdead
        have hX : g'.exposures = st.1.exposures ++ q.1.2.toList := by simp [hg', FtsBankSpec.ghostSign, hf, hh]
        rw [hX]
        by_cases hmm : m = request.message
        · subst hmm
          obtain ⟨hcache, hnonce⟩ := hf
          have heval := hres.eval A hA
          rw [S.eval_authenticatedRecord pay, if_pos hcache,
            CaseC.eval_privateNonce A (lazyOf q.2) hA request.message hm] at heval
          have hsel := S.eval_recordForNonce_selected pay A published (nonceOf (lazyOf q.2) request.message)
            request.message
          rw [heval, hs] at hsel
          apply List.mem_append_right
          rw [hsel]
          simp
        · have hn := S.sign_other_nonce pay hAvoids published request (lazyOf st.2) (q.1, lazyOf q.2) hlazy m hmm
          have hm0 : (lazyOf st.2).1 (.inr (.inl m)) ≠ none := by rwa [← hn]
          obtain ⟨hno, _⟩ := CaseC.nonceOf_extends hext m hm0
          rw [hno] at hs
          exact List.mem_append_left _ (hinv.exposed hdead0 m hm0 A (hA.mono hext) c out hs)
    · have hdead0 : st.1.dead = false := by simpa [hg', FtsBankSpec.ghostSign, hf] using hdead
      have hX : g'.exposures = st.1.exposures := by simp [hg', FtsBankSpec.ghostSign, hf]
      rw [hX]
      have hm0 : (lazyOf st.2).1 (.inr (.inl m)) ≠ none := by
        by_cases hmm : m = request.message
        · subst hmm
          by_cases hc : request.cache = published
          · intro hnone
            exact hf ⟨hc, hnone⟩
          · have := (S.sign_unpublished pay published request hc (lazyOf st.2) (q.1, lazyOf q.2) hlazy).1
            rwa [← this]
        · have hn := S.sign_other_nonce pay hAvoids published request (lazyOf st.2) (q.1, lazyOf q.2) hlazy m hmm
          rwa [← hn]
      obtain ⟨hno, _⟩ := CaseC.nonceOf_extends hext m hm0
      rw [hno] at hs
      exact hinv.exposed hdead0 m hm0 A (hA.mono hext) c out hs
  ·
    intro entry he σ hσ
    rw [hlog, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨h1, h2, h3⟩ := hinv.logged entry he σ hσ
      obtain ⟨hno, hc'⟩ := CaseC.nonceOf_extends hext entry.1.message h2
      exact ⟨h1, hc', by rw [hno]; exact h3⟩
    · rw [List.mem_singleton] at he
      subst he
      change q.1.1 = some σ at hσ
      have hA : Agrees (SourceReplay.answers (lazyOf q.2)) (lazyOf q.2) :=
        fun input answer hk => SourceReplay.answers_known _ input answer hk
      have heval := hres.eval _ hA
      rw [S.eval_authenticatedRecord pay] at heval
      by_cases hc : request.cache = published
      · rw [if_pos hc] at heval
        have hreq : request = ⟨request.message, published⟩ := by cases request; simp_all
        have hcached : (lazyOf q.2).1 (.inr (.inl request.message)) ≠ none := by
          have := S.sign_published_nonce pay published request.message (lazyOf st.2) (q.1, lazyOf q.2)
            (by rw [← hreq]; exact hlazy)
          exact this
        refine ⟨hc, hcached, ?_⟩
        have hsig : (evalWithAnswerFn (SourceReplay.answers (lazyOf q.2)) (S.recordForNonce pay published
            (evalWithAnswerFn (SourceReplay.answers (lazyOf q.2)) (privateNonce request.message))
            request.message)).1 = some σ := by rw [heval]; exact hσ
        have hrho' := S.eval_recordForNonce_rho pay sigRho hrho _ published _ request.message σ hsig
        rw [hrho', CaseC.eval_privateNonce _ (lazyOf q.2) hA request.message hcached]
      · rw [if_neg hc] at heval
        rw [← heval] at hσ
        cases hσ
theorem bankInv_step (hhash : PayHashOnly pay) (hrho : PayRho pay sigRho) (hAvoids : PayAvoids pay)
    (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (input : (Interaction' Sig).Domain) (st : BankState Sig) (hinv : S.BankInv pay sigRho published budget kg st)
    (r : (Interaction' Sig).Range input × BankState Sig)
    (hr : r ∈ ((S.bankImpl pay published budget input).run st).support) :
    S.BankInv pay sigRho published budget kg r.2 := by
  cases input with
  | inl input => exact S.bankInv_world pay sigRho published budget kg input st hinv r hr
  | inr request => exact S.bankInv_sign pay sigRho hhash hrho hAvoids published budget kg request st hinv r hr
theorem bankInv_run {α : Type} (hhash : PayHashOnly pay) (hrho : PayRho pay sigRho) (hAvoids : PayAvoids pay)
    (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (program : OracleComp (Interaction' Sig) α) (st : BankState Sig)
    (hinv : S.BankInv pay sigRho published budget kg st)
    (r : α × BankState Sig) (hr : r ∈ ((simulateQ (S.bankImpl pay published budget) program).run st).support) :
    S.BankInv pay sigRho published budget kg r.2 := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure] at hr
      change r ∈ (PMF.pure (value, st)).support at hr
      rw [PMF.support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact hinv
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hr
      change r ∈ (PMF.bind _ _).support at hr
      rw [PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      exact ih middle.1 middle.2
        (S.bankInv_step pay sigRho hhash hrho hAvoids published budget kg input st hinv middle hm) hr
theorem bankInv_initial (published : T3.Cache) (budget : Nat)
    (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    S.BankInv pay sigRho published budget generated.2.events ((Ghost.empty : Ghost Sig), generated.2) := by
  have hl := CaseC.recorded_lazy_support keygen QueryRecorded.initial generated hg
  constructor
  · simp [Ghost.empty]
  · simp [Ghost.empty]
  · intro e he
    exact Or.inl he
  · intro _ m hm
    exfalso
    apply hm
    exact NonceFreshness.keygen_nonce_fresh m (generated.1, lazyOf generated.2) hl
  · intro entry he
    simp [Ghost.empty] at he
theorem bankInv_experiment (hhash : PayHashOnly pay) (hrho : PayRho pay sigRho) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) (b : Bool × BankState Sig)
    (hb : b ∈ (S.bankExperiment pay rest budget).support) :
    ∃ generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial),
      S.BankInv pay sigRho generated.1.2 budget generated.2.events b.2 := by
  unfold bankExperiment at hb
  change b ∈ (PMF.bind _ _).support at hb
  rw [PMF.mem_support_bind_iff] at hb
  obtain ⟨generated, hg, hb⟩ := hb
  rw [MonitoredPrivate.pmf_support] at hg
  exact ⟨generated, hg, S.bankInv_run pay sigRho hhash hrho hAvoids generated.1.2 budget generated.2.events _
    (Ghost.empty, generated.2) (S.bankInv_initial pay sigRho generated.1.2 budget generated hg) b hb⟩
theorem BankInv.alive {published : T3.Cache} {budget : Nat} {kg : List FirstHit.QueryEvent} {st : BankState Sig}
    (hinv : S.BankInv pay sigRho published budget kg st) (hlog : st.1.log.length ≤ S.horizon) :
    st.1.dead = false := by
  cases hd : st.1.dead
  · rfl
  · have := hinv.dead hd
    omega
theorem BankInv.logged_exposed {published : T3.Cache} {budget : Nat} {kg : List FirstHit.QueryEvent}
    {st : BankState Sig} (hinv : S.BankInv pay sigRho published budget kg st) (halive : st.1.dead = false)
    (entry : (_ : Request) × Option Sig) (he : entry ∈ st.1.log) (σ : Sig) (hσ : entry.2 = some σ)
    (A : Correctness.Answers) (hA : Agrees A (lazyOf st.2)) (c : BitVec 32) (out : HashOutput)
    (hs : evalWithAnswerFn A (S.search (sigRho σ) entry.1.message 0 S.limit) = some (c, out)) :
    out ∈ st.1.exposures := by
  obtain ⟨-, hcached, hrho⟩ := hinv.logged entry he σ hσ
  rw [hrho] at hs
  exact hinv.exposed halive entry.1.message hcached A hA c out hs
end FtsBankSpecL
end ClaudeWCT.Bank
end
-- ==== merged from ClaudeWCT_WCT9_TopDecode ====
section

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
theorem producerDecode_decode {lay : Layer} {answer : Digest} {digits : List Nat}
    (h : producerDecode lay answer = some digits) : decode lay answer = some digits := by
  unfold producerDecode at h
  cases hd : decode lay answer with
  | none => simp [hd] at h
  | some ds =>
      simp only [hd] at h
      split_ifs at h
      cases h
      rfl
theorem producerDecode_credit {lay : Layer} {answer : Digest} {digits : List Nat}
    (h : producerDecode lay answer = some digits) : producerFloor lay + dispatchPenalty lay digits ≤ wordCredit lay digits + 4 * savedCopies lay digits := by
  unfold producerDecode at h
  cases hd : decode lay answer with
  | none => simp [hd] at h
  | some ds =>
      simp only [hd] at h
      split_ifs at h with hc
      cases h
      exact hc.1
theorem producerDecode_zeroBound {lay : Layer} {answer : Digest} {digits : List Nat}
    (h : producerDecode lay answer = some digits) : producerZeroBound lay digits := by
  unfold producerDecode at h
  cases hd : decode lay answer with
  | none => simp [hd] at h
  | some ds =>
      simp only [hd] at h
      split_ifs at h with hc
      cases h
      exact hc.2.1
theorem producerDecode_rankBound {lay : Layer} {answer : Digest} {digits : List Nat}
    (h : producerDecode lay answer = some digits) : producerRankBound lay answer := by
  unfold producerDecode at h
  cases hd : decode lay answer with
  | none => simp [hd] at h
  | some ds =>
      simp only [hd] at h
      split_ifs at h with hc
      cases h
      exact hc.2.2
theorem producerDecode_lowerRankGood {lay : Layer} (hlay : lay ≠ 0)
    {answer : Digest} {digits : List Nat} (h : producerDecode lay answer = some digits) :
    lowerRankGood answer := (producerDecode_rankBound h).resolve_left hlay
theorem lowerFirstBad_le (answer : Digest) : lowerFirstBad answer ≤ 14 := by
  unfold lowerFirstBad
  cases h : (List.range 14).find? (fun i => decide
      (lowerWord answer / 2 ^ (9 * i) % 512 < producerRankFloor i)) with
  | none => simp
  | some i =>
      have hi := List.mem_of_find?_eq_some h
      simp only [List.mem_range] at hi
      simp only [Option.getD_some]
      omega
theorem lowerFirstBad_find (answer : Digest) (h : ¬lowerRankGood answer) :
    (List.range 14).find? (fun i => decide
      (lowerWord answer / 2 ^ (9 * i) % 512 < producerRankFloor i)) = some (lowerFirstBad answer) := by
  unfold lowerFirstBad
  cases he : (List.range 14).find? (fun i => decide
      (lowerWord answer / 2 ^ (9 * i) % 512 < producerRankFloor i)) with
  | some i => rfl
  | none =>
      exfalso
      apply h
      intro i
      have hi := List.find?_eq_none.mp he i.val (List.mem_range.mpr i.isLt)
      simp only [decide_eq_true_eq, not_lt] at hi
      exact hi
theorem lowerFirstBad_lt (answer : Digest) (h : ¬lowerRankGood answer) : lowerFirstBad answer < 14 := by
  exact List.mem_range.mp (List.mem_of_find?_eq_some (lowerFirstBad_find answer h))
theorem lowerFirstBad_bad (answer : Digest) (h : ¬lowerRankGood answer) :
    lowerWord answer / 2 ^ (9 * lowerFirstBad answer) % 512 < producerRankFloor (lowerFirstBad answer) := by
  have hb := List.find?_some (lowerFirstBad_find answer h)
  exact of_decide_eq_true hb
theorem lowerFirstBad_before (answer : Digest) (h : ¬lowerRankGood answer) (i : Nat)
    (hi : i < lowerFirstBad answer) : producerRankFloor i ≤ lowerWord answer / 2 ^ (9 * i) % 512 := by
  obtain ⟨_, j, hj, hjeq, hbefore⟩ := List.find?_eq_some_iff_getElem.mp (lowerFirstBad_find answer h)
  simp only [List.getElem_range] at hjeq
  subst j
  have hb := hbefore i hi
  simpa only [List.getElem_range, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] using hb
theorem lowerGuardedRun_of_good {α : Type} (run : Nat → M Digest) (finish : M α) (answer : Digest)
    (h : lowerRankGood answer) : lowerGuardedRun run finish answer = some <$> finish := by
  simp only [lowerGuardedRun, if_pos h]
theorem recoverLayerPairGuard_of_good (sig : Signature) (index : Nat) (lay : Layer) (answer : Digest)
    (digits : List Nat) (h : lowerRankGood answer) :
    recoverLayerPairGuard sig index lay answer digits = some <$> recoverLayerPair sig index lay digits :=
  lowerGuardedRun_of_good _ _ _ h
/-- Only producer-selected lower words, not all broad-decoder words, satisfy the B4 cap. -/
theorem lower_zero_count_le_producer {lay : Layer} (hlay : lay ≠ 0)
    {value : Digest} {digits : List Nat} (h : producerDecode lay value = some digits) :
    (digits.filter (· = 0)).length ≤ 5 :=
  (producerDecode_zeroBound h).resolve_left hlay
theorem producerDecode_of {lay : Layer} {answer : Digest} {digits : List Nat}
    (hd : decode lay answer = some digits) (hc : producerFloor lay + dispatchPenalty lay digits ≤ wordCredit lay digits + 4 * savedCopies lay digits)
    (hz : producerZeroBound lay digits) (hr : producerRankBound lay answer) : producerDecode lay answer = some digits := by
  unfold producerDecode
  simp only [hd, hc, hz, hr, and_self, ↓reduceIte]
theorem producerDecode_eq_some_iff (lay : Layer) (answer : Digest) (digits : List Nat) :
    producerDecode lay answer = some digits ↔
      decode lay answer = some digits ∧ producerFloor lay + dispatchPenalty lay digits ≤ wordCredit lay digits + 4 * savedCopies lay digits ∧ producerZeroBound lay digits ∧ producerRankBound lay answer :=
  ⟨fun h => ⟨producerDecode_decode h, producerDecode_credit h, producerDecode_zeroBound h, producerDecode_rankBound h⟩,
    fun h => producerDecode_of h.1 h.2.1 h.2.2.1 h.2.2.2⟩
theorem producerDecode_eq_none_or (lay : Layer) (answer : Digest) :
    producerDecode lay answer = none ∨ producerDecode lay answer = decode lay answer := by
  unfold producerDecode
  cases decode lay answer with
  | none => exact Or.inl rfl
  | some ds =>
      simp only
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
theorem producerFloor_values :
    producerFloor 0 = 21 ∧ producerFloor 1 = 10 ∧ producerFloor 2 = 9 ∧ producerFloor 3 = 9 :=
  ⟨rfl, rfl, rfl, rfl⟩
theorem searchLimit_top : searchLimit 0 = topSearchLimit := rfl
/-- Every lower window is at least `lowerSearchLimit` (L3 is 3·2^20). -/
theorem searchLimit_lower {lay : Layer} (h : lay ≠ 0) : lowerSearchLimit ≤ searchLimit lay := by
  unfold searchLimit lowerSearchLimit
  fin_cases lay <;> simp_all
theorem searchLimit_le (lay : Layer) : searchLimit lay ≤ counterLimit := by
  unfold searchLimit counterLimit
  fin_cases lay <;> simp
theorem searchLimit_values : searchLimit 0 = 2 ^ 20 ∧ searchLimit 1 = 2 ^ 21 ∧ searchLimit 2 = 2 ^ 21 ∧
    searchLimit 3 = 3 * 2 ^ 20 := by decide
theorem lowerSearchLimit_eq : lowerSearchLimit = 2 ^ 21 := rfl
theorem chainCount_top : chainCount 0 = 51 := rfl
theorem dataDigits_top_length (answer : Digest) : (dataDigits 0 answer).length = 50 := by
  simp [dataDigits, dataCount]
/-- Campaign T51: a decoded top word has valid fields (9 r6 ranks < 216, 7 r5 ranks < 125, the r7 rank < 49), its
checksum digit `target 0 - sum` lies in `[0, 5]`, and the digits are the 50 data digits followed by the checksum. -/
theorem decode_top_some {answer : Digest} {digits : List Nat} (h : decode 0 answer = some digits) :
    answer.toNat < 2 ^ encodedBits 0 ∧ topRanksValid answer = true ∧
      ((dataDigits 0 answer).sum ≤ target 0 ∧ target 0 - (dataDigits 0 answer).sum < 6) ∧
      digits = dataDigits 0 answer ++ [target 0 - (dataDigits 0 answer).sum] := by
  unfold decode at h
  split at h
  · cases h
  · rename_i hg
    simp only [↓reduceIte] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨by omega, hc.1, hc.2, rfl⟩
    · cases h
theorem decode_top_of {answer : Digest} (hg : answer.toNat < 2 ^ encodedBits 0)
    (hr : topRanksValid answer = true) (hs : (dataDigits 0 answer).sum ≤ target 0)
    (hc : target 0 - (dataDigits 0 answer).sum < 6) :
    decode 0 answer = some (dataDigits 0 answer ++ [target 0 - (dataDigits 0 answer).sum]) := by
  unfold decode
  rw [if_neg (by omega)]
  simp only [↓reduceIte, hr, hs, hc, and_self]
theorem topGroupBad_eq_false_iff (answer : Digest) (i : Nat) :
    topGroupBad answer i = false ↔
      ¬(i % 3 = 0 ∧ i < 50 ∧ topGroupValid answer (i / 3) = false) ∧ ¬(i = 50 ∧ topChecksumOk answer = false) := by
  unfold topGroupBad
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
/-- Campaign T51: `topRanksValid` is exactly the per-group checks of the 50 data chains (r6 groups 0..8, r5 groups
9..15, the r7 pair at chain 48). -/
theorem topRanksValid_iff_good (answer : Digest) :
    topRanksValid answer = true ↔ ∀ i : Fin (chainCount 0), i.val < 50 → topGroupBad answer i.val = false := by
  unfold topRanksValid
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, List.mem_range'_1]
  constructor
  · rintro ⟨⟨h6, h5⟩, h7⟩
    refine fun i hi => (topGroupBad_eq_false_iff answer i.val).2 ⟨fun ⟨_, _, hv⟩ => ?_, fun ⟨he, _⟩ => by omega⟩
    unfold topGroupValid at hv
    split_ifs at hv with hg hg'
    · rw [h6 _ hg] at hv; cases hv
    · have h5' := h5 (i.val / 3) ⟨by omega, by omega⟩
      simp only [decide_eq_false_iff_not] at hv
      exact hv h5'
    · simp only [decide_eq_false_iff_not] at hv
      exact hv h7
  · intro h
    have hv : ∀ g, g < 17 → topGroupValid answer g = true := by
      intro g hg
      have hb := ((topGroupBad_eq_false_iff answer (3 * g)).1
        (h ⟨3 * g, by rw [chainCount_top]; omega⟩ (by simp only; omega))).1
      by_contra hc
      exact hb ⟨by omega, by omega, by rw [show 3 * g / 3 = g by omega]; simpa using hc⟩
    refine ⟨⟨fun g hg => ?_, fun q hq => ?_⟩, ?_⟩
    · simpa [topGroupValid, hg] using hv g (by omega)
    · have := hv q (by omega)
      simpa [topGroupValid, show ¬ q < 9 by omega, show q < 16 by omega] using this
    · simpa [topGroupValid] using hv 16 (by omega)
/-- Campaign T51: the top decoder accepts iff no check of the verifier's chain loop fires. -/
theorem decode_top_isSome_iff (answer : Digest) :
    (decode 0 answer).isSome = true ↔ ∀ i : Fin (chainCount 0), topGroupBad answer i.val = false := by
  have hlt : answer.toNat < 2 ^ encodedBits 0 := answer.isLt
  constructor
  · intro h
    obtain ⟨digits, hd⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨-, hr, ⟨hs, hc⟩, -⟩ := decode_top_some hd
    have hg := (topRanksValid_iff_good answer).1 hr
    intro i
    by_cases hi : i.val < 50
    · exact hg i hi
    · have hi50 : i.val = 50 := by have : i.val < 51 := i.isLt; omega
      rw [topGroupBad_eq_false_iff]
      refine ⟨fun ⟨_, h2, _⟩ => by omega, fun ⟨_, hk⟩ => ?_⟩
      unfold topChecksumOk at hk
      simp only [decide_eq_false_iff_not, not_and, not_lt] at hk
      have := hk hs
      omega
  · intro hg
    have hr : topRanksValid answer = true := (topRanksValid_iff_good answer).2 (fun i _ => hg i)
    have hk := ((topGroupBad_eq_false_iff answer 50).1 (hg ⟨50, by rw [chainCount_top]; omega⟩)).2
    have hk' : topChecksumOk answer = true := by
      by_contra hc
      exact hk ⟨rfl, by simpa using hc⟩
    unfold topChecksumOk at hk'
    simp only [decide_eq_true_eq] at hk'
    rw [decode_top_of hlt hr hk'.1 hk'.2]
    rfl
/-- Campaign T51: the digit the verifier runs on top chain `i` is the decoded digit `i` (checksum included). -/
theorem topRunDigit_of_decode {answer : Digest} {digits : List Nat} (h : decode 0 answer = some digits) (i : Nat)
    (hi : i < 51) : topRunDigit answer i = digits.getD i 0 := by
  obtain ⟨-, -, -, rfl⟩ := decode_top_some h
  have hl := dataDigits_top_length answer
  unfold topRunDigit
  split_ifs with h50
  · rw [List.getD_append _ _ _ _ (by omega)]
  · have : i = 50 := by omega
    subst this
    rw [List.getD_append_right _ _ _ _ (by omega), hl]
    rfl
section Loop
variable (run : Fin (chainCount 0) → Nat → M Digest) (answer : Digest)
theorem topDecodeStep_none (i : Fin (chainCount 0)) : topDecodeStep run answer none i = pure none := rfl
theorem topDecodeStep_bad (ends : List Digest) (i : Fin (chainCount 0)) (h : topGroupBad answer i.val = true) :
    topDecodeStep run answer (some ends) i = pure none := by
  simp only [topDecodeStep, h, ↓reduceIte]
theorem topDecodeStep_good (ends : List Digest) (i : Fin (chainCount 0)) (h : topGroupBad answer i.val = false) :
    topDecodeStep run answer (some ends) i =
      (fun value => some (ends ++ [value])) <$> run i (topRunDigit answer i.val) := by
  simp only [topDecodeStep, h, Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp]
  rfl
theorem foldlM_topDecodeStep_none :
    ∀ L : List (Fin (chainCount 0)), L.foldlM (topDecodeStep run answer) none = pure none
  | [] => rfl
  | i :: L => by
      rw [List.foldlM_cons, topDecodeStep_none, pure_bind, foldlM_topDecodeStep_none L]
theorem foldlM_topDecodeStep_good :
    ∀ (L : List (Fin (chainCount 0))) (acc : List Digest), (∀ i ∈ L, topGroupBad answer i.val = false) →
      L.foldlM (topDecodeStep run answer) (some acc) =
        (fun ends => some (acc ++ ends)) <$> L.mapM (fun i => run i (topRunDigit answer i.val))
  | [], acc, _ => by simp
  | i :: L, acc, h => by
      rw [List.foldlM_cons, List.mapM_cons, topDecodeStep_good run answer acc i (h i List.mem_cons_self),
        bind_map_left, map_bind]
      congr 1
      funext value
      rw [foldlM_topDecodeStep_good L (acc ++ [value]) (fun j hj => h j (List.mem_cons_of_mem _ hj)),
        map_eq_bind_pure_comp, map_eq_bind_pure_comp, bind_assoc]
      congr 1
      funext ends
      simp
theorem eval_foldlM_topDecodeStep_none (answers : QueryImpl Spec Id) (L : List (Fin (chainCount 0))) :
    evalWithAnswerFn answers (L.foldlM (topDecodeStep run answer) none) = none := by
  rw [foldlM_topDecodeStep_none, evalWithAnswerFn_pure]
theorem eval_foldlM_topDecodeStep_some (answers : QueryImpl Spec Id) :
    ∀ (L : List (Fin (chainCount 0))) (state : Option (List Digest)) (ends : List Digest),
      evalWithAnswerFn answers (L.foldlM (topDecodeStep run answer) state) = some ends →
        ∀ i ∈ L, topGroupBad answer i.val = false
  | [], _, _, _ => by simp
  | i :: L, state, ends, h => by
      rw [List.foldlM_cons, evalWithAnswerFn_bind] at h
      cases state with
      | none =>
          rw [topDecodeStep_none, evalWithAnswerFn_pure, eval_foldlM_topDecodeStep_none] at h
          cases h
      | some acc =>
          cases hb : topGroupBad answer i.val with
          | true =>
              rw [topDecodeStep_bad run answer acc i hb, evalWithAnswerFn_pure,
                eval_foldlM_topDecodeStep_none] at h
              cases h
          | false =>
              intro j hj
              rcases List.mem_cons.mp hj with rfl | hj
              · exact hb
              · exact eval_foldlM_topDecodeStep_some answers L _ ends h j hj
end Loop
theorem topDecodeRun_of_decode {run : Fin (chainCount 0) → Nat → M Digest} {finish : List Digest → M Digest}
    {answer : Digest} {digits : List Nat} (h : decode 0 answer = some digits) :
    topDecodeRun run finish answer =
      some <$> ((List.finRange (chainCount 0)).mapM (fun i => run i (digits.getD i.val 0)) >>= finish) := by
  have hsome : (decode 0 answer).isSome = true := by rw [h]; rfl
  have hgood := (decode_top_isSome_iff answer).1 hsome
  have hfun : (fun i : Fin (chainCount 0) => run i (topRunDigit answer i.val)) =
      fun i => run i (digits.getD i.val 0) := by
    funext i
    rw [topRunDigit_of_decode h i.val i.isLt]
  unfold topDecodeRun
  rw [if_neg (by have := answer.isLt; simp only [encodedBits]; omega),
    foldlM_topDecodeStep_good run answer _ [] (fun i _ => hgood i), bind_map_left, map_bind, hfun]
  simp only [List.nil_append]
/-- Chains run before a top rejection: those before the first failing check (T51: no spare bit). -/
def topRejectLength (answer : Digest) : Nat :=
  if answer.toNat ≥ 2 ^ encodedBits 0 then 0
  else (List.finRange (chainCount 0)).findIdx fun i => topGroupBad answer i.val
/-- The chains the verifier runs before it rejects a bad top word (T51: digits as `topDecodeStep` runs them). -/
def topRejectChains (run : Fin (chainCount 0) → Nat → M Digest) (answer : Digest) : M (List Digest) :=
  ((List.finRange (chainCount 0)).take (topRejectLength answer)).mapM
    fun i => run i (topRunDigit answer i.val)
theorem topDecodeRun_of_decode_none {run : Fin (chainCount 0) → Nat → M Digest}
    {finish : List Digest → M Digest} {answer : Digest} (h : decode 0 answer = none) :
    topDecodeRun run finish answer = (fun _ => none) <$> topRejectChains run answer := by
  unfold topDecodeRun topRejectChains topRejectLength
  by_cases hg : answer.toNat ≥ 2 ^ encodedBits 0
  · rw [if_pos hg, if_pos hg]
    simp
  rw [if_neg hg, if_neg hg]
  generalize hL : List.finRange (chainCount 0) = L
  generalize hk : L.findIdx (fun i => topGroupBad answer i.val) = k
  have hgood : ∀ i ∈ L.take k, topGroupBad answer i.val = false := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
    rw [List.length_take] at hj
    have hj' : j < L.findIdx (fun i => topGroupBad answer i.val) := by rw [hk]; omega
    rw [List.getElem_take]
    exact List.not_of_lt_findIdx hj'
  conv_lhs => rw [← List.take_append_drop k L, List.foldlM_append]
  rw [foldlM_topDecodeStep_good run answer _ [] hgood, bind_map_left, bind_assoc, map_eq_bind_pure_comp]
  refine bind_congr fun ends => ?_
  by_cases hlt : k < L.length
  · have hbad : topGroupBad answer (L[k]'hlt).val = true := by
      subst hk
      exact List.findIdx_getElem (w := hlt)
    rw [List.drop_eq_getElem_cons hlt, List.foldlM_cons, topDecodeStep_bad run answer _ _ hbad, pure_bind,
      foldlM_topDecodeStep_none, pure_bind]
    rfl
  · exfalso
    have hkL : k = L.length := le_antisymm (hk ▸ List.findIdx_le_length) (by omega)
    have hall : ∀ i : Fin (chainCount 0), topGroupBad answer i.val = false := by
      intro i
      have := List.findIdx_eq_length.mp (hk.trans hkL)
      exact this i (hL ▸ List.mem_finRange i)
    have hs := (decode_top_isSome_iff answer).2 hall
    rw [h] at hs
    cases hs
theorem eval_topDecodeRun_none (answers : QueryImpl Spec Id) {run : Fin (chainCount 0) → Nat → M Digest}
    {finish : List Digest → M Digest} {answer : Digest} (h : decode 0 answer = none) :
    evalWithAnswerFn answers (topDecodeRun run finish answer) = none := by
  rw [topDecodeRun_of_decode_none h, map_eq_bind_pure_comp, evalWithAnswerFn_bind]
  rfl
theorem decode_of_eval_topDecodeRun (answers : QueryImpl Spec Id) {run : Fin (chainCount 0) → Nat → M Digest}
    {finish : List Digest → M Digest} {answer : Digest} {out : Digest}
    (h : evalWithAnswerFn answers (topDecodeRun run finish answer) = some out) :
    ∃ digits, decode 0 answer = some digits := by
  cases hd : decode 0 answer with
  | none => rw [eval_topDecodeRun_none answers hd] at h; cases h
  | some digits => exact ⟨digits, rfl⟩
theorem topRejectLength_le (answer : Digest) : topRejectLength answer ≤ chainCount 0 := by
  unfold topRejectLength
  split_ifs
  · exact Nat.zero_le _
  · exact List.findIdx_le_length.trans (le_of_eq List.length_finRange)
theorem dataDigits_top_getD (answer : Digest) {i : Nat} (hi : i < 50) :
    (dataDigits 0 answer).getD i 0 = coreDigit 0 answer i := by
  simp [dataDigits, dataCount, List.getD_eq_getElem?_getD, hi]
/-- Campaigns R6/T51: the canonical top credit of a decoded word is the legacy `topCredit` (every chain one below its
maximum, the checksum included). -/
theorem wordCredit_top {answer : Digest} {digits : List Nat} (h : decode 0 answer = some digits) :
    wordCredit 0 digits = topCredit answer := by
  obtain ⟨-, -, -, rfl⟩ := decode_top_some h
  unfold wordCredit topCredit
  rw [chainCount_top]
  generalize dataDigits 0 answer ++ [target 0 - (dataDigits 0 answer).sum] = ds
  have key : ∀ L : List Nat, (L.filter fun i => ds.getD i 0 + 1 = maxDigit 0 i).length =
      (L.map fun i => if ds.getD i 0 + 1 = maxDigit 0 i then 1 else 0).sum := by
    intro L
    induction L with
    | nil => rfl
    | cons i L ih =>
        by_cases hc : ds.getD i 0 + 1 = maxDigit 0 i
        · rw [List.filter_cons_of_pos (by simpa using hc), List.length_cons, List.map_cons, List.sum_cons, if_pos hc,
            ih]
          omega
        · rw [List.filter_cons_of_neg (by simpa using hc), List.map_cons, List.sum_cons, if_neg hc, ih]
          omega
  exact key _
theorem verifyTop_of_decode (sig : WCT9.Signature) (index : Nat) {answer : Digest} {digits : List Nat}
    (h : decode 0 answer = some digits) :
    verifyTop sig index answer = some <$> recoverLayer (toT3Signature sig) index 0 digits := by
  unfold verifyTop recoverLayer
  generalize route index 0 = p
  obtain ⟨leaf, tree⟩ := p
  dsimp only
  rw [topDecodeRun_of_decode h]
  rfl
theorem eval_verifyTop_none (answers : QueryImpl Spec Id) (sig : WCT9.Signature) (index : Nat) {answer : Digest}
    (h : decode 0 answer = none) : evalWithAnswerFn answers (verifyTop sig index answer) = none := by
  unfold verifyTop
  generalize route index 0 = p
  obtain ⟨leaf, tree⟩ := p
  dsimp only
  exact eval_topDecodeRun_none answers h
def dummyLowData : List Nat := List.replicate 10 6 ++ List.replicate 3 7 ++ List.replicate 29 4
def dummyLowDigits (lay : Layer) : List Nat := dummyLowData ++ [target lay - 197]
def dummyLowDigest : Digest := 267364716866451649868032922661926170038
theorem producerDecode_dummyLow (lay : Layer) (h : lay ≠ 0) :
    producerDecode lay dummyLowDigest = some (dummyLowDigits lay) := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide +kernel
end ClaudeWCT.WCT9
end
-- ==== merged from ClaudeWCT_WCT9_Correctness ====
section

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def shortAnswer (answers : Answers) (input : HashInput) : Digest :=
  (answers (.inl (.inr input))).extractLsb' 0 128
/-- Witness stack: the answer half kept by a step whose half is selected by `high`. -/
def projAnswer (answers : Answers) (high : Bool) (input : HashInput) : Digest :=
  projHalf high (answers (.inl (.inr input)))
theorem eval_chain_add (answers : Answers) (index coord selected i start a b : Nat)
    (initial : Digest) :
    evalWithAnswerFn answers (chain index coord selected i start (a + b) initial) =
      evalWithAnswerFn answers (chain index coord selected i (start + a) b
        (evalWithAnswerFn answers (chain index coord selected i start a initial))) := by
  rw [chain_add, evalWithAnswerFn_bind]
theorem chainInput_length (index coord selected i step : Nat) (value : Digest) :
    (chainInput index coord selected i step value).length = 64 := by
  simp only [chainInput, zero16, List.length_append, bytesLE_length, List.length_replicate]
theorem eval_short (answers : Answers) (input : HashInput) (hlen : input.length = 64) :
    evalWithAnswerFn answers (shortHash input) = shortAnswer answers input := by
  have hpad : pad64 input = input := by simp only [pad64, hlen]; simp
  change (answers (.inl (.inr (pad64 input)))).extractLsb' 0 128 =
    (answers (.inl (.inr input))).extractLsb' 0 128
  rw [hpad]
theorem eval_proj (answers : Answers) (high : Bool) (input : HashInput) (hlen : input.length = 64) :
    evalWithAnswerFn answers (projHash high input) = projAnswer answers high input := by
  have hpad : pad64 input = input := by simp only [pad64, hlen]; simp
  change projHalf high (answers (.inl (.inr (pad64 input)))) = projHalf high (answers (.inl (.inr input)))
  rw [hpad]
/-- Witness stack: the FTS chain (G chains 1, 3) as a `walk` of projected answers. -/
theorem eval_chain_walk (answers : Answers) (index coord selected i start count : Nat)
    (initial : Digest) :
    evalWithAnswerFn answers (chain index coord selected i start count initial) =
      walk (fun step current => projAnswer answers (ftsChainHigh i step)
        (ftsChainInputW index coord selected i step current)) start count initial := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [eval_chain_add]
    change evalWithAnswerFn answers (projHash (ftsChainHigh i (start + count)) (ftsChainInputW index coord selected i
      (start + count) (evalWithAnswerFn answers
        (chain index coord selected i start count initial)))) = _
    rw [eval_proj _ _ _ (ftsChainInputW_length _ _ _ _ _ _), ih]
    rfl
def CarryOk (answers : Answers) (pairQuery : Nat → M (Digest × Digest)) (q : Nat) (carry : Digest) : Prop :=
  q % 2 = 1 → carry = (evalWithAnswerFn answers (pairQuery (q / 2))).2
theorem eval_packedSecret (answers : Answers) (pairQuery : Nat → M (Digest × Digest)) (q : Nat) (carry : Digest)
    (hcarry : CarryOk answers pairQuery q carry) :
    evalWithAnswerFn answers (packedSecret pairQuery q carry) =
      (seedHalf (evalWithAnswerFn answers (pairQuery (q / 2))) q,
        (evalWithAnswerFn answers (pairQuery (q / 2))).2) := by
  unfold packedSecret seedHalf
  by_cases h : q % 2 = 0
  · rw [if_pos h, if_pos h, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  · rw [if_neg h, if_neg h, evalWithAnswerFn_pure, hcarry (by omega)]
theorem carryOk_next (answers : Answers) (pairQuery : Nat → M (Digest × Digest)) (q : Nat) :
    CarryOk answers pairQuery (q + 1) (evalWithAnswerFn answers (pairQuery (q / 2))).2 := by
  intro h
  have : (q + 1) / 2 = q / 2 := by omega
  rw [this]
theorem carryOk_even (answers : Answers) (pairQuery : Nat → M (Digest × Digest)) (q : Nat) (carry : Digest)
    (h : q % 2 = 0) : CarryOk answers pairQuery q carry := by
  intro h1; omega
theorem eval_ftsCoefs_range (answers : Answers) (index coord : Nat) :
    evalWithAnswerFn answers (ftsCoefs index coord) = (List.range (2 * ftsCoefPairs)).map
      (fun j => seedHalf (evalWithAnswerFn answers (ftsSeedPair index coord (j / 2))) j) := by
  unfold ftsCoefs
  refine eval_foldlM_range_inv answers ftsCoefPairs _
    (fun n acc => acc = (List.range (2 * n)).map
      (fun j => seedHalf (evalWithAnswerFn answers (ftsSeedPair index coord (j / 2))) j)) [] rfl ?_
  intro n _ acc hacc
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, hacc]
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, List.range_succ, List.range_succ, List.map_append,
    List.map_append, List.append_assoc]
  have h0 : 2 * n / 2 = n := by omega
  have h1 : (2 * n + 1) / 2 = n := by omega
  simp [seedHalf, h0, h1]
/-- The coefficient list the signer reads is `List.ofFn (ftsCoef answers index coord)`. -/
theorem eval_ftsCoefs (answers : Answers) (index coord : Nat) :
    evalWithAnswerFn answers (ftsCoefs index coord) = List.ofFn (ftsCoef answers index coord) := by
  rw [eval_ftsCoefs_range]
  apply List.ext_getElem (by simp [ftsCoefPairs])
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, ftsCoef]
/-- Answer-level FTS seed of chain `i` of child `selected`: the seed family of `(index, coord)` evaluated at
`ftsPoint selected i`. -/
def seed (answers : Answers) (index coord selected : Nat) (i : Fin 6) : Digest :=
  ClaudeWCT.Arith.familyEval (List.ofFn (ftsCoef answers index coord)) (ftsPoint selected i.val)
theorem seed_eq_family (answers : Answers) (index coord selected : Nat) (i : Fin 6) :
    seed answers index coord selected i =
      ftsFamilySeed (evalWithAnswerFn answers (ftsCoefs index coord)) selected i.val := by
  rw [eval_ftsCoefs]; rfl
def chainValue (answers : Answers) (index coord selected : Nat) (word : Rank)
    (i : Fin 6) : Digest :=
  evalWithAnswerFn answers (chain index coord selected i.val 0
    (4 - wordDigit word i) (seed answers index coord selected i))
def chainEnd (answers : Answers) (index coord selected : Nat) (i : Fin 6) : Digest :=
  evalWithAnswerFn answers (chain index coord selected i.val 0 4
    (seed answers index coord selected i))
theorem value_completes (answers : Answers) (index coord selected : Nat) (word : Rank)
    (i : Fin 6) :
    evalWithAnswerFn answers (chain index coord selected i.val
      (4 - wordDigit word i) (wordDigit word i) (chainValue answers index coord selected word i)) =
      chainEnd answers index coord selected i := by
  unfold chainValue chainEnd
  have hd := wordDigit_le_four word i
  have hc := eval_chain_add answers index coord selected i.val 0
    (4 - wordDigit word i) (wordDigit word i) (seed answers index coord selected i)
  rw [Nat.zero_add, Nat.sub_add_cancel hd] at hc
  exact hc.symm
def stepFn (answers : Answers) (index coord selected : Nat) (t : Fin 6) :
    Nat → Digest → Digest :=
  fun step current => projAnswer answers (ftsChainHigh t.val step)
    (ftsChainInputW index coord selected t.val step current)
theorem chainValue_eq_opening (answers : Answers) (index coord selected : Nat) (word : Rank)
    (i : Fin 6) :
    chainValue answers index coord selected word i =
      opening (stepFn answers index coord selected) (seed answers index coord selected) (embed word) i := by
  unfold chainValue opening stepFn
  exact eval_chain_walk _ _ _ _ _ _ _ _
theorem chainEnd_eq_walk (answers : Answers) (index coord selected : Nat) (i : Fin 6) :
    chainEnd answers index coord selected i =
      walk (stepFn answers index coord selected i) 0 4 (seed answers index coord selected i) := by
  unfold chainEnd stepFn
  exact eval_chain_walk _ _ _ _ _ _ _ _
theorem recover_eq (answers : Answers) (index coord selected : Nat) (word : Rank)
    (values : Fin 6 → Digest) (i : Fin 6) :
    evalWithAnswerFn answers (chain index coord selected i.val (4 - wordDigit word i)
      (wordDigit word i) (values i)) =
      recover (stepFn answers index coord selected) (embed word) values i := by
  unfold recover stepFn
  exact eval_chain_walk _ _ _ _ _ _ _ _
theorem getD_append_singleton {α : Type} (xs : List α) (x d : α) (n : Nat) :
    (xs ++ [x]).getD n d = if n < xs.length then xs.getD n d else if n = xs.length then x else d := by
  by_cases hn : n < xs.length
  · rw [if_pos hn, List.getD_append _ _ _ _ hn]
  · rw [if_neg hn, List.getD_append_right _ _ _ _ (by omega)]
    by_cases he : n = xs.length
    · subst he; simp
    · rw [if_neg he]
      rw [List.getD_eq_default _ _ (by simp only [List.length_singleton]; omega)]
def Rows (answers : Answers) (index coord selected : Nat) (word : Rank)
    (done : Nat) (rows : List Digest × List Digest) : Prop :=
  rows.1.length = done ∧ rows.2.length = done ∧
    (∀ i : Fin 6, i.val < done → rows.1.getD i.val 0 = chainEnd answers index coord selected i) ∧
    (∀ i : Fin 6, i.val < done →
      rows.2.getD i.val 0 = chainValue answers index coord selected word i)
def childStep (index coord selected : Nat) (word : Rank) (coefs : List Digest) (state : List Digest × List Digest)
    (i : Fin 6) : M (List Digest × List Digest) := do
  let secret := ftsFamilySeed coefs selected i.val
  let deficit := wordDigit word i
  let value ← chain index coord selected i.val 0 (4 - deficit) secret
  let last ← chain index coord selected i.val (4 - deficit) deficit value
  pure (state.1 ++ [last], state.2 ++ [value])
def childRows (index coord selected : Nat) (word : Rank) (coefs : List Digest) :
    M (List Digest × List Digest) :=
  (List.finRange 6).foldlM (childStep index coord selected word coefs) ([], [])
theorem buildChildF_factor (index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    buildChildF index coord selected word coefs pad = (do
      let rows ← childRows index coord selected word coefs
      let root ← leafHashP index coord selected pad rows.1
      pure (root, rows.2)) := by
  rfl
theorem rows_step (answers : Answers) (index coord selected : Nat) (word : Rank)
    (i : Fin 6) (rows : List Digest × List Digest)
    (hrows : Rows answers index coord selected word i.val rows) :
    Rows answers index coord selected word (i.val + 1)
      (evalWithAnswerFn answers (childStep index coord selected word
        (List.ofFn (ftsCoef answers index coord)) rows i)) := by
  rcases hrows with ⟨he, hv, hend, hval⟩
  unfold childStep
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change Rows answers index coord selected word (i.val + 1)
    (rows.1 ++ [evalWithAnswerFn answers (chain index coord selected i.val
      (4 - wordDigit word i) (wordDigit word i) (chainValue answers index coord selected word i))],
     rows.2 ++ [chainValue answers index coord selected word i])
  rw [value_completes]
  refine ⟨by simp [he], by simp [hv], ?_, ?_⟩
  · intro j hj
    rw [getD_append_singleton, he]
    by_cases hji : j.val < i.val
    · rw [if_pos hji]; exact hend j hji
    · have hji' : j = i := Fin.ext (by omega)
      subst j
      simp
  · intro j hj
    rw [getD_append_singleton, hv]
    by_cases hji : j.val < i.val
    · rw [if_pos hji]; exact hval j hji
    · have hji' : j = i := Fin.ext (by omega)
      subst j
      simp
theorem eval_childRows (answers : Answers) (index coord selected : Nat) (word : Rank) :
    Rows answers index coord selected word 6
      (evalWithAnswerFn answers (childRows index coord selected word (List.ofFn (ftsCoef answers index coord)))) := by
  unfold childRows
  have key := eval_foldlM_list_inv answers (List.finRange 6)
    (childStep index coord selected word (List.ofFn (ftsCoef answers index coord)))
    (fun i rows => Rows answers index coord selected word i rows) ([], [])
    (by simp [Rows]) (by
      intro i hi rows hrows
      have hi7 : i < 6 := by simpa using hi
      simp only [List.getElem_finRange, Fin.cast_mk]
      exact rows_step answers index coord selected word ⟨i, hi7⟩ rows hrows)
  simp only [List.length_finRange] at key
  exact key
/-- Honest FTS leaf of child `selected`, with leaf pad `pad` (nested FTS r1-1: the previous coordinate's left top). -/
def childRoot (answers : Answers) (index coord selected : Nat) (pad : Digest) : Digest :=
  evalWithAnswerFn answers (leafHashP index coord selected pad
    (List.ofFn (fun i : Fin 6 => chainEnd answers index coord selected i)))
theorem buildChildF_result (answers : Answers) (index coord selected : Nat) (word : Rank) (pad : Digest) :
    evalWithAnswerFn answers (buildChildF index coord selected word (List.ofFn (ftsCoef answers index coord)) pad) =
      (childRoot answers index coord selected pad,
        List.ofFn (fun i : Fin 6 => chainValue answers index coord selected word i)) := by
  let rows := evalWithAnswerFn answers (childRows index coord selected word
    (List.ofFn (ftsCoef answers index coord)))
  have hr : Rows answers index coord selected word 6 rows :=
    eval_childRows answers index coord selected word
  rcases hr with ⟨he, hv, hend, hval⟩
  have hends : rows.1 = List.ofFn (fun i : Fin 6 => chainEnd answers index coord selected i) := by
    apply List.ext_getElem (by simpa only [List.length_ofFn] using he)
    intro i hi hj
    simpa only [List.getD_eq_getElem _ _ hi, List.getElem_ofFn] using
      hend ⟨i, by omega⟩ (by omega)
  have hvals : rows.2 = List.ofFn (fun i : Fin 6 => chainValue answers index coord selected word i) := by
    apply List.ext_getElem (by simpa only [List.length_ofFn] using hv)
    intro i hi hj
    simpa only [List.getD_eq_getElem _ _ hi, List.getElem_ofFn] using
      hval ⟨i, by omega⟩ (by omega)
  rw [buildChildF_factor, evalWithAnswerFn_bind]
  change (evalWithAnswerFn answers (leafHashP index coord selected pad rows.1), rows.2) = _
  rw [hends, hvals]
  rfl
theorem childRoot_word_independent (answers : Answers) (index coord selected : Nat) (left right : Rank)
    (pad : Digest) :
    (evalWithAnswerFn answers (buildChildF index coord selected left (List.ofFn (ftsCoef answers index coord)) pad)).1 =
      (evalWithAnswerFn answers (buildChildF index coord selected right
        (List.ofFn (ftsCoef answers index coord)) pad)).1 := by
  rw [buildChildF_result, buildChildF_result]
/-- C1: evaluating an FTS hash reads the half `ftsHalf heap` of the answer. -/
theorem eval_ftsHash (answers : Answers) (heap : Nat) (input : HashInput) :
    evalWithAnswerFn answers (ftsHash heap input) = ftsHalf heap (answers (.inl (.inr (pad64 input)))) := by
  unfold ftsHash ftsHalf
  cases ftsHighHeap heap <;> rfl
theorem buildChildH_factor (heap index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    buildChildH heap index coord selected word coefs pad = (do
      let rows ← childRows index coord selected word coefs
      let root ← leafHashH heap index coord selected pad rows.1
      pure (root, rows.2)) := by
  rfl
/-- C1: honest FTS leaf of raw child `selected` placed at heap `heap`, with leaf pad `pad`. -/
def childRootH (answers : Answers) (heap index coord selected : Nat) (pad : Digest) : Digest :=
  evalWithAnswerFn answers (leafHashH heap index coord selected pad
    (List.ofFn (fun i : Fin 6 => chainEnd answers index coord selected i)))
theorem childRootH_of_low (answers : Answers) {heap : Nat} (h : ftsHighHeap heap = false)
    (index coord selected : Nat) (pad : Digest) :
    childRootH answers heap index coord selected pad = childRoot answers index coord selected pad := by
  unfold childRootH childRoot
  rw [leafHashH_of_low h]
theorem buildChildH_result (answers : Answers) (heap index coord selected : Nat) (word : Rank) (pad : Digest) :
    evalWithAnswerFn answers
        (buildChildH heap index coord selected word (List.ofFn (ftsCoef answers index coord)) pad) =
      (childRootH answers heap index coord selected pad,
        List.ofFn (fun i : Fin 6 => chainValue answers index coord selected word i)) := by
  let rows := evalWithAnswerFn answers (childRows index coord selected word
    (List.ofFn (ftsCoef answers index coord)))
  have hr : Rows answers index coord selected word 6 rows :=
    eval_childRows answers index coord selected word
  rcases hr with ⟨he, hv, hend, hval⟩
  have hends : rows.1 = List.ofFn (fun i : Fin 6 => chainEnd answers index coord selected i) := by
    apply List.ext_getElem (by simpa only [List.length_ofFn] using he)
    intro i hi hj
    simpa only [List.getD_eq_getElem _ _ hi, List.getElem_ofFn] using
      hend ⟨i, by omega⟩ (by omega)
  have hvals : rows.2 = List.ofFn (fun i : Fin 6 => chainValue answers index coord selected word i) := by
    apply List.ext_getElem (by simpa only [List.length_ofFn] using hv)
    intro i hi hj
    simpa only [List.getD_eq_getElem _ _ hi, List.getElem_ofFn] using
      hval ⟨i, by omega⟩ (by omega)
  rw [buildChildH_factor, evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (evalWithAnswerFn answers (leafHashH heap index coord selected pad rows.1), rows.2) = _
  rw [hends, hvals]
  rfl
theorem childRootH_word_independent (answers : Answers) (heap index coord selected : Nat) (left right : Rank)
    (pad : Digest) :
    (evalWithAnswerFn answers
        (buildChildH heap index coord selected left (List.ofFn (ftsCoef answers index coord)) pad)).1 =
      (evalWithAnswerFn answers (buildChildH heap index coord selected right
        (List.ofFn (ftsCoef answers index coord)) pad)).1 := by
  rw [buildChildH_result, buildChildH_result]
theorem getD_take_lt {α : Type} (L : List α) {n j : Nat} (hj : j < n) (d : α) :
    (L.take n).getD j d = L.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]
theorem treeValue_take_lt (L : List (List Digest)) {n j : Nat} (hj : j < n) (x : Nat) :
    treeValue (L.take n) j x = treeValue L j x := by
  unfold treeValue
  rw [getD_take_lt L hj]
theorem wctHeapNode_low {coord index heap : Nat} (h : 4 ≤ heap) (padR left right : Digest) :
    wctHeapNode coord index heap padR left right = wctNodeHash coord index heap left right := by
  simp only [wctHeapNode, if_neg (show ¬heap < 4 by omega)]
theorem wctHeapNode_top {coord index heap : Nat} (h : heap < 4) (padR left right : Digest) :
    wctHeapNode coord index heap padR left right = wctTopHash coord index heap left padR right := by
  simp only [wctHeapNode, if_pos h]
def HeapInv (answers : Answers) (index coord : Nat) (padR : Digest) (leaves : List Digest)
    (done : Nat) (nodes : Array Digest) : Prop :=
  nodes.size = 256 ∧
    (∀ i, 128 ≤ i → i < 256 → nodes.getD i 0 = leaves.getD (i - 128) 0) ∧
    (∀ i, 2 ≤ i → i < 128 → 128 - done ≤ i → nodes.getD i 0 =
      evalWithAnswerFn answers (wctHeapNode coord index i padR
        (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0)))
theorem getD_set_self (nodes : Array Digest) (i : Nat) (v : Digest) (hi : i < nodes.size) :
    (nodes.set! i v).getD i 0 = v := by
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_self_of_lt hi, Option.getD_some]
theorem getD_set_other (nodes : Array Digest) (i j : Nat) (v : Digest) (hij : i ≠ j) :
    (nodes.set! i v).getD j 0 = nodes.getD j 0 := by
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_ne hij]
theorem heap_order (i : Nat) (hi : i < 126) :
    ((List.range' 2 126).reverse)[i]'(by simpa using hi) = 127 - i := by
  rw [List.getElem_reverse]
  simp only [List.length_range', List.getElem_range', Nat.one_mul]
  omega
theorem heap_initial (answers : Answers) (index coord : Nat) (padR : Digest) (leaves : List Digest)
    (hlen : leaves.length = 128) :
    HeapInv answers index coord padR leaves 0 ((List.replicate 128 (0 : Digest) ++ leaves).toArray) := by
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro i hlo hhi
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      ← List.getD_eq_getElem?_getD]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega)]
    simp only [List.length_replicate]
  · intro i _ hi hlo
    omega
theorem heap_step (answers : Answers) (index coord : Nat) (padR : Digest) (leaves : List Digest) (done : Nat)
    (hdone : done < 126) (nodes : Array Digest)
    (hinv : HeapInv answers index coord padR leaves done nodes) :
    HeapInv answers index coord padR leaves (done + 1)
      (nodes.set! (127 - done) (evalWithAnswerFn answers (wctHeapNode coord index (127 - done) padR
        (nodes.getD (2 * (127 - done)) 0) (nodes.getD (2 * (127 - done) + 1) 0)))) := by
  let heap := 127 - done
  let v := evalWithAnswerFn answers (wctHeapNode coord index heap padR
    (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0))
  change HeapInv answers index coord padR leaves (done + 1) (nodes.set! heap v)
  rcases hinv with ⟨hsize, hleaf, hnode⟩
  have hh : 2 ≤ heap ∧ heap < 128 := by dsimp only [heap]; omega
  refine ⟨by rw [Array.size_set!, hsize], ?_, ?_⟩
  · intro i hlo hhi
    rw [getD_set_other nodes heap i v (by omega)]
    exact hleaf i hlo hhi
  · intro i hlo hhi hdone'
    have hheap : heap ≤ i := by dsimp only [heap]; omega
    have hl : (nodes.set! heap v).getD (2 * i) 0 = nodes.getD (2 * i) 0 :=
      getD_set_other nodes heap (2 * i) v (by omega)
    have hr : (nodes.set! heap v).getD (2 * i + 1) 0 = nodes.getD (2 * i + 1) 0 :=
      getD_set_other nodes heap (2 * i + 1) v (by omega)
    rw [hl, hr]
    by_cases he : i = heap
    · subst i
      rw [getD_set_self nodes heap v (by omega)]
    · rw [getD_set_other nodes heap i v (Ne.symm he)]
      exact hnode i hlo hhi (by dsimp only [heap] at he hheap; omega)
theorem heap_complete (answers : Answers) (index coord : Nat) (padR : Digest) (leaves : List Digest)
    (hlen : leaves.length = 128) :
    HeapInv answers index coord padR leaves 126 (evalWithAnswerFn answers (heapBuild index coord padR leaves)) := by
  unfold heapBuild
  refine eval_foldlM_list_inv answers (List.range' 2 126).reverse _
    (HeapInv answers index coord padR leaves) _ (heap_initial answers index coord padR leaves hlen) ?_
  intro done hdone nodes hinv
  have hd : done < 126 := by simpa only [List.length_reverse, List.length_range'] using hdone
  rw [heap_order done hd]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact heap_step answers index coord padR leaves done hd nodes hinv
def coordRows (index : Nat) (coord : Coord) (selected : Child) (word : Rank) (coefs : List Digest) (pad : Digest) :
    M (List Digest × List Digest) :=
  (List.range 128).foldlM (fun (state : List Digest × List Digest) j => do
    let (root, values) ← buildChildF index coord.val j word coefs pad
    pure (state.1 ++ [root], (if j = selected.val then values else state.2))) ([], [])
def CoordRows (answers : Answers) (index : Nat) (coord : Coord) (selected : Child)
    (word : Rank) (pad : Digest) (done : Nat) (rows : List Digest × List Digest) : Prop :=
  rows.1.length = done ∧
    (∀ j, j < done → rows.1.getD j 0 = childRoot answers index coord.val j pad) ∧
    rows.2 = (if selected.val < done then
      List.ofFn (fun i : Fin 6 => chainValue answers index coord.val selected.val word i)
      else [])
/-! ### Nested FTS (r1-1) honest values: coordinate `c` is built with pads `ftsPrev c`, the top pair of `c - 1`. -/
def coordLeavesWith (answers : Answers) (index coord : Nat) (padL : Digest) : List Digest :=
  List.ofFn (fun j : Fin 128 => childRoot answers index coord j.val padL)
def coordNodesWith (answers : Answers) (index coord : Nat) (prev : Digest × Digest) : Array Digest :=
  evalWithAnswerFn answers (heapBuild index coord prev.2 (coordLeavesWith answers index coord prev.1))
def coordPairWith (answers : Answers) (index coord : Nat) (prev : Digest × Digest) : Digest × Digest :=
  ((coordNodesWith answers index coord prev).getD 2 0, (coordNodesWith answers index coord prev).getD 3 0)
/-- Honest pads of coordinate `c`: `ftsStart` for `c = 0`, else the honest top pair of coordinate `c - 1`. -/
def ftsPrev (answers : Answers) (index : Nat) : Nat → Digest × Digest
  | 0 => ftsStart
  | c + 1 => coordPairWith answers index c (ftsPrev answers index c)
def coordLeaves (answers : Answers) (index : Nat) (coord : Coord) : List Digest :=
  coordLeavesWith answers index coord.val (ftsPrev answers index coord.val).1
def coordNodes (answers : Answers) (index : Nat) (coord : Coord) : Array Digest :=
  coordNodesWith answers index coord.val (ftsPrev answers index coord.val)
def coordinatePair (answers : Answers) (index : Nat) (coord : Coord) : Digest × Digest :=
  ((coordNodes answers index coord).getD 2 0, (coordNodes answers index coord).getD 3 0)
theorem ftsPrev_succ (answers : Answers) (index : Nat) (coord : Coord) :
    ftsPrev answers index (coord.val + 1) = coordinatePair answers index coord := rfl
theorem coordRows_step (answers : Answers) (index : Nat) (coord : Coord)
    (selected : Child) (word : Rank) (pad : Digest) (done : Nat) (rows : List Digest × List Digest)
    (hrows : CoordRows answers index coord selected word pad done rows) :
    CoordRows answers index coord selected word pad (done + 1)
      (rows.1 ++ [childRoot answers index coord.val done pad],
       (if done = selected.val then
         List.ofFn (fun i : Fin 6 => chainValue answers index coord.val done word i)
       else rows.2)) := by
  rcases hrows with ⟨hlen, hroot, hvalues⟩
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro j hj
    rw [getD_append_singleton, hlen]
    by_cases hjd : j < done
    · rw [if_pos hjd]; exact hroot j hjd
    · have he : j = done := by omega
      subst j
      simp
  · by_cases hs : done = selected.val
    · subst hs; simp
    · have hs' : selected.val < done + 1 ↔ selected.val < done := by omega
      simp only [if_neg hs, hvalues, hs']
theorem eval_coordRows (answers : Answers) (index : Nat) (coord : Coord)
    (selected : Child) (word : Rank) (pad : Digest) :
    CoordRows answers index coord selected word pad 128
      (evalWithAnswerFn answers (coordRows index coord selected word
        (List.ofFn (ftsCoef answers index coord.val)) pad)) := by
  unfold coordRows
  refine eval_foldlM_range_inv answers 128 _ (CoordRows answers index coord selected word pad)
    ([], []) ?_ ?_
  · simp [CoordRows]
  · intro done _ rows hrows
    simp only [evalWithAnswerFn_bind, buildChildF_result, evalWithAnswerFn_pure]
    exact coordRows_step answers index coord selected word pad done rows hrows
theorem buildCoordinateF_factor (index : Nat) (coord : Coord) (selected : Child) (word : Rank)
    (prev : Digest × Digest) :
    buildCoordinateF index coord selected word prev = (do
      let coefs ← ftsCoefs index coord.val
      let rows ← coordRows index coord selected word coefs prev.1
      let heap ← heapBuild index coord.val prev.2 rows.1
      pure (heapLevels heap, rows.2)) := by
  rfl
theorem buildCoordinateF_resultWith (answers : Answers) (index : Nat) (coord : Coord)
    (selected : Child) (word : Rank) (prev : Digest × Digest) :
    evalWithAnswerFn answers (buildCoordinateF index coord selected word prev) =
      (heapLevels (coordNodesWith answers index coord.val prev),
       List.ofFn (fun i : Fin 6 => chainValue answers index coord.val selected.val word i)) := by
  let rows := evalWithAnswerFn answers (coordRows index coord selected word
    (List.ofFn (ftsCoef answers index coord.val)) prev.1)
  have hr : CoordRows answers index coord selected word prev.1 128 rows :=
    eval_coordRows answers index coord selected word prev.1
  rcases hr with ⟨hlen, hroot, hvalues⟩
  have hroots : rows.1 = coordLeavesWith answers index coord.val prev.1 := by
    apply List.ext_getElem (by simpa only [coordLeavesWith, List.length_ofFn] using hlen)
    intro j hj hk
    simpa only [coordLeavesWith, List.getD_eq_getElem _ _ hj, List.getElem_ofFn] using
      hroot j (by omega)
  rw [if_pos selected.isLt] at hvalues
  rw [buildCoordinateF_factor, evalWithAnswerFn_bind, eval_ftsCoefs]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (heapLevels (evalWithAnswerFn answers (heapBuild index coord.val prev.2 rows.1)), rows.2) = _
  rw [hroots, hvalues]
  rfl
theorem buildCoordinateF_result (answers : Answers) (index : Nat) (coord : Coord)
    (selected : Child) (word : Rank) :
    evalWithAnswerFn answers (buildCoordinateF index coord selected word (ftsPrev answers index coord.val)) =
      (heapLevels (coordNodes answers index coord),
       List.ofFn (fun i : Fin 6 => chainValue answers index coord.val selected.val word i)) :=
  buildCoordinateF_resultWith answers index coord selected word _
theorem coordNodesWith_graph (answers : Answers) (index coord : Nat) (prev : Digest × Digest) :
    HeapInv answers index coord prev.2 (coordLeavesWith answers index coord prev.1) 126
      (coordNodesWith answers index coord prev) :=
  heap_complete answers index coord prev.2 _ (by simp [coordLeavesWith])
theorem coordNodes_graph (answers : Answers) (index : Nat) (coord : Coord) :
    HeapInv answers index coord.val (ftsPrev answers index coord.val).2 (coordLeaves answers index coord) 126
      (coordNodes answers index coord) :=
  coordNodesWith_graph answers index coord.val _
theorem heapLevels_value (heap : Array Digest) (level j : Nat) (hl : level < 7)
    (hj : j < 2 ^ (7 - level)) :
    treeValue (heapLevels heap) level j = heap.getD (2 ^ (7 - level) + j) 0 := by
  unfold treeValue heapLevels
  rw [List.getD_eq_getElem _ [] (by simp only [List.length_map, List.length_range]; exact hl)]
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; exact hj)]
  simp only [List.getElem_map, List.getElem_range]
theorem coordinate_treeLevels (answers : Answers) (index : Nat) (coord : Coord) :
    TreeLevels answers 3 (nodeLayer coord.val) index 7 (coordLeaves answers index coord) 5
      ((heapLevels (coordNodes answers index coord)).take 6) := by
  have hg := coordNodes_graph answers index coord
  refine ⟨⟨by simp only [heapLevels, List.length_take, List.length_map, List.length_range]; rfl, ?_⟩, ?_, ?_⟩
  · intro j hj
    rw [getD_take_lt _ (by omega)]
    unfold heapLevels
    rw [List.getD_eq_getElem _ [] (by simp only [List.length_map, List.length_range]; omega)]
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
  · rw [getD_take_lt _ (by decide)]
    have h0 : (heapLevels (coordNodes answers index coord)).getD 0 [] =
        (List.range 128).map (fun i => (coordNodes answers index coord).getD (128 + i) 0) := rfl
    rw [h0]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, coordLeaves, coordLeavesWith, List.length_ofFn]
    · intro i hi hj
      have hi' : i < 128 := by simpa only [List.length_map, List.length_range] using hi
      simp only [List.getElem_map, List.getElem_range, coordLeaves, coordLeavesWith, List.getElem_ofFn]
      rw [hg.2.1 (128 + i) (by omega) (by omega), Nat.add_sub_cancel_left, coordLeaves, coordLeavesWith,
        List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hi'), List.getElem_ofFn]
  · intro level hlevel node hnode
    rw [getD_take_lt _ (by omega : level + 1 < 6), getD_take_lt _ (by omega : level < 6)]
    have hpow : 2 ^ (7 - level) = 2 * 2 ^ (7 - (level + 1)) := by
      rw [show 7 - level = 7 - (level + 1) + 1 by omega, pow_succ]
      omega
    have hpos : 4 ≤ 2 ^ (7 - (level + 1)) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (7 - (level + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    have hle : 2 ^ (7 - (level + 1)) ≤ 64 :=
      Nat.pow_le_pow_right (by decide) (by omega : 7 - (level + 1) ≤ 6) |>.trans (by decide)
    have hv := heapLevels_value (coordNodes answers index coord) (level + 1) node (by omega) hnode
    unfold treeValue at hv
    rw [hv]
    have hl := heapLevels_value (coordNodes answers index coord) level (2 * node) (by omega)
      (by omega)
    have hr := heapLevels_value (coordNodes answers index coord) level (2 * node + 1) (by omega)
      (by omega)
    unfold treeValue at hl hr
    rw [hl, hr]
    have hn := hg.2.2 (2 ^ (7 - (level + 1)) + node) (by omega) (by omega) (by omega)
    rw [hn, wctHeapNode_low (by omega)]
    have e1 : 2 * (2 ^ (7 - (level + 1)) + node) = 2 ^ (7 - level) + 2 * node := by omega
    simp only [e1, Nat.add_assoc]
    rfl
/-- Nested FTS (r1-1): the two top values of a coordinate are high-half hashes with the previous right top as pad. -/
theorem coordinate_top (answers : Answers) (index : Nat) (coord : Coord) (j : Nat) (hj : j < 2) :
    treeValue (heapLevels (coordNodes answers index coord)) 6 j =
      evalWithAnswerFn answers (wctTopHash coord.val index (2 + j)
        (treeValue (heapLevels (coordNodes answers index coord)) 5 (2 * j)) (ftsPrev answers index coord.val).2
        (treeValue (heapLevels (coordNodes answers index coord)) 5 (2 * j + 1))) := by
  have hg := coordNodes_graph answers index coord
  rw [heapLevels_value _ 6 j (by decide) (by norm_num; omega), heapLevels_value _ 5 (2 * j) (by decide)
    (by norm_num; omega), heapLevels_value _ 5 (2 * j + 1) (by decide) (by norm_num; omega)]
  rw [hg.2.2 (2 ^ (7 - 6) + j) (by norm_num) (by norm_num; omega) (by norm_num),
    wctHeapNode_top (by norm_num; omega)]
  have e1 : 2 * (2 ^ (7 - 6) + j) = 2 ^ (7 - 5) + 2 * j := by norm_num; omega
  have e2 : 2 ^ (7 - 6) + j = 2 + j := by norm_num
  rw [e1, e2, Nat.add_assoc]
theorem built_pair (answers : Answers) (index : Nat) (coord : Coord) (selected : Child)
    (word : Rank) :
    (((evalWithAnswerFn answers (buildCoordinateF index coord selected word (ftsPrev answers index coord.val))).1.getD 6 []).getD 0 0,
      ((evalWithAnswerFn answers (buildCoordinateF index coord selected word (ftsPrev answers index coord.val))).1.getD 6 []).getD 1 0) =
      coordinatePair answers index coord := by
  rw [buildCoordinateF_result]
  have h0 := heapLevels_value (coordNodes answers index coord) 6 0 (by decide) (by decide)
  have h1 := heapLevels_value (coordNodes answers index coord) 6 1 (by decide) (by decide)
  unfold treeValue at h0 h1
  rw [h0, h1]
  rfl
theorem eval_merklePath_le (answers : Answers) (tag lay tree h completed start n node : Nat)
    (levels : List (List Digest)) (leaves : List Digest)
    (htree : TreeLevels answers tag lay tree h leaves completed levels)
    (hc : completed ≤ h) (hsteps : start + n ≤ completed) (hnode : node < 2 ^ (h - start))
    (path : Fin n → Digest)
    (hpath : ∀ j, path j = treeValue levels (start + j.val) (node / 2 ^ j.val ^^^ 1)) :
    evalWithAnswerFn answers ((List.finRange n).foldlM (fun value j => do
      let other := path j
      let pair := if node / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
      nodeHash tag lay tree (2 ^ (h - (start + j.val + 1)) + node / 2 ^ (j.val + 1)) pair.1 pair.2)
      (treeValue levels start node)) = treeValue levels (start + n) (node / 2 ^ n) := by
  have hi := eval_foldlM_list_inv answers (List.finRange n)
    (fun value j => do
      let other := path j
      let pair := if node / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
      nodeHash tag lay tree (2 ^ (h - (start + j.val + 1)) + node / 2 ^ (j.val + 1)) pair.1 pair.2)
    (fun i value => value = treeValue levels (start + i) (node / 2 ^ i))
    (treeValue levels start node) (by simp) (fun i hi value hv => ?_)
  · simpa only [List.length_finRange] using hi
  · simp only [List.length_finRange] at hi
    simp only [List.getElem_finRange, Fin.val_cast, hpath, hv]
    rw [sibling_pair, div_pow_succ]
    have hp := htree.2.2 (start + i) (by omega) (node / 2 ^ (i + 1))
      (div_pow_bound (start := start) (level := i + 1) (by omega) hnode)
    simpa only [treeValue, Nat.add_assoc] using hp.symm
def honestOpening (built : List (List Digest) × List Digest) (selected : Child) : Opening :=
  let path := (List.range 7).map fun level =>
    (built.1.getD level []).getD (selected.val / 2 ^ level ^^^ 1) 0
  ⟨fun i => built.2.getD i.val 0, fun i => path.getD i.val 0⟩
def expectedOpening (answers : Answers) (index : Nat) (output : HashOutput) (coord : Coord) :
    Opening :=
  honestOpening (evalWithAnswerFn answers
    (buildCoordinateF index coord (child output coord) (rank output coord) (ftsPrev answers index coord.val)))
    (child output coord)
theorem order_pair (levels : List (List Digest)) (selected : Nat) (hs : selected < 128) :
    (if selected / 2 ^ 6 % 2 = 0 then (treeValue levels 6 (selected / 2 ^ 6), treeValue levels 6 (selected / 2 ^ 6 ^^^ 1))
      else (treeValue levels 6 (selected / 2 ^ 6 ^^^ 1), treeValue levels 6 (selected / 2 ^ 6))) =
      (treeValue levels 6 0, treeValue levels 6 1) := by
  have hq : selected / 2 ^ 6 < 2 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    norm_num; omega
  rcases (show selected / 2 ^ 6 = 0 ∨ selected / 2 ^ 6 = 1 by omega) with h | h <;> rw [h] <;> rfl
theorem recoverCoordinate_honest (answers : Answers) (sig : Signature) (index : Nat)
    (output : HashOutput) (coord : Coord)
    (hopen : sig.openings coord = expectedOpening answers index output coord) :
    evalWithAnswerFn answers (recoverCoordinate sig index output coord (ftsPrev answers index coord.val)) =
      coordinatePair answers index coord := by
  let selected := child output coord
  let word := rank output coord
  let levels := heapLevels (coordNodes answers index coord)
  have hbuilt := buildCoordinateF_result answers index coord selected word
  have hvalues : ∀ i : Fin 6, (sig.openings coord).values i =
      chainValue answers index coord.val selected.val word i := by
    intro i
    rw [hopen]
    simp only [expectedOpening, honestOpening]
    change (evalWithAnswerFn answers (buildCoordinateF index coord selected word
      (ftsPrev answers index coord.val))).2.getD i.val 0 = _
    rw [hbuilt]
    change (List.ofFn _).getD i.val 0 = _
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
  have hpath7 : ∀ j : Fin 7, (sig.openings coord).path j =
      treeValue levels j.val (selected.val / 2 ^ j.val ^^^ 1) := by
    intro j
    rw [hopen]
    simp only [expectedOpening, honestOpening]
    change ((List.range 7).map fun level =>
      ((evalWithAnswerFn answers (buildCoordinateF index coord selected word
        (ftsPrev answers index coord.val))).1.getD level []).getD
        (selected.val / 2 ^ level ^^^ 1) 0).getD j.val 0 = _
    rw [hbuilt]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp [treeValue, levels]
  have hpath : ∀ j : Fin 5, (sig.openings coord).path (Fin.castLE (by decide) j) =
      treeValue (levels.take 6) (0 + j.val) (selected.val / 2 ^ j.val ^^^ 1) := by
    intro j
    rw [hpath7, Nat.zero_add, treeValue_take_lt _ (by omega)]
    rfl
  have hends : (List.finRange 6).map (fun i => evalWithAnswerFn answers
      (chain index coord.val selected.val i.val (4 - wordDigit word i) (wordDigit word i)
        ((sig.openings coord).values i))) =
      List.ofFn (fun i : Fin 6 => chainEnd answers index coord.val selected.val i) := by
    simp_rw [hvalues, value_completes]
    exact List.ofFn_eq_map.symm
  have hleaf : childRoot answers index coord.val selected.val (ftsPrev answers index coord.val).1 =
      treeValue (levels.take 6) 0 selected.val := by
    have ht := (coordinate_treeLevels answers index coord).2.1
    unfold treeValue
    change _ = (((heapLevels (coordNodes answers index coord)).take 6).getD 0 []).getD selected.val 0
    rw [ht]
    unfold coordLeaves coordLeavesWith
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact selected.isLt),
      List.getElem_ofFn]
  have hmerkle := eval_merklePath_le answers 3 (nodeLayer coord.val) index 7 5 0 5 selected.val (levels.take 6)
    (coordLeaves answers index coord) (coordinate_treeLevels answers index coord)
    (by decide) (by decide) (by simp only [Nat.sub_zero]; exact selected.isLt)
    (fun j => (sig.openings coord).path (Fin.castLE (by decide) j)) hpath
  have hother : (sig.openings coord).path 6 = treeValue levels 6 (selected.val / 2 ^ 6 ^^^ 1) := hpath7 6
  have hother5 : (sig.openings coord).path 5 = treeValue levels 5 (selected.val / 2 ^ 5 ^^^ 1) := hpath7 5
  have hroot : evalWithAnswerFn answers (leafHashP index coord.val selected.val (ftsPrev answers index coord.val).1
      (List.ofFn fun i : Fin 6 => chainEnd answers index coord.val selected.val i)) =
      treeValue (levels.take 6) 0 selected.val := hleaf
  simp only [Nat.zero_add, show ∀ j : Nat, 7 - (j + 1) = 6 - j from fun j => by omega] at hmerkle
  rw [treeValue_take_lt _ (by decide)] at hmerkle
  have hq : selected.val / 2 ^ 6 < 2 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    have := selected.isLt; norm_num
  have hpair5 : (if selected.val / 2 ^ 5 % 2 = 0 then
      (treeValue levels 5 (selected.val / 2 ^ 5), treeValue levels 5 (selected.val / 2 ^ 5 ^^^ 1))
      else (treeValue levels 5 (selected.val / 2 ^ 5 ^^^ 1), treeValue levels 5 (selected.val / 2 ^ 5))) =
      (treeValue levels 5 (2 * (selected.val / 2 ^ 6)), treeValue levels 5 (2 * (selected.val / 2 ^ 6) + 1)) := by
    rw [sibling_pair (fun n => treeValue levels 5 n), div_pow_succ]
  have htop := coordinate_top answers index coord (selected.val / 2 ^ 6) hq
  unfold recoverCoordinate
  simp only [evalWithAnswerFn_bind, eval_mapM, evalWithAnswerFn_pure, wctNodeHash]
  rw [hends, hroot]
  erw [hmerkle]
  erw [hother5, hpair5, ← htop, hother, order_pair levels selected.val selected.isLt]
  have h0 := heapLevels_value (coordNodes answers index coord) 6 0 (by decide) (by decide)
  have h1 := heapLevels_value (coordNodes answers index coord) 6 1 (by decide) (by decide)
  rw [h0, h1]
  rfl
/-- The nested coordinate fold reproduces the honest pairs coordinate by coordinate. -/
theorem recoverFts_pairs (answers : Answers) (sig : Signature) (index : Nat)
    (output : HashOutput)
    (hopen : ∀ coord, sig.openings coord = expectedOpening answers index output coord) (n : Nat) (hn : n ≤ 9) :
    evalWithAnswerFn answers (((List.finRange 9).take n).foldlM (fun (pairs : List (Digest × Digest)) coord => do
      let pair ← recoverCoordinate sig index output coord (prevPair ftsStart pairs)
      pure (pairs ++ [pair])) []) = (List.range n).map (fun c => ftsPrev answers index (c + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : n < 9 := by omega
    rw [show (List.finRange 9).take (n + 1) = (List.finRange 9).take n ++ [⟨n, hlt⟩] by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hlt)]; simp]
    rw [List.foldlM_append, evalWithAnswerFn_bind, ih (by omega)]
    simp only [List.foldlM_cons, List.foldlM_nil, evalWithAnswerFn_bind, evalWithAnswerFn_pure, bind_pure]
    have hprev : prevPair ftsStart ((List.range n).map (fun c => ftsPrev answers index (c + 1))) =
        ftsPrev answers index n := by
      cases n with
      | zero => rfl
      | succ m =>
        unfold prevPair
        rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
        simp
    rw [hprev, recoverCoordinate_honest answers sig index output ⟨n, hlt⟩ (hopen _), List.range_succ, List.map_append]
    rfl
theorem recoverFts_honest (answers : Answers) (sig : Signature) (index : Nat)
    (output : HashOutput)
    (hopen : ∀ coord, sig.openings coord = expectedOpening answers index output coord) :
    evalWithAnswerFn answers (recoverFts sig index output) = ftsPrev answers index 9 := by
  unfold recoverFts recoverFtsFrom
  rw [evalWithAnswerFn_bind]
  have h := recoverFts_pairs answers sig index output hopen 9 le_rfl
  rw [List.take_of_length_le (by simp)] at h
  rw [h, evalWithAnswerFn_pure]
  unfold prevPair
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
  simp
theorem layerEncodingInput_forest (lay : Layer) (tree leaf : Nat) (root : Digest) (counter : BitVec 32) :
    layerEncodingInput lay tree leaf (.forest root) counter = encodingInput lay tree leaf root counter := rfl
theorem layerCounterSearch_some_search (answers : Answers) (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter found digits, counter + fuel ≤ 2 ^ 32 →
      evalWithAnswerFn answers (layerCounterSearch lay tree leaf msg counter fuel) = some (found, digits) →
      counter ≤ found.toNat ∧ found.toNat < counter + fuel ∧
        producerDecode lay (evalWithAnswerFn answers (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf msg found))) =
          some digits := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter found digits _ he
      simp [layerCounterSearch] at he
  | succ fuel ih =>
      intro counter found digits hlimit he
      simp only [layerCounterSearch, evalWithAnswerFn_bind] at he
      cases hd : producerDecode lay (evalWithAnswerFn answers
        (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)))) with
      | none =>
          simp only [hd] at he
          obtain ⟨hlo, hhi, hgood⟩ := ih (counter + 1) found digits (by omega) he
          exact ⟨by omega, by omega, hgood⟩
      | some values =>
          simp only [hd, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          have hcount : (BitVec.ofNat 32 counter).toNat = counter := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact ⟨by rw [hcount], by rw [hcount]; omega, hd⟩
theorem layerCounterSearch_some (answers : Answers) (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter found digits, counter + fuel ≤ 2 ^ 32 →
      evalWithAnswerFn answers (layerCounterSearch lay tree leaf msg counter fuel) = some (found, digits) →
      counter ≤ found.toNat ∧ found.toNat < counter + fuel ∧
        decode lay (evalWithAnswerFn answers (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf msg found))) =
          some digits := by
  intro fuel counter found digits hlimit he
  obtain ⟨h1, h2, h3⟩ := layerCounterSearch_some_search answers lay tree leaf msg fuel counter found digits hlimit he
  exact ⟨h1, h2, producerDecode_decode h3⟩
theorem ofNat_layer_val (n : Nat) (hn : n < 4) : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt hn
theorem expandLayersBC_verified (answers : Answers) (sig : Signature) (index : Nat) :
    ∀ n, n ≤ 4 → ∀ msg root counters,
      evalWithAnswerFn answers (expandLayersBC sig index n msg) = some (root, counters) →
      counters.length = n ∧ ∀ w : Witness, w.signature = sig →
        (∀ lay : Layer, lay.val < n → w.counters lay = counters.getD lay.val 0) →
        evalWithAnswerFn answers (verifyLayersBC w index n msg) = some root := by
  intro n
  induction n with
  | zero =>
      intro _ msg root counters he
      simp [expandLayersBC] at he
  | succ n ih =>
      intro hn msg root counters he
      simp only [expandLayersBC, evalWithAnswerFn_bind] at he
      split at he
      · rename_i counter digits hs
        have hlim := searchLimit_le (Fin.ofNat 4 n)
        obtain ⟨_, hbound, hproducer⟩ := layerCounterSearch_some_search answers _ _ _ _
          _ 0 counter digits (by unfold counterLimit at hlim; omega) hs
        have hdecode := producerDecode_decode hproducer
        have hnot : ¬counter.toNat ≥ verifyWindow := ctr_not_ge_verifyWindow counter
        have hlay := ofNat_layer_val n (by omega)
        by_cases hn0 : n = 0
        · subst n
          simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq,
            Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          refine ⟨rfl, fun w hw hc => ?_⟩
          have hcounter : w.counters (Fin.ofNat 4 0) = counter := by
            rw [hc _ (by rw [hlay]; omega), hlay]; rfl
          simp only [verifyLayersBC, hcounter, hnot, ite_false, evalWithAnswerFn_bind, if_true]
          rw [verifyTop_of_decode _ _ hdecode, evalWithAnswerFn_map, hw]
          rfl
        · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
          cases hr : evalWithAnswerFn answers (expandLayersBC sig index n
            (.pair (evalWithAnswerFn answers (recoverLayerPair sig index (Fin.ofNat 4 n) digits)).1
              (evalWithAnswerFn answers (recoverLayerPair sig index (Fin.ofNat 4 n) digits)).2)) with
          | none => simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at he
          | some previous =>
              obtain ⟨previousRoot, previousCounters⟩ := previous
              simp only [hr, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
              obtain ⟨rfl, rfl⟩ := he
              obtain ⟨hlen, hverify⟩ := ih (by omega) _ _ _ hr
              refine ⟨by simp [hlen], fun w hw hc => ?_⟩
              have hcounter : w.counters (Fin.ofNat 4 n) = counter := by
                rw [hc _ (by rw [hlay]; omega), hlay,
                  List.getD_append_right previousCounters [counter] 0 n (by omega), hlen]
                simp
              have hgood := producerDecode_lowerRankGood
                (lay := Fin.ofNat 4 n) (by intro h; have := congrArg Fin.val h; rw [hlay] at this; exact hn0 this) hproducer
              simp only [verifyLayersBC, hcounter, hnot, ite_false, evalWithAnswerFn_bind, hdecode, hn0, hw,
                recoverLayerPairGuard_of_good _ _ _ _ _ hgood, evalWithAnswerFn_map]
              apply hverify w hw
              intro lay hsmall
              rw [hc lay (by omega), List.getD_append previousCounters [counter] 0 lay.val (by omega)]
      · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
/-- v6: the coefficients of family `f` of `(lay, tree)` as the signer reads them (ordinals `famBase · f + j`,
`j < famSize lay f`, packed halves of `lowerSeedPair lay tree`). -/
def famCoefL (answers : Answers) (lay : Layer) (tree f : Nat) : List Digest :=
  (List.range (famSize lay f)).map fun j =>
    seedHalf (evalWithAnswerFn answers (lowerSeedPair lay tree ((famBase lay * f + j) / 2))) (famBase lay * f + j)
/-- The lower WOTS seed of chain `i`: the leaf's family evaluated at `famPoint`. -/
def lowerSeed (answers : Answers) (lay : Layer) (tree leaf i : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval (famCoefL answers lay tree (famOf lay leaf)) (famPoint lay leaf i)
/-! ### Campaign T8D: one seed family per leaf at every layer (security-facing view)
Top leaves (24 coefficients, `Correctness.topCoefN`) and lower leaves (17 coefficients, `lowerCoefN`) are both read
through the cells `lowerSeedPair lay tree (famOrdinal lay leaf j / 2)`, half `famOrdinal lay leaf j % 2`, and the seed
of chain `i` is the family evaluated at `i + 1` (`wotsSeed_fam`). -/
def famCount (lay : Layer) : Nat := famBase lay
/-! #### Seed-family layout (r3-lean-seedfam): `famGrp`, `famBase`, `famSize`, `famStride`, `famOf`, `famPoint`,
`famOrdinal` are scheme definitions (`Core`). The facts below are the only ones the security layer uses about the
layout values (re-prove them when the layout changes). -/
def famCoefN (answers : Answers) (lay : Layer) (tree leaf j : Nat) : Digest :=
  seedHalf (evalWithAnswerFn answers (lowerSeedPair lay tree (famOrdinal lay leaf j / 2))) (famOrdinal lay leaf j)
def famCoef (answers : Answers) (lay : Layer) (tree leaf : Nat) (j : Fin (famSize lay (famOf lay leaf))) : Digest :=
  famCoefN answers lay tree leaf j.val
theorem famGrp_pos (lay : Layer) : 0 < famGrp lay := by unfold famGrp; split_ifs <;> decide
theorem famGrp_le (lay : Layer) : famGrp lay ≤ 7 := by unfold famGrp; split_ifs <;> decide
theorem famSize_le_base (lay : Layer) (f : Nat) : famSize lay f ≤ famBase lay := by
  unfold famSize famBase; split_ifs
  · exact le_rfl
  · have := min_le_left 7 (2 ^ height lay - 7 * f); omega
theorem famBase_le (lay : Layer) : famBase lay ≤ 39 := by
  unfold famBase; split_ifs <;> decide
theorem famStride_ge (lay : Layer) : chainCount lay ≤ famStride lay := by
  unfold famStride; split_ifs with h
  · subst h; decide
  · fin_cases lay <;> first | exact absurd rfl h | decide
theorem famStride_top : 58 ≤ famStride 0 := by decide
theorem famPoint_lt (lay : Layer) (leaf i : Nat) (hi : i < 58) : famPoint lay leaf i < 1024 := by
  have hg := famGrp_le lay
  have hm : leaf % famGrp lay < famGrp lay := Nat.mod_lt _ (famGrp_pos lay)
  have hc : chainCount lay ≤ 54 := by fin_cases lay <;> decide
  have hs : famStride lay ≤ 64 := by unfold famStride; split_ifs <;> decide
  have h1 : leaf % famGrp lay * famStride lay ≤ 6 * 64 := Nat.mul_le_mul (by omega) hs
  have h2 : famGrp lay * famStride lay ≤ 7 * 64 := Nat.mul_le_mul hg hs
  have h3 : leaf % famGrp lay * (58 - chainCount lay) ≤ 6 * 58 := Nat.mul_le_mul (by omega) (by omega)
  unfold famPoint
  split_ifs <;> omega
theorem famBase_lower {lay : Layer} (h : lay ≠ 0) : famBase lay = 38 := by unfold famBase; rw [if_neg h]
theorem famGrp_lower {lay : Layer} (h : lay ≠ 0) : famGrp lay = 7 := by unfold famGrp; rw [if_neg h]
/-! Top-layer identities (v6: families of 4 leaves, `T3.topCoefOrdinal` / `T3.topPoint`). -/
theorem famOf_top (leaf : Nat) : famOf 0 leaf = leaf / 4 := by unfold famOf famGrp; simp
theorem famPoint_top (leaf i : Nat) : famPoint 0 leaf i = topPoint leaf i := by
  unfold famPoint famGrp famStride topPoint; simp
theorem famOrdinal_top (leaf j : Nat) : famOrdinal 0 leaf j = topCoefOrdinal leaf j := by
  unfold famOrdinal famBase topCoefOrdinal; rw [famOf_top]; simp
theorem famSize_top (f : Nat) : famSize 0 f = topCoefCount := by unfold famSize; simp
theorem famCount_top : famCount 0 = 31 := rfl

theorem famCount_ge (lay : Layer) : 8 ≤ famCount lay := by
  unfold famCount famBase; split_ifs <;> decide
theorem famCount_le (lay : Layer) : famCount lay ≤ 39 := famBase_le lay
theorem famOrdinal_div_lt {lay : Layer} {leaf j : Nat} (hl : leaf < 2 ^ 24) (hj : j < famBase lay) :
    famOrdinal lay leaf j / 2 < 2 ^ 32 := by
  have h39 := famBase_le lay
  have hf : famOf lay leaf ≤ leaf := Nat.div_le_self _ _
  have : famBase lay * famOf lay leaf ≤ 39 * leaf := Nat.mul_le_mul h39 hf
  unfold famOrdinal
  omega
/-- Family ordinals determine the family and the coefficient (generic layout). -/
theorem famOrdinal_inj_fam {lay : Layer} {l l' j j' : Nat} (hj : j < famBase lay) (hj' : j' < famBase lay)
    (h : famOrdinal lay l j = famOrdinal lay l' j') : famOf lay l = famOf lay l' ∧ j = j' := by
  unfold famOrdinal at h
  rcases Nat.lt_or_ge (famOf lay l) (famOf lay l') with hlt | hge
  · exfalso
    have : famBase lay * famOf lay l + famBase lay ≤ famBase lay * famOf lay l' := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
    omega
  · rcases Nat.lt_or_ge (famOf lay l') (famOf lay l) with hlt' | hge'
    · exfalso
      have : famBase lay * famOf lay l' + famBase lay ≤ famBase lay * famOf lay l := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt'
      omega
    · have hll : famOf lay l = famOf lay l' := by omega
      rw [hll] at h
      exact ⟨hll, by omega⟩
/-- The WOTS seed of chain `i` of leaf `(lay, tree, leaf)`: its family evaluated at `famPoint lay leaf i` (campaign
T8D: every layer; the cells are tree-indexed, `lowerSeedPair lay tree`, so at the top only tree `0` is the keygen tree,
`wotsSeed_top`). -/
def wotsSeed (answers : Answers) (lay : Layer) (tree leaf i : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval (List.ofFn (famCoef answers lay tree leaf)) (famPoint lay leaf i)
theorem wotsSeed_fam (answers : Answers) (lay : Layer) (tree leaf i : Nat) :
    wotsSeed answers lay tree leaf i =
      ClaudeWCT.Arith.familyEval (List.ofFn (famCoef answers lay tree leaf)) (famPoint lay leaf i) := rfl
/-- C3: the chains of the current scheme (`chainW`, lower chain 0's step 6 keeps the high half). -/
def wotsValue (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat) (i : Nat) : Digest :=
  evalWithAnswerFn answers (chainW lay tree leaf i 0 (digits.getD i 0)
    (wotsSeed answers lay tree leaf i))
def wotsEnd (answers : Answers) (lay : Layer) (tree leaf i : Nat) : Digest :=
  evalWithAnswerFn answers (chainW lay tree leaf i 0 (maxDigit lay i)
    (wotsSeed answers lay tree leaf i))
/-- C2: lower leaves use the half of their index (`lowerLeafHash`); the top (layer 0) is `T3.leafHash`. -/
def wotsRoot (answers : Answers) (lay : Layer) (tree leaf : Nat) : Digest :=
  evalWithAnswerFn answers (lowerLeafHash lay tree leaf
    ((List.range (chainCount lay)).map (wotsEnd answers lay tree leaf)))
/-- C2: lower nodes use the half of their heap (`lowerLevels`). Top-bytes layer: the top tree (`lay = 0`) is the nonce-searched `builtTree`. -/
def wotsTree (answers : Answers) (lay : Layer) (tree : Nat) : List (List Digest) :=
  if lay = 0 then evalWithAnswerFn answers (buildTopLevels ((List.range (2 ^ height lay)).map (wotsRoot answers lay tree)))
  else evalWithAnswerFn answers (lowerLevels lay.val tree (height lay)
    ((List.range (2 ^ height lay)).map (wotsRoot answers lay tree)))
def wotsPieces (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat) : Pieces :=
  ((List.range (chainCount lay)).map (wotsValue answers lay tree leaf digits),
   (List.range (height lay)).map fun j => treeValue (wotsTree answers lay tree) j (leaf / 2 ^ j ^^^ 1))
/-- The keygen top tree (tree `0`): the family seeds of `T3.Correctness.leafSeed` (`topLeafSeed`). -/
theorem ofFn_famCoef (answers : Answers) (lay : Layer) (tree leaf : Nat) :
    List.ofFn (famCoef answers lay tree leaf) = famCoefL answers lay tree (famOf lay leaf) := by
  apply List.ext_getElem (by simp [famCoefL])
  intro j h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, famCoef, famCoefN, famCoefL, famOrdinal]
theorem wotsSeed_top (answers : Answers) (leaf i : Nat) :
    wotsSeed answers 0 0 leaf i = leafSeed answers 0 0 leaf i := by
  rw [leafSeed_top, wotsSeed_fam, famPoint_top]
  unfold topLeafSeed topSeed topCoefList
  refine congrArg (ClaudeWCT.Arith.familyEval · _) ?_
  apply List.ext_getElem (by simp [famSize_top, topCoefCount])
  intro j h1 h2
  simp only [List.getElem_ofFn, famCoef, famCoefN, topCoef, topCoefN, seedHalf, famOrdinal_top,
    topCoefOrdinal, topSeedPair, lowerSeedPair]
  rfl
theorem wotsSeed_lower (answers : Answers) {lay : Layer} (_hlay : lay ≠ 0) (tree leaf i : Nat) :
    wotsSeed answers lay tree leaf i = lowerSeed answers lay tree leaf i := by
  rw [wotsSeed_fam, ofFn_famCoef]
  rfl
theorem wotsValue_top (answers : Answers) (leaf : Nat) (digits : List Nat) :
    wotsValue answers 0 0 leaf digits = leafValue answers 0 0 leaf digits := by
  funext i; unfold wotsValue leafValue; rw [wotsSeed_top, chainW_top_eq, layChain_top]
theorem wotsEnd_top (answers : Answers) (leaf : Nat) :
    wotsEnd answers 0 0 leaf = leafEnd answers 0 0 leaf := by
  funext i; unfold wotsEnd leafEnd; rw [wotsSeed_top, chainW_top_eq, layChain_top]
theorem wotsRoot_top (answers : Answers) :
    wotsRoot answers 0 0 = leafRoot answers 0 0 := by
  funext leaf; unfold wotsRoot leafRoot; rw [wotsEnd_top, lowerLeafHash_top]
theorem wotsTree_top (answers : Answers) :
    wotsTree answers 0 0 = builtTree answers 0 0 := by
  unfold wotsTree builtTree; rw [if_pos rfl, if_pos rfl, wotsRoot_top]
theorem wotsPieces_top (answers : Answers) (leaf : Nat) (digits : List Nat) :
    wotsPieces answers 0 0 leaf digits = honestPieces answers 0 0 leaf digits := by
  unfold wotsPieces honestPieces; rw [wotsValue_top, wotsTree_top]
theorem eval_chainW_add (answers : Answers) (lay : Layer) (tree leaf i start a b : Nat) (value : Digest) :
    evalWithAnswerFn answers (chainW lay tree leaf i start (a + b) value) =
      evalWithAnswerFn answers (chainW lay tree leaf i (start + a) b
        (evalWithAnswerFn answers (chainW lay tree leaf i start a value))) := by
  rw [chainW_add, evalWithAnswerFn_bind]
theorem wotsValue_completes (answers : Answers) (lay : Layer) (tree leaf : Nat)
    (digits : List Nat) (hvalid : Cost.ValidDigits lay digits) (i : Nat) (hi : i < chainCount lay) :
    evalWithAnswerFn answers (chainW lay tree leaf i (digits.getD i 0)
      (maxDigit lay i - digits.getD i 0) (wotsValue answers lay tree leaf digits i)) =
      wotsEnd answers lay tree leaf i := by
  unfold wotsValue wotsEnd
  have hd := hvalid i hi
  have hc := eval_chainW_add answers lay tree leaf i 0 (digits.getD i 0)
    (maxDigit lay i - digits.getD i 0) (wotsSeed answers lay tree leaf i)
  rw [Nat.zero_add, Nat.add_sub_of_le hd] at hc
  exact hc.symm
theorem eval_lowerFamCoefs (answers : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree f : Nat) :
    evalWithAnswerFn answers (lowerFamCoefs lay tree f) = famCoefL answers lay tree f := by
  have hb := famBase_lower hlay
  let g : Nat → Digest := fun k =>
    seedHalf (evalWithAnswerFn answers (lowerSeedPair lay tree (famBase lay * f / 2 + k / 2))) k
  have hfold := eval_foldlM_range_inv answers (famPairs lay f) (fun (acc : List Digest) j => do
      let p ← lowerSeedPair lay tree (famBase lay * f / 2 + j)
      pure (acc ++ [p.1, p.2])) (fun n acc => acc = (List.range (2 * n)).map g) [] rfl
    (fun i _ acc hacc => by
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, hacc]
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, List.range_succ, List.range_succ, List.map_append,
        List.map_append, List.append_assoc]
      simp only [List.map_cons, List.map_nil, List.singleton_append, g, seedHalf]
      rw [if_pos (by omega), if_neg (by omega), show 2 * i / 2 = i by omega, show (2 * i + 1) / 2 = i by omega])
  unfold lowerFamCoefs
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [hfold]
  have hle : famSize lay f ≤ 2 * famPairs lay f := by unfold famPairs; omega
  apply List.ext_getElem (by simp [famCoefL]; omega)
  intro k h1 h2
  simp only [List.length_take, List.length_map, List.length_range] at h1
  simp only [List.getElem_take, List.getElem_map, List.getElem_range, famCoefL, g, seedHalf, hb]
  rw [show 38 * f / 2 + k / 2 = (38 * f + k) / 2 by omega]
  split_ifs <;> first | rfl | omega
/-- The coefficient state after leaf `leaf`: its family's coefficients. -/
def leafCarryOut (answers : Answers) (lay : Layer) (tree leaf : Nat) : List Digest :=
  famCoefL answers lay tree (famOf lay leaf)
theorem eval_lowerCoefs (answers : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (carry : List Digest)
    (hcarry : leaf % famGrp lay ≠ 0 → carry = famCoefL answers lay tree (famOf lay leaf)) :
    evalWithAnswerFn answers (lowerCoefs lay tree leaf carry) =
      (famCoefL answers lay tree (famOf lay leaf), leafCarryOut answers lay tree leaf) := by
  unfold lowerCoefs leafCarryOut
  split_ifs with h
  · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_lowerFamCoefs answers hlay]
  · rw [evalWithAnswerFn_pure, hcarry h]
theorem lowerFamilySeed_eq (answers : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf i : Nat) :
    lowerFamilySeed (famCoefL answers lay tree (famOf lay leaf)) lay leaf i = wotsSeed answers lay tree leaf i := by
  rw [wotsSeed_lower answers hlay]
  rfl
def LeafRowsF (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat) (done : Nat)
    (rows : List Digest × List Digest) : Prop :=
  rows.1.length = done ∧ rows.2.length = done ∧
    (∀ i, i < done → rows.1.getD i 0 = wotsEnd answers lay tree leaf i) ∧
    (∀ i, i < done → rows.2.getD i 0 = wotsValue answers lay tree leaf digits i)
def leafStepF (lay : Layer) (tree leaf : Nat) (digits : List Nat) (coefs : List Digest)
    (state : List Digest × List Digest) (i : Nat) : M (List Digest × List Digest) := do
  let digit := digits.getD i 0
  let value ← chainW lay tree leaf i 0 digit (lowerFamilySeed coefs lay leaf i)
  let last ← chainW lay tree leaf i digit (maxDigit lay i - digit) value
  pure (state.1 ++ [last], state.2 ++ [value])
def leafRowsF (lay : Layer) (tree leaf : Nat) (digits : List Nat) (coefs : List Digest) :
    M (List Digest × List Digest) :=
  (List.range (chainCount lay)).foldlM (leafStepF lay tree leaf digits coefs) ([], [])
theorem buildLeafPF_factor (lay : Layer) (tree leaf : Nat) (digits : List Nat) (carry : List Digest) :
    buildLeafPF lay tree leaf digits carry = (do
      let coefs ← lowerCoefs lay tree leaf carry
      let rows ← leafRowsF lay tree leaf digits coefs.1
      let root ← lowerLeafHash lay tree leaf rows.1
      pure ((root, rows.2), coefs.2)) := by
  rfl
theorem leafStepF_inv (answers : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (i : Nat) (hi : i < chainCount lay) (rows : List Digest × List Digest)
    (hrows : LeafRowsF answers lay tree leaf digits i rows) :
    LeafRowsF answers lay tree leaf digits (i + 1)
      (evalWithAnswerFn answers (leafStepF lay tree leaf digits (famCoefL answers lay tree (famOf lay leaf)) rows i)) := by
  rcases hrows with ⟨he, hv, hend, hval⟩
  unfold leafStepF
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [lowerFamilySeed_eq answers hlay]
  change LeafRowsF answers lay tree leaf digits (i + 1)
    (rows.1 ++ [evalWithAnswerFn answers (chainW lay tree leaf i (digits.getD i 0)
      (maxDigit lay i - digits.getD i 0) (wotsValue answers lay tree leaf digits i))],
     rows.2 ++ [wotsValue answers lay tree leaf digits i])
  rw [wotsValue_completes answers lay tree leaf digits hvalid i hi]
  refine ⟨by simp [he], by simp [hv], ?_, ?_⟩
  · intro j hj
    rw [getD_append_singleton, he]
    by_cases hji : j < i
    · rw [if_pos hji]; exact hend j hji
    · have hji' : j = i := by omega
      subst j
      simp
  · intro j hj
    rw [getD_append_singleton, hv]
    by_cases hji : j < i
    · rw [if_pos hji]; exact hval j hji
    · have hji' : j = i := by omega
      subst j
      simp
theorem eval_leafRowsF (answers : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) :
    evalWithAnswerFn answers (leafRowsF lay tree leaf digits (famCoefL answers lay tree (famOf lay leaf))) =
      ((List.range (chainCount lay)).map (wotsEnd answers lay tree leaf),
        (List.range (chainCount lay)).map (wotsValue answers lay tree leaf digits)) := by
  have hr : LeafRowsF answers lay tree leaf digits (chainCount lay)
      (evalWithAnswerFn answers (leafRowsF lay tree leaf digits (famCoefL answers lay tree (famOf lay leaf)))) := by
    unfold leafRowsF
    exact eval_foldlM_range_inv answers (chainCount lay) _ (LeafRowsF answers lay tree leaf digits) ([], [])
      (by simp [LeafRowsF]) (fun i hi rows hrows => leafStepF_inv answers hlay tree leaf digits hvalid i hi rows hrows)
  rcases hr with ⟨he, hv, hend, hval⟩
  exact Prod.ext (list_eq_range_map _ _ _ he hend) (list_eq_range_map _ _ _ hv hval)
theorem chainCount_pos (lay : Layer) : 0 < chainCount lay := by fin_cases lay <;> decide
theorem buildLeafPF_result (answers : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (carry : List Digest)
    (hcarry : leaf % famGrp lay ≠ 0 → carry = famCoefL answers lay tree (famOf lay leaf)) :
    evalWithAnswerFn answers (buildLeafPF lay tree leaf digits carry) =
      ((wotsRoot answers lay tree leaf, (List.range (chainCount lay)).map (wotsValue answers lay tree leaf digits)),
       leafCarryOut answers lay tree leaf) := by
  rw [buildLeafPF_factor, evalWithAnswerFn_bind, eval_lowerCoefs answers hlay tree leaf carry hcarry]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [eval_leafRowsF answers hlay tree leaf digits hvalid]
  rfl
/-! ### C2: honest lower trees (`lowerLevels`, the half of each heap) -/
theorem eval_lowerLevel (answers : Answers) (lay tree h level : Nat) (nodes : List Digest) :
    evalWithAnswerFn answers (lowerLevel lay tree h level nodes) =
      (List.range (nodes.length / 2)).map fun i => evalWithAnswerFn answers
        (lowerNodeHash lay tree (2 ^ (h - level) + i) (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0)) :=
  eval_mapM answers _ _
theorem eval_lowerLevel_length (answers : Answers) (lay tree h level : Nat) (nodes : List Digest) :
    (evalWithAnswerFn answers (lowerLevel lay tree h level nodes)).length = nodes.length / 2 := by
  rw [eval_lowerLevel, List.length_map, List.length_range]
theorem eval_lowerLevel_getD (answers : Answers) (lay tree h level : Nat) (nodes : List Digest)
    (i : Nat) (hi : i < nodes.length / 2) :
    (evalWithAnswerFn answers (lowerLevel lay tree h level nodes)).getD i 0 =
      evalWithAnswerFn answers (lowerNodeHash lay tree (2 ^ (h - level) + i)
        (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0)) := by
  rw [eval_lowerLevel]
  simp [List.getD_eq_getElem, hi]
/-- `T3.Correctness.TreeLevels` for the trees of the current scheme (`lowerNodeHash`; at layer 0 it is
`nodeHash 3 0`, `lowerNodeHash_top`). -/
def TreeLevelsL (answers : Answers) (lay tree h : Nat) (leaves : List Digest)
    (completed : Nat) (levels : List (List Digest)) : Prop :=
  SigGolfCandidate.T3.Cost.LevelShape h completed levels ∧ levels.getD 0 [] = leaves ∧
    ∀ level, level < completed → ∀ node, node < 2 ^ (h - (level + 1)) →
      (levels.getD (level + 1) []).getD node 0 = evalWithAnswerFn answers
        (lowerNodeHash lay tree (2 ^ (h - (level + 1)) + node)
          ((levels.getD level []).getD (2 * node) 0) ((levels.getD level []).getD (2 * node + 1) 0))
theorem treeLevelsL_top {answers : Answers} {tree h : Nat} {leaves : List Digest} {completed : Nat}
    {levels : List (List Digest)} :
    TreeLevelsL answers 0 tree h leaves completed levels ↔ TreeLevels answers 3 0 tree h leaves completed levels := by
  unfold TreeLevelsL TreeLevels
  simp only [lowerNodeHash_top]
theorem eval_lowerLevels_correct (answers : Answers) (lay tree h : Nat)
    (leaves : List Digest) (hlen : leaves.length = 2 ^ h) :
    TreeLevelsL answers lay tree h leaves h (evalWithAnswerFn answers (lowerLevels lay tree h leaves)) := by
  unfold lowerLevels
  refine eval_foldlM_range'_inv answers 1 h _ (TreeLevelsL answers lay tree h leaves) [leaves]
    ⟨⟨rfl, ?_⟩, rfl, ?_⟩ (fun i hi levels hlevels => ?_)
  · intro j hj
    have he : j = 0 := by omega
    subst j
    simpa using hlen
  · intro j hj
    omega
  · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    let next := evalWithAnswerFn answers (lowerLevel lay tree h (1 + i) (levels.getD (1 + i - 1) []))
    have hlength : levels.length = i + 1 := hlevels.1.1
    have hprevious : (levels.getD (1 + i - 1) []).length = 2 ^ (h - i) := by
      simpa using hlevels.1.2 i le_rfl
    have hnext : next.length = 2 ^ (h - (i + 1)) := by
      rw [eval_lowerLevel_length, hprevious, show h - i = h - (i + 1) + 1 by omega, pow_succ,
        Nat.mul_div_cancel _ (by decide : 0 < 2)]
    change TreeLevelsL answers lay tree h leaves (i + 1) (levels ++ [next])
    refine ⟨⟨by simp [hlength], ?_⟩, ?_, ?_⟩
    · intro j hj
      by_cases hold : j ≤ i
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact hlevels.1.2 j hold
      · have he : j = i + 1 := by omega
        subst j
        rw [List.getD_append_right _ _ _ _ (by omega), hlength]
        simp only [Nat.sub_self, List.getD_cons_zero]
        exact hnext
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact hlevels.2.1
    · intro level hlevel node hnode
      by_cases hold : level < i
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ level (by omega)]
        exact hlevels.2.2 level hold node hnode
      · have he : level = i := by omega
        subst level
        rw [List.getD_append_right _ _ _ _ (by omega), hlength]
        simp only [Nat.sub_self, List.getD_cons_zero]
        rw [List.getD_append _ _ _ i (by omega)]
        have hwidth : (levels.getD (1 + i - 1) []).length / 2 = 2 ^ (h - (i + 1)) := by
          rw [hprevious, show h - i = h - (i + 1) + 1 by omega, pow_succ,
            Nat.mul_div_cancel _ (by decide : 0 < 2)]
        have hc := eval_lowerLevel_getD answers lay tree h (1 + i) (levels.getD (1 + i - 1) []) node
          (by rw [hwidth]; exact hnode)
        simpa only [next, show 1 + i = i + 1 by omega, Nat.add_sub_cancel] using hc
theorem eval_merklePathL (answers : Answers) (lay tree h start n node : Nat)
    (levels : List (List Digest)) (leaves : List Digest)
    (htree : TreeLevelsL answers lay tree h leaves h levels)
    (hsteps : start + n ≤ h) (hnode : node < 2 ^ (h - start)) (path : Fin n → Digest)
    (hpath : ∀ j, path j = treeValue levels (start + j.val) (node / 2 ^ j.val ^^^ 1)) :
    evalWithAnswerFn answers ((List.finRange n).foldlM (fun value j => do
      let other := path j
      let pair := if node / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
      lowerNodeHash lay tree (2 ^ (h - (start + j.val + 1)) + node / 2 ^ (j.val + 1)) pair.1 pair.2)
      (treeValue levels start node)) = treeValue levels (start + n) (node / 2 ^ n) := by
  have hi := eval_foldlM_list_inv answers (List.finRange n)
    (fun value j => do
      let other := path j
      let pair := if node / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
      lowerNodeHash lay tree (2 ^ (h - (start + j.val + 1)) + node / 2 ^ (j.val + 1)) pair.1 pair.2)
    (fun i value => value = treeValue levels (start + i) (node / 2 ^ i))
    (treeValue levels start node) (by simp) (fun i hi value hv => ?_)
  · simpa only [List.length_finRange] using hi
  · simp only [List.length_finRange] at hi
    simp only [List.getElem_finRange, Fin.val_cast, Fin.val_mk, hpath, hv]
    rw [sibling_pair, div_pow_succ]
    have hp := htree.2.2 (start + i) (by omega) (node / 2 ^ (i + 1))
      (div_pow_bound (start := start) (level := i + 1) (by omega) hnode)
    simpa only [treeValue, Nat.add_assoc] using hp.symm
def treeCarry (answers : Answers) (lay : Layer) (tree leaf : Nat) : List Digest :=
  if leaf = 0 then [] else leafCarryOut answers lay tree (leaf - 1)
theorem famOf_pred {lay : Layer} {leaf : Nat} (h : leaf % famGrp lay ≠ 0) :
    famOf lay (leaf - 1) = famOf lay leaf := by
  have hg := famGrp_pos lay
  have e := Nat.div_add_mod leaf (famGrp lay)
  have hr := Nat.mod_lt leaf hg
  unfold famOf
  refine Nat.div_eq_of_lt_le ?_ ?_
  · rw [Nat.mul_comm]; omega
  · rw [Nat.succ_mul, Nat.mul_comm]; omega
theorem carryOk_treeCarry (answers : Answers) (lay : Layer) (tree leaf : Nat) :
    leaf % famGrp lay ≠ 0 → treeCarry answers lay tree leaf = famCoefL answers lay tree (famOf lay leaf) := by
  intro h
  have h0 : leaf ≠ 0 := by rintro rfl; simp at h
  unfold treeCarry leafCarryOut
  rw [if_neg h0, famOf_pred h]
def treeRowsP (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    M (List Digest × List Digest × List Digest) :=
  (List.range (2 ^ height lay)).foldlM
    (fun (state : List Digest × List Digest × List Digest) leaf => do
      let ((root, values), carry) ← buildLeafPF lay tree leaf (if leaf = selected then digits else []) state.2.2
      pure (state.1 ++ [root], (if leaf = selected then values else state.2.1), carry)) ([], [], [])
theorem buildTreeP_factor (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    buildTreeP lay tree selected digits = (do
      let rows ← treeRowsP lay tree selected digits
      let levels ← buildLevelsBelow 3 lay.val tree (height lay) rows.1
      pure (levels, rows.2.1)) := by
  rfl
/-- C2: `buildLevelsBelow` builds the levels below the root of `lowerLevels`. -/
theorem buildLevels_eq_below (tag lay tree h : Nat) (leaves : List Digest) (hh : 1 ≤ h) :
    lowerLevels lay tree h leaves = (buildLevelsBelow tag lay tree h leaves >>= fun levels => do
      let nodes ← lowerLevel lay tree h h (levels.getD (h - 1) [])
      pure (levels ++ [nodes])) := by
  unfold lowerLevels buildLevelsBelow
  rw [show h = (h - 1) + 1 from by omega, ← List.range'_append_1, List.foldlM_append]
  simp only [show 1 + (h - 1) = h - 1 + 1 by omega, List.range'_one, List.foldlM_cons, List.foldlM_nil, bind_pure,
    Nat.add_sub_cancel]
theorem eval_buildLevelsBelow (answers : Answers) (tag lay tree h : Nat) (leaves : List Digest)
    (hlen : leaves.length = 2 ^ h) (hh : 1 ≤ h) :
    evalWithAnswerFn answers (buildLevelsBelow tag lay tree h leaves) =
      (evalWithAnswerFn answers (lowerLevels lay tree h leaves)).take h := by
  have hfull := (eval_lowerLevels_correct answers lay tree h leaves hlen).1.1
  rw [buildLevels_eq_below tag lay tree h leaves hh] at hfull ⊢
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure] at hfull ⊢
  generalize evalWithAnswerFn answers (buildLevelsBelow tag lay tree h leaves) = L at hfull ⊢
  simp only [List.length_append, List.length_singleton] at hfull
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
theorem getD_take_of_lt {α : Type} (L : List α) {n j : Nat} (hj : j < n) (d : α) :
    (L.take n).getD j d = L.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]
theorem topPair_take (lay : Layer) (L : List (List Digest)) : topPair lay (L.take (height lay)) = topPair lay L := by
  have : 1 ≤ height lay := by fin_cases lay <;> decide
  unfold topPair
  rw [getD_take_of_lt L (by omega)]
theorem map_range_take_path (L : List (List Digest)) (h : Nat) (f : Nat → Nat) :
    (List.range h).map (fun j => ((L.take h).getD j []).getD (f j) 0) =
      (List.range h).map (fun j => (L.getD j []).getD (f j) 0) :=
  List.map_congr_left fun j hj => by rw [getD_take_of_lt L (List.mem_range.mp hj)]
theorem treeValue_take (L : List (List Digest)) {n j : Nat} (hj : j < n) (x : Nat) :
    treeValue (L.take n) j x = treeValue L j x := by
  unfold treeValue
  rw [getD_take_of_lt L hj]
def TreeRowsP (answers : Answers) (lay : Layer) (tree selected : Nat) (digits : List Nat) (done : Nat)
    (rows : List Digest × List Digest × List Digest) : Prop :=
  rows.1.length = done ∧ (∀ j, j < done → rows.1.getD j 0 = wotsRoot answers lay tree j) ∧
    rows.2.1 = (if selected < done then (List.range (chainCount lay)).map (wotsValue answers lay tree selected digits)
      else []) ∧
    rows.2.2 = treeCarry answers lay tree done
theorem eval_treeRowsP (answers : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) :
    TreeRowsP answers lay tree selected digits (2 ^ height lay)
      (evalWithAnswerFn answers (treeRowsP lay tree selected digits)) := by
  unfold treeRowsP
  refine eval_foldlM_range_inv answers (2 ^ height lay) _ (TreeRowsP answers lay tree selected digits)
    ([], [], []) (by simp [TreeRowsP, treeCarry]) ?_
  intro done _ rows hrows
  rcases hrows with ⟨hlen, hroot, hvalues, hc⟩
  have hv : Cost.ValidDigits lay (if done = selected then digits else []) := by
    split
    · exact hvalid
    · exact Cost.validDigits_nil lay
  simp only [evalWithAnswerFn_bind, hc,
    buildLeafPF_result answers hlay tree done _ hv _ (carryOk_treeCarry answers lay tree done),
    evalWithAnswerFn_pure]
  refine ⟨by simp [hlen], ?_, ?_, ?_⟩
  · intro j hj
    rw [getD_append_singleton, hlen]
    by_cases hjd : j < done
    · rw [if_pos hjd]; exact hroot j hjd
    · have he : j = done := by omega
      subst j
      simp
  · by_cases hs : done = selected
    · subst hs; simp
    · have hs' : selected < done + 1 ↔ selected < done := by omega
      simp only [if_neg hs, hvalues, hs']
  · show leafCarryOut answers lay tree done = treeCarry answers lay tree (done + 1)
    unfold treeCarry
    rw [if_neg (show done + 1 ≠ 0 by omega), Nat.add_sub_cancel]
theorem eval_buildTreeP_result (answers : Answers) {lay : Layer} (hlay : lay ≠ 0) (tree selected : Nat)
    (digits : List Nat) (hvalid : Cost.ValidDigits lay digits) (hsel : selected < 2 ^ height lay) :
    evalWithAnswerFn answers (buildTreeP lay tree selected digits) =
      ((wotsTree answers lay tree).take (height lay),
        (List.range (chainCount lay)).map (wotsValue answers lay tree selected digits)) := by
  let rows := evalWithAnswerFn answers (treeRowsP lay tree selected digits)
  have hr : TreeRowsP answers lay tree selected digits (2 ^ height lay) rows :=
    eval_treeRowsP answers hlay tree selected digits hvalid
  rcases hr with ⟨hlen, hroot, hvalues, -⟩
  have hroots : rows.1 = (List.range (2 ^ height lay)).map (wotsRoot answers lay tree) :=
    list_eq_range_map _ _ _ hlen hroot
  rw [if_pos hsel] at hvalues
  rw [buildTreeP_factor, evalWithAnswerFn_bind]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (evalWithAnswerFn answers (buildLevelsBelow 3 lay.val tree (height lay) rows.1), rows.2.1) = _
  rw [hroots, hvalues, eval_buildLevelsBelow answers 3 lay.val tree (height lay) _ (by simp)
    (by fin_cases lay <;> decide), wotsTree, if_neg hlay]
/-- Lower layers only: the top tree's nodes are nonce-searched (`T3.Correctness.builtTopTree_correct`). -/
theorem wotsTree_correct (answers : Answers) {lay : Layer} (hl : lay ≠ 0) (tree : Nat) :
    TreeLevelsL answers lay.val tree (height lay)
      ((List.range (2 ^ height lay)).map (wotsRoot answers lay tree)) (height lay) (wotsTree answers lay tree) := by
  unfold wotsTree
  rw [if_neg hl]
  exact eval_lowerLevels_correct answers lay.val tree (height lay) _ (by simp)
theorem wotsTree_leaves (answers : Answers) (lay : Layer) (tree : Nat) :
    (wotsTree answers lay tree).getD 0 [] = (List.range (2 ^ height lay)).map (wotsRoot answers lay tree) := by
  by_cases hl : lay = 0
  · subst hl
    unfold wotsTree
    rw [if_pos rfl]
    exact (eval_buildTopLevels_correct answers _ (by simp [height])).2.1
  · exact (wotsTree_correct answers hl tree).2.1
theorem wotsTree_leaf (answers : Answers) (lay : Layer) (tree leaf : Nat) (hleaf : leaf < 2 ^ height lay) :
    treeValue (wotsTree answers lay tree) 0 leaf = wotsRoot answers lay tree leaf := by
  unfold treeValue
  rw [wotsTree_leaves]
  simp [List.getD_eq_getElem, hleaf]
theorem eval_wots_chains_honest (answers : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (values : Fin (chainCount lay) → Digest)
    (hvalues : ∀ i, values i = wotsValue answers lay tree leaf digits i.val) :
    evalWithAnswerFn answers ((List.finRange (chainCount lay)).mapM fun i =>
      chainW lay tree leaf i.val (digits.getD i.val 0)
        (maxDigit lay i.val - digits.getD i.val 0) (values i)) =
      (List.range (chainCount lay)).map (wotsEnd answers lay tree leaf) := by
  rw [eval_mapM]
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.length_map, List.length_finRange] at hi
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, hvalues, Fin.val_cast, Fin.val_mk]
  exact wotsValue_completes answers lay tree leaf digits hvalid i hi
def builtPair (answers : Answers) (lay : Layer) (tree : Nat) : Digest × Digest :=
  topPair lay (wotsTree answers lay tree)
theorem height_pos (lay : Layer) : 1 ≤ height lay := by fin_cases lay <;> decide
theorem eval_recoverLayerPair_honest (answers : Answers) (sig : Signature) (index : Nat)
    (lay : Layer) (hl : lay ≠ 0) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (hvalues : ∀ i, (sig.layers lay).values i =
      wotsValue answers lay (route index lay).2 (route index lay).1 digits i.val)
    (hpath : ∀ j, (sig.layers lay).path j = treeValue (wotsTree answers lay (route index lay).2)
      j.val ((route index lay).1 / 2 ^ j.val ^^^ 1)) :
    evalWithAnswerFn answers (recoverLayerPair sig index lay digits) =
      builtPair answers lay (route index lay).2 := by
  have hh := height_pos lay
  have hleafB := route_leaf_bound index lay
  have hp := eval_merklePathL answers lay.val (route index lay).2 (height lay) 0 (height lay - 1)
    (route index lay).1 (wotsTree answers lay (route index lay).2)
    ((List.range (2 ^ height lay)).map (wotsRoot answers lay (route index lay).2))
    (wotsTree_correct answers hl (route index lay).2) (by omega)
    (by simpa using hleafB) (fun j => (sig.layers lay).path (Fin.castLE (Nat.sub_le _ _) j))
    (fun j => by rw [hpath, Nat.zero_add]; rfl)
  rw [wotsTree_leaf answers lay _ _ hleafB] at hp
  simp only [Nat.zero_add] at hp
  have hother : (sig.layers lay).path (topLevel lay) =
      treeValue (wotsTree answers lay (route index lay).2) (height lay - 1)
        ((route index lay).1 / 2 ^ (height lay - 1) ^^^ 1) := hpath (topLevel lay)
  have hq : (route index lay).1 / 2 ^ (height lay - 1) < 2 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    have he : 2 ^ (height lay - 1) * 2 = 2 ^ height lay := by
      rw [← pow_succ, Nat.sub_add_cancel hh]
    rw [Nat.mul_comm, he]
    exact hleafB
  have hq2 : (route index lay).1 / 2 ^ (height lay - 1) = 0 ∨
      (route index lay).1 / 2 ^ (height lay - 1) = 1 := by
    generalize (route index lay).1 / 2 ^ (height lay - 1) = q at hq ⊢
    omega
  have hlr : evalWithAnswerFn answers (lowerLeafHash lay (route index lay).2 (route index lay).1
      ((List.range (chainCount lay)).map (wotsEnd answers lay (route index lay).2 (route index lay).1))) =
      wotsRoot answers lay (route index lay).2 (route index lay).1 := rfl
  unfold recoverLayerPair
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, Nat.sub_sub]
  rw [eval_wots_chains_honest answers lay _ _ digits hvalid _ hvalues, hlr, hp, hother]
  unfold builtPair topPair
  rcases hq2 with h | h <;> rw [h] <;> rfl
def TopSearchesSucceedBC (answers : Answers) : Prop :=
  ∀ index, index < 2 ^ 31 → ∀ msg : LayerMsg, ∃ found,
    evalWithAnswerFn answers (layerCounterSearch (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2
      (route index (Fin.ofNat 4 0)).1 msg 0 (searchLimit (Fin.ofNat 4 0))) = some found
theorem signLayersBC_length (answers : Answers) (cache : Cache) (index : Nat) :
    ∀ n msg pieces, evalWithAnswerFn answers (signLayersBC cache index n msg) = some pieces →
      pieces.length = n := by
  intro n
  induction n with
  | zero =>
      intro msg pieces he
      simp only [signLayersBC, evalWithAnswerFn_pure, Option.some.injEq] at he
      subst pieces
      rfl
  | succ n ih =>
      intro msg pieces he
      by_cases hn0 : n = 0
      · subst n
        unfold signLayersBC at he
        rw [evalWithAnswerFn_bind] at he
        rw [if_pos rfl, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at he
        subst pieces
        rfl
      · simp only [signLayersBC, evalWithAnswerFn_bind] at he
        simp only [hn0, if_false] at he
        split at he
        · rename_i counter digits hs
          have hlim := searchLimit_le (Fin.ofNat 4 n)
          have hd := (layerCounterSearch_some answers _ _ _ _
            _ 0 counter digits (by unfold counterLimit at hlim; omega) hs).2.2
          have hvalid := Cost.validDigits_decode hd
          simp only [evalWithAnswerFn_bind] at he
          generalize evalWithAnswerFn answers (buildTreeP (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
            (route index (Fin.ofNat 4 n)).1 digits) = built at he
          obtain ⟨levels, values⟩ := built
          simp only [evalWithAnswerFn_bind] at he
          cases hp : evalWithAnswerFn answers (signLayersBC cache index n
            (.pair (topPair (Fin.ofNat 4 n) levels).1 (topPair (Fin.ofNat 4 n) levels).2)) with
          | none => simp only [hp, evalWithAnswerFn_pure, reduceCtorEq] at he
          | some previous =>
              simp only [hp, evalWithAnswerFn_pure, Option.some.injEq] at he
              subst pieces
              simp [ih _ previous hp]
        · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
theorem digestSearch_some_good (answers : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter found output, counter + fuel ≤ 2 ^ 32 →
      evalWithAnswerFn answers (digestSearch rho message counter fuel) = some (found, output) →
      counter ≤ found.toNat ∧ found.toNat < counter + fuel ∧
        evalWithAnswerFn answers (digest rho message found) = output ∧
        producerAdmissible output = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter found output _ he
      simp [digestSearch] at he
  | succ fuel ih =>
      intro counter found output hlimit he
      simp only [digestSearch, evalWithAnswerFn_bind] at he
      split at he
      · rename_i hgood
        simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hcount : (BitVec.ofNat 32 counter).toNat = counter := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact ⟨by rw [hcount], by rw [hcount]; omega, rfl, hgood⟩
      · obtain ⟨hlo, hhi, hrest⟩ := ih (counter + 1) found output (by omega) he
        exact ⟨by omega, by omega, hrest⟩
theorem expand_implies_verify (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (w : Witness)
    (he : evalWithAnswerFn answers (expand message pk sig) = some w) :
    evalWithAnswerFn answers (verify message pk w) = true := by
  simp only [expand, evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (digestSearch sig.rho message 0 attemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn answers (expandLayersBC sig (digestIndex output) 4
          (.pair (evalWithAnswerFn answers (recoverFts sig (digestIndex output) output)).1
            (evalWithAnswerFn answers (recoverFts sig (digestIndex output) output)).2)) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some layers =>
          obtain ⟨root, counters⟩ := layers
          simp only [hl] at he
          split at he
          · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
          · rename_i hroot
            have hroot : root = pk := by simpa using hroot
            simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
            subst w
            obtain ⟨_, hcounter, houtput, hprod⟩ := digestSearch_some_good answers sig.rho message
              attemptLimit 0 counter output (by decide) hd
            have hadm := admissible_of_producer hprod
            have hnot : ¬counter.toNat ≥ attemptLimit := by omega
            have hverified := (expandLayersBC_verified answers sig
              (digestIndex output) 4 (by decide) _ root counters hl).2
              ⟨sig, counter, fun lay => counters.getD lay.val 0⟩ rfl (fun _ _ => rfl)
            simp only [verify, hnot, ite_false, evalWithAnswerFn_bind, houtput, hadm,
              Bool.not_true, Bool.false_eq_true, hverified, evalWithAnswerFn_pure, hroot,
              beq_self_eq_true]
end ClaudeWCT.WCT9
end
-- ==== merged from ClaudeWCT_WCT9_Limits ====
section

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
def digestAttemptLimit : Nat := 2 ^ 21
/- The verifier can accept the full serialized counter range without changing
the signer's bounded search.  The machine normalizes the upper padding word. -/
def digestVerifyWindow : Nat := 2 ^ 32
theorem digestAttemptLimit_eq : digestAttemptLimit = 2097152 := by
  norm_num [digestAttemptLimit]
theorem digestAttemptLimit_eq_two_mul : digestAttemptLimit = 2 * SigGolfCandidate.T3.attemptLimit := by
  norm_num [digestAttemptLimit, SigGolfCandidate.T3.attemptLimit]
theorem digestAttemptLimit_le : digestAttemptLimit ≤ 2 ^ 32 := by
  norm_num [digestAttemptLimit]
theorem attemptLimit_le_digestAttemptLimit : SigGolfCandidate.T3.attemptLimit ≤ digestAttemptLimit := by
  norm_num [digestAttemptLimit, SigGolfCandidate.T3.attemptLimit]
def signPayloadWith (limit : Nat) (cache : Cache) (message : Message) : M (Option Signature) := do
  let rho ← privateNonce message
  let some (_, output) ← digestSearch rho message 0 limit | pure none
  let index := digestIndex output
  let state ← (List.finRange 9).foldlM
    (fun (state : List Opening × List (Digest × Digest)) coord => do
      let selected := child output coord
      let (levels, values) ← buildCoordinateF index coord selected (rank output coord) (prevPair ftsStart state.2)
      let path := (List.range 7).map fun level =>
        (levels.getD level []).getD (selected.val / 2 ^ level ^^^ 1) 0
      let opening : Opening := ⟨fun i => values.getD i.val 0, fun i => path.getD i.val 0⟩
      pure (state.1 ++ [opening],
        state.2 ++ [((levels.getD 6 []).getD 0 0, (levels.getD 6 []).getD 1 0)])) ([], [])
  let top := prevPair ftsStart state.2
  let some layers ← signLayersBC cache index 4 (.pair top.1 top.2) | pure none
  pure (some ⟨rho, fun coord => state.1.getD coord.val ⟨fun _ => 0, fun _ => 0⟩,
    fun lay => piecesSignature lay (layers.getD lay.val ([], []))⟩)
def signWith (limit : Nat) (cache : Cache) (message : Message) : M (Option Signature) := do
  let tag ← privateMac cache.region
  if tag ≠ cache.tag then return none
  signPayloadWith limit cache message
def expandWith (limit : Nat) (message : Message) (pk : Digest) (sig : Signature) :
    M (Option Witness) := do
  let some (counter, output) ← digestSearch sig.rho message 0 limit | pure none
  let index := digestIndex output
  let top ← recoverFts sig index output
  let some (root, counters) ← expandLayersBC sig index 4 (.pair top.1 top.2) | pure none
  if root ≠ pk then return none
  pure (some ⟨sig, counter, fun lay => counters.getD lay.val 0⟩)
def verifyWith (limit : Nat) (message : Message) (pk : Digest) (w : Witness) : M Bool := do
  if w.digestCounter.toNat ≥ limit then return false
  let output ← digest w.signature.rho message w.digestCounter
  if !admissible output then return false
  let index := digestIndex output
  let top ← recoverFts w.signature index output
  let some root ← verifyLayersBC w index 4 (.pair top.1 top.2) | pure false
  pure (root == pk)
theorem signPayloadWith_attemptLimit :
    signPayloadWith SigGolfCandidate.T3.attemptLimit = signPayload := rfl
theorem signWith_attemptLimit : signWith SigGolfCandidate.T3.attemptLimit = sign := rfl
theorem expandWith_attemptLimit : expandWith SigGolfCandidate.T3.attemptLimit = expand := rfl
theorem verifyWith_attemptLimit : verifyWith SigGolfCandidate.T3.attemptLimit = verify := rfl
/-! ### H2: the compact signature omits the top 16 bits (112..127, T51; #938 img-v6: 19 bits 109..127) of the top
layer's level-11 sibling. Expand recovers everything up to the level-11 node `v` with those bits zero, then searches
the 2^16 completions against the public key. The witness carries the completed signature, so verify is unchanged. -/
def setTop (d : Digest) (c : Nat) : Digest := BitVec.ofNat 128 (d.toNat % 2 ^ 112 + c % 2 ^ 16 * 2 ^ 112)
def fillLayer (lay : Layer) (ls : LayerSignature lay) (c : Nat) : LayerSignature lay :=
  ⟨ls.values, fun j => if lay.val = 0 ∧ j.val = 11 then setTop (ls.path j) c else ls.path j⟩
def fillTop (sig : Signature) (c : Nat) : Signature :=
  ⟨sig.rho, sig.openings, fun lay => fillLayer lay (sig.layers lay) c⟩
def proj (sig : Signature) : Signature := fillTop sig 0
def topJ : Fin (height 0) := ⟨11, by decide⟩
def topSib (sig : Signature) : Digest := (sig.layers 0).path topJ
def topStep (sig : Signature) (index : Nat) (value : Digest) (j : Fin (height 0)) : M Digest := do
  let other := (sig.layers 0).path j
  let pair := if (route index 0).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
  nodeHash 3 (0 : Layer).val (route index 0).2 (2 ^ (height 0 - j.val - 1) + (route index 0).1 / 2 ^ (j.val + 1))
    pair.1 pair.2
def topNode (index : Nat) (value other : Digest) : M Digest := do
  let pair := if (route index 0).1 / 2 ^ topJ.val % 2 = 0 then (value, other) else (other, value)
  nodeHash 3 (0 : Layer).val (route index 0).2 (2 ^ (height 0 - topJ.val - 1) + (route index 0).1 / 2 ^ (topJ.val + 1))
    pair.1 pair.2
def topEnds (sig : Signature) (index : Nat) (digits : List Nat) : M (List Digest) :=
  (List.finRange (chainCount 0)).mapM fun i =>
    SigGolfCandidate.T3.layChain 0 (route index 0).2 (route index 0).1 i.val (digits.getD i.val 0)
      (maxDigit 0 i.val - digits.getD i.val 0) ((sig.layers 0).values i)
/-- The top layer folded to its level-11 node (the input of the last node hash). -/
def topFold (sig : Signature) (index : Nat) (digits : List Nat) : M Digest := do
  let ends ← topEnds sig index digits
  let value ← SigGolfCandidate.T3.leafHash 0 (route index 0).2 (route index 0).1 ends
  ((List.finRange (height 0)).take 11).foldlM (topStep sig index) value
/-- Top-bytes layer: one step of the top path with the node nonce search (heights 1..11); the accumulator
collects the nonces (height `j + 1` at position `j`). -/
def topStepN (sig : Signature) (index : Nat) (acc : Digest × List Nat) (j : Fin (height 0)) :
    M (Digest × List Nat) := do
  let other := (sig.layers 0).path j
  let pair := if (route index 0).1 / 2 ^ j.val % 2 = 0 then (acc.1, other) else (other, acc.1)
  let found ← topNodeAt (j.val + 1) (2 ^ (height 0 - j.val - 1) + (route index 0).1 / 2 ^ (j.val + 1)) pair.1 pair.2
  pure (found.2, acc.2 ++ [found.1])
/-- Top-bytes layer: the top layer folded to its level-11 node, with the 11 re-derived node nonces. -/
def topFoldN (sig : Signature) (index : Nat) (digits : List Nat) : M (Digest × List Nat) := do
  let ends ← topEnds sig index digits
  let value ← SigGolfCandidate.T3.leafHash 0 (route index 0).2 (route index 0).1 ends
  ((List.finRange (height 0)).take 11).foldlM (topStepN sig index) (value, [])
/-- `expandLayersBC` that also returns the top layer's level-11 node and takes the top sibling as an argument. -/
def expandLayersT (sig : Signature) (index : Nat) (other : Digest) :
    Nat → LayerMsg → M (Option (Digest × Digest × List (BitVec 32)))
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let some (counter, digits) ← layerCounterSearch lay tree leaf msg 0 (searchLimit lay) | pure none
      if n = 0 then
        let v ← topFold sig index digits
        let root ← topNode index v other
        pure (some (v, root, [counter]))
      else
        let pair ← recoverLayerPair sig index lay digits
        let some (v, root, counters) ← expandLayersT sig index other n (.pair pair.1 pair.2) | pure none
        pure (some (v, root, counters ++ [counter]))
def searchFuel : Nat := 65535
/-- Candidates `c, c + 1, ...` for the omitted bits; the first whose root is `pk`. -/
def searchTop (index : Nat) (v sib pk : Digest) : Nat → Nat → M (Option Nat)
  | 0, _ => pure none
  | fuel + 1, c => do
      let root ← topNode index v (setTop sib c)
      if root = pk then pure (some c) else searchTop index v sib pk fuel (c + 1)
/-- The H2 expander on a signature whose omitted bits are ignored (read as zero). -/
def expandS (limit : Nat) (message : Message) (pk : Digest) (sig : Signature) :
    M (Option (HashOutput × Witness)) := do
  let sig0 := proj sig
  let some (counter, output) ← digestSearch sig0.rho message 0 limit | pure none
  let index := digestIndex output
  let top ← recoverFts sig0 index output
  let some (v, root, counters) ← expandLayersT sig0 index (topSib sig0) 4 (.pair top.1 top.2) | pure none
  if root = pk then return some (output, ⟨sig0, counter, fun lay => counters.getD lay.val 0⟩)
  let some c ← searchTop index v (topSib sig0) pk searchFuel 1 | pure none
  pure (some (output, ⟨fillTop sig0 c, counter, fun lay => counters.getD lay.val 0⟩))
namespace Rev3
def signPayload (cache : Cache) (message : Message) : M (Option Signature) :=
  signPayloadWith digestAttemptLimit cache message
def sign (cache : Cache) (message : Message) : M (Option Signature) :=
  signWith digestAttemptLimit cache message
def expand (message : Message) (pk : Digest) (sig : Signature) : M (Option Witness) :=
  Option.map Prod.snd <$> expandS digestAttemptLimit message pk sig
def verify (message : Message) (pk : Digest) (w : Witness) : M Bool :=
  verifyWith digestAttemptLimit message pk w
def keygen : M (Digest × Cache) := ClaudeWCT.WCT9.keygen
theorem sign_eq (cache : Cache) (message : Message) : sign cache message = (do
    let tag ← privateMac cache.region
    if tag ≠ cache.tag then return none
    signPayload cache message) := rfl
end Rev3
end ClaudeWCT.WCT9
end
-- ==== merged from ClaudeWCT_WCT9_Forest ====
section

section
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def openingStep (index : Nat) (output : HashOutput) (state : List Opening × List (Digest × Digest))
    (coord : Coord) : M (List Opening × List (Digest × Digest)) := do
  let selected := child output coord
  let (levels, values) ← buildCoordinateF index coord selected (rank output coord) (prevPair ftsStart state.2)
  let path := (List.range 7).map fun level =>
    (levels.getD level []).getD (selected.val / 2 ^ level ^^^ 1) 0
  let opening : Opening := ⟨fun i => values.getD i.val 0, fun i => path.getD i.val 0⟩
  pure (state.1 ++ [opening],
    state.2 ++ [((levels.getD 6 []).getD 0 0, (levels.getD 6 []).getD 1 0)])
theorem signPayload_rows (cache : Cache) (message : Message) : signPayload cache message = (do
    let rho ← privateNonce message
    let some (_, output) ← digestSearch rho message 0 attemptLimit | pure none
    let index := digestIndex output
    let state ← (List.finRange 9).foldlM (openingStep index output) ([], [])
    let top := prevPair ftsStart state.2
    let some layers ← signLayersBC cache index 4 (.pair top.1 top.2) | pure none
    pure (some ⟨rho, fun coord => state.1.getD coord.val ⟨fun _ => 0, fun _ => 0⟩,
      fun lay => piecesSignature lay (layers.getD lay.val ([], []))⟩)) := rfl
theorem eval_openingStep (answers : Answers) (index : Nat) (output : HashOutput)
    (state : List Opening × List (Digest × Digest)) (coord : Coord)
    (hprev : prevPair ftsStart state.2 = ftsPrev answers index coord.val) :
    evalWithAnswerFn answers (openingStep index output state coord) =
      (state.1 ++ [expectedOpening answers index output coord],
        state.2 ++ [coordinatePair answers index coord]) := by
  have hroot := built_pair answers index coord (child output coord) (rank output coord)
  unfold openingStep expectedOpening
  rw [hprev]
  simp only [evalWithAnswerFn_bind]
  generalize evalWithAnswerFn answers
    (buildCoordinateF index coord (child output coord) (rank output coord)
      (ftsPrev answers index coord.val)) = built at hroot ⊢
  obtain ⟨levels, values⟩ := built
  simp only [evalWithAnswerFn_pure] at hroot ⊢
  rw [← hroot]
  rfl
def SignerRows (answers : Answers) (index : Nat) (output : HashOutput) (done : Nat)
    (state : List Opening × List (Digest × Digest)) : Prop :=
  state.1.length = done ∧ state.2.length = done ∧
    (∀ c : Coord, c.val < done →
      state.1.getD c.val ⟨fun _ => 0, fun _ => 0⟩ = expectedOpening answers index output c) ∧
    (∀ c : Coord, c.val < done → state.2.getD c.val (0, 0) = coordinatePair answers index c)
theorem signerRows_step (answers : Answers) (index : Nat) (output : HashOutput) (c : Coord)
    (state : List Opening × List (Digest × Digest)) (hrows : SignerRows answers index output c.val state) :
    SignerRows answers index output (c.val + 1)
      (state.1 ++ [expectedOpening answers index output c],
        state.2 ++ [coordinatePair answers index c]) := by
  rcases hrows with ⟨h1, h2, h3, h4⟩
  refine ⟨by simp [h1], by simp [h2], ?_, ?_⟩
  · intro d hd
    rw [getD_append_singleton, h1]
    by_cases hdc : d.val < c.val
    · rw [if_pos hdc]; exact h3 d hdc
    · have he : d = c := Fin.ext (by omega)
      subst d
      simp
  · intro d hd
    rw [getD_append_singleton, h2]
    by_cases hdc : d.val < c.val
    · rw [if_pos hdc]; exact h4 d hdc
    · have he : d = c := Fin.ext (by omega)
      subst d
      simp
theorem prevPair_of_rows (answers : Answers) (index : Nat) (output : HashOutput) (d : Nat) (hd : d ≤ 9)
    (state : List Opening × List (Digest × Digest)) (hrows : SignerRows answers index output d state) :
    prevPair ftsStart state.2 = ftsPrev answers index d := by
  rcases hrows with ⟨-, h2, -, h4⟩
  cases d with
  | zero => rw [List.length_eq_zero_iff.mp h2]; rfl
  | succ d =>
    unfold prevPair
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, h2, Nat.add_sub_cancel,
      List.getElem?_eq_getElem (by omega), Option.getD_some, ← List.getD_eq_getElem _ (0, 0) (by omega),
      h4 ⟨d, by omega⟩ (by simp)]
    rfl
theorem prevPair_ofFn (answers : Answers) (index : Nat) :
    prevPair ftsStart (List.ofFn (coordinatePair answers index)) = ftsPrev answers index 9 := by
  unfold prevPair
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
  simp only [List.length_ofFn, List.getElem?_ofFn]
  rfl
theorem eval_signerRows (answers : Answers) (index : Nat) (output : HashOutput) :
    SignerRows answers index output 9
      (evalWithAnswerFn answers ((List.finRange 9).foldlM (openingStep index output) ([], []))) := by
  have h := eval_foldlM_list_inv answers (List.finRange 9) (openingStep index output)
    (SignerRows answers index output) ([], []) (by simp [SignerRows]) (by
      intro i hi state hstate
      have hi9 : i < 9 := by simpa using hi
      simp only [List.getElem_finRange, Fin.cast_mk]
      rw [eval_openingStep _ _ _ _ _ (prevPair_of_rows answers index output i (by omega) state hstate)]
      exact signerRows_step answers index output ⟨i, hi9⟩ state hstate)
  simpa only [List.length_finRange] using h
theorem signerRows_roots (answers : Answers) (index : Nat) (output : HashOutput)
    (state : List Opening × List (Digest × Digest)) (hrows : SignerRows answers index output 9 state) :
    state.2 = List.ofFn (coordinatePair answers index) := by
  apply List.ext_getElem (by simp [hrows.2.1])
  intro i hi hj
  have hi9 : i < 9 := by simpa using hj
  rw [← List.getD_eq_getElem _ ((0, 0) : Digest × Digest) hi, hrows.2.2.2 ⟨i, hi9⟩ hi9, List.getElem_ofFn]
theorem keygen_correct (answers : Answers) :
    KeygenCorrect answers (evalWithAnswerFn answers keygen) :=
  SigGolfCandidate.T3.Correctness.keygen_correct answers
end ClaudeWCT.WCT9
end
section
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def forestRows (index : Nat) (output : HashOutput) : M (List Opening × List (Digest × Digest)) :=
  (List.finRange 9).foldlM (openingStep index output) ([], [])
/-- The FTS part of signing (nested FTS r1-1): the 9 openings and the last top pair (the L3 message). -/
def signForest (index : Nat) (output : HashOutput) : M (List Opening × (Digest × Digest)) := do
  let state ← forestRows index output
  pure (state.1, prevPair ftsStart state.2)
def assembledSignature (rho : Digest) (openings : List Opening) (pieces : List Pieces) : Signature :=
  ⟨rho, fun coord => openings.getD coord.val ⟨fun _ => 0, fun _ => 0⟩,
    fun lay => piecesSignature lay (pieces.getD lay.val ([], []))⟩
@[simp] theorem assembledSignature_rho (rho : Digest) (openings : List Opening) (pieces : List Pieces) :
    (assembledSignature rho openings pieces).rho = rho := rfl
@[simp] theorem assembledSignature_openings (rho : Digest) (openings : List Opening)
    (pieces : List Pieces) (coord : Coord) :
    (assembledSignature rho openings pieces).openings coord =
      openings.getD coord.val ⟨fun _ => 0, fun _ => 0⟩ := rfl
/-- Honest L3 message (nested FTS r1-1): the top pair of coordinate 8. -/
def honestTop (answers : Answers) (index : Nat) : Digest × Digest := ftsPrev answers index 9
theorem signPayloadWith_eq (limit : Nat) (cache : Cache) (message : Message) :
    signPayloadWith limit cache message = (do
      let rho ← privateNonce message
      let some (_, output) ← digestSearch rho message 0 limit | pure none
      let forest ← signForest (digestIndex output) output
      let some pieces ← signLayersBC cache (digestIndex output) 4 (.pair forest.2.1 forest.2.2) | pure none
      pure (some (assembledSignature rho forest.1 pieces))) := by
  unfold signPayloadWith signForest forestRows
  refine bind_congr fun rho => bind_congr fun found => ?_
  rcases found with _ | ⟨_, output⟩
  · rfl
  · simp only [bind_assoc, pure_bind]
    rfl
theorem signPayload_eq (cache : Cache) (message : Message) :
    signPayload cache message = (do
      let rho ← privateNonce message
      let some (_, output) ← digestSearch rho message 0 SigGolfCandidate.T3.attemptLimit | pure none
      let forest ← signForest (digestIndex output) output
      let some pieces ← signLayersBC cache (digestIndex output) 4 (.pair forest.2.1 forest.2.2) | pure none
      pure (some (assembledSignature rho forest.1 pieces))) :=
  signPayloadWith_eq SigGolfCandidate.T3.attemptLimit cache message
theorem Rev3.signPayload_eq (cache : Cache) (message : Message) :
    Rev3.signPayload cache message = (do
      let rho ← privateNonce message
      let some (_, output) ← digestSearch rho message 0 digestAttemptLimit | pure none
      let forest ← signForest (digestIndex output) output
      let some pieces ← signLayersBC cache (digestIndex output) 4 (.pair forest.2.1 forest.2.2) | pure none
      pure (some (assembledSignature rho forest.1 pieces))) :=
  signPayloadWith_eq digestAttemptLimit cache message
theorem eval_forestRows (answers : Answers) (index : Nat) (output : HashOutput) :
    evalWithAnswerFn answers (forestRows index output) =
      (List.ofFn (expectedOpening answers index output), List.ofFn (coordinatePair answers index)) := by
  have hrows := eval_signerRows answers index output
  unfold forestRows
  generalize evalWithAnswerFn answers ((List.finRange 9).foldlM (openingStep index output) ([], [])) =
    state at hrows ⊢
  have h2 := signerRows_roots answers index output state hrows
  refine Prod.ext ?_ h2
  apply List.ext_getElem (by simp [hrows.1])
  intro i hi hj
  have hi9 : i < 9 := by simpa using hj
  rw [← List.getD_eq_getElem _ ⟨fun _ => 0, fun _ => 0⟩ hi, hrows.2.2.1 ⟨i, hi9⟩ hi9, List.getElem_ofFn]
theorem eval_signForest (answers : Answers) (index : Nat) (output : HashOutput) :
    evalWithAnswerFn answers (signForest index output) =
      (List.ofFn (expectedOpening answers index output), honestTop answers index) := by
  unfold signForest
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_forestRows]
  rw [prevPair_ofFn]
  rfl
theorem signForest_root (answers : Answers) (index : Nat) (output : HashOutput) :
    (evalWithAnswerFn answers (signForest index output)).2 = honestTop answers index := by
  rw [eval_signForest]
theorem signForest_openings (answers : Answers) (index : Nat) (output : HashOutput) (coord : Coord) :
    (evalWithAnswerFn answers (signForest index output)).1.getD coord.val ⟨fun _ => 0, fun _ => 0⟩ =
      expectedOpening answers index output coord := by
  rw [eval_signForest]
  simp only
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact coord.isLt), List.getElem_ofFn]
theorem signForest_length (answers : Answers) (index : Nat) (output : HashOutput) :
    (evalWithAnswerFn answers (signForest index output)).1.length = 9 := by
  rw [eval_signForest]
  simp only [List.length_ofFn]
theorem assembled_forest_recovery (answers : Answers) (rho : Digest) (index : Nat) (output : HashOutput)
    (pieces : List Pieces) :
    evalWithAnswerFn answers (recoverFts
      (assembledSignature rho (evalWithAnswerFn answers (signForest index output)).1 pieces) index output) =
      (evalWithAnswerFn answers (signForest index output)).2 := by
  rw [recoverFts_honest answers _ index output (fun coord => by
    rw [assembledSignature_openings, signForest_openings]), signForest_root]
  rfl
theorem expandWith_implies_verifyWith (limit : Nat) (hlimit : limit ≤ 2 ^ 32) (answers : Answers)
    (message : Message) (pk : Digest) (sig : Signature) (w : Witness)
    (he : evalWithAnswerFn answers (expandWith limit message pk sig) = some w) :
    evalWithAnswerFn answers (verifyWith limit message pk w) = true := by
  simp only [expandWith, evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (digestSearch sig.rho message 0 limit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn answers (expandLayersBC sig (digestIndex output) 4
          (.pair (evalWithAnswerFn answers (recoverFts sig (digestIndex output) output)).1
            (evalWithAnswerFn answers (recoverFts sig (digestIndex output) output)).2)) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some layers =>
          obtain ⟨root, counters⟩ := layers
          simp only [hl] at he
          split at he
          · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
          · rename_i hroot
            have hroot : root = pk := by simpa using hroot
            simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
            subst w
            obtain ⟨_, hcounter, houtput, hprod⟩ := digestSearch_some_good answers sig.rho message
              limit 0 counter output (by omega) hd
            have hadm := admissible_of_producer hprod
            have hnot : ¬counter.toNat ≥ limit := by omega
            have hverified := (expandLayersBC_verified answers sig
              (digestIndex output) 4 (by decide) _ root counters hl).2
              ⟨sig, counter, fun lay => counters.getD lay.val 0⟩ rfl (fun _ _ => rfl)
            simp only [verifyWith, hnot, ite_false, evalWithAnswerFn_bind, houtput, hadm,
              Bool.not_true, Bool.false_eq_true, hverified, evalWithAnswerFn_pure, hroot,
              beq_self_eq_true]
theorem digestSearch_none_iff (answers : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter,
      evalWithAnswerFn answers (digestSearch rho message counter fuel) = none ↔
      ∀ offset, offset < fuel → producerAdmissible (evalWithAnswerFn answers
        (digest rho message (BitVec.ofNat 32 (counter + offset)))) = false := by
  intro fuel
  induction fuel with
  | zero => intro counter; simp [digestSearch]
  | succ fuel ih =>
      intro counter
      simp only [digestSearch, evalWithAnswerFn_bind]
      split
      · rename_i hgood
        simp only [evalWithAnswerFn_pure, reduceCtorEq, false_iff]
        intro hall
        have := hall 0 (by omega)
        simp only [Nat.add_zero, hgood, Bool.true_eq_false] at this
      · rename_i hbad
        have hbad : producerAdmissible (evalWithAnswerFn answers
          (digest rho message (BitVec.ofNat 32 counter))) = false := by simpa using hbad
        rw [ih]
        constructor
        · intro hall offset hoff
          cases offset with
          | zero => simpa using hbad
          | succ offset =>
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hall offset (by omega)
        · intro hall offset hoff
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hall (offset + 1) (by omega)
theorem verifyWith_counter_ge (limit : Nat) (answers : Answers) (message : Message) (pk : Digest) (w : Witness)
    (h : limit ≤ w.digestCounter.toNat) : evalWithAnswerFn answers (verifyWith limit message pk w) = false := by
  simp only [verifyWith, ge_iff_le, h, ite_true, evalWithAnswerFn_pure]
theorem verifyWith_inadmissible (limit : Nat) (answers : Answers) (message : Message) (pk : Digest) (w : Witness)
    (h : admissible (evalWithAnswerFn answers (digest w.signature.rho message w.digestCounter)) = false) :
    evalWithAnswerFn answers (verifyWith limit message pk w) = false := by
  by_cases hc : limit ≤ w.digestCounter.toNat
  · exact verifyWith_counter_ge limit answers message pk w hc
  · simp only [verifyWith, ge_iff_le, hc, ite_false, evalWithAnswerFn_bind, h, Bool.not_false, ite_true,
      evalWithAnswerFn_pure]
end ClaudeWCT.WCT9
end
end
-- ==== merged from ClaudeWCT_WCT9_Domains ====
section

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
theorem header_byte1 (tag lay tree position index : Nat) :
    (header tag lay tree position index).toNat / 2 ^ 8 % 256 = tag % 256 := by
  rw [header_toNat]
  have := Nat.mod_lt tag (show 0 < 256 by decide)
  have := Nat.mod_lt lay (show 0 < 256 by decide)
  split <;> omega
theorem header_byte2 (tag lay tree position index : Nat) :
    (header tag lay tree position index).toNat / 2 ^ 16 % 256 = lay % 256 := by
  rw [header_toNat]
  have := Nat.mod_lt tag (show 0 < 256 by decide)
  have := Nat.mod_lt lay (show 0 < 256 by decide)
  split <;> omega
theorem ftsChainHeaderP_firstByte (index coord selected chain step : Nat) (high : BitVec 64) :
    (ftsChainHeaderP index coord selected chain step high).toNat % 256 = 128 + 4 * (chain % 8) := by
  rw [ftsChainHeaderP_toNat, ← ftsChainLow_byte0 index coord selected chain step]
  omega
theorem ftsChainHeaderP_ne_header (index coord selected chain step : Nat) (high : BitVec 64)
    (tag lay tree position idx : Nat) :
    ftsChainHeaderP index coord selected chain step high ≠ header tag lay tree position idx := by
  intro h
  have hc := ftsChainHeaderP_firstByte index coord selected chain step high
  rw [h, header_firstByte] at hc
  omega
theorem chainHeader_low_band (lay : Layer) (tree leaf i step : Nat) :
    193 * 2 ^ 56 ≤ ((chainHeader lay tree leaf i step).extractLsb' 0 64).toNat ∧
      ((chainHeader lay tree leaf i step).extractLsb' 0 64).toNat < 194 * 2 ^ 56 := by
  rw [chainHeader_low, chainHeaderFlaggedLow_toNat]
  have hb := chainHeaderLow_band lay tree leaf i step
  split_ifs <;> omega
theorem ftsChainHeaderP_low_ne_chainHeader (index coord selected chain step : Nat) (high : BitVec 64)
    (lay : Layer) (tree leaf i st : Nat) :
    (ftsChainHeaderP index coord selected chain step high).extractLsb' 0 64 ≠
      (chainHeader lay tree leaf i st).extractLsb' 0 64 := by
  intro h
  have hw := chainHeader_low_band lay tree leaf i st
  rw [← h, ftsChainHeaderP_low, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_trans (ftsChainLow_lt ..) (by decide))] at hw
  have := ftsChainLow_lt index coord selected chain step
  omega
theorem ftsChainHeaderP_ne_chainHeader (index coord selected chain step : Nat) (high : BitVec 64)
    (lay : Layer) (tree leaf i st : Nat) :
    ftsChainHeaderP index coord selected chain step high ≠ chainHeader lay tree leaf i st := fun h =>
  ftsChainHeaderP_low_ne_chainHeader index coord selected chain step high lay tree leaf i st
    (congrArg (fun x : BitVec 128 => x.extractLsb' 0 64) h)
theorem ftsLeafHeader_ne_header (index coord selected tag lay tree position idx : Nat) (ht : tag % 256 ≠ 6) :
    ftsLeafHeader index coord selected ≠ header tag lay tree position idx := by
  intro h
  have h1 := ftsLeafHeader_byte1 index coord selected
  rw [h, header_byte1] at h1
  exact ht h1
theorem ftsLeafHeader_ne_chainHeader (index coord selected : Nat) (lay : Layer) (tree leaf i st : Nat) :
    ftsLeafHeader index coord selected ≠ chainHeader lay tree leaf i st := by
  intro h
  have hc := chainHeader_firstByte lay tree leaf i st
  rw [← h, ftsLeafHeader_firstByte] at hc
  omega
theorem ftsLeafHeader_ne_ftsChainHeaderP (index coord selected : Nat) (i k j t s : Nat) (high : BitVec 64) :
    ftsLeafHeader index coord selected ≠ ftsChainHeaderP i k j t s high := by
  intro h
  have hc := ftsChainHeaderP_firstByte i k j t s high
  rw [← h, ftsLeafHeader_firstByte] at hc
  omega
theorem wctNodeHeader_ne_chainHeader (coord index heap : Nat) (lay : Layer) (tree leaf i st : Nat) :
    wctNodeHeader coord index heap ≠ chainHeader lay tree leaf i st := by
  intro h
  by_cases hn : coord < 9 ∧ FtsNew heap
  · have hw := chainHeader_low_band lay tree leaf i st
    rw [← h, wctNodeHeader_low hn.1, if_pos hn.2, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans (ftsNodeLowN_lt ..) (by decide))] at hw
    have := ftsNodeLowN_lt index coord heap
    omega
  · have hc := chainHeader_firstByte lay tree leaf i st
    rw [← h, wctNodeHeader_firstByte, if_neg hn] at hc
    omega
theorem wctNodeHeader_low_ne_chainHeader {coord : Nat} (hk : coord < 9) (index heap : Nat) (lay : Layer)
    (tree leaf i st : Nat) :
    (wctNodeHeader coord index heap).extractLsb' 0 64 ≠ (chainHeader lay tree leaf i st).extractLsb' 0 64 := by
  intro h
  have hw := chainHeader_low_band lay tree leaf i st
  rw [← h, wctNodeHeader_low hk, BitVec.toNat_ofNat] at hw
  have h1 := ftsNodeLowN_lt index coord heap
  have h2 := ftsLeafLow_lt index coord 0
  split at hw <;> omega
theorem wctNodeHeader_ne_header {coord : Nat} (hk : coord < 9) (index heap tag lay tree position idx : Nat)
    (ht : tag % 256 ≠ 6) : wctNodeHeader coord index heap ≠ header tag lay tree position idx := by
  intro h
  by_cases hn : FtsNew heap
  · have h1 := wctNodeHeader_firstByteN hk index hn
    rw [h, header_firstByte] at h1
    obtain ⟨-, h128⟩ := hn; omega
  · have h1 := wctNodeHeader_byte1 hk index heap
    rw [h, header_byte1, if_neg hn] at h1
    exact ht h1
theorem wctNodeHeader_ne_ftsChainHeaderP (coord index heap : Nat) (i k j t s : Nat) (high : BitVec 64) :
    wctNodeHeader coord index heap ≠ ftsChainHeaderP i k j t s high := by
  intro h
  by_cases hn : coord < 9 ∧ FtsNew heap
  · have h1 := wctNodeHeader_byte1 hn.1 index heap
    rw [if_pos hn.2, h, ftsChainHeaderP_toNat] at h1
    unfold ftsChainLow at h1
    have := Nat.mod_lt t (show 0 < 8 by decide)
    have := Nat.mod_lt s (show 0 < 4 by decide)
    have := Nat.mod_lt k (show 0 < 16 by decide)
    have := Nat.mod_lt j (show 0 < 128 by decide)
    omega
  · have hc := ftsChainHeaderP_firstByte i k j t s high
    rw [← h, wctNodeHeader_firstByte, if_neg hn] at hc
    omega
theorem ftsLeafHeader_tweakMarker (index coord selected : Nat) : tweakMarker (ftsLeafHeader index coord selected) = 1 :=
  ftsLeafHeader_firstByte index coord selected
theorem ftsLeafHeader_tweakTag (index coord selected : Nat) : tweakTag (ftsLeafHeader index coord selected) = 6 := by
  unfold tweakTag; have := ftsLeafHeader_byte1 index coord selected; norm_num at this ⊢; omega
theorem wctNodeHeader_tweakMarker (coord index heap : Nat) :
    tweakMarker (wctNodeHeader coord index heap) = if coord < 9 ∧ FtsNew heap then 257 - heap else 1 :=
  wctNodeHeader_firstByte coord index heap
theorem wctNodeHeader_tweakMarker_ne_zero (coord index heap : Nat) : tweakMarker (wctNodeHeader coord index heap) ≠ 0 :=
  wctNodeHeader_firstByte_ne_zero coord index heap
theorem wctNodeHeader_tweakTag {coord : Nat} (hk : coord < 9) (index heap : Nat) :
    tweakTag (wctNodeHeader coord index heap) = if FtsNew heap then 5 else 6 := by
  unfold tweakTag; have := wctNodeHeader_byte1 hk index heap
  by_cases hn : FtsNew heap
  · rw [if_pos hn] at this ⊢; norm_num at this ⊢; omega
  · rw [if_neg hn] at this ⊢; norm_num at this ⊢; omega
theorem ftsChainHeaderP_tweakMarker (index coord selected chain step : Nat) (high : BitVec 64) :
    128 ≤ tweakMarker (ftsChainHeaderP index coord selected chain step high) := by
  unfold tweakMarker; rw [ftsChainHeaderP_firstByte]; omega
theorem ftsLeafHeader_ne_rowTweak (index coord selected : Nat) (lay : Layer) (tree leaf : Nat) :
    ftsLeafHeader index coord selected ≠ rowTweak lay tree leaf :=
  ne_of_tweakTag (by rw [ftsLeafHeader_tweakTag, rowTweak_tag]; decide)
theorem ftsLeafHeader_ne_leafTweak (index coord selected : Nat) (lay : Layer) (tree leaf : Nat) :
    ftsLeafHeader index coord selected ≠ leafTweak lay tree leaf :=
  ne_of_tweakTag (by rw [ftsLeafHeader_tweakTag, leafTweak_tag]; decide)
theorem ftsLeafHeader_ne_digestHeader (index coord selected : Nat) (counter : BitVec 32) :
    ftsLeafHeader index coord selected ≠ digestHeader counter :=
  ne_of_tweakMarker (by rw [ftsLeafHeader_tweakMarker, digestHeader_marker]; decide)
theorem wctNodeHeader_ne_rowTweak {coord : Nat} (hk : coord < 9) (index heap : Nat) (lay : Layer) (tree leaf : Nat) :
    wctNodeHeader coord index heap ≠ rowTweak lay tree leaf :=
  ne_of_tweakTag (by rw [wctNodeHeader_tweakTag hk, rowTweak_tag]; split <;> decide)
theorem wctNodeHeader_ne_leafTweak {coord : Nat} (hk : coord < 9) (index heap : Nat) (lay : Layer) (tree leaf : Nat) :
    wctNodeHeader coord index heap ≠ leafTweak lay tree leaf :=
  ne_of_tweakTag (by rw [wctNodeHeader_tweakTag hk, leafTweak_tag]; split <;> decide)
theorem wctNodeHeader_ne_digestHeader (coord index heap : Nat) (counter : BitVec 32) :
    wctNodeHeader coord index heap ≠ digestHeader counter :=
  ne_of_tweakMarker (by rw [digestHeader_marker]; exact wctNodeHeader_tweakMarker_ne_zero _ _ _)
theorem ftsChainHeaderP_ne_rowTweak (index coord selected chain step : Nat) (high : BitVec 64) (lay : Layer)
    (tree leaf : Nat) : ftsChainHeaderP index coord selected chain step high ≠ rowTweak lay tree leaf := by
  apply ne_of_tweakMarker
  have := ftsChainHeaderP_tweakMarker index coord selected chain step high
  rw [rowTweak_marker]; omega
theorem ftsChainHeaderP_ne_leafTweak (index coord selected chain step : Nat) (high : BitVec 64) (lay : Layer)
    (tree leaf : Nat) : ftsChainHeaderP index coord selected chain step high ≠ leafTweak lay tree leaf := by
  apply ne_of_tweakMarker
  have := ftsChainHeaderP_tweakMarker index coord selected chain step high
  rw [leafTweak_marker]; omega
theorem ftsChainHeaderP_ne_digestHeader (index coord selected chain step : Nat) (high : BitVec 64)
    (counter : BitVec 32) : ftsChainHeaderP index coord selected chain step high ≠ digestHeader counter := by
  apply ne_of_tweakMarker
  have := ftsChainHeaderP_tweakMarker index coord selected chain step high
  rw [digestHeader_marker]; omega
theorem pairs_bytes_length (pairs : List (Digest × Digest)) :
    (pairs.flatMap (fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2)).length = 32 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p ps ih => simp only [List.flatMap_cons, List.length_append, bytesLE_length, ih, List.length_cons]; ring
theorem pairs_bytes_injective : ∀ {ps qs : List (Digest × Digest)}, ps.length = qs.length →
    ps.flatMap (fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2) = qs.flatMap (fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2) →
      ps = qs
  | [], [], _, _ => rfl
  | p :: ps, q :: qs, hl, h => by
      simp only [List.flatMap_cons] at h
      obtain ⟨hpq, hrest⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
      obtain ⟨h1, h2⟩ := List.append_inj hpq (by simp only [bytesLE_length])
      rw [show p = q from Prod.ext (bytesLE_injective h1) (bytesLE_injective h2),
        pairs_bytes_injective (by simpa using hl) hrest]
theorem forestInput_length (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9) :
    (forestInput index pairs).length = 320 := by
  simp only [forestInput, zero16, List.length_append, List.length_replicate, bytesLE_length, pairs_bytes_length, h]
theorem forestInput_injective {index index' : Nat} {pairs pairs' : List (Digest × Digest)}
    (hi : index < 2 ^ 40) (hi' : index' < 2 ^ 40) (hl : pairs.length = pairs'.length)
    (h : forestInput index pairs = forestInput index' pairs') : index = index' ∧ pairs = pairs' := by
  unfold forestInput at h
  obtain ⟨hh, hp⟩ := List.append_inj h (by simp only [zero16, List.length_append, List.length_replicate,
    bytesLE_length])
  obtain ⟨-, hh⟩ := List.append_inj hh (by simp only [zero16, List.length_replicate])
  obtain ⟨-, -, e, -, -⟩ := header_injective (by decide) (by decide) hi (by norm_num) (by norm_num)
    (by decide) (by decide) hi' (by norm_num) (by norm_num) (bytesLE_injective hh)
  exact ⟨e, pairs_bytes_injective hl hp⟩
theorem pairEncodingInputP_length (up : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (pad : BitVec 96) : (pairEncodingInputP up tree leaf left right counter pad).length = 64 := by
  simp only [pairEncodingInputP, List.length_append, bytesLE_length]
theorem pairEncodingInputP_injective {up up' : Layer} {tree leaf tree' leaf' : Nat} {l r l' r' : Digest}
    {c c' : BitVec 32} {pad pad' : BitVec 96}
    (hl : leaf < 2 ^ height up) (hr : tree * 2 ^ height up + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height up') (hr' : tree' * 2 ^ height up' + leaf' < 2 ^ 32)
    (h : pairEncodingInputP up tree leaf l r c pad = pairEncodingInputP up' tree' leaf' l' r' c' pad') :
    up = up' ∧ tree = tree' ∧ leaf = leaf' ∧ l = l' ∧ r = r' ∧ c = c' ∧ pad = pad' := by
  unfold pairEncodingInputP at h
  obtain ⟨h, hR⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hp⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hc⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨hL, hh⟩ := List.append_inj h (by simp only [bytesLE_length])
  obtain ⟨e1, e2, e3⟩ := rowTweak_injective hl hr hl' hr' (bytesLE_injective hh)
  exact ⟨e1, e2, e3, bytesLE_injective hL, bytesLE_injective hR, bytesLE_injective hc, bytesLE_injective hp⟩
theorem pairEncodingInputH_length (up : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (pad : BitVec 96) (hi : BitVec 64) : (pairEncodingInputH up tree leaf left right counter pad hi).length = 64 := by
  simp only [pairEncodingInputH, List.length_append, bytesLE_length]
theorem rowTweakW_injective {up up' : Layer} {tree leaf tree' leaf' : Nat} {hi hi' : BitVec 64}
    (hl : leaf < 2 ^ height up) (hr : tree * 2 ^ height up + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height up') (hr' : tree' * 2 ^ height up' + leaf' < 2 ^ 32)
    (h : rowTweakW up tree leaf hi = rowTweakW up' tree' leaf' hi') :
    up = up' ∧ tree = tree' ∧ leaf = leaf' ∧ hi = hi' := by
  obtain ⟨hh, hw⟩ := append64_inj h
  obtain ⟨e1, e2, e3⟩ := leafTweak_injective hl hr hl' hr' (by rw [leafTweak, leafTweak, hw])
  exact ⟨e1, e2, e3, hh⟩
/-- C2/C3 (FULL): the padded encoding block is injective in its coordinates, halves, counter, pads and the row
tweak's high word. -/
theorem pairEncodingInputH_injective {up up' : Layer} {tree leaf tree' leaf' : Nat} {l r l' r' : Digest}
    {c c' : BitVec 32} {pad pad' : BitVec 96} {hi hi' : BitVec 64}
    (hl : leaf < 2 ^ height up) (hr : tree * 2 ^ height up + leaf < 2 ^ 32)
    (hl' : leaf' < 2 ^ height up') (hr' : tree' * 2 ^ height up' + leaf' < 2 ^ 32)
    (h : pairEncodingInputH up tree leaf l r c pad hi = pairEncodingInputH up' tree' leaf' l' r' c' pad' hi') :
    up = up' ∧ tree = tree' ∧ leaf = leaf' ∧ l = l' ∧ r = r' ∧ c = c' ∧ pad = pad' ∧ hi = hi' := by
  rw [pairEncodingInputH_eq, pairEncodingInputH_eq] at h
  obtain ⟨h, hR⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hp⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hc⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨hL, hh⟩ := List.append_inj h (by simp only [bytesLE_length])
  obtain ⟨e1, e2, e3, e4⟩ := rowTweakW_injective hl hr hl' hr' (bytesLE_injective hh)
  exact ⟨e1, e2, e3, bytesLE_injective hL, bytesLE_injective hR, bytesLE_injective hc, bytesLE_injective hp, e4⟩
theorem pairEncoding_separation (up : Layer) (tree leaf : Nat) :
    (∀ (lay : Layer) (tree' leaf' i st : Nat), rowTweak up tree leaf ≠ chainHeader lay tree' leaf' i st) ∧
    (∀ (i k j t s : Nat) (high : BitVec 64), rowTweak up tree leaf ≠ ftsChainHeaderP i k j t s high) ∧
    (∀ (tag lay tree' position idx : Nat), tag % 256 ≠ 2 →
      rowTweak up tree leaf ≠ header tag lay tree' position idx) ∧
    (up.val < 3 → ∀ tree' leaf' : Nat, rowTweak up tree leaf ≠ rowTweak 3 tree' leaf') := by
  refine ⟨fun lay tree' leaf' i st h => ?_, fun i k j t s high h => ?_,
    fun tag lay tree' position idx ht => rowTweak_ne_header up tree leaf ht lay tree' position idx,
    fun hup tree' leaf' h => ?_⟩
  · have hc := chainHeader_firstByte lay tree' leaf' i st
    have hm := rowTweak_marker up tree leaf
    unfold tweakMarker at hm
    rw [← h, hm] at hc
    omega
  · have hc := ftsChainHeaderP_firstByte i k j t s high
    have hm := rowTweak_marker up tree leaf
    unfold tweakMarker at hm
    rw [← h, hm] at hc
    omega
  · obtain ⟨-, hw⟩ := append64_inj h
    have hb := congrArg (fun x : BitVec 64 => x.toNat / 2 ^ 48 % 256) hw
    simp only [hyperWord_toNat] at hb
    have := up.isLt
    omega
theorem ordinal_slot_injective {q q' : Nat} (h1 : q / 2 = q' / 2) (h2 : q % 2 = q' % 2) : q = q' := by
  omega
theorem ftsOrdinal_injective {child chain child' chain' : Nat} (hc : chain < 6) (hc' : chain' < 6)
    (h : ftsOrdinal child chain = ftsOrdinal child' chain') : child = child' ∧ chain = chain' := by
  unfold ftsOrdinal at h
  omega
theorem ftsSlot_injective {child chain child' chain' : Nat} (hc : chain < 6) (hc' : chain' < 6)
    (h1 : ftsOrdinal child chain / 2 = ftsOrdinal child' chain' / 2)
    (h2 : ftsOrdinal child chain % 2 = ftsOrdinal child' chain' % 2) : child = child' ∧ chain = chain' :=
  ftsOrdinal_injective hc hc' (ordinal_slot_injective h1 h2)
theorem ftsOrdinal_pair_lt {child chain : Nat} (hs : child < 128) (hc : chain < 6) :
    ftsOrdinal child chain / 2 < 384 := by
  unfold ftsOrdinal; omega
theorem lowerOrdinal_injective (lay : Layer) {leaf chain leaf' chain' : Nat} (hc : chain < chainCount lay)
    (hc' : chain' < chainCount lay) (h : lowerOrdinal lay leaf chain = lowerOrdinal lay leaf' chain') :
    leaf = leaf' ∧ chain = chain' := by
  unfold lowerOrdinal at h
  have hpos : 0 < chainCount lay := by fin_cases lay <;> decide
  rcases Nat.lt_trichotomy leaf leaf' with hl | hl | hl
  · have : chainCount lay * leaf + chainCount lay ≤ chainCount lay * leaf' := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hl
    omega
  · subst hl; omega
  · have : chainCount lay * leaf' + chainCount lay ≤ chainCount lay * leaf := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hl
    omega
theorem lowerSlot_injective (lay : Layer) {leaf chain leaf' chain' : Nat} (hc : chain < chainCount lay)
    (hc' : chain' < chainCount lay) (h1 : lowerOrdinal lay leaf chain / 2 = lowerOrdinal lay leaf' chain' / 2)
    (h2 : lowerOrdinal lay leaf chain % 2 = lowerOrdinal lay leaf' chain' % 2) : leaf = leaf' ∧ chain = chain' :=
  lowerOrdinal_injective lay hc hc' (ordinal_slot_injective h1 h2)
theorem lowerOrdinal_pair_lt (lay : Layer) {leaf chain : Nat} (hl : leaf < 2 ^ height lay)
    (hc : chain < chainCount lay) : lowerOrdinal lay leaf chain / 2 < chainCount lay * 2 ^ height lay / 2 + 1 := by
  unfold lowerOrdinal
  have : chainCount lay * leaf + chainCount lay ≤ chainCount lay * 2 ^ height lay := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hl
  omega
theorem lowerOrdinal_pair_lt_pow (lay : Layer) {leaf chain : Nat} (hl : leaf < 2 ^ height lay)
    (hc : chain < chainCount lay) : lowerOrdinal lay leaf chain / 2 < 2 ^ 32 := by
  have h := lowerOrdinal_pair_lt lay hl hc
  have hb : chainCount lay * 2 ^ height lay / 2 + 1 ≤ 2 ^ 32 := by
    fin_cases lay <;> decide
  omega
theorem ftsSeedHeader_injective {coord index pair coord' index' pair' : Nat}
    (hk : coord < 256) (hi : index < 2 ^ 40) (hp : pair < 2 ^ 32)
    (hk' : coord' < 256) (hi' : index' < 2 ^ 40) (hp' : pair' < 2 ^ 32)
    (h : ftsSeedHeader coord index pair = ftsSeedHeader coord' index' pair') :
    coord = coord' ∧ index = index' ∧ pair = pair' := by
  obtain ⟨-, e1, e2, -, e3⟩ := header_injective (by decide) hk hi (by norm_num) hp
    (by decide) hk' hi' (by norm_num) hp' h
  exact ⟨e1, e2, e3⟩
theorem lowerSeedHeader_injective {lay lay' : Layer} {tree pair tree' pair' : Nat}
    (ht : tree < 2 ^ 40) (hp : pair < 2 ^ 32) (ht' : tree' < 2 ^ 40) (hp' : pair' < 2 ^ 32)
    (h : lowerSeedHeader lay tree pair = lowerSeedHeader lay' tree' pair') :
    lay = lay' ∧ tree = tree' ∧ pair = pair' := by
  have hl := lay.isLt
  have hl' := lay'.isLt
  obtain ⟨-, e1, e2, e3, -⟩ := header_injective (by decide) (by omega) ht hp (by norm_num)
    (by decide) (by omega) ht' hp' (by norm_num) h
  exact ⟨Fin.ext e1, e2, e3⟩
theorem ftsSeedHeader_ne_tag (coord index pair tag lay tree position idx : Nat) (ht : tag % 256 ≠ 8) :
    ftsSeedHeader coord index pair ≠ header tag lay tree position idx := by
  intro h
  have h1 := header_byte1 8 coord index 0 pair
  unfold ftsSeedHeader at h
  rw [h, header_byte1] at h1
  omega
theorem lowerSeedHeader_ne_tag (lay : Layer) (tree pair tag lay' tree' position idx : Nat) (ht : tag % 256 ≠ 0) :
    lowerSeedHeader lay tree pair ≠ header tag lay' tree' position idx := by
  intro h
  have h1 := header_byte1 0 lay.val tree pair 0
  unfold lowerSeedHeader at h
  rw [h, header_byte1] at h1
  omega
theorem lowerSeedHeader_ne_top (lay : Layer) (hlay : lay ≠ 0) (tree pair tree' position idx : Nat) :
    lowerSeedHeader lay tree pair ≠ header 0 0 tree' position idx := by
  intro h
  have h2 := header_byte2 0 lay.val tree pair 0
  unfold lowerSeedHeader at h
  rw [h, header_byte2] at h2
  have := lay.isLt
  have : lay.val ≠ 0 := fun h0 => hlay (Fin.ext h0)
  omega
theorem ftsSeedHeader_ne_lowerSeedHeader (coord index pair : Nat) (lay : Layer) (tree pair' : Nat) :
    ftsSeedHeader coord index pair ≠ lowerSeedHeader lay tree pair' :=
  ftsSeedHeader_ne_tag coord index pair 0 lay.val tree pair' 0 (by decide)
/-! ### C2 (FULL): the packed lower node tweak -/
theorem lowerNodeWord_toNat {heap : Nat} (hh : heap < 128) (lay tree : Nat) :
    (lowerNodeWord lay tree heap).toNat = 1920 + heap + tree % 2 ^ 32 * 2 ^ 16 + lay % 256 * 2 ^ 48 + 193 * 2 ^ 56 := by
  unfold lowerNodeWord lowerK
  rw [BitVec.toNat_add, hyperWord_toNat, BitVec.toNat_ofNat]
  have h1 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h2 := Nat.mod_lt lay (show 0 < 256 by decide)
  rw [Nat.mod_eq_of_lt (show 1407 + heap < 2 ^ 64 by omega)]
  apply (Nat.mod_eq_of_lt _).trans
  · omega
  · omega
theorem lowerTweak_toNat {heap : Nat} (hh : heap < 128) (lay tree : Nat) :
    (lowerTweak lay tree heap).toNat = 1920 + heap + tree % 2 ^ 32 * 2 ^ 16 + (lay - 1) % 256 * 2 ^ 48 + 193 * 2 ^ 56 := by
  unfold lowerTweak
  rw [append64_toNat, lowerNodeWord_toNat hh]
  simp
theorem lowerTweak_marker {heap : Nat} (hh : heap < 128) (lay tree : Nat) :
    tweakMarker (lowerTweak lay tree heap) = 128 + heap := by
  unfold tweakMarker; rw [lowerTweak_toNat hh]; omega
theorem lowerTweak_firstByte {heap : Nat} (hh : heap < 128) (lay tree : Nat) :
    (lowerTweak lay tree heap).toNat % 256 = 128 + heap := lowerTweak_marker hh lay tree
theorem lowerTweak_tag {heap : Nat} (hh : heap < 128) (lay tree : Nat) :
    tweakTag (lowerTweak lay tree heap) = 7 := by
  unfold tweakTag; rw [lowerTweak_toNat hh]; omega
theorem lowerTweak_high' (lay tree heap : Nat) : tweakHigh (lowerTweak lay tree heap) = 0 := by
  unfold lowerTweak; rw [append64_high]; rfl
theorem lowerTweak_injective {lay lay' tree tree' heap heap' : Nat} (h1 : 1 ≤ lay) (h4 : lay < 4)
    (h1' : 1 ≤ lay') (h4' : lay' < 4) (ht : tree < 2 ^ 32) (ht' : tree' < 2 ^ 32) (hh : heap < 128)
    (hh' : heap' < 128) (h : lowerTweak lay tree heap = lowerTweak lay' tree' heap') :
    lay = lay' ∧ tree = tree' ∧ heap = heap' := by
  have e := congrArg BitVec.toNat h
  rw [lowerTweak_toNat hh, lowerTweak_toNat hh', Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht',
    Nat.mod_eq_of_lt (show lay - 1 < 256 by omega), Nat.mod_eq_of_lt (show lay' - 1 < 256 by omega)] at e
  omega
theorem chainHeader_byte1_low (lay : Layer) (tree leaf i step : Nat) :
    (chainHeader lay tree leaf i step).toNat / 256 % 8 = step % 8 := by
  rw [chainHeader_toNat, chainHeaderFlaggedLow_toNat, chainHeaderLow_toNat]
  have := Nat.mod_lt i (show 0 < 64 by decide)
  have := Nat.mod_lt step (show 0 < 8 by decide)
  generalize (tree % 2 ^ 31 / 2 ^ (32 - height lay) + leaf % 4096 / 2 ^ height lay * 2 ^ (height lay - 1)) = x
  generalize (tree % 2 ^ 31 * 2 ^ height lay + leaf % 4096) % 2 ^ 32 = r
  have := Nat.mod_lt x (show 0 < 2 by decide)
  have := Nat.mod_lt (x / 2) (show 0 < 32 by decide)
  split_ifs <;> omega
theorem lowerTweak_ne_chainHeader {heap : Nat} (hh : heap < 128) (lay tree : Nat) (lay' : Layer)
    (tree' leaf i step : Nat) (hs : step % 8 ≠ 7) : lowerTweak lay tree heap ≠ chainHeader lay' tree' leaf i step := by
  intro h
  have e := chainHeader_byte1_low lay' tree' leaf i step
  rw [← h, lowerTweak_toNat hh] at e
  omega
theorem lowerTweak_low_ge {heap : Nat} (hh : heap < 128) (lay tree : Nat) :
    193 * 2 ^ 56 ≤ (lowerTweak lay tree heap).toNat % 2 ^ 64 := by
  rw [lowerTweak_toNat hh]
  have h1 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h2 := Nat.mod_lt (lay - 1) (show 0 < 256 by decide)
  rw [Nat.mod_eq_of_lt (by omega)]; omega
theorem lowerTweak_ne_of_low_lt {heap : Nat} (hh : heap < 128) (lay tree : Nat) {x : BitVec 128}
    (hx : x.toNat % 2 ^ 64 < 2 ^ 58) : lowerTweak lay tree heap ≠ x := by
  intro h
  have := lowerTweak_low_ge hh lay tree
  rw [h] at this
  omega
theorem lowerTweak_ne_ftsChainHeaderP {heap : Nat} (hh : heap < 128) (lay tree : Nat)
    (index coord selected chain step : Nat) (high : BitVec 64) :
    lowerTweak lay tree heap ≠ ftsChainHeaderP index coord selected chain step high := by
  apply lowerTweak_ne_of_low_lt hh
  have e : (ftsChainHeaderP index coord selected chain step high).toNat % 2 ^ 64 =
      ((ftsChainHeaderP index coord selected chain step high).extractLsb' 0 64).toNat := by
    rw [BitVec.extractLsb'_toNat]; simp
  rw [e, ftsChainHeaderP_low, BitVec.toNat_ofNat]
  have := ftsChainLow_lt index coord selected chain step
  rw [Nat.mod_eq_of_lt (by omega)]; exact this
theorem lowerTweak_ne_wctNodeHeader {heap : Nat} (hh : heap < 128) (lay tree : Nat) {coord : Nat} (hk : coord < 9)
    (index heap' : Nat) : lowerTweak lay tree heap ≠ wctNodeHeader coord index heap' := by
  apply lowerTweak_ne_of_low_lt hh
  rw [wctNodeHeader_toNat hk]
  split_ifs
  · have := ftsNodeLowN_lt index coord heap'
    omega
  · have := ftsLeafLow_lt index coord 0
    omega
end ClaudeWCT.WCT9
end
-- ==== merged from ClaudeWCT_WCT9_Queries ====
section

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness SigGolfCandidate.T3.Cost
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def leafInput (index coord selected : Nat) (ends : List Digest) : HashInput :=
  bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (ftsLeafHeader index coord selected) ++ zero16 ++
    (ends.drop 1).flatMap (bytesLE 16)
def nodeInput (coord index heap : Nat) (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 (wctNodeHeader coord index heap) ++ zero16 ++ bytesLE 16 right
theorem leafHash_eq (index coord selected : Nat) (ends : List Digest) :
    leafHash index coord selected ends = shortHash (leafInput index coord selected ends) := rfl
theorem leafInputP_zero (index coord selected : Nat) (ends : List Digest) :
    leafInputP index coord selected 0 ends = leafInput index coord selected ends := by
  unfold leafInputP leafInput
  rw [bytesLE_zero16]
theorem leafInputP_length (index coord selected : Nat) (pad : Digest) (ends : List Digest) (hlen : ends.length = 6) :
    (leafInputP index coord selected pad ends).length = 128 := by
  simp only [leafInputP, List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop, hlen]
theorem nodeHash_eq (coord index heap : Nat) (left right : Digest) :
    wctNodeHash coord index heap left right = shortHash (nodeInput coord index heap left right) := by
  rw [wctNodeHash_eq_short]; rfl
theorem forestPk_eq (index : Nat) (pairs : List (Digest × Digest)) :
    forestPk index pairs = shortHash (forestInput index pairs) := rfl
theorem leafInput_length (index coord selected : Nat) (ends : List Digest) (hlen : ends.length = 6) :
    (leafInput index coord selected ends).length = 128 := by
  simp only [leafInput, zero16, List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop,
    List.length_replicate, hlen]
theorem wctTopInput_length (coord index heap : Nat) (left pad right : Digest) :
    (wctTopInput coord index heap left pad right).length = 64 := by
  simp only [wctTopInput, List.length_append, bytesLE_length]
theorem nodeInput_length (coord index heap : Nat) (left right : Digest) :
    (nodeInput coord index heap left right).length = 64 := by
  simp only [nodeInput, zero16, List.length_append, bytesLE_length, List.length_replicate]
theorem pad64_of_mod {x : HashInput} (h : x.length % 64 = 0) : pad64 x = x := by
  simp only [pad64, h, Nat.sub_zero, Nat.mod_self, List.replicate_zero, List.append_nil]
inductive FtsInput (index : Nat) : HashInput → Prop
  | chain {coord selected t step : Nat} (value : Digest) (hcoord : coord < 9) (hsel : selected < 128)
      (ht : t < 6) (hstep : step < 4) :
      FtsInput index (pad64 (ftsChainInputW index coord selected t step value))
  | leaf {coord selected : Nat} {pad : Digest} {ends : List Digest} (hcoord : coord < 9) (hsel : selected < 128)
      (hlen : ends.length = 6) :
      FtsInput index (pad64 (leafInputP index coord selected pad ends))
  | node {coord heap : Nat} (left right : Digest) (hcoord : coord < 9) (hlo : 2 ≤ heap) (hhi : heap < 128) :
      FtsInput index (pad64 (nodeInput coord index heap left right))
  | top {coord heap : Nat} (left pad right : Digest) (hcoord : coord < 9) (hlo : 2 ≤ heap) (hhi : heap < 4) :
      FtsInput index (pad64 (wctTopInput coord index heap left pad right))
  | forest {pairs : List (Digest × Digest)} (hlen : pairs.length = 9) :
      FtsInput index (pad64 (forestInput index pairs))
/-- FTS private queries: the 51 coefficient pairs of each coordinate's seed family (campaign X1, stage A). -/
def FtsSeed (index : Nat) (tweak : BitVec 128) : Prop :=
  ∃ coord pair, coord < 9 ∧ pair < ftsCoefPairs ∧ tweak = ftsSeedHeader coord index pair
def FtsQuery (index : Nat) : Query → Prop
  | .inl (.inr input) => FtsInput index input
  | .inr (.inl tweak) => FtsSeed index tweak
  | _ => False
@[simp] theorem ftsQuery_public (index : Nat) (input : HashInput) :
    FtsQuery index (.inl (.inr input)) ↔ FtsInput index input := Iff.rfl
@[simp] theorem ftsQuery_private (index : Nat) (tweak : BitVec 128) :
    FtsQuery index (.inr (.inl tweak)) ↔ FtsSeed index tweak := Iff.rfl
theorem FtsInput.length {index : Nat} {x : HashInput} (h : FtsInput index x) :
    x.length = 64 ∨ x.length = 128 ∨ x.length = 320 := by
  cases h with
  | chain value hcoord hsel ht hstep =>
      left
      rw [pad64_of_mod (by rw [ftsChainInputW_length])]
      exact ftsChainInputW_length _ _ _ _ _ _
  | leaf hcoord hsel hlen =>
      right; left
      rw [pad64_of_mod (by rw [leafInputP_length _ _ _ _ _ hlen])]
      exact leafInputP_length _ _ _ _ _ hlen
  | node left right hcoord hlo hhi =>
      left
      rw [pad64_of_mod (by rw [nodeInput_length])]
      exact nodeInput_length _ _ _ _ _
  | top left pad right hcoord hlo hhi =>
      left
      rw [pad64_of_mod (by rw [wctTopInput_length])]
      exact wctTopInput_length _ _ _ _ _ _
  | forest hlen =>
      right; right
      rw [pad64_of_mod (by rw [forestInput_length _ _ hlen]), forestInput_length _ _ hlen]
theorem FtsInput.length_le {index : Nat} {x : HashInput} (h : FtsInput index x) : x.length ≤ 320 := by
  rcases h.length with h | h | h <;> omega
theorem ftsQuery_good {index : Nat} {q : Query} (h : FtsQuery index q) : GoodQuery q := by
  rcases q with (coin | input) | (tweak | other)
  · exact h.elim
  · rcases (show FtsInput index input from h).length with hl | hl | hl <;>
      exact ⟨by omega, by omega⟩
  · trivial
  · exact h.elim
theorem hdrBlock_pad64_prefix (a : HashInput) (h : BitVec 128) (rest : HashInput) (ha : a.length = 16) :
    SigGolfCandidate.T3M.Extract.hdrBlock (pad64 (a ++ bytesLE 16 h ++ rest)) = bytesLE 16 h := by
  rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp [ha, bytesLE_length]; omega)]
  unfold SigGolfCandidate.T3M.Extract.hdrBlock
  rw [List.append_assoc, List.drop_left' ha, List.take_left' (bytesLE_length 16 h)]
theorem FtsInput.hdrBlock {index : Nat} {x : HashInput} (h : FtsInput index x) :
    (∃ coord selected t step, SigGolfCandidate.T3M.Extract.hdrBlock x =
      bytesLE 16 (ftsChainHeader index coord selected t step)) ∨
    (∃ coord selected, coord < 9 ∧ selected < 128 ∧
      SigGolfCandidate.T3M.Extract.hdrBlock x = bytesLE 16 (ftsLeafHeader index coord selected)) ∨
    (∃ coord heap, coord < 9 ∧ 2 ≤ heap ∧ heap < 128 ∧
      SigGolfCandidate.T3M.Extract.hdrBlock x = bytesLE 16 (wctNodeHeader coord index heap)) ∨
    SigGolfCandidate.T3M.Extract.hdrBlock x = bytesLE 16 (header 15 0 index 0 0) := by
  cases h with
  | @chain coord selected t step value hcoord hsel ht hstep =>
      refine Or.inl ⟨coord, selected, t, step, ?_⟩
      unfold ftsChainInputW
      split
      · rw [List.append_assoc (bytesLE 16 value ++ _), hdrBlock_pad64_prefix _ _ _ (by simp [bytesLE_length])]
      · unfold chainInput
        rw [List.append_assoc (zero16 ++ _), hdrBlock_pad64_prefix _ _ _ (by simp [zero16])]
  | @leaf coord selected pad ends hcoord hsel hlen =>
      refine Or.inr (Or.inl ⟨coord, selected, hcoord, hsel, ?_⟩)
      unfold leafInputP
      rw [List.append_assoc (bytesLE 16 _ ++ bytesLE 16 _), hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _)]
  | @node coord heap left right hcoord hlo hhi =>
      refine Or.inr (Or.inr (Or.inl ⟨coord, heap, hcoord, hlo, hhi, ?_⟩))
      unfold nodeInput
      rw [List.append_assoc (bytesLE 16 left ++ _), hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _)]
  | @top coord heap left pad right hcoord hlo hhi =>
      refine Or.inr (Or.inr (Or.inl ⟨coord, heap, hcoord, hlo, by omega, ?_⟩))
      unfold wctTopInput
      rw [List.append_assoc (bytesLE 16 left ++ _), hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _)]
  | @forest pairs hlen =>
      refine Or.inr (Or.inr (Or.inr ?_))
      unfold forestInput
      rw [show zero16 = bytesLE 16 (0 : Digest) by decide, hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _)]
theorem bound_shortHashP {P : Query → Prop} (input : HashInput) (k : Nat)
    (hq : P (.inl (.inr (pad64 input)))) (hk : (pad64 input).length / 64 ≤ k) :
    Bound P (fun _ => True) k (shortHash input) := by
  unfold shortHash publicHash
  exact Bound.qry_bind (k := 0) hq (fun _ => .pure _ 0 trivial) (by simpa only [weight, Nat.add_zero] using hk)
theorem bound_highHashP {P : Query → Prop} (input : HashInput) (k : Nat)
    (hq : P (.inl (.inr (pad64 input)))) (hk : (pad64 input).length / 64 ≤ k) :
    Bound P (fun _ => True) k (highHash input) := by
  unfold highHash publicHash
  exact Bound.qry_bind (k := 0) hq (fun _ => .pure _ 0 trivial) (by simpa only [weight, Nat.add_zero] using hk)
/-- A high-half hash makes the same single query as the low-half hash of the same input. -/
theorem allQ_highHash_of_shortHash {P : Query → Prop} (input : HashInput)
    (h : AllQueriesSatisfy (shortHash input) P) : AllQueriesSatisfy (highHash input) P := by
  have hq : P (.inl (.inr (pad64 input))) := by
    unfold shortHash publicHash at h
    exact ((allQueriesSatisfy_query_bind_iff _ _ _).mp h).1
  unfold highHash publicHash
  exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hq, fun _ => allQueriesSatisfy_pure _ _⟩
/-- C1: an FTS hash (either half) makes the one query `pad64 input`. -/
theorem bound_ftsHashP {P : Query → Prop} (heap : Nat) (input : HashInput) (k : Nat)
    (hq : P (.inl (.inr (pad64 input)))) (hk : (pad64 input).length / 64 ≤ k) :
    Bound P (fun _ => True) k (ftsHash heap input) := by
  rw [ftsHash_eq]
  split
  · exact bound_highHashP input k hq hk
  · exact bound_shortHashP input k hq hk
/-- C1: an FTS hash (either half) makes the same single query as the low-half hash of the same input. -/
theorem allQ_ftsHash_of_shortHash {P : Query → Prop} (heap : Nat) (input : HashInput)
    (h : AllQueriesSatisfy (shortHash input) P) : AllQueriesSatisfy (ftsHash heap input) P := by
  rw [ftsHash_eq]
  split
  · exact allQ_highHash_of_shortHash input h
  · exact h
theorem nodeHashH_eq (coord index heap : Nat) (left right : Digest) :
    wctNodeHashH coord index heap left right = ftsHash heap (nodeInput coord index heap left right) := rfl
theorem bound_privatePairP {P : Query → Prop} (tag lay tree position index : Nat)
    (hq : P (.inr (.inl (header tag lay tree position index)))) :
    Bound P (fun _ => True) 1 (privatePair tag lay tree position index) := by
  unfold privatePair privateHash
  exact Bound.qry_bind (k := 0) hq (fun _ => .pure _ 0 trivial) (by simp only [weight]; omega)
theorem allQueriesSatisfy_of_bound {P : Query → Prop} {α : Type} {Post : α → Prop} {k : Nat} {oa : M α}
    (h : Bound P Post k oa) : AllQueriesSatisfy oa P := by
  induction h with
  | pure a k hp => exact allQueriesSatisfy_pure _ _
  | query q f k hq _ ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hq, ih⟩
theorem cbound_of_ftsBound {index : Nat} {α : Type} {Post : α → Prop} {k : Nat} {oa : M α}
    (h : Bound (FtsQuery index) Post k oa) : CBound Post k oa :=
  h.mono (fun _ hq => ftsQuery_good hq) (fun _ hp => hp)
section Programs
variable (index : Nat)
theorem ftsBound_chain (coord selected t start count : Nat) (value : Digest)
    (hcoord : coord < 9) (hsel : selected < 128) (ht : t < 6) (hend : start + count ≤ 4) :
    Bound (FtsQuery index) (fun _ => True) count (chain index coord selected t start count value) := by
  unfold chain
  refine Bound.foldlM_range'_le start count _ (fun _ _ => True) (fun _ => 1) value trivial
    (fun n hn value _ => ?_) (fun _ _ => trivial) (by simp)
  unfold projHash publicHash
  exact Bound.qry_bind (k := 0) (FtsInput.chain value hcoord hsel ht (by omega)) (fun _ => .pure _ 0 trivial)
    (by simp [weight, Cost.pad64_length, ftsChainInputW_length])
theorem ftsBound_leafHashP (coord selected : Nat) (pad : Digest) (ends : List Digest)
    (hcoord : coord < 9) (hsel : selected < 128) (hlen : ends.length = 6) :
    Bound (FtsQuery index) (fun _ => True) 2 (leafHashP index coord selected pad ends) := by
  unfold leafHashP
  exact bound_shortHashP _ 2 (FtsInput.leaf hcoord hsel hlen)
    (by rw [pad64_of_mod (by rw [leafInputP_length _ _ _ _ _ hlen]), leafInputP_length _ _ _ _ _ hlen])
theorem ftsBound_leafHash (coord selected : Nat) (ends : List Digest)
    (hcoord : coord < 9) (hsel : selected < 128) (hlen : ends.length = 6) :
    Bound (FtsQuery index) (fun _ => True) 2 (leafHash index coord selected ends) := by
  rw [← leafHashP_zero]
  exact ftsBound_leafHashP index coord selected 0 ends hcoord hsel hlen
theorem ftsBound_nodeHash (coord heap : Nat) (left right : Digest)
    (hcoord : coord < 9) (hlo : 2 ≤ heap) (hhi : heap < 128) :
    Bound (FtsQuery index) (fun _ => True) 1 (wctNodeHash coord index heap left right) := by
  rw [nodeHash_eq]
  exact bound_shortHashP _ 1 (FtsInput.node left right hcoord hlo hhi)
    (by rw [pad64_of_mod (by rw [nodeInput_length]), nodeInput_length])
theorem ftsBound_topHash (coord heap : Nat) (left pad right : Digest)
    (hcoord : coord < 9) (hlo : 2 ≤ heap) (hhi : heap < 4) :
    Bound (FtsQuery index) (fun _ => True) 1 (wctTopHash coord index heap left pad right) := by
  unfold wctTopHash
  exact bound_highHashP _ 1 (FtsInput.top left pad right hcoord hlo hhi)
    (by rw [pad64_of_mod (by rw [wctTopInput_length]), wctTopInput_length])
theorem ftsBound_heapNode (coord heap : Nat) (padR left right : Digest)
    (hcoord : coord < 9) (hlo : 2 ≤ heap) (hhi : heap < 128) :
    Bound (FtsQuery index) (fun _ => True) 1 (wctHeapNode coord index heap padR left right) := by
  unfold wctHeapNode
  split
  · exact ftsBound_topHash index coord heap left padR right hcoord hlo (by omega)
  · exact ftsBound_nodeHash index coord heap left right hcoord hlo hhi
theorem ftsBound_forestPk (pairs : List (Digest × Digest)) (hlen : pairs.length = 9) :
    Bound (FtsQuery index) (fun _ => True) 5 (forestPk index pairs) := by
  rw [forestPk_eq]
  exact bound_shortHashP _ 5 (FtsInput.forest hlen)
    (by rw [pad64_of_mod (by rw [forestInput_length _ _ hlen]), forestInput_length _ _ hlen])
theorem ftsBound_seedPair (coord pair : Nat) (hcoord : coord < 9) (hpair : pair < ftsCoefPairs) :
    Bound (FtsQuery index) (fun _ => True) 1 (ftsSeedPair index coord pair) :=
  bound_privatePairP _ _ _ _ _ ⟨coord, pair, hcoord, hpair, rfl⟩
/-- Kept for the lower layers' packed seeds (`Cost.lean`): one private query per even ordinal. -/
def seedCost (q : Nat) : Nat := if q % 2 = 0 then 1 else 0
theorem ftsBound_ftsCoefs (coord : Nat) (hcoord : coord < 9) :
    Bound (FtsQuery index) (fun _ => True) ftsCoefPairs (ftsCoefs index coord) := by
  unfold ftsCoefs
  refine Bound.foldlM_range_le (P := FtsQuery index) ftsCoefPairs _ (fun _ _ => True) (fun _ => 1) []
    trivial (fun j hj acc _ => ?_) (fun _ _ => trivial) (by simp)
  exact (ftsBound_seedPair index coord j hcoord hj).bind' (l := 0)
    (fun _ _ => .pure _ 0 trivial) (by omega)
theorem ftsBound_childStep (coord selected : Nat) (word : Rank) (coefs : List Digest)
    (state : List Digest × List Digest) (i : Fin 6) (hcoord : coord < 9) (hsel : selected < 128)
    (hstate : state.1.length = i.val ∧ state.2.length = i.val) :
    Bound (FtsQuery index)
      (fun rows : List Digest × List Digest => rows.1.length = i.val + 1 ∧ rows.2.length = i.val + 1)
      4 (childStep index coord selected word coefs state i) := by
  unfold childStep
  have hd := wordDigit_le_four word i
  refine (ftsBound_chain index coord selected _ 0 _ _ hcoord hsel i.isLt (by omega)).bind'
    (l := wordDigit word i) (fun value _ => ?_) (by omega)
  refine (ftsBound_chain index coord selected _ _ _ value hcoord hsel i.isLt (by omega)).bind'
    (l := 0) (fun last _ => ?_) (by omega)
  exact .pure _ 0 ⟨by simp only [List.length_append, List.length_singleton]; omega,
    by simp only [List.length_append, List.length_singleton]; omega⟩
theorem ftsBound_childRows (coord selected : Nat) (word : Rank) (coefs : List Digest) (hcoord : coord < 9)
    (hsel : selected < 128) :
    Bound (FtsQuery index) (fun rows : List Digest × List Digest => rows.1.length = 6 ∧ rows.2.length = 6)
      24 (childRows index coord selected word coefs) := by
  unfold childRows
  refine ((Bound.foldlM_list (P := FtsQuery index) (List.finRange 6) _
    (fun i (rows : List Digest × List Digest) => rows.1.length = i ∧ rows.2.length = i)
    (fun _ => 4) ([], []) ⟨rfl, rfl⟩
    (fun i hi rows hrows => ?_)).mono (fun _ h => h) (fun rows h => by simpa using h)).mono_k (by simp)
  have hi7 : i < 6 := by simpa using hi
  simp only [List.getElem_finRange, Fin.cast_mk]
  exact ftsBound_childStep index coord selected word coefs rows ⟨i, hi7⟩ hcoord hsel hrows
/-- Compressions per FTS child: 24 chain steps (6 chains of 4) and the 2-block leaf (no seed queries: stage-A
family seeds). -/
def childCost : Nat := 26
theorem ftsBound_buildChildF (coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest)
    (hcoord : coord < 9) (hsel : selected < 128) :
    Bound (FtsQuery index) (fun result : Digest × List Digest => result.2.length = 6)
      childCost (buildChildF index coord selected word coefs pad) := by
  rw [buildChildF_factor]
  refine (ftsBound_childRows index coord selected word coefs hcoord hsel).bind' (l := 2)
    (fun rows hrows => ?_) (by unfold childCost; omega)
  exact (ftsBound_leafHashP index coord selected pad rows.1 hcoord hsel hrows.1).bind' (l := 0)
    (fun root _ => .pure _ 0 hrows.2) (by decide)
/-- C1: the leaf of heap `heap` makes the same two-block query as the legacy padded leaf. -/
theorem ftsBound_leafHashH (heap coord selected : Nat) (pad : Digest) (ends : List Digest)
    (hcoord : coord < 9) (hsel : selected < 128) (hlen : ends.length = 6) :
    Bound (FtsQuery index) (fun _ => True) 2 (leafHashH heap index coord selected pad ends) := by
  rw [leafHashH_eq]
  exact bound_ftsHashP _ _ 2 (FtsInput.leaf hcoord hsel hlen)
    (by rw [pad64_of_mod (by rw [leafInputP_length _ _ _ _ _ hlen]), leafInputP_length _ _ _ _ _ hlen])
theorem ftsBound_nodeHashH (coord heap : Nat) (left right : Digest)
    (hcoord : coord < 9) (hlo : 2 ≤ heap) (hhi : heap < 128) :
    Bound (FtsQuery index) (fun _ => True) 1 (wctNodeHashH coord index heap left right) := by
  rw [nodeHashH_eq]
  exact bound_ftsHashP _ _ 1 (FtsInput.node left right hcoord hlo hhi)
    (by rw [pad64_of_mod (by rw [nodeInput_length]), nodeInput_length])
theorem ftsBound_buildChildH (heap coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest)
    (hcoord : coord < 9) (hsel : selected < 128) :
    Bound (FtsQuery index) (fun result : Digest × List Digest => result.2.length = 6)
      childCost (buildChildH heap index coord selected word coefs pad) := by
  rw [buildChildH_factor]
  refine (ftsBound_childRows index coord selected word coefs hcoord hsel).bind' (l := 2)
    (fun rows hrows => ?_) (by unfold childCost; omega)
  exact (ftsBound_leafHashH index heap coord selected pad rows.1 hcoord hsel hrows.1).bind' (l := 0)
    (fun root _ => .pure _ 0 hrows.2) (by decide)
theorem ftsBound_coordRows (coord : Coord) (selected : Child) (word : Rank) (coefs : List Digest) (pad : Digest) :
    Bound (FtsQuery index) (fun _ => True) 3328 (coordRows index coord selected word coefs pad) := by
  unfold coordRows
  refine Bound.foldlM_range_le (P := FtsQuery index) 128 _ (fun _ _ => True) (fun _ => childCost) ([], [])
    trivial (fun j hj state _ => ?_) (fun _ _ => trivial) (by simp [childCost])
  exact (ftsBound_buildChildF index coord.val j word coefs pad coord.isLt hj).bind' (l := 0)
    (fun result _ => .pure _ 0 trivial) (by omega)
theorem ftsBound_heapBuild (coord : Nat) (hcoord : coord < 9) (padR : Digest) (leaves : List Digest) :
    Bound (FtsQuery index) (fun _ => True) 126 (heapBuild index coord padR leaves) := by
  unfold heapBuild
  refine ((Bound.foldlM_list (P := FtsQuery index) (List.range' 2 126).reverse _ (fun _ _ => True)
    (fun _ => 1) _ trivial (fun i hi nodes _ => ?_)).mono (fun _ h => h) (fun _ _ => trivial)).mono_k
    (by simp)
  have hi' : i < 126 := by simpa using hi
  rw [heap_order i hi']
  exact (ftsBound_heapNode index coord (127 - i) _ _ _ hcoord (by omega) (by omega)).bind' (l := 0)
    (fun _ _ => .pure _ 0 trivial) (by omega)
/-- Per coordinate: 51 coefficient pairs, 128 children of 26, 126 heap nodes. -/
theorem ftsBound_buildCoordinateF (coord : Coord) (selected : Child) (word : Rank) (prev : Digest × Digest) :
    Bound (FtsQuery index) (fun _ => True) 3481 (buildCoordinateF index coord selected word prev) := by
  rw [buildCoordinateF_factor]
  refine (ftsBound_ftsCoefs index coord.val coord.isLt).bind' (l := 3454) (fun coefs _ => ?_)
    (by simp [ftsCoefPairs])
  refine (ftsBound_coordRows index coord selected word coefs prev.1).bind' (l := 126) (fun rows _ => ?_)
    (by decide)
  exact (ftsBound_heapBuild index coord.val coord.isLt prev.2 rows.1).bind' (l := 0)
    (fun _ _ => .pure _ 0 trivial) (by decide)
theorem ftsBound_forestRows (output : HashOutput) :
    Bound (FtsQuery index)
      (fun state : List Opening × List (Digest × Digest) => state.1.length = 9 ∧ state.2.length = 9)
      31329 (forestRows index output) := by
  unfold forestRows
  refine ((Bound.foldlM_list (P := FtsQuery index) (List.finRange 9) _
    (fun i (state : List Opening × List (Digest × Digest)) => state.1.length = i ∧ state.2.length = i)
    (fun _ => 3481) ([], []) ⟨rfl, rfl⟩ (fun i hi state hstate => ?_)).mono (fun _ h => h)
    (fun state h => by simpa using h)).mono_k (by simp)
  unfold openingStep
  exact (ftsBound_buildCoordinateF index _ _ _ _).bind' (l := 0)
    (fun result _ => .pure _ 0 ⟨by simp [hstate.1], by simp [hstate.2]⟩) (by decide)
/-- The nested FTS needs 31329 compressions; the stated bound keeps the old 31334 (5 to spare). -/
theorem ftsBound_signForest (output : HashOutput) :
    Bound (FtsQuery index) (fun result : List Opening × (Digest × Digest) => result.1.length = 9) 31334
      (signForest index output) := by
  unfold signForest
  exact (ftsBound_forestRows index output).bind' (l := 0) (fun state hstate => .pure _ 0 hstate.1) (by decide)
theorem recover_heap_bounds (level s : Nat) (hl : level < 6) (hs : s < 128) :
    2 ≤ 2 ^ (6 - level) + s / 2 ^ (level + 1) ∧ 2 ^ (6 - level) + s / 2 ^ (level + 1) < 128 := by
  interval_cases level <;> simp <;> omega
theorem ftsBound_recoverCoordinate (sig : Signature) (output : HashOutput) (coord : Coord)
    (prev : Digest × Digest) :
    Bound (FtsQuery index) (fun _ => True) 15 (recoverCoordinate sig index output coord prev) := by
  unfold recoverCoordinate
  dsimp only
  refine (Bound.mapM_list (P := FtsQuery index) (List.finRange 6) _ (fun i => wordDigit (rank output coord) i)
    (fun i _ => ftsBound_chain index coord.val (child output coord).val i.val _ _ _ coord.isLt
      (child output coord).isLt i.isLt (by have := wordDigit_le_four (rank output coord) i; omega))).bind'
    (l := 8) (fun ends hends => ?_) ?_
  · refine (ftsBound_leafHashP index coord.val (child output coord).val prev.1 ends coord.isLt
      (child output coord).isLt (by simpa using hends)).bind' (l := 6) (fun root _ => ?_) (by decide)
    refine ((Bound.foldlM_list (P := FtsQuery index) (List.finRange 5) _ (fun _ _ => True) (fun _ => 1) root
      trivial (fun i hi value _ => ?_)).mono (fun _ h => h) (fun _ _ => trivial)).bind' (l := 1)
      (fun v _ => ?_) (by simp)
    · have hi5 : i < 5 := by simpa using hi
      simp only [List.getElem_finRange, Fin.cast_mk]
      have hb := recover_heap_bounds i (child output coord).val (by omega) (child output coord).isLt
      exact ftsBound_nodeHash index coord.val _ _ _ coord.isLt hb.1 hb.2
    · have hq : (child output coord).val / 2 ^ 6 < 2 := by
        have := (child output coord).isLt
        apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr; norm_num
      exact (ftsBound_topHash index coord.val _ _ _ _ coord.isLt (by omega) (by omega)).bind' (l := 0)
        (fun _ _ => .pure _ 0 trivial) (by decide)
  · rw [← Fin.sum_univ_def, wordStep_count]
theorem ftsBound_recoverFtsFrom (start : Digest × Digest) (sig : Signature) (output : HashOutput) :
    Bound (FtsQuery index) (fun _ => True) 140 (recoverFtsFrom start sig index output) := by
  unfold recoverFtsFrom
  refine ((Bound.foldlM_list (P := FtsQuery index) (List.finRange 9) _ (fun _ _ => True) (fun _ => 15) []
    trivial (fun i hi pairs _ => ?_)).mono (fun _ h => h) (fun _ _ => trivial)).bind' (l := 0)
    (fun _ _ => .pure _ 0 trivial) (by simp)
  exact (ftsBound_recoverCoordinate index sig output _ _).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by omega)
theorem ftsBound_recoverFts (sig : Signature) (output : HashOutput) :
    Bound (FtsQuery index) (fun _ => True) 140 (recoverFts sig index output) :=
  ftsBound_recoverFtsFrom index ftsStart sig output
theorem chain_queries (coord selected t start count : Nat) (value : Digest)
    (hcoord : coord < 9) (hsel : selected < 128) (ht : t < 6) (hend : start + count ≤ 4) :
    AllQueriesSatisfy (chain index coord selected t start count value) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_chain index coord selected t start count value hcoord hsel ht hend)
theorem leafHash_queries (coord selected : Nat) (ends : List Digest)
    (hcoord : coord < 9) (hsel : selected < 128) (hlen : ends.length = 6) :
    AllQueriesSatisfy (leafHash index coord selected ends) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_leafHash index coord selected ends hcoord hsel hlen)
theorem forestPk_queries (pairs : List (Digest × Digest)) (hlen : pairs.length = 9) :
    AllQueriesSatisfy (forestPk index pairs) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_forestPk index pairs hlen)
theorem buildChildF_queries (coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest)
    (hcoord : coord < 9) (hsel : selected < 128) :
    AllQueriesSatisfy (buildChildF index coord selected word coefs pad) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_buildChildF index coord selected word coefs pad hcoord hsel)
theorem buildChildH_queries (heap coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest)
    (hcoord : coord < 9) (hsel : selected < 128) :
    AllQueriesSatisfy (buildChildH heap index coord selected word coefs pad) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_buildChildH index heap coord selected word coefs pad hcoord hsel)
theorem buildCoordinateF_queries (coord : Coord) (selected : Child) (word : Rank) (prev : Digest × Digest) :
    AllQueriesSatisfy (buildCoordinateF index coord selected word prev) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_buildCoordinateF index coord selected word prev)
theorem forestRows_queries (output : HashOutput) :
    AllQueriesSatisfy (forestRows index output) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_forestRows index output)
theorem signForest_queries (output : HashOutput) :
    AllQueriesSatisfy (signForest index output) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_signForest index output)
theorem recoverCoordinate_queries (sig : Signature) (output : HashOutput) (coord : Coord) (prev : Digest × Digest) :
    AllQueriesSatisfy (recoverCoordinate sig index output coord prev) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_recoverCoordinate index sig output coord prev)
theorem recoverFtsFrom_queries (start : Digest × Digest) (sig : Signature) (output : HashOutput) :
    AllQueriesSatisfy (recoverFtsFrom start sig index output) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_recoverFtsFrom index start sig output)
theorem recoverFts_queries (sig : Signature) (output : HashOutput) :
    AllQueriesSatisfy (recoverFts sig index output) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_recoverFts index sig output)
end Programs
end ClaudeWCT.WCT9
end
-- ==== merged from ClaudeWCT_WCT9_Cost ====
section

namespace ClaudeWCT.WCT9.Cost
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
/-! ### C2/C3: cost bounds of the half-selecting hashes (same single query as `shortHash`) -/
theorem bound_halfHash (high : Bool) (input : HashInput) (k : Nat) (hpos : 0 < input.length)
    (hlen : (pad64 input).length / 64 ≤ k) : CBound (fun _ => True) k (halfHash high input) := by
  cases high
  · exact bound_shortHash input k hpos hlen
  · show CBound (fun _ => True) k (highHash input)
    unfold highHash publicHash
    exact Bound.qry_bind (k := 0) ⟨pad64_positive input hpos, pad64_aligned input⟩ (fun _ => .pure _ 0 trivial)
      (by simpa only [weight, Nat.add_zero] using hlen)
theorem bound_chainW (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    CBound (fun _ => True) count (chainW lay tree leaf i start count value) := by
  unfold chainW
  refine Bound.foldlM_range'_le start count _ (fun _ _ => True) (fun _ => 1) value trivial
    (fun n _ value _ => ?_) (fun _ _ => trivial) (by simp)
  apply bound_halfHash <;> simp [chainInputW_length, pad64_length]
theorem bound_lowerLeafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : ends.length = chainCount lay) :
    CBound (fun _ => True) (leafHashCost lay) (lowerLeafHash lay tree leaf ends) := by
  rw [lowerLeafHash_eq]
  unfold lowerHash
  apply bound_halfHash <;> simp only [pad64_length, SigGolfCandidate.T3.leafInput_length, hlen]
  · fin_cases lay <;> decide
  · fin_cases lay <;> decide
theorem bound_lowerNodeHash (lay tree heap : Nat) (left right : Digest) :
    CBound (fun _ => True) 1 (lowerNodeHash lay tree heap left right) := by
  unfold lowerNodeHash lowerHash
  apply bound_halfHash <;> simp [merkleNodeInput, pad64_length, zero16, SphincsSecurity.bytesLE_length]
theorem bound_lowerLevel (lay tree h level : Nat) (nodes : List Digest) :
    CBound (fun result => result.length = nodes.length / 2) (nodes.length / 2)
      (lowerLevel lay tree h level nodes) := by
  unfold lowerLevel
  have hc := Bound.mapM_list (P := GoodQuery) (List.range (nodes.length / 2))
    (fun i => lowerNodeHash lay tree (2 ^ (h - level) + i) (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0))
    (fun _ => 1) (fun _ _ => bound_lowerNodeHash _ _ _ _ _)
  simpa using hc
theorem bound_buildChildF (index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest)
    (hcoord : coord < 9) (hsel : selected < 128) :
    CBound (fun result : Digest × List Digest => result.2.length = 6) childCost
      (buildChildF index coord selected word coefs pad) :=
  cbound_of_ftsBound (ftsBound_buildChildF index coord selected word coefs pad hcoord hsel)
/-- C1: the child of heap `heap` costs the same `childCost` blocks as the legacy child. -/
theorem bound_buildChildH (heap index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest)
    (hcoord : coord < 9) (hsel : selected < 128) :
    CBound (fun result : Digest × List Digest => result.2.length = 6) childCost
      (buildChildH heap index coord selected word coefs pad) :=
  cbound_of_ftsBound (ftsBound_buildChildH index heap coord selected word coefs pad hcoord hsel)
theorem bound_buildCoordinateF (index : Nat) (coord : Coord) (selected : Child) (word : Rank)
    (prev : Digest × Digest) :
    CBound (fun _ => True) 3481 (buildCoordinateF index coord selected word prev) :=
  cbound_of_ftsBound (ftsBound_buildCoordinateF index coord selected word prev)
theorem bound_forestPk (index : Nat) (pairs : List (Digest × Digest)) (hlen : pairs.length = 9) :
    CBound (fun _ => True) 5 (WCT9.forestPk index pairs) :=
  cbound_of_ftsBound (ftsBound_forestPk index pairs hlen)
theorem bound_forestRows (index : Nat) (output : HashOutput) :
    CBound (fun state : List Opening × List (Digest × Digest) => state.1.length = 9 ∧ state.2.length = 9) 31329
      (forestRows index output) :=
  cbound_of_ftsBound (ftsBound_forestRows index output)
theorem bound_signForest (index : Nat) (output : HashOutput) :
    CBound (fun result : List Opening × (Digest × Digest) => result.1.length = 9) 31334 (signForest index output) :=
  cbound_of_ftsBound (ftsBound_signForest index output)
theorem bound_recoverCoordinate (sig : Signature) (index : Nat) (output : HashOutput) (coord : Coord)
    (prev : Digest × Digest) :
    CBound (fun _ => True) 15 (recoverCoordinate sig index output coord prev) :=
  cbound_of_ftsBound (ftsBound_recoverCoordinate index sig output coord prev)
theorem bound_recoverFts (sig : Signature) (index : Nat) (output : HashOutput) :
    CBound (fun _ => True) 140 (recoverFts sig index output) :=
  cbound_of_ftsBound (ftsBound_recoverFts index sig output)
/-- Stage-A FTS signing (T8 child code): per coordinate 51 coefficient pairs, 128 children of 24 chain steps + a
2-block leaf, and 126 heap nodes; then the 5-block forest key. -/
theorem signForest_blocks : 9 * (27 + 128 * (24 + 2) + 126) + 5 = 31334 := by norm_num
theorem verifyFts_blocks : 9 * (7 + 2 + 6) + 5 + 1 = 141 := by norm_num
def DigestResult (out : Option (BitVec 32 × HashOutput)) : Prop :=
  ∀ counter output, out = some (counter, output) → producerAdmissible output = true
theorem bound_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, CBound DigestResult fuel (digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter
      exact .pure none 0 (by simp [DigestResult])
  | succ fuel ih =>
      intro counter
      unfold digestSearch
      refine (bound_digest rho message (BitVec.ofNat 32 counter)).bind' (l := fuel)
        (fun output _ => ?_) (by omega)
      split
      · rename_i hgood
        refine .pure (some (BitVec.ofNat 32 counter, output)) fuel ?_
        intro other value hv
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hv)
        exact hgood
      · exact ih (counter + 1)
theorem bound_layerEncoding (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) (counter : BitVec 32) :
    CBound (fun _ => True) 1 (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInput lay tree leaf msg counter)) := by
  cases msg <;> apply bound_encodingHash <;>
    simp [layerEncodingInput, encodingInput, pairEncodingInputP, pad64_length, SphincsSecurity.bytesLE_length]
theorem bound_layerCounterSearch (lay : Layer) (tree leaf : Nat) (msg : LayerMsg) :
    ∀ fuel counter, CBound (CounterResult lay) fuel (layerCounterSearch lay tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter
      exact .pure none 0 (by simp [CounterResult])
  | succ fuel ih =>
      intro counter
      unfold layerCounterSearch
      refine (bound_layerEncoding lay tree leaf msg (BitVec.ofNat 32 counter)).bind' (l := fuel)
        (fun answer _ => ?_) (by omega)
      cases hs : producerDecode lay answer with
      | none => exact ih (counter + 1)
      | some digits =>
          have hd := producerDecode_decode hs
          refine .pure (some (BitVec.ofNat 32 counter, digits)) fuel ?_
          intro other values hv
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hv)
          exact ⟨(decode_length_sum hd).1, (decode_length_sum hd).2, validDigits_decode hd⟩
/-- v6: private pairs read for leaf `leaf`'s coefficients: its family's pairs at the family's first leaf, none for
the other members. -/
def leafSeedsP (lay : Layer) (leaf : Nat) : Nat :=
  if leaf % famGrp lay = 0 then famPairs lay (famOf lay leaf) else 0
def digitTotal (lay : Layer) : Nat := ∑ i ∈ Finset.range (chainCount lay), maxDigit lay i
def leafCostP (lay : Layer) (leaf : Nat) : Nat := leafSeedsP lay leaf + digitTotal lay + leafHashCost lay
theorem bound_lowerFamCoefs (lay : Layer) (tree f : Nat) :
    CBound (fun _ => True) (famPairs lay f) (lowerFamCoefs lay tree f) := by
  unfold lowerFamCoefs
  refine (Bound.foldlM_range (famPairs lay f) _ (fun _ _ => True) (fun _ => 1) [] trivial
    (fun j _ acc _ => ?_)).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by simp)
  exact (bound_privatePair 0 lay.val tree _ 0).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by omega)
theorem bound_lowerCoefs (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    CBound (fun _ => True) (leafSeedsP lay leaf) (lowerCoefs lay tree leaf carry) := by
  unfold lowerCoefs leafSeedsP
  split_ifs
  · exact (bound_lowerFamCoefs lay tree (famOf lay leaf)).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by omega)
  · exact .pure _ 0 trivial
theorem bound_buildLeafPF (lay : Layer) (tree leaf : Nat) (digits : List Nat) (hd : ValidDigits lay digits)
    (carry : List Digest) :
    CBound (fun result : (Digest × List Digest) × List Digest => result.1.2.length = chainCount lay) (leafCostP lay leaf)
      (buildLeafPF lay tree leaf digits carry) := by
  unfold buildLeafPF
  refine (bound_lowerCoefs lay tree leaf carry).bind' (l := digitTotal lay + leafHashCost lay)
    (fun res _ => ?_) (by unfold leafCostP; omega)
  refine Bound.bind' (l := leafHashCost lay) (Bound.foldlM_range (chainCount lay) _
    (fun i (state : List Digest × List Digest) => state.1.length = i ∧ state.2.length = i)
    (fun i => maxDigit lay i) ([], []) ⟨rfl, rfl⟩
    (fun i hi state hstate => ?_)) (fun state hstate => ?_) ?_
  · have hc := hd i hi
    refine (bound_chainW lay tree leaf i 0 (digits.getD i 0) _).bind'
      (l := maxDigit lay i - digits.getD i 0) (fun value _ => ?_) (by omega)
    refine (bound_chainW lay tree leaf i (digits.getD i 0) (maxDigit lay i - digits.getD i 0) value).bind'
      (l := 0) (fun last _ => ?_) (by omega)
    exact .pure _ 0 ⟨by simp only [List.length_append, List.length_singleton]; omega,
      by simp only [List.length_append, List.length_singleton]; omega⟩
  · refine (bound_lowerLeafHash lay tree leaf state.1 hstate.1).bind' (l := 0) (fun root _ => ?_) (by omega)
    exact .pure _ 0 hstate.2
  · unfold digitTotal
    exact le_refl _
theorem bound_buildLevelsBelow (tag lay tree h : Nat) (leaves : List Digest) (hlen : leaves.length = 2 ^ h)
    (hh : 1 ≤ h) : CBound (LevelShape h (h - 1)) (2 ^ h - 2) (buildLevelsBelow tag lay tree h leaves) := by
  unfold buildLevelsBelow
  refine Bound.foldlM_range'_le 1 (h - 1) _ (LevelShape h) (fun i => 2 ^ (h - i) / 2) [leaves]
    ⟨rfl, fun j hj => by
      have he : j = 0 := by omega
      subst j
      simpa using hlen⟩
    (fun i hi levels hlevels => ?_) (fun _ h => h) ?_
  · have hprevious : (levels.getD (1 + i - 1) []).length = 2 ^ (h - i) := by
      simpa using hlevels.2 i le_rfl
    refine (bound_lowerLevel lay tree h (1 + i) (levels.getD (1 + i - 1) [])).bind' (l := 0)
      (fun nodes hnodes => ?_) (by rw [hprevious]; omega)
    have hnext : nodes.length = 2 ^ (h - (i + 1)) := by
      rw [hprevious, show h - i = h - (i + 1) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)]
        at hnodes
      exact hnodes
    refine .pure (levels ++ [nodes]) 0 ⟨by simp [hlevels.1], ?_⟩
    intro j hj
    by_cases hold : j ≤ i
    · rw [List.getD_append levels [nodes] [] j (by have := hlevels.1; omega)]
      exact hlevels.2 j hold
    · have he : j = i + 1 := by omega
      subst j
      rw [List.getD_append_right levels [nodes] [] (i + 1) (by have := hlevels.1; omega)]
      simp only [hlevels.1, Nat.sub_self, List.getD_cons_zero]
      exact hnext
  · have hs := sum_levels h
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
    rw [Finset.sum_range_succ, show k + 1 - k = 1 by omega] at hs
    simp only [Nat.add_sub_cancel]
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    norm_num at hs
    omega
def treeCostP (lay : Layer) : Nat := (∑ leaf ∈ Finset.range (2 ^ height lay), leafCostP lay leaf) + (2 ^ height lay - 2)
theorem bound_buildTreeP (lay : Layer) (tree selected : Nat) (digits : List Nat) (hd : ValidDigits lay digits) :
    CBound (fun result => LevelShape (height lay) (height lay - 1) result.1) (treeCostP lay)
      (buildTreeP lay tree selected digits) := by
  unfold buildTreeP
  refine Bound.bind' (l := 2 ^ height lay - 2) (Bound.foldlM_range (2 ^ height lay) _
    (fun i (state : List Digest × List Digest × List Digest) => state.1.length = i)
    (leafCostP lay) ([], [], []) rfl (fun leaf _ state hstate => ?_))
    (fun state hstate => ?_) le_rfl
  · have hd' : ValidDigits lay (if leaf = selected then digits else []) := by
      split <;> first | exact hd | exact validDigits_nil lay
    refine (bound_buildLeafPF lay tree leaf _ hd' state.2.2).bind' (l := 0) (fun result _ => ?_) (by omega)
    exact .pure _ 0 (by simp [hstate])
  · refine (bound_buildLevelsBelow 3 lay.val tree (height lay) state.1 hstate
      (by fin_cases lay <;> decide)).bind' (l := 0)
      (fun levels hlevels => .pure (levels, state.2.1) 0 hlevels) (by omega)
theorem chainCount_lower {lay : Layer} (hlay : lay ≠ 0) : chainCount lay = 43 := by
  fin_cases lay <;> first | exact absurd rfl hlay | rfl
theorem maxDigit_lower {lay : Layer} (hlay : lay ≠ 0) (i : Nat) : maxDigit lay i = 7 := by
  unfold maxDigit; rw [if_neg hlay]
theorem digitTotal_lower {lay : Layer} (hlay : lay ≠ 0) : digitTotal lay = 301 := by
  unfold digitTotal
  rw [chainCount_lower hlay]
  simp only [maxDigit_lower hlay, Finset.sum_const, Finset.card_range, smul_eq_mul]
/-- Lower leaves: chains 301 + leaf hash 11, plus the family pairs at a family's first leaf. -/
theorem leafCostP_lower {lay : Layer} (hlay : lay ≠ 0) (leaf : Nat) :
    leafCostP lay leaf = leafSeedsP lay leaf + 312 := by
  unfold leafCostP
  rw [digitTotal_lower hlay]
  simp [leafHashCost, hlay]
/-- v6 lower trees: L1 reads 349 pairs (18 families of 19 + a 7-pair remainder), L2/L3 175 (9 · 19 + 4). -/
theorem treeCostP_one : treeCostP 1 = 40411 := by
  unfold treeCostP
  rw [Finset.sum_congr rfl (fun leaf _ => leafCostP_lower (by decide) leaf)]
  decide
theorem treeCostP_two : treeCostP 2 = 20205 := by
  unfold treeCostP
  rw [Finset.sum_congr rfl (fun leaf _ => leafCostP_lower (by decide) leaf)]
  decide
theorem treeCostP_three : treeCostP 3 = 20205 := by
  unfold treeCostP
  rw [Finset.sum_congr rfl (fun leaf _ => leafCostP_lower (by decide) leaf)]
  decide
theorem treeCostP_lower :
    treeCostP 1 + 2468 = treeCost 1 ∧ treeCostP 2 + 1234 = treeCost 2 ∧ treeCostP 3 + 1234 = treeCost 3 := by
  rw [treeCostP_one, treeCostP_two, treeCostP_three]
  decide
def layerFixedCostP : Nat → Nat
  | 0 => 0
  | n + 1 => if n = 0 then layerFixedCost 1 else treeCostP (Fin.ofNat 4 n) + layerFixedCostP n
theorem layerFixedCostP_succ (n : Nat) :
    layerFixedCostP (n + 1) = if n = 0 then layerFixedCost 1 else treeCostP (Fin.ofNat 4 n) + layerFixedCostP n := rfl
theorem layerFixedCostP_one : layerFixedCostP 1 = layerFixedCost 1 := (layerFixedCostP_succ 0).trans (if_pos rfl)
theorem layerFixedCostP_succ_succ (n : Nat) :
    layerFixedCostP (n + 2) = treeCostP (Fin.ofNat 4 (n + 1)) + layerFixedCostP (n + 1) := rfl
theorem layerFixedCost_succ_succ (n : Nat) :
    layerFixedCost (n + 2) = treeCost (Fin.ofNat 4 (n + 1)) + layerFixedCost (n + 1) := rfl
theorem layerFixedCostP_four : layerFixedCostP 4 + 4936 = layerFixedCost 4 := by
  obtain ⟨h1, h2, h3⟩ := treeCostP_lower
  have e3 : (Fin.ofNat 4 3 : Layer) = 3 := rfl
  have e2 : (Fin.ofNat 4 2 : Layer) = 2 := rfl
  have e1 : (Fin.ofNat 4 1 : Layer) = 1 := rfl
  simp only [layerFixedCostP_succ_succ, layerFixedCost_succ_succ, e3, e2, e1, Nat.zero_add, layerFixedCostP_one]
  omega
theorem bound_signLayersBC (cache : Cache) (index : Nat) :
    ∀ n msg, CBound (fun _ => True) (n * counterLimit + layerFixedCostP n) (signLayersBC cache index n msg) := by
  intro n
  induction n with
  | zero =>
      intro msg
      exact .pure _ _ trivial
  | succ n ih =>
      intro msg
      unfold signLayersBC
      dsimp only
      refine (bound_layerCounterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 msg (searchLimit (Fin.ofNat 4 n)) 0).bind'
        (l := n * counterLimit + layerFixedCostP (n + 1)) (fun out hout => ?_)
        (by have := searchLimit_le (Fin.ofNat 4 n); simp only [Nat.add_mul, Nat.one_mul]; omega)
      by_cases hn : n = 0
      · subst n
        simp only [ite_true]
        have hlen : ((out.map Prod.snd).getD dummyTop).length = 51 := by
          cases out with
          | none => decide
          | some pair =>
              obtain ⟨counter, digits⟩ := pair
              exact (hout counter digits rfl).1
        have hsum : ((out.map Prod.snd).getD dummyTop).sum = 152 ∨
            ((out.map Prod.snd).getD dummyTop).sum = target 0 := by
          cases out with
          | none => first | exact Or.inl (by decide) | exact Or.inr (by decide)
          | some pair =>
              obtain ⟨counter, digits⟩ := pair
              exact Or.inr (hout counter digits rfl).2.1
        have h126 : 152 ≤ target 0 := by decide
        have hle : ((out.map Prod.snd).getD dummyTop).sum ≤ target 0 := by
          rcases hsum with h | h <;> omega
        first
          | exact (bound_signTop cache _ _ hlen (le_of_le_of_eq hle (by decide))).bind'
              (l := 0) (fun _ _ => .pure _ 0 trivial) (by simp [layerFixedCostP, layerFixedCost])
          | exact (bound_signTop cache _ _ hlen (hsum.elim id fun h => h.trans (by decide))).bind'
              (l := 0) (fun _ _ => .pure _ 0 trivial) (by simp [layerFixedCostP, layerFixedCost])
      · simp only [hn, ite_false]
        cases out with
        | none => exact .pure _ _ trivial
        | some pair =>
            obtain ⟨counter, digits⟩ := pair
            have hd := hout counter digits rfl
            dsimp only
            refine (bound_buildTreeP (Fin.ofNat 4 n) _ _ digits hd.2.2).bind'
              (l := n * counterLimit + layerFixedCostP n) (fun result _ => ?_)
              (by simp only [layerFixedCostP, hn, ite_false]; omega)
            refine (ih _).bind' (l := 0) (fun previous _ => ?_) (by omega)
            cases previous <;> exact .pure _ 0 trivial
def recoverLayerPairCost (lay : Layer) : Nat := capacity lay - target lay + leafHashCost lay + (height lay - 1)
theorem recoverLayerPairCost_succ (lay : Layer) : recoverLayerPairCost lay + 1 = recoverLayerCost lay := by
  have : 1 ≤ height lay := by fin_cases lay <;> decide
  unfold recoverLayerPairCost recoverLayerCost
  omega
theorem bound_recoverLayerPair (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (hd : ValidDigits lay digits) (hlen : digits.length = chainCount lay) (hsum : digits.sum = target lay) :
    CBound (fun _ => True) (recoverLayerPairCost lay) (recoverLayerPair sig index lay digits) := by
  unfold recoverLayerPair
  dsimp only
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount lay)) _
    (fun i => maxDigit lay i.val - digits.getD i.val 0) (fun i _ => bound_chainW _ _ _ _ _ _ _)).bind'
    (l := leafHashCost lay + (height lay - 1)) (fun ends hends => ?_) ?_
  · refine (bound_lowerLeafHash lay _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine ((Bound.foldlM_list (P := GoodQuery) (List.finRange (height lay - 1)) _
      (fun _ _ => True) (fun _ => 1) root trivial (fun i hi value _ => ?_)).bind' (l := 0)
      (fun _ _ => .pure _ 0 trivial) (by simp))
    exact bound_lowerNodeHash _ _ _ _ _
  · rw [sum_finRange (chainCount lay) (fun i => maxDigit lay i - digits.getD i 0),
      remaining_steps lay digits hd hlen hsum]
    simp only [recoverLayerPairCost]
    omega
theorem bound_recoverLayerPairGuard (sig : Signature) (index : Nat) (lay : Layer) (answer : Digest)
    (digits : List Nat) (hd : ValidDigits lay digits) (hlen : digits.length = chainCount lay)
    (hsum : digits.sum = target lay) :
    CBound (fun _ => True) (recoverLayerPairCost lay) (recoverLayerPairGuard sig index lay answer digits) := by
  unfold recoverLayerPairGuard lowerGuardedRun
  split_ifs
  · exact Bound.map _ (bound_recoverLayerPair sig index lay digits hd hlen hsum) (fun _ _ => trivial)
  · refine (Bound.mapM_list (P := GoodQuery) (List.range (3 * lowerFirstBad answer)) _
      (fun i => maxDigit lay i - digits.getD i 0) (fun i _ => bound_chainW _ _ _ _ _ _ _)).bind'
      (l := 0) (fun _ _ => .pure _ 0 trivial) ?_
    have hn : 3 * lowerFirstBad answer ≤ chainCount lay := by
      have := lowerFirstBad_le answer
      have hc : 43 ≤ chainCount lay := by fin_cases lay <;> decide
      omega
    have hsplit := congrArg (fun xs : List Nat => (xs.map (fun i => maxDigit lay i - digits.getD i 0)).sum)
      (List.range_add (n := 3 * lowerFirstBad answer) (m := chainCount lay - 3 * lowerFirstBad answer))
    rw [Nat.add_sub_of_le hn] at hsplit
    simp only [List.map_append, List.sum_append] at hsplit
    have htotal : ((List.range (chainCount lay)).map
        (fun i => maxDigit lay i - digits.getD i 0)).sum = capacity lay - target lay := by
      rw [← List.sum_toFinset _ (List.nodup_range)]
      have he : (List.range (chainCount lay)).toFinset = Finset.range (chainCount lay) := by
        ext i
        simp
      rw [he]
      exact remaining_steps lay digits hd hlen hsum
    simp only [recoverLayerPairCost]
    omega
def recoveryLayersCostBC : Nat → Nat
  | 0 => 0
  | n + 1 => (if n = 0 then recoverLayerCost (Fin.ofNat 4 n) else recoverLayerPairCost (Fin.ofNat 4 n)) +
      recoveryLayersCostBC n
theorem recoveryLayersCostBC_add : recoveryLayersCostBC 4 + 3 = recoveryLayersCost 4 := by
  have h1 := recoverLayerPairCost_succ (Fin.ofNat 4 1)
  have h2 := recoverLayerPairCost_succ (Fin.ofNat 4 2)
  have h3 := recoverLayerPairCost_succ (Fin.ofNat 4 3)
  simp only [recoveryLayersCostBC, recoveryLayersCost, if_true, show (3 : Nat) ≠ 0 by decide,
    show (2 : Nat) ≠ 0 by decide, show (1 : Nat) ≠ 0 by decide, if_false]
  omega
theorem recoveryLayersCostBC_four_le : recoveryLayersCostBC 4 ≤ 481 := by
  have h := recoveryLayersCostBC_add
  have h4 := recoveryLayersCost_four
  omega
theorem bound_topDecodeRun (run : Fin (chainCount 0) → Nat → M Digest) (finish : List Digest → M Digest)
    (answer : Digest) (F : Nat) (hrun : ∀ i digit, CBound (fun _ => True) (maxDigit 0 i.val - digit) (run i digit))
    (hfinish : ∀ ends : List Digest, ends.length = chainCount 0 → CBound (fun _ => True) F (finish ends))
    (hF : capacity 0 - target 0 + F ≤ capacity 0) :
    CBound (fun _ => True) (capacity 0) (topDecodeRun run finish answer) := by
  cases hd : decode 0 answer with
  | some digits =>
      rw [topDecodeRun_of_decode hd]
      refine Bound.map some ((Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount 0)) _
        (fun i => maxDigit 0 i.val - digits.getD i.val 0) (fun i _ => hrun i _)).bind' (l := F)
        (fun ends hends => hfinish ends (by simpa using hends)) ?_) (fun _ _ => trivial)
      rw [sum_finRange (chainCount 0) (fun i => maxDigit 0 i - digits.getD i 0),
        remaining_steps 0 digits (validDigits_decode hd) (decode_length_sum hd).1 (decode_length_sum hd).2]
      exact hF
  | none =>
      rw [topDecodeRun_of_decode_none hd]
      unfold topRejectChains
      refine Bound.map _ ((Bound.mapM_list (P := GoodQuery) _ _ (fun i => maxDigit 0 i.val)
        (fun i _ => (hrun i _).mono_k (Nat.sub_le _ _))).mono_k ?_) (fun _ _ => trivial)
      have hsplit := congrArg (fun l : List (Fin (chainCount 0)) => (l.map fun i => maxDigit 0 i.val).sum)
        (List.take_append_drop (topRejectLength answer) (List.finRange (chainCount 0)))
      simp only [List.map_append, List.sum_append] at hsplit
      have htot : ((List.finRange (chainCount 0)).map fun i => maxDigit 0 i.val).sum = capacity 0 := by
        rw [sum_finRange (chainCount 0) (fun i => maxDigit 0 i), capacity_sum]
      omega
theorem bound_verifyTop (sig : Signature) (index : Nat) (answer : Digest) :
    CBound (fun _ => True) (capacity 0) (verifyTop sig index answer) := by
  unfold verifyTop
  generalize route index 0 = p
  obtain ⟨leaf, tree⟩ := p
  dsimp only
  refine bound_topDecodeRun _ _ answer (leafHashCost 0 + height 0) (fun i digit => bound_layChain _ _ _ _ _ _ _)
    (fun ends hends => ?_) (by decide)
  refine (bound_leafHash 0 _ _ ends hends).bind (fun root _ => ?_)
  exact (Bound.foldlM_list (P := GoodQuery) (List.finRange (height 0)) _ (fun _ _ => True) (fun _ => 1) root
    trivial (fun i hi value _ => bound_nodeHash _ _ _ _ _ _)).mono_k (by simp)
def verifyLayersCostBC : Nat → Nat
  | 0 => 0
  | n + 1 => (if n = 0 then capacity 0 else recoverLayerPairCost (Fin.ofNat 4 n)) + verifyLayersCostBC n
/-- Campaign T51: 236 (top capacity) + 119 + 118 + 118 (lower targets 199/199/199). -/
theorem verifyLayersCostBC_four_le : verifyLayersCostBC 4 ≤ 591 := by decide
theorem bound_verifyLayersBC (w : Witness) (index : Nat) :
    ∀ n msg, CBound (fun _ => True) (n + verifyLayersCostBC n) (verifyLayersBC w index n msg) := by
  intro n
  induction n with
  | zero => intro msg; exact .pure _ _ trivial
  | succ n ih =>
      intro msg
      unfold verifyLayersBC
      dsimp only
      split
      · exact .pure _ _ trivial
      · refine (bound_layerEncoding _ _ _ msg _).bind'
          (l := verifyLayersCostBC (n + 1) + n) (fun answer _ => ?_) (by simp only [verifyLayersCostBC]; omega)
        by_cases hn : n = 0
        · subst n
          rw [if_pos rfl]
          exact (bound_verifyTop w.signature index answer).mono_k (by simp [verifyLayersCostBC])
        · rw [if_neg hn]
          cases hd : decode (Fin.ofNat 4 n) answer with
          | none => exact .pure _ _ trivial
          | some digits =>
              dsimp only
              refine (bound_recoverLayerPairGuard w.signature index (Fin.ofNat 4 n) answer digits
                (validDigits_decode hd) (decode_length_sum hd).1 (decode_length_sum hd).2).bind'
                (l := n + verifyLayersCostBC n) (fun pair _ => ?_)
                (by simp only [verifyLayersCostBC, hn, ite_false]; omega)
              cases pair
              · exact .pure _ _ trivial
              · exact ih _
theorem bound_expandLayersBC (sig : Signature) (index : Nat) :
    ∀ n msg, CBound (fun _ => True) (n * counterLimit + recoveryLayersCostBC n) (expandLayersBC sig index n msg) := by
  intro n
  induction n with
  | zero => intro msg; exact .pure _ _ trivial
  | succ n ih =>
      intro msg
      unfold expandLayersBC
      dsimp only
      refine (bound_layerCounterSearch (Fin.ofNat 4 n) _ _ msg (searchLimit (Fin.ofNat 4 n)) 0).bind'
        (l := recoveryLayersCostBC (n + 1) + n * counterLimit)
        (fun found hf => ?_)
        (by have := searchLimit_le (Fin.ofNat 4 n); simp only [recoveryLayersCostBC, Nat.add_mul, Nat.one_mul]; omega)
      cases found with
      | none => exact .pure _ _ trivial
      | some pair =>
          obtain ⟨counter, digits⟩ := pair
          have hd := hf counter digits rfl
          dsimp only
          by_cases hn : n = 0
          · subst n
            simp only [ite_true]
            refine (bound_recoverLayer _ index (Fin.ofNat 4 0) digits hd.2.2 hd.1 hd.2.1).bind'
              (l := 0) (fun value _ => .pure _ 0 trivial) (by simp [recoveryLayersCostBC])
          · simp only [hn, ite_false]
            refine (bound_recoverLayerPair sig index (Fin.ofNat 4 n) digits hd.2.2 hd.1 hd.2.1).bind'
              (l := n * counterLimit + recoveryLayersCostBC n) (fun value _ => ?_)
              (by simp only [recoveryLayersCostBC, hn, ite_false]; omega)
            refine (ih _).bind' (l := 0) (fun result _ => ?_) (by omega)
            cases result <;> exact .pure _ 0 trivial
def signPayloadFixed : Nat := 2 + 31334 + layerFixedCostP 4
theorem signPayloadFixed_eq : signPayloadFixed + 5512 = 2 + 31910 + layerFixedCost 4 := by
  have h := layerFixedCostP_four
  unfold signPayloadFixed
  omega
theorem bound_signPayloadWith (limit : Nat) (cache : Cache) (message : Message) :
    CBound (fun _ => True) (signPayloadFixed + limit + 4 * counterLimit) (signPayloadWith limit cache message) := by
  rw [signPayloadWith_eq]
  refine (bound_privateNonce message).bind' (l := signPayloadFixed - 2 + limit + 4 * counterLimit)
    (fun rho _ => ?_) (by unfold signPayloadFixed; omega)
  refine (bound_digestSearch rho message limit 0).bind' (l := signPayloadFixed - 2 + 4 * counterLimit)
    (fun found _ => ?_) (by omega)
  cases found with
  | none => exact .pure _ _ trivial
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      dsimp only
      refine (bound_signForest _ output).bind' (l := layerFixedCostP 4 + 4 * counterLimit)
        (fun forest _ => ?_) (by unfold signPayloadFixed; omega)
      refine (bound_signLayersBC cache _ 4 (.pair forest.2.1 forest.2.2)).bind' (l := 0) (fun layers _ => ?_)
        (by omega)
      cases layers <;> exact .pure _ 0 trivial
theorem bound_signWith (limit : Nat) (cache : Cache) (message : Message) :
    CBound (fun _ => True) (signPayloadFixed + 2 + limit + 4 * counterLimit) (signWith limit cache message) := by
  unfold signWith
  refine (bound_privateMac cache.region).bind' (l := signPayloadFixed + limit + 4 * counterLimit)
    (fun tag _ => ?_) (by omega)
  split
  · exact .pure _ _ trivial
  · exact bound_signPayloadWith limit cache message
theorem bound_verifyWith (limit : Nat) (message : Message) (pk : Digest) (w : Witness) :
    CBound (fun _ => True) 737 (verifyWith limit message pk w) := by
  unfold verifyWith
  split
  · exact .pure _ _ trivial
  · refine (bound_digest w.signature.rho message w.digestCounter).bind' (l := 736)
      (fun output _ => ?_) (by decide)
    dsimp only
    split
    · exact .pure _ _ trivial
    · refine (bound_recoverFts w.signature _ output).bind' (l := 596) (fun root _ => ?_) (by decide)
      refine (bound_verifyLayersBC w _ 4 (.pair root.1 root.2)).bind' (l := 0) (fun r _ => ?_)
        (by have := verifyLayersCostBC_four_le; omega)
      cases r <;> exact .pure _ 0 trivial
theorem bound_expandWith (limit : Nat) (message : Message) (pk : Digest) (sig : Signature) :
    CBound (fun _ => True) (limit + 4 * counterLimit + 621) (expandWith limit message pk sig) := by
  unfold expandWith
  refine (bound_digestSearch sig.rho message limit 0).bind' (l := 4 * counterLimit + 621)
    (fun found _ => ?_) (by omega)
  cases found with
  | none => exact .pure _ _ trivial
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      dsimp only
      refine (bound_recoverFts sig _ output).bind' (l := 4 * counterLimit + 481)
        (fun root _ => ?_) (by omega)
      refine (bound_expandLayersBC sig _ 4 (.pair root.1 root.2)).bind' (l := 0)
        (fun layers _ => ?_) (by have := recoveryLayersCostBC_four_le; omega)
      cases layers with
      | none => exact .pure _ 0 trivial
      | some pair =>
          obtain ⟨root, counters⟩ := pair
          dsimp only
          split <;> exact .pure _ 0 trivial
theorem bound_signPayload (cache : Cache) (message : Message) :
    CBound (fun _ => True) (signPayloadFixed + digestAttemptLimit + 4 * counterLimit) (Rev3.signPayload cache message) :=
  bound_signPayloadWith digestAttemptLimit cache message
theorem bound_sign (cache : Cache) (message : Message) :
    CBound (fun _ => True) (signPayloadFixed + 2 + digestAttemptLimit + 4 * counterLimit) (Rev3.sign cache message) :=
  bound_signWith digestAttemptLimit cache message
theorem bound_verify (message : Message) (pk : Digest) (w : Witness) :
    CBound (fun _ => True) 737 (Rev3.verify message pk w) :=
  bound_verifyWith digestAttemptLimit message pk w
theorem sign_compression_ceiling (secret : BitVec 256) (cache : Cache) (message : Message) :
    ∀ result ∈ support (World.countBlocks (realize secret (Rev3.sign cache message))),
      result.2 ≤ 18995993 := by
  intro result hr
  rw [World.countBlocks, ← realize_count] at hr
  have hc := (bound_sign cache message).count_support result
    (realize_support_subset secret _ hr) |>.2
  have h := signPayloadFixed_eq
  rw [layerFixedCost_four] at h
  exact hc.trans (by norm_num [digestAttemptLimit, counterLimit]; omega)
theorem verify_compression_bound (secret : BitVec 256) (message : Message) (pk : Digest) (w : Witness) :
    ∀ result ∈ support (World.countBlocks (realize secret (Rev3.verify message pk w))), result.2 ≤ 737 := by
  intro result hr
  rw [World.countBlocks, ← realize_count] at hr
  exact (bound_verify message pk w).count_support result (realize_support_subset secret _ hr) |>.2
end ClaudeWCT.WCT9.Cost

/-!
# Executable source-level prototype of adjacent lower-leaf sharing

This standalone prototype materializes 14 coefficients (7 private pairs)
once per two leaves, then evaluates them at disjoint stride-58 points. It
is not the sign image and is not installed in the candidate certificate.
The compression bound below is for the actual OracleComp program, not a
numerical relabeling of the current independent-leaf program.
-/
namespace ClaudeWCT.WCT9.Cost.AdjacentLeafResearch
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Cost

/-- Padded pair family: avoids carry reuse between 13-coefficient groups. -/
def pairCoefs (lay : Layer) (tree group : Nat) : M (List Digest) :=
  (List.range 7).foldlM (fun cs j => do
    let p ← privatePair 0 lay.val tree (7*group+j) 0
    pure (cs ++ [p.1,p.2])) []

theorem bound_pairCoefs (lay : Layer) (tree group : Nat) :
    CBound (fun cs => cs.length = 14) 7 (pairCoefs lay tree group) := by
  unfold pairCoefs
  refine Bound.foldlM_range_le 7 _ (fun i (cs : List Digest) => cs.length = 2*i)
    (fun _ => 1) [] rfl (fun j _ cs hcs => ?_) (fun cs hcs => hcs) (by norm_num)
  refine (bound_privatePair 0 lay.val tree (7*group+j) 0).bind' (l := 0)
    (fun p _ => .pure _ 0 (by simp only [List.length_append, List.length_cons, List.length_nil]; omega))
    (by omega)

/-- Both leaves use the same coefficients, but no same-seed aliases. -/
def sharedLeaf (lay : Layer) (tree leaf : Nat) (digits : List Nat) (coefs : List Digest) :
    M (Digest × List Digest) := do
  let state ← (List.range (chainCount lay)).foldlM
    (fun (state : List Digest × List Digest) i => do
      let digit := digits.getD i 0
      let seed := ClaudeWCT.Arith.familyEval coefs (58*(leaf%2)+i+1)
      let value ← SigGolfCandidate.T3.chain lay tree leaf i 0 digit seed
      let last ← SigGolfCandidate.T3.chain lay tree leaf i digit (maxDigit lay i-digit) value
      pure (state.1 ++ [last], state.2 ++ [value])) ([],[])
  let root ← SigGolfCandidate.T3.leafHash lay tree leaf state.1
  pure (root,state.2)

theorem bound_sharedLeaf (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (hd : ValidDigits lay digits) (coefs : List Digest) :
    CBound (fun result => result.2.length = chainCount lay)
      (digitTotal lay+leafHashCost lay) (sharedLeaf lay tree leaf digits coefs) := by
  unfold sharedLeaf
  refine Bound.bind' (l := leafHashCost lay) (Bound.foldlM_range (chainCount lay) _
    (fun i (state : List Digest × List Digest) => state.1.length = i ∧ state.2.length = i)
    (fun i => maxDigit lay i) ([],[]) ⟨rfl,rfl⟩
    (fun i hi state hstate => ?_)) (fun state hstate => ?_) ?_
  · have hc := hd i hi
    refine (bound_chain lay tree leaf i 0 (digits.getD i 0) _).bind'
      (l := maxDigit lay i-digits.getD i 0) (fun value _ => ?_) (by omega)
    refine (bound_chain lay tree leaf i (digits.getD i 0) (maxDigit lay i-digits.getD i 0) value).bind'
      (l := 0) (fun last _ => ?_) (by omega)
    exact .pure _ 0 ⟨by simp only [List.length_append,List.length_singleton]; omega,
      by simp only [List.length_append,List.length_singleton]; omega⟩
  · refine (bound_leafHash lay tree leaf state.1 hstate.1).bind' (l := 0)
      (fun root _ => .pure _ 0 hstate.2) (by omega)
  · unfold digitTotal
    exact le_refl _

/-- A real pair of leaf roots and their selected signature values. -/
def sharedPair (lay : Layer) (tree group : Nat) (digits0 digits1 : List Nat) :
    M ((Digest × List Digest) × (Digest × List Digest)) := do
  let cs ← pairCoefs lay tree group
  let p0 ← sharedLeaf lay tree (2*group) digits0 cs
  let p1 ← sharedLeaf lay tree (2*group+1) digits1 cs
  pure (p0,p1)

theorem bound_sharedPair (lay : Layer) (hlay : lay ≠ 0) (tree group : Nat)
    (digits0 digits1 : List Nat) (h0 : ValidDigits lay digits0) (h1 : ValidDigits lay digits1) :
    CBound (fun result => result.1.2.length = 43 ∧ result.2.2.length = 43)
      631 (sharedPair lay tree group digits0 digits1) := by
  have hd : digitTotal lay = 301 := digitTotal_lower hlay
  have hl : leafHashCost lay = 11 := by simp [leafHashCost,hlay]
  have hc : chainCount lay = 43 := chainCount_lower hlay
  unfold sharedPair
  refine (bound_pairCoefs lay tree group).bind' (l := 624) (fun cs _ => ?_) (by omega)
  refine (bound_sharedLeaf lay tree (2*group) digits0 h0 cs).bind' (l := 312)
    (fun p0 hp0 => ?_) (by simp only [hd,hl]; omega)
  refine (bound_sharedLeaf lay tree (2*group+1) digits1 h1 cs).bind' (l := 0)
    (fun p1 hp1 => .pure _ 0 (by simpa only [hc] using And.intro hp0 hp1))
    (by simp only [hd,hl]; omega)

/-- Independent B4 leaf bound 316+316 versus actual sharedPair bound 631. -/
theorem pair_saves_one_compression : 316+316-631 = 1 := by decide

/-- Leaves+Merkle-node cost of the proposed three paired lower trees. -/
theorem paired_tree_costs :
    (128/2*631+(128-2)) = 40510 ∧
    (64/2*631+(64-2)) = 20254 ∧
    (128*316+(128-2)) + 2*(64*316+(64-2)) -
      ((128/2*631+(128-2))+2*(64/2*631+(64-2))) = 128 := by decide


/-- Complete source-level paired lower tree, including selected-leaf
signature values and all Merkle levels. This still is not the sign image. -/
def sharedTree (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    M (List (List Digest) × List Digest) := do
  let state ← (List.range (2^height lay/2)).foldlM
    (fun (state : List Digest × List Digest) group => do
      let p ← sharedPair lay tree group
        (if 2*group = selected then digits else [])
        (if 2*group+1 = selected then digits else [])
      pure (state.1 ++ [p.1.1,p.2.1],
        if 2*group = selected then p.1.2 else if 2*group+1 = selected then p.2.2 else state.2)) ([],[])
  let levels ← buildLevelsBelow 3 lay.val tree (height lay) state.1
  pure (levels,state.2)

def sharedTreeCost (lay : Layer) : Nat := (2^height lay/2)*631+(2^height lay-2)

/-- Compression bound for the complete actual OracleComp tree prototype. -/
theorem bound_sharedTree (lay : Layer) (hlay : lay ≠ 0) (tree selected : Nat) (digits : List Nat)
    (hd : ValidDigits lay digits) :
    CBound (fun result => LevelShape (height lay) (height lay-1) result.1)
      (sharedTreeCost lay) (sharedTree lay tree selected digits) := by
  have he : 2*(2^height lay/2) = 2^height lay := by
    fin_cases lay <;> decide
  unfold sharedTree sharedTreeCost
  refine Bound.bind' (l := 2^height lay-2) (Bound.foldlM_range_le (2^height lay/2) _
    (fun i (state : List Digest × List Digest) => state.1.length = 2*i)
    (fun _ => 631) ([],[]) rfl (fun group _ state hs => ?_)
    (fun state hs => hs) (by simp)) (fun state hs => ?_) le_rfl
  · have hd0 : ValidDigits lay (if 2*group=selected then digits else []) := by
      split <;> first | exact hd | exact validDigits_nil lay
    have hd1 : ValidDigits lay (if 2*group+1=selected then digits else []) := by
      split <;> first | exact hd | exact validDigits_nil lay
    refine (bound_sharedPair lay hlay tree group _ _ hd0 hd1).bind' (l := 0)
      (fun p _ => .pure _ 0 (by simp only [List.length_append,List.length_cons,List.length_nil]; omega))
      (by omega)
  · have hlen : state.1.length = 2^height lay := hs.trans he
    refine (bound_buildLevelsBelow 3 lay.val tree (height lay) state.1 hlen
      (by fin_cases lay <;> decide)).bind' (l := 0)
      (fun levels hlevels => .pure (levels,state.2) 0 hlevels) (by omega)


end ClaudeWCT.WCT9.Cost.AdjacentLeafResearch
end
-- ==== merged from ClaudeWCT_WCT9_Omit ====
section

/-! # H2: two omitted signature bytes, recovered by a 2^16 search against the public key

`Limits.lean` defines the omission (`setTop`, `fillTop`, `proj`, `topSib`) and the expander `expandS`: it runs the
old expansion on `proj sig` (the omitted top 16 bits of the top layer's level-11 sibling read as zero), keeps the
level-11 node `v`, and if the root is not the public key it searches the completions `c = 1, 2, ...` with one node
hash each. This file relates `expandS` to the old expander `expandWith`: every answer of `expandS` is the answer of
`expandWith` on a completion `fillTop sig c` (`eval_expandS`), and whenever `expandWith` succeeds on a signature,
`expandS` succeeds on it too (`expandS_complete`). Exact recovery of the original bits is not claimed. -/

section
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-! ### Bits -/

theorem setTop_toNat (d : Digest) (c : Nat) :
    (setTop d c).toNat = d.toNat % 2 ^ 112 + c % 2 ^ 16 * 2 ^ 112 := by
  unfold setTop
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h1 : d.toNat % 2 ^ 112 < 2 ^ 112 := Nat.mod_lt _ (by positivity)
  have h2 : c % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by positivity)
  have h3 : c % 2 ^ 16 * 2 ^ 112 ≤ (2 ^ 16 - 1) * 2 ^ 112 := Nat.mul_le_mul_right _ (by omega)
  have h4 : (2 ^ 16 - 1) * 2 ^ 112 + 2 ^ 112 = (2 : Nat) ^ 128 := by norm_num
  omega

theorem setTop_setTop (d : Digest) (a b : Nat) : setTop (setTop d a) b = setTop d b := by
  apply BitVec.eq_of_toNat_eq
  rw [setTop_toNat, setTop_toNat, setTop_toNat]
  congr 1
  rw [Nat.add_mul_mod_self_right, Nat.mod_mod]

theorem setTop_self (d : Digest) : setTop d (d.toNat / 2 ^ 112) = d := by
  apply BitVec.eq_of_toNat_eq
  rw [setTop_toNat]
  have hd := d.isLt
  have h : d.toNat / 2 ^ 112 < 2 ^ 16 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    norm_num at hd ⊢
    omega
  rw [Nat.mod_eq_of_lt h]
  have := Nat.mod_add_div d.toNat (2 ^ 112)
  rw [Nat.mul_comm] at this
  omega

theorem top_lt (d : Digest) : d.toNat / 2 ^ 112 < 2 ^ 16 := by
  have hd := d.isLt
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  norm_num at hd ⊢
  omega

/-! ### Completions -/

theorem fillLayer_values (lay : Layer) (ls : LayerSignature lay) (c : Nat) :
    (fillLayer lay ls c).values = ls.values := rfl

theorem fillLayer_path_ne (lay : Layer) (ls : LayerSignature lay) (c : Nat) (j : Fin (height lay))
    (hj : ¬(lay.val = 0 ∧ j.val = 11)) : (fillLayer lay ls c).path j = ls.path j := by
  simp only [fillLayer, if_neg hj]

theorem fillLayer_ne (lay : Layer) (ls : LayerSignature lay) (c : Nat) (h : lay.val ≠ 0) :
    fillLayer lay ls c = ls := by
  cases ls with
  | mk values path =>
    simp only [fillLayer, LayerSignature.mk.injEq, true_and]
    funext j
    rw [if_neg (fun h' => h h'.1)]

theorem fillLayer_fillLayer (lay : Layer) (ls : LayerSignature lay) (a b : Nat) :
    fillLayer lay (fillLayer lay ls a) b = fillLayer lay ls b := by
  cases ls with
  | mk values path =>
    simp only [fillLayer, LayerSignature.mk.injEq, true_and]
    funext j
    by_cases hj : lay.val = 0 ∧ j.val = 11
    · simp only [if_pos hj, setTop_setTop]
    · simp only [if_neg hj]

@[simp] theorem fillTop_rho (sig : Signature) (c : Nat) : (fillTop sig c).rho = sig.rho := rfl
@[simp] theorem fillTop_openings (sig : Signature) (c : Nat) : (fillTop sig c).openings = sig.openings := rfl
theorem fillTop_layers (sig : Signature) (c : Nat) (lay : Layer) :
    (fillTop sig c).layers lay = fillLayer lay (sig.layers lay) c := rfl

theorem fillTop_fillTop (sig : Signature) (a b : Nat) : fillTop (fillTop sig a) b = fillTop sig b := by
  unfold fillTop
  simp only [Signature.mk.injEq, true_and]
  funext lay
  exact fillLayer_fillLayer lay (sig.layers lay) a b

theorem proj_fillTop (sig : Signature) (c : Nat) : proj (fillTop sig c) = proj sig := by
  unfold proj; exact fillTop_fillTop sig c 0

theorem proj_proj (sig : Signature) : proj (proj sig) = proj sig := proj_fillTop sig 0

theorem fillTop_proj (sig : Signature) (c : Nat) : fillTop (proj sig) c = fillTop sig c := by
  unfold proj; exact fillTop_fillTop sig 0 c

theorem topSib_fillTop (sig : Signature) (c : Nat) : topSib (fillTop sig c) = setTop (topSib sig) c := by
  unfold topSib
  rw [fillTop_layers]
  simp only [fillLayer]
  rw [if_pos ⟨rfl, rfl⟩]

theorem fillTop_self (sig : Signature) : fillTop sig ((topSib sig).toNat / 2 ^ 112) = sig := by
  cases sig with
  | mk rho openings layers =>
    unfold fillTop
    simp only [Signature.mk.injEq, true_and]
    funext lay
    cases hls : layers lay with
    | mk values path =>
      simp only [fillLayer, LayerSignature.mk.injEq, true_and]
      funext j
      by_cases hj : lay.val = 0 ∧ j.val = 11
      · rw [if_pos hj]
        have hl : lay = 0 := Fin.ext hj.1
        subst hl
        have hjj : j = topJ := Fin.ext hj.2
        subst hjj
        have : topSib ⟨rho, openings, layers⟩ = path topJ := by
          unfold topSib; simp only [hls]
        rw [this, setTop_self]
      · rw [if_neg hj]

theorem fillLayer_rest (lay : Layer) (ls : LayerSignature lay) (a b : Nat) (j : Fin (height lay))
    (hj : ¬(lay.val = 0 ∧ j.val = 11)) : (fillLayer lay ls a).path j = (fillLayer lay ls b).path j := by
  rw [fillLayer_path_ne _ _ _ _ hj, fillLayer_path_ne _ _ _ _ hj]

/-! ### The top layer split at its last node -/

theorem recoverLayer_unfold (sig : SigGolfCandidate.T3.Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    recoverLayer sig index lay digits =
      ((List.finRange (chainCount lay)).mapM fun i => SigGolfCandidate.T3.layChain lay (route index lay).2
        (route index lay).1 i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
        ((sig.layers lay).values i)) >>=
      fun ends => SigGolfCandidate.T3.leafHash lay (route index lay).2 (route index lay).1 ends >>= fun value =>
        (List.finRange (height lay)).foldlM (fun value j => do
          let other := (sig.layers lay).path j
          let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
          nodeHash 3 lay.val (route index lay).2 (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1))
            pair.1 pair.2) value := rfl

theorem finRange_top_split : List.finRange (height (0 : Layer)) = (List.finRange (height 0)).take 11 ++ [topJ] := by
  decide

theorem take_top_lt : ∀ j ∈ (List.finRange (height (0 : Layer))).take 11, j.val < 11 := by
  decide

theorem recoverLayer_top (sig : Signature) (index : Nat) (digits : List Nat) :
    recoverLayer (toT3Signature sig) index 0 digits =
      topFold sig index digits >>= fun v => topNode index v (topSib sig) := by
  rw [recoverLayer_unfold]
  unfold topFold topEnds
  simp only [bind_assoc]
  refine bind_congr fun ends => ?_
  refine bind_congr fun value => ?_
  conv_lhs => rw [finRange_top_split]
  simp only [List.foldlM_append, List.foldlM_cons, List.foldlM_nil, bind_pure]
  rfl

theorem foldlM_congr_mem {m : Type → Type} [Monad m] {α β : Type} (f g : α → β → m α) :
    ∀ (l : List β), (∀ a, ∀ b ∈ l, f a b = g a b) → ∀ init, l.foldlM f init = l.foldlM g init
  | [], _, _ => rfl
  | b :: l, h, init => by
      rw [List.foldlM_cons, List.foldlM_cons, h init b (List.mem_cons_self ..)]
      refine bind_congr fun x => ?_
      exact foldlM_congr_mem f g l (fun a b' hb => h a b' (List.mem_cons_of_mem _ hb)) x

theorem topStep_fill (sig : Signature) (index : Nat) (a b : Nat) (value : Digest) (j : Fin (height 0))
    (hj : j.val < 11) : topStep (fillTop sig a) index value j = topStep (fillTop sig b) index value j := by
  unfold topStep
  rw [fillTop_layers, fillTop_layers, fillLayer_rest 0 (sig.layers 0) a b j (fun h => by omega)]

theorem topFold_fill (sig : Signature) (index : Nat) (digits : List Nat) (a b : Nat) :
    topFold (fillTop sig a) index digits = topFold (fillTop sig b) index digits := by
  unfold topFold topEnds
  rw [fillTop_layers, fillTop_layers, fillLayer_values, fillLayer_values]
  refine bind_congr fun ends => ?_
  refine bind_congr fun value => ?_
  exact foldlM_congr_mem _ _ _ (fun x j hj => topStep_fill sig index a b x j (take_top_lt j hj)) value

theorem topStepN_fill (sig : Signature) (index : Nat) (a b : Nat) (st : Digest × List Nat) (j : Fin (height 0))
    (hj : j.val < 11) : topStepN (fillTop sig a) index st j = topStepN (fillTop sig b) index st j := by
  unfold topStepN
  rw [fillTop_layers, fillTop_layers, fillLayer_rest 0 (sig.layers 0) a b j (fun h => by omega)]

/-- Top-bytes layer: the nonce re-derivation ignores the omitted top sibling bits. -/
theorem topFoldN_fill (sig : Signature) (index : Nat) (digits : List Nat) (a b : Nat) :
    topFoldN (fillTop sig a) index digits = topFoldN (fillTop sig b) index digits := by
  unfold topFoldN topEnds
  rw [fillTop_layers, fillTop_layers, fillLayer_values, fillLayer_values]
  refine bind_congr fun ends => ?_
  refine bind_congr fun value => ?_
  exact foldlM_congr_mem _ _ _ (fun x j hj => topStepN_fill sig index a b x j (take_top_lt j hj)) _

theorem topFold_proj (sig : Signature) (index : Nat) (digits : List Nat) :
    topFold (proj sig) index digits = topFold sig index digits := by
  have h := topFold_fill sig index digits 0 ((topSib sig).toNat / 2 ^ 112)
  rw [fillTop_self] at h
  exact h

theorem recoverLayerPair_fill (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) (c : Nat)
    (h : lay.val ≠ 0) : recoverLayerPair (fillTop sig c) index lay digits = recoverLayerPair sig index lay digits := by
  unfold recoverLayerPair
  rw [fillTop_layers, fillLayer_ne lay (sig.layers lay) c h]

theorem fin_ofNat_succ_ne (k : Nat) (hk : k + 1 < 4) : (Fin.ofNat 4 (k + 1) : Layer).val ≠ 0 := by
  simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hk]
  omega

/-- The old layer expansion is the new one on `proj sig` with the old sibling, with `v` dropped. -/
theorem expandLayersBC_eq_T (sig : Signature) (index : Nat) :
    ∀ n, n ≤ 4 → ∀ msg, expandLayersBC sig index n msg =
      (Option.map fun x => (x.2.1, x.2.2)) <$> expandLayersT (proj sig) index (topSib sig) n msg := by
  intro n
  induction n with
  | zero => intro _ msg; simp [expandLayersBC, expandLayersT]
  | succ n ih =>
    intro hn msg
    simp only [expandLayersBC, expandLayersT, map_bind]
    refine bind_congr fun r => ?_
    rcases r with _ | ⟨counter, digits⟩
    · simp
    · cases n with
      | zero =>
        simp only [if_true, map_bind, map_pure, Option.map_some]
        have h0 : (Fin.ofNat 4 0 : Layer) = 0 := rfl
        rw [h0, recoverLayer_top, topFold_proj, bind_assoc]
      | succ k =>
        have hne := fin_ofNat_succ_ne k (by omega)
        simp only [Nat.succ_ne_zero, if_false, map_bind]
        unfold proj
        rw [recoverLayerPair_fill sig index _ digits 0 hne]
        refine bind_congr fun pair => ?_
        rw [ih (by omega), bind_map_left]
        unfold proj
        refine bind_congr fun r' => ?_
        rcases r' with _ | ⟨v, root, counters⟩ <;> simp

/-- Changing the top sibling only changes the last node hash. -/
theorem eval_expandLayersT_other (answers : Answers) (s : Signature) (index : Nat) (o o' : Digest) :
    ∀ n msg, evalWithAnswerFn answers (expandLayersT s index o' n msg) =
      (evalWithAnswerFn answers (expandLayersT s index o n msg)).map
        (fun x => (x.1, evalWithAnswerFn answers (topNode index x.1 o'), x.2.2)) := by
  intro n
  induction n with
  | zero => intro msg; simp [expandLayersT]
  | succ n ih =>
    intro msg
    simp only [expandLayersT, evalWithAnswerFn_bind]
    split
    · rename_i counter digits _
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, if_false, evalWithAnswerFn_bind, ih]
        cases evalWithAnswerFn answers (expandLayersT s index o n _) with
        | none => simp
        | some x => simp
    · simp

theorem map_some_inv {α β : Type} {f : α → β} {x : Option α} {y : β} (h : x.map f = some y) :
    ∃ a, x = some a ∧ f a = y := by
  cases x with
  | none => simp at h
  | some a => exact ⟨a, rfl, Option.some.inj h⟩

/-! ### The search -/

theorem eval_searchTop (answers : Answers) (index : Nat) (v sib pk : Digest) :
    ∀ fuel c0 c, evalWithAnswerFn answers (searchTop index v sib pk fuel c0) = some c →
      c0 ≤ c ∧ c < c0 + fuel ∧ evalWithAnswerFn answers (topNode index v (setTop sib c)) = pk := by
  intro fuel
  induction fuel with
  | zero => intro c0 c h; simp [searchTop] at h
  | succ fuel ih =>
    intro c0 c h
    simp only [searchTop, evalWithAnswerFn_bind] at h
    split at h
    · rename_i hr
      simp only [evalWithAnswerFn_pure, Option.some.injEq] at h
      subst h
      exact ⟨le_refl _, by omega, hr⟩
    · obtain ⟨h1, h2, h3⟩ := ih (c0 + 1) c h
      exact ⟨by omega, by omega, h3⟩

theorem searchTop_complete (answers : Answers) (index : Nat) (v sib pk : Digest) :
    ∀ fuel c0 c, c0 ≤ c → c < c0 + fuel → evalWithAnswerFn answers (topNode index v (setTop sib c)) = pk →
      ∃ c', evalWithAnswerFn answers (searchTop index v sib pk fuel c0) = some c' := by
  intro fuel
  induction fuel with
  | zero => intro c0 c h1 h2; omega
  | succ fuel ih =>
    intro c0 c h1 h2 h3
    simp only [searchTop, evalWithAnswerFn_bind]
    split
    · exact ⟨c0, rfl⟩
    · rename_i hne
      by_cases hc : c = c0
      · subst hc; exact absurd h3 hne
      · exact ih (c0 + 1) c (by omega) (by omega) h3

/-! ### The old expander with its digest output -/

/-- `expandWith` keeping the digest output (the W9 witness encoding needs it). -/
def expandWithN (limit : Nat) (message : Message) (pk : Digest) (sig : Signature) :
    M (Option (HashOutput × Witness)) := do
  let some (counter, output) ← digestSearch sig.rho message 0 limit | pure none
  let index := digestIndex output
  let root ← recoverFts sig index output
  let some (root, counters) ← expandLayersBC sig index 4 (.pair root.1 root.2) | pure none
  if root ≠ pk then return none
  pure (some (output, ⟨sig, counter, fun lay => counters.getD lay.val 0⟩))

theorem expandWith_eq_N (limit : Nat) (m : Message) (pk : Digest) (σ : Signature) :
    expandWith limit m pk σ = Option.map Prod.snd <$> expandWithN limit m pk σ := by
  unfold expandWith expandWithN
  rw [map_bind]; congr 1; funext r
  rcases r with _ | ⟨counter, output⟩
  · simp
  · simp only
    rw [map_bind]; congr 1; funext root
    rw [map_bind]; congr 1; funext r
    rcases r with _ | ⟨root, counters⟩
    · simp
    · simp only
      split <;> simp

theorem recoverFts_fillTop (sig : Signature) (c : Nat) (index : Nat) (output : HashOutput) :
    recoverFts (fillTop sig c) index output = recoverFts sig index output := rfl

theorem eval_expandWithN_fill (answers : Answers) (limit : Nat) (m : Message) (pk : Digest) (σ : Signature)
    (c : Nat) :
    evalWithAnswerFn answers (expandWithN limit m pk (fillTop σ c)) =
      match evalWithAnswerFn answers (digestSearch σ.rho m 0 limit) with
      | none => none
      | some (counter, output) =>
        match (evalWithAnswerFn answers (expandLayersT (proj σ) (digestIndex output) (topSib (proj σ)) 4
            (.pair (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)).1 (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)).2))).map
            (fun x => (x.1, evalWithAnswerFn answers (topNode (digestIndex output) x.1 (setTop (topSib σ) c)),
              x.2.2)) with
        | none => none
        | some (_, root, counters) =>
          if root ≠ pk then none else some (output, ⟨fillTop σ c, counter, fun lay => counters.getD lay.val 0⟩) := by
  unfold expandWithN
  simp only [evalWithAnswerFn_bind, fillTop_rho]
  cases evalWithAnswerFn answers (digestSearch σ.rho m 0 limit) with
  | none => rfl
  | some found =>
    obtain ⟨counter, output⟩ := found
    simp only [evalWithAnswerFn_bind, recoverFts_fillTop]
    rw [expandLayersBC_eq_T (fillTop σ c) _ 4 le_rfl, evalWithAnswerFn_map, proj_fillTop, topSib_fillTop,
      eval_expandLayersT_other answers (proj σ) _ (topSib (proj σ)) (setTop (topSib σ) c), Option.map_map]
    cases evalWithAnswerFn answers (expandLayersT (proj σ) (digestIndex output) (topSib (proj σ)) 4
        (.pair (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)).1 (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)).2)) with
    | none => rfl
    | some x =>
      obtain ⟨v, root, counters⟩ := x
      simp only [Option.map_some, Function.comp]
      split <;> simp_all

theorem topSib_proj (σ : Signature) : topSib (proj σ) = setTop (topSib σ) 0 := by
  unfold proj; exact topSib_fillTop σ 0

/-- Every answer of the H2 expander is the old expander's answer on some completion. -/
theorem eval_expandS (answers : Answers) (limit : Nat) (m : Message) (pk : Digest) (σ : Signature)
    (N : HashOutput) (w : Witness) (h : evalWithAnswerFn answers (expandS limit m pk σ) = some (N, w)) :
    ∃ c, c < 2 ^ 19 ∧ w.signature = fillTop σ c ∧
      evalWithAnswerFn answers (expandWithN limit m pk (fillTop σ c)) = some (N, w) := by
  unfold expandS at h
  simp only [evalWithAnswerFn_bind] at h
  have hrho : (proj σ).rho = σ.rho := rfl
  rw [hrho] at h
  cases hd : evalWithAnswerFn answers (digestSearch σ.rho m 0 limit) with
  | none => rw [hd] at h; simp at h
  | some found =>
    obtain ⟨counter, output⟩ := found
    rw [hd] at h
    simp only [evalWithAnswerFn_bind] at h
    have hfts : recoverFts (proj σ) (digestIndex output) output = recoverFts σ (digestIndex output) output :=
      recoverFts_fillTop σ 0 _ _
    rw [hfts] at h
    cases hl : evalWithAnswerFn answers (expandLayersT (proj σ) (digestIndex output) (topSib (proj σ)) 4
        (.pair (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)).1 (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)).2)) with
    | none => rw [hl] at h; simp at h
    | some x =>
      obtain ⟨v, root, counters⟩ := x
      rw [hl] at h
      simp only at h
      have hroot : evalWithAnswerFn answers (topNode (digestIndex output) v (topSib (proj σ))) = root := by
        have := eval_expandLayersT_other answers (proj σ) (digestIndex output) (topSib (proj σ))
          (topSib (proj σ)) 4 (.pair (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)).1 (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)).2)
        rw [hl] at this
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
        exact this.2.1.symm
      by_cases hpk : root = pk
      · rw [if_pos hpk] at h
        simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨0, by norm_num, rfl, ?_⟩
        rw [eval_expandWithN_fill, hd]
        simp only
        rw [hl]
        simp only [Option.map_some]
        rw [← topSib_proj, hroot, if_neg (not_not.mpr hpk)]
        rfl
      · rw [if_neg hpk] at h
        simp only [evalWithAnswerFn_bind] at h
        cases hs : evalWithAnswerFn answers (searchTop (digestIndex output) v (topSib (proj σ)) pk searchFuel 1) with
        | none => rw [hs] at h; simp at h
        | some c =>
          rw [hs] at h
          simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2, h3⟩ := eval_searchTop answers _ v _ pk searchFuel 1 c hs
          refine ⟨c, by unfold searchFuel at h2; omega, fillTop_proj σ c, ?_⟩
          rw [fillTop_proj, eval_expandWithN_fill, hd]
          simp only
          rw [hl]
          simp only [Option.map_some]
          rw [topSib_proj, setTop_setTop] at h3
          rw [h3, if_neg (not_not.mpr rfl)]

/-- Whenever the old expander accepts a signature, the H2 expander returns something on it. -/
theorem expandS_complete (answers : Answers) (limit : Nat) (m : Message) (pk : Digest) (σ : Signature)
    (x : HashOutput × Witness) (h : evalWithAnswerFn answers (expandWithN limit m pk σ) = some x) :
    ∃ y, evalWithAnswerFn answers (expandS limit m pk σ) = some y := by
  have hσ := fillTop_self σ
  set ch := (topSib σ).toNat / 2 ^ 112 with hch
  rw [← hσ, eval_expandWithN_fill] at h
  unfold expandS
  simp only [evalWithAnswerFn_bind]
  have hrho : (proj σ).rho = σ.rho := rfl
  rw [hrho]
  cases hd : evalWithAnswerFn answers (digestSearch σ.rho m 0 limit) with
  | none => rw [hd] at h; simp at h
  | some found =>
    obtain ⟨counter, output⟩ := found
    rw [hd] at h
    simp only at h
    simp only [evalWithAnswerFn_bind]
    rw [show recoverFts (proj σ) = recoverFts σ from rfl]
    cases hl : evalWithAnswerFn answers (expandLayersT (proj σ) (digestIndex output) (topSib (proj σ)) 4
        (.pair (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)).1 (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)).2)) with
    | none => rw [hl] at h; simp at h
    | some y =>
      obtain ⟨v, root, counters⟩ := y
      rw [hl] at h
      simp only [Option.map_some] at h
      have hmatch : evalWithAnswerFn answers (topNode (digestIndex output) v (setTop (topSib σ) ch)) = pk := by
        by_contra hne
        rw [if_pos hne] at h
        simp at h
      simp only
      split
      · exact ⟨_, rfl⟩
      · rename_i hne
        have hroot : evalWithAnswerFn answers (topNode (digestIndex output) v (topSib (proj σ))) = root := by
          have := eval_expandLayersT_other answers (proj σ) (digestIndex output) (topSib (proj σ))
            (topSib (proj σ)) 4 (.pair (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)).1 (evalWithAnswerFn answers (recoverFts σ (digestIndex output) output)).2)
          rw [hl] at this
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
          exact this.2.1.symm
        have hch0 : ch ≠ 0 := by
          intro h0
          rw [h0, ← topSib_proj, hroot] at hmatch
          exact hne hmatch
        have hsib : setTop (topSib (proj σ)) ch = setTop (topSib σ) ch := by rw [topSib_proj, setTop_setTop]
        obtain ⟨c', hc'⟩ := searchTop_complete answers (digestIndex output) v (topSib (proj σ)) pk searchFuel 1 ch
          (by omega) (by have := top_lt (topSib σ); unfold searchFuel; omega) (by rw [hsib]; exact hmatch)
        simp only [evalWithAnswerFn_bind, hc', evalWithAnswerFn_pure]
        exact ⟨_, rfl⟩

/-! ### Rev3: the H2 expander's correctness, from the old expander's -/

namespace Rev3

theorem eval_expand (answers : Answers) (message : Message) (pk : Digest) (sig : Signature) :
    evalWithAnswerFn answers (expand message pk sig) =
      (evalWithAnswerFn answers (expandS digestAttemptLimit message pk sig)).map Prod.snd := by
  unfold expand; rw [evalWithAnswerFn_map]

theorem expand_completes (answers : Answers) (message : Message) (pk : Digest) (sig : Signature) (w : Witness)
    (he : evalWithAnswerFn answers (expand message pk sig) = some w) :
    ∃ c, c < 2 ^ 19 ∧ w.signature = fillTop sig c ∧
      evalWithAnswerFn answers (expandWith digestAttemptLimit message pk (fillTop sig c)) = some w := by
  rw [eval_expand] at he
  obtain ⟨⟨N, w'⟩, hx, rfl⟩ := map_some_inv he
  obtain ⟨c, hc, hsig, hN⟩ := eval_expandS answers _ message pk sig N w' hx
  refine ⟨c, hc, hsig, ?_⟩
  rw [expandWith_eq_N, evalWithAnswerFn_map, hN]
  rfl

theorem expand_implies_verify (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (w : Witness) (he : evalWithAnswerFn answers (expand message pk sig) = some w) :
    evalWithAnswerFn answers (verify message pk w) = true := by
  obtain ⟨c, -, -, h⟩ := expand_completes answers message pk sig w he
  exact expandWith_implies_verifyWith digestAttemptLimit digestAttemptLimit_le answers message pk _ w h

theorem expand_of_expandWith (answers : Answers) (message : Message) (pk : Digest) (sig : Signature)
    (w : Witness) (he : evalWithAnswerFn answers (expandWith digestAttemptLimit message pk sig) = some w) :
    ∃ w', evalWithAnswerFn answers (expand message pk sig) = some w' ∧
      evalWithAnswerFn answers (verify message pk w') = true := by
  rw [expandWith_eq_N, evalWithAnswerFn_map] at he
  obtain ⟨x, hx, -⟩ := map_some_inv he
  obtain ⟨y, hy⟩ := expandS_complete answers _ message pk sig x hx
  have he' : evalWithAnswerFn answers (expand message pk sig) = some y.2 := by
    rw [eval_expand, hy]; rfl
  exact ⟨y.2, he', expand_implies_verify answers message pk sig y.2 he'⟩

end Rev3
end ClaudeWCT.WCT9
end

section
namespace ClaudeWCT.WCT9.Cost
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem take_top_length : ((List.finRange (height (0 : Layer))).take 11).length = 11 := by decide

theorem bound_topFold (s : Signature) (index : Nat) (digits : List Nat)
    (hd : ValidDigits 0 digits) (hlen : digits.length = chainCount 0) (hsum : digits.sum = target 0) :
    CBound (fun _ => True) (capacity 0 - target 0 + leafHashCost 0 + 11) (topFold s index digits) := by
  unfold topFold topEnds
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount 0)) _
    (fun i => maxDigit 0 i.val - digits.getD i.val 0) (fun i _ => bound_layChain _ _ _ _ _ _ _)).bind'
    (l := leafHashCost 0 + 11) (fun ends hends => ?_) ?_
  · refine (bound_leafHash 0 _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine (Bound.foldlM_list (P := GoodQuery) ((List.finRange (height 0)).take 11) _
      (fun _ _ => True) (fun _ => 1) root trivial (fun i hi value _ => ?_)).mono_k (by rw [take_top_length]; simp)
    unfold topStep
    exact bound_nodeHash _ _ _ _ _ _
  · rw [sum_finRange (chainCount 0) (fun i => maxDigit 0 i - digits.getD i 0),
      remaining_steps 0 digits hd hlen hsum]
    omega

theorem bound_topNode (index : Nat) (v o : Digest) : CBound (fun _ => True) 1 (topNode index v o) := by
  unfold topNode; exact bound_nodeHash _ _ _ _ _ _

theorem recoverLayerCost_top : capacity 0 - target 0 + leafHashCost 0 + 11 + 1 = recoverLayerCost 0 := by
  decide

theorem bound_expandLayersT (sig : Signature) (index : Nat) (o : Digest) :
    ∀ n msg, CBound (fun _ => True) (n * counterLimit + recoveryLayersCostBC n) (expandLayersT sig index o n msg) := by
  intro n
  induction n with
  | zero => intro msg; exact .pure _ _ trivial
  | succ n ih =>
      intro msg
      unfold expandLayersT
      dsimp only
      refine (bound_layerCounterSearch (Fin.ofNat 4 n) _ _ msg (searchLimit (Fin.ofNat 4 n)) 0).bind'
        (l := recoveryLayersCostBC (n + 1) + n * counterLimit)
        (fun found hf => ?_)
        (by have := searchLimit_le (Fin.ofNat 4 n); simp only [recoveryLayersCostBC, Nat.add_mul, Nat.one_mul]; omega)
      cases found with
      | none => exact .pure _ _ trivial
      | some pair =>
          obtain ⟨counter, digits⟩ := pair
          have hd := hf counter digits rfl
          dsimp only
          by_cases hn : n = 0
          · subst n
            simp only [ite_true]
            refine (bound_topFold sig index digits hd.2.2 hd.1 hd.2.1).bind' (l := 1)
              (fun v _ => (bound_topNode index v o).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by omega))
              (by decide)
          · simp only [hn, ite_false]
            refine (bound_recoverLayerPair sig index (Fin.ofNat 4 n) digits hd.2.2 hd.1 hd.2.1).bind'
              (l := n * counterLimit + recoveryLayersCostBC n) (fun value _ => ?_)
              (by simp only [recoveryLayersCostBC, hn, ite_false]; omega)
            refine (ih _).bind' (l := 0) (fun result _ => ?_) (by omega)
            cases result <;> exact .pure _ 0 trivial

theorem bound_searchTop (index : Nat) (v sib pk : Digest) :
    ∀ fuel c, CBound (fun _ => True) fuel (searchTop index v sib pk fuel c) := by
  intro fuel
  induction fuel with
  | zero => intro c; exact .pure _ _ trivial
  | succ fuel ih =>
      intro c
      unfold searchTop
      refine (bound_topNode index v (setTop sib c)).bind' (l := fuel) (fun r _ => ?_) (by omega)
      split
      · exact .pure _ _ trivial
      · exact ih (c + 1)

theorem bound_expandS (limit : Nat) (message : Message) (pk : Digest) (sig : Signature) :
    CBound (fun _ => True) (limit + 4 * counterLimit + 621 + searchFuel) (expandS limit message pk sig) := by
  unfold expandS
  refine (bound_digestSearch (proj sig).rho message limit 0).bind' (l := 4 * counterLimit + 621 + searchFuel)
    (fun found _ => ?_) (by omega)
  cases found with
  | none => exact .pure _ _ trivial
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      dsimp only
      refine (bound_recoverFts (proj sig) _ output).bind' (l := 4 * counterLimit + 481 + searchFuel)
        (fun root _ => ?_) (by omega)
      refine (bound_expandLayersT (proj sig) _ (topSib (proj sig)) 4 (.pair root.1 root.2)).bind' (l := searchFuel)
        (fun layers _ => ?_) (by have := recoveryLayersCostBC_four_le; omega)
      cases layers with
      | none => exact .pure _ _ trivial
      | some triple =>
          obtain ⟨v, root, counters⟩ := triple
          dsimp only
          split
          · exact .pure _ _ trivial
          · refine (bound_searchTop _ v _ pk searchFuel 1).bind' (l := 0) (fun c _ => ?_) (by omega)
            cases c <;> exact .pure _ 0 trivial

theorem bound_expand (message : Message) (pk : Digest) (sig : Signature) :
    CBound (fun _ => True) (digestAttemptLimit + 4 * counterLimit + 621 + searchFuel) (Rev3.expand message pk sig) := by
  unfold Rev3.expand
  exact Bound.map _ (bound_expandS digestAttemptLimit message pk sig) (fun _ _ => trivial)

theorem expand_compression_ceiling (secret : BitVec 256) (message : Message) (pk : Digest) (sig : Signature) :
    ∀ result ∈ support (World.countBlocks (realize secret (Rev3.expand message pk sig))),
      result.2 ≤ 19399276 := by
  intro result hr
  rw [World.countBlocks, ← realize_count] at hr
  have hc := (bound_expand message pk sig).count_support result
    (realize_support_subset secret _ hr) |>.2
  exact hc.trans (by norm_num [digestAttemptLimit, counterLimit, searchFuel])

end ClaudeWCT.WCT9.Cost
end
end
-- ==== merged from ClaudeWCT_WCT9_TopNonce ====
section

/-! Top-bytes layer: the verifier's top path with witness nonces agrees with the expander's nonce re-derivation
(`topFoldN`), and the honest top path through the nonce-searched top tree. -/
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem eval_foldlM_eq {α β : Type} (answers : Answers) (f : α → β → M α) :
    ∀ (l : List β) (a : α),
      evalWithAnswerFn answers (l.foldlM f a) = l.foldl (fun s x => evalWithAnswerFn answers (f s x)) a
  | [], a => by simp [evalWithAnswerFn_pure]
  | x :: l, a => by
      rw [List.foldlM_cons, evalWithAnswerFn_bind, eval_foldlM_eq answers f l]
      rfl

theorem eval_topNonceSearch_hash (answers : Answers) (h heap : Nat) (left right : Digest) :
    ∀ fuel n, evalWithAnswerFn answers
        (topNodeHashN heap (evalWithAnswerFn answers (topNonceSearch h heap left right fuel n)).1 left right) =
      (evalWithAnswerFn answers (topNonceSearch h heap left right fuel n)).2
  | 0, n => by
      simp only [topNonceSearch, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  | fuel+1, n => by
      simp only [topNonceSearch, evalWithAnswerFn_bind]
      split
      · simp only [evalWithAnswerFn_pure]
      · exact eval_topNonceSearch_hash answers h heap left right fuel (n+1)

theorem eval_topNodeAt_hash (answers : Answers) (h heap : Nat) (left right : Digest) :
    evalWithAnswerFn answers
        (topNodeHashN heap (evalWithAnswerFn answers (topNodeAt h heap left right)).1 left right) =
      (evalWithAnswerFn answers (topNodeAt h heap left right)).2 :=
  eval_topNonceSearch_hash answers h heap left right _ 0

/-- The evaluated recovery step (`topStepN`). -/
def rstep (answers : Answers) (sig : Signature) (index : Nat) (st : Digest × List Nat) (j : Fin (height 0)) :
    Digest × List Nat :=
  evalWithAnswerFn answers (topStepN sig index st j)

theorem rstep_prefix (answers : Answers) (sig : Signature) (index : Nat) :
    ∀ (js : List (Fin (height 0))) (st : Digest × List Nat) (k : Nat), k < st.2.length →
      (js.foldl (rstep answers sig index) st).2.getD k 0 = st.2.getD k 0
  | [], _, _, _ => rfl
  | j :: rest, st, k, hk => by
      rw [List.foldl_cons, rstep_prefix answers sig index rest _ k (by
        simp only [rstep, topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.length_append,
          List.length_singleton]; omega)]
      simp only [rstep, topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      rw [List.getD_append _ _ _ _ hk]

theorem rstep_length (answers : Answers) (sig : Signature) (index : Nat) :
    ∀ (js : List (Fin (height 0))) (st : Digest × List Nat),
      (js.foldl (rstep answers sig index) st).2.length = st.2.length + js.length
  | [], _ => by simp
  | j :: rest, st => by
      rw [List.foldl_cons, rstep_length answers sig index rest]
      simp only [rstep, topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.length_append,
        List.length_cons, List.length_nil]
      omega

/-- The verifier's step with nonce list `N` (heights ≤ 11). -/
def vstep (answers : Answers) (sig : Signature) (index : Nat) (N : List Nat) (value : Digest)
    (j : Fin (height 0)) : Digest :=
  let other := (sig.layers 0).path j
  let pair := if (route index 0).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
  evalWithAnswerFn answers (topNodeHashN (2 ^ (height 0 - j.val - 1) + (route index 0).1 / 2 ^ (j.val + 1))
    (N.getD j.val 0) pair.1 pair.2)

theorem vstep_fold (answers : Answers) (sig : Signature) (index : Nat) (N : List Nat) :
    ∀ (js : List (Fin (height 0))) (st : Digest × List Nat),
      js.map Fin.val = List.range' st.2.length js.length →
      (∀ k, k < st.2.length + js.length → N.getD k 0 = (js.foldl (rstep answers sig index) st).2.getD k 0) →
      js.foldl (vstep answers sig index N) st.1 = (js.foldl (rstep answers sig index) st).1
  | [], _, _, _ => rfl
  | j :: rest, st, hjs, hN => by
      have hj : j.val = st.2.length := by
        simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hjs
        exact hjs.1
      have hrest : rest.map Fin.val = List.range' (st.2.length + 1) rest.length := by
        simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hjs
        exact hjs.2
      rw [List.foldl_cons, List.foldl_cons]
      have hstep : vstep answers sig index N st.1 j = (rstep answers sig index st j).1 := by
        have hn := hN st.2.length (by simp)
        rw [List.foldl_cons, rstep_prefix answers sig index rest _ st.2.length (by
          simp only [rstep, topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.length_append,
            List.length_singleton]; omega)] at hn
        simp only [rstep, topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.getD_append_right _ _ _ _ le_rfl,
          Nat.sub_self, List.getD_cons_zero] at hn
        simp only [vstep, rstep, topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hj, hn]
        exact eval_topNodeAt_hash answers _ _ _ _
      rw [hstep]
      apply vstep_fold answers sig index N rest
      · simp only [rstep, topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.length_append,
          List.length_singleton]
        exact hrest
      · intro k hk
        rw [hN k (by
          simp only [rstep, topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.length_append,
            List.length_singleton] at hk ⊢
          simp only [List.length_cons]; omega), List.foldl_cons]

theorem topLevelNode_lt (answers : Answers) {level : Nat} (hl : level ≠ 12) (heap : Nat) (left right : Digest) :
    topLevelNode answers level heap left right = (evalWithAnswerFn answers (topNodeAt level heap left right)).2 := by
  unfold topLevelNode; rw [if_neg hl]

/-- The expander's nonce fold climbs the honest (nonce-searched) top tree up to level 11. -/
theorem eval_topFoldN_steps_honest (answers : Answers) (sig : Signature) (index : Nat)
    (levels leaves : _) (htree : TopTreeLevels answers leaves 12 levels)
    (hleaf : (route index 0).1 < 2 ^ 12)
    (hpath : ∀ j : Fin (height 0), (sig.layers 0).path j =
      treeValue levels j.val ((route index 0).1 / 2 ^ j.val ^^^ 1)) (acc : List Nat) :
    (evalWithAnswerFn answers (((List.finRange (height 0)).take 11).foldlM (topStepN sig index)
      (treeValue levels 0 (route index 0).1, acc))).1 = treeValue levels 11 ((route index 0).1 / 2 ^ 11) := by
  have hi := eval_foldlM_list_inv answers ((List.finRange (height 0)).take 11) (topStepN sig index)
    (fun i (st : Digest × List Nat) => st.1 = treeValue levels i ((route index 0).1 / 2 ^ i))
    (treeValue levels 0 (route index 0).1, acc) (by simp) (fun i hi st hv => ?_)
  · have hl : ((List.finRange (height 0)).take 11).length = 11 := by decide
    rw [hl] at hi
    exact hi
  · have hi' : i < 11 := by
      have h' := hi
      simp only [List.length_take, List.length_finRange] at h'
      change i < min 11 12 at h'
      omega
    generalize hj : ((List.finRange (height 0)).take 11)[i]'hi = j
    have hjv : j.val = i := by
      subst hj
      simp [List.getElem_take]
    simp only [topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hpath, hv, hjv]
    rw [sibling_pair (fun k => treeValue levels i k), div_pow_succ]
    have hp := htree.2.2 i (by omega) ((route index 0).1 / 2 ^ (i+1))
      (by simpa only [Nat.zero_add] using
        div_pow_bound (height := 12) (start := 0) (level := i+1) (by omega) (by simpa using hleaf))
    rw [topLevelNode_lt answers (level := i+1) (by omega)] at hp
    have hh : height 0 - i - 1 = 12 - (i+1) := by
      change 12 - i - 1 = 12 - (i+1); omega
    rw [hh]
    simpa only [treeValue] using hp.symm

theorem eval_verifyTopN_topFoldN (answers : Answers) (sig : Signature) (index : Nat) {answer : Digest}
    {digits : List Nat} (h : decode 0 answer = some digits) :
    evalWithAnswerFn answers (verifyTopN sig (evalWithAnswerFn answers (topFoldN sig index digits)).2 index answer) =
      some (evalWithAnswerFn answers (topNode index (evalWithAnswerFn answers (topFoldN sig index digits)).1
        ((sig.layers 0).path topJ))) := by
  have hsplit : List.finRange (height 0) = (List.finRange (height 0)).take 11 ++ [topJ] := by decide
  have hlt : ∀ j ∈ (List.finRange (height 0)).take 11, j.val < 11 := by decide
  have hmap : ((List.finRange (height 0)).take 11).map Fin.val = List.range' 0 11 := by decide
  unfold verifyTopN
  rw [topDecodeRun_of_decode h]
  simp only [evalWithAnswerFn_map, evalWithAnswerFn_bind, topFoldN, eval_foldlM_eq]
  generalize hv0 : evalWithAnswerFn answers (SigGolfCandidate.T3.leafHash 0 (route index 0).2 (route index 0).1
    (evalWithAnswerFn answers (topEnds sig index digits))) = v0
  have hv0' : evalWithAnswerFn answers (SigGolfCandidate.T3.leafHash 0 (route index 0).2 (route index 0).1
      (evalWithAnswerFn answers ((List.finRange (chainCount 0)).mapM fun i =>
        SigGolfCandidate.T3.layChain 0 (route index 0).2 (route index 0).1 i.val (digits.getD i.val 0)
          (maxDigit 0 i.val - digits.getD i.val 0) ((sig.layers 0).values i)))) = v0 := hv0
  rw [hv0']
  generalize hR : List.foldl (fun s x => evalWithAnswerFn answers (topStepN sig index s x)) (v0, [])
    ((List.finRange (height 0)).take 11) = R
  conv_lhs => rw [hsplit, List.foldl_append]
  rw [List.foldl_ext _ (vstep answers sig index R.2) v0 (fun a b hb => by
    rw [if_pos (hlt b hb)]; rfl)]
  have hv := vstep_fold answers sig index R.2 ((List.finRange (height 0)).take 11) (v0, [])
    (by rw [hmap]; rfl) (fun k _ => by rw [← hR]; rfl)
  simp only at hv
  rw [show List.foldl (rstep answers sig index) (v0, []) ((List.finRange (height 0)).take 11) = R from hR] at hv
  rw [hv]
  rfl
/-- Top-bytes layer: on an honest top signature the expander's nonce fold followed by the root node reproduces the
keygen top tree's root. -/
theorem eval_topNode_topFoldN_honest (answers : Answers) (sig : Signature) (index : Nat) (hindex : index < 2 ^ 31)
    (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (hvalues : ∀ i, (sig.layers 0).values i = leafValue answers 0 0 (route index 0).1 digits i.val)
    (hpath : ∀ j : Fin (height 0), (sig.layers 0).path j =
      treeValue (builtTree answers 0 0) j.val ((route index 0).1 / 2 ^ j.val ^^^ 1)) :
    evalWithAnswerFn answers (topNode index (evalWithAnswerFn answers (topFoldN sig index digits)).1
      ((sig.layers 0).path topJ)) = treeValue (builtTree answers 0 0) 12 0 := by
  have ht : (route index 0).2 = 0 := route_top_tree index hindex
  have hleaf : (route index 0).1 < 2 ^ 12 := route_leaf_bound index 0
  have htree := builtTopTree_correct answers 0
  have hends : evalWithAnswerFn answers (topEnds sig index digits) =
      (List.range (chainCount 0)).map (leafEnd answers 0 0 (route index 0).1) := by
    unfold topEnds
    rw [ht]
    exact eval_chains_honest answers 0 0 _ digits hvalid _ hvalues
  have hroot : evalWithAnswerFn answers (SigGolfCandidate.T3.leafHash 0 (route index 0).2 (route index 0).1
      (evalWithAnswerFn answers (topEnds sig index digits))) =
      treeValue (builtTree answers 0 0) 0 (route index 0).1 := by
    rw [hends, ht, builtTree_leaf answers 0 0 _ hleaf]
    rfl
  have hfold : (evalWithAnswerFn answers (topFoldN sig index digits)).1 =
      treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11) := by
    unfold topFoldN
    simp only [evalWithAnswerFn_bind]
    rw [hroot]
    exact eval_topFoldN_steps_honest answers sig index _ _ htree hleaf hpath []
  rw [hfold, hpath topJ]
  unfold topNode
  have hpair := sibling_pair (fun k => treeValue (builtTree answers 0 0) 11 k) ((route index 0).1 / 2 ^ 11)
  have hz : (route index 0).1 / 2 ^ 11 / 2 = 0 := by
    rw [div_pow_succ]; exact Nat.div_eq_of_lt (by simpa using hleaf)
  rw [hz] at hpair
  change evalWithAnswerFn answers (nodeHash 3 0 (route index 0).2 (2 ^ (12 - 11 - 1) + (route index 0).1 / 2 ^ (11 + 1))
    (if (route index 0).1 / 2 ^ 11 % 2 = 0 then
        (treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11),
          treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11 ^^^ 1))
      else (treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11 ^^^ 1),
          treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11))).1
    (if (route index 0).1 / 2 ^ 11 % 2 = 0 then
        (treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11),
          treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11 ^^^ 1))
      else (treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11 ^^^ 1),
          treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11))).2) = _
  rw [hpair, ht, show (route index 0).1 / 2 ^ (11 + 1) = 0 by rw [← div_pow_succ]; exact hz]
  have hp := htree.2.2 11 (by decide) 0 (by decide)
  simp only [treeValue] at hp ⊢
  rw [hp]
  simp [topLevelNode]

end ClaudeWCT.WCT9
end
-- ==== merged from Research_V7Composed198Gate ====
section
set_option autoImplicit false
namespace SigGolfCandidate.Research.V7Composed198Gate
theorem even_gate (g : Nat) : g / 2 < 1182 ↔ g < 2364 := by omega

theorem gate_shift44_toNat (answer : BitVec 256) :
    (answer.extractLsb' 192 64 >>> 44).toNat =
      (answer.toNat / 2^235 % 2^21) / 2 := by
  rw [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

theorem gate_ult_shift44 (answer : BitVec 256) :
    BitVec.ult (answer.extractLsb' 192 64 >>> 44) 1182#64 =
      decide (answer.toNat / 2^235 % 2^21 < 2364) := by
  simp only [BitVec.ult, gate_shift44_toNat, show (1182#64 : BitVec 64).toNat = 1182 from rfl,
    even_gate]

/-- T8E gate (14 bits at 242, limit 1353): the top 14 bits of the last 64-bit digest word. -/
theorem gate_shift50_toNat (answer : BitVec 256) :
    (answer.extractLsb' 192 64 >>> 50).toNat = answer.toNat / 2^242 % 2^14 := by
  rw [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h := BitVec.isLt answer
  omega

theorem gate_ult_shift50 (answer : BitVec 256) :
    BitVec.ult (answer.extractLsb' 192 64 >>> 50) 1353#64 =
      decide (answer.toNat / 2^242 % 2^14 < 1353) := by
  simp only [BitVec.ult, gate_shift50_toNat, show (1353#64 : BitVec 64).toNat = 1353 from rfl]

theorem gate_ult_const (answer : BitVec 256) :
    BitVec.ult (answer.extractLsb' 192 64) 0x1524000000000000#64 =
      decide (answer.toNat / 2^242 % 2^14 < 1353) := by
  rw [← gate_ult_shift50]
  simp only [BitVec.ult, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (0x1524000000000000#64 : BitVec 64).toNat = 1523342573958070272 from rfl,
    show (1353#64 : BitVec 64).toNat = 1353 from rfl, decide_eq_decide]
  omega

end SigGolfCandidate.Research.V7Composed198Gate
/-! Finite layout certificates for the proposed shared-path forest. These definitions
are not connected to the submitted machine image or the scheme parameters. -/
namespace SigGolfCandidate.Research.SharedPathPacking

/-- C1 (FTS Merkle half-swap, stage 1): the fold window bases of child levels `0..4`, in bytes, indexed by the
five low path bits (`plans_merged.json`, the first optimal plan per class of the exhaustive search with the
level-four window pinned at `X = 128`, R pad at 160). -/
def plans : List (List Nat) :=
  [[16,64,208,256,128],
   [0,64,208,256,128],
   [16,192,256,64,128],
   [0,192,256,64,128],
   [16,64,192,256,128],
   [0,64,192,256,128],
   [64,0,192,256,128],
   [0,80,192,256,128],
   [16,64,256,192,128],
   [0,64,256,192,128],
   [16,192,256,80,128],
   [0,192,256,80,128],
   [16,256,192,80,128],
   [0,256,192,80,128],
   [256,192,0,80,128],
   [0,192,272,80,128],
   [16,64,192,240,128],
   [0,64,192,240,128],
   [16,176,240,64,128],
   [256,0,64,192,128],
   [16,64,176,240,128],
   [0,64,176,240,128],
   [64,0,176,240,128],
   [48,0,176,240,128],
   [16,64,240,176,128],
   [0,64,240,176,128],
   [64,0,240,176,128],
   [48,0,240,176,128],
   [64,240,176,0,128],
   [0,64,176,256,128],
   [64,0,176,256,128],
   [0,272,224,176,128]]

def bitAt (j l : Nat) : Nat := j / 2 ^ l % 2
def block (j l : Nat) : Nat := ((plans.getD (j % 32) []).getD l 0)
def current (j l : Nat) : Nat := block j l + 48 * bitAt j l
def sibling (j l : Nat) : Nat := block j l + 48 * (1 - bitAt j l)
def pad (j l : Nat) : Nat := block j l + 32
/-- C1: the high header word `block + 24` stays witness memory on every packed level `0..3` (the verifier writes
only the low header word there); level four writes both header words. -/
def keepsHigh (_j l : Nat) : Bool := decide (l < 4)
/-- C1: the value of level `l` (the leaf for `l = 0`) uses the high half of its hash output on a left input of
levels `0..3` (an even heap `16..255`); the 32-byte answer is then written at `current - 16`, otherwise at
`current`. -/
def highValue (j l : Nat) : Bool := decide (l ≤ 3 ∧ bitAt j l = 0)
def outO (j l : Nat) : Nat := if highValue j l then current j l - 16 else current j l
/-- The eight-byte words written by the time the fold of level `l` reads its window: the 32-byte answer carrying
the level-`l` value, the low header word and, on level four, the high header word. -/
def writes (j l : Nat) : List Nat :=
  [outO j l, outO j l + 8, outO j l + 16, outO j l + 24,
   block j l + 16] ++ (if keepsHigh j l then [] else [block j l + 24])
def priorWrites (j n : Nat) : List Nat := (List.range n).flatMap (writes j)

/-- C1 layout rules. The prior coordinate writes a whole hash answer at 144: its low (junk) half occupies the
level-four header at 144, its high half is the R pad at 160. Every window is 16-aligned inside `[0, 400)`; every
sibling, non-R pad and high header word lies in `[0, 320)` and is still witness memory when its fold reads it; the
R pad survives until the level-four fold; siblings are pairwise distinct and never share a 16-byte granule with a
pad, a high header word or the hand-off granules 144 and 160. -/
def planOK (j : Nat) : Bool :=
  decide (block j 4 = 128) &&
  (List.range 5).all (fun l =>
    decide (block j l % 16 = 0 ∧ block j l + 64 ≤ 400 ∧ sibling j l + 16 ≤ 320 ∧
      (l < 4 → pad j l + 16 ≤ 320 ∧ block j l ≠ 128) ∧ (highValue j l = true → 16 ≤ current j l)) &&
    decide (sibling j l ≠ 144 ∧ sibling j l ≠ 160 ∧
      (l < 4 → pad j l ≠ 144 ∧ pad j l ≠ 160 ∧ block j l + 16 ≠ 144 ∧ block j l + 16 ≠ 160)) &&
    (priorWrites j (l + 1)).all (fun a =>
      decide (a ≠ sibling j l ∧ a ≠ sibling j l + 8 ∧ a ≠ pad j l ∧ a ≠ pad j l + 8)) &&
    (if keepsHigh j l then (priorWrites j (l + 1)).all
      (fun a => decide (a ≠ block j l + 24)) else true)) &&
  (List.range 5).all (fun i => (List.range 5).all (fun l =>
    decide (sibling j i ≠ pad j l ∧ (i ≠ l → sibling j i ≠ sibling j l)) &&
    (if keepsHigh j l then decide (sibling j i ≠ block j l + 16) else true)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem planOK_all : ∀ j : Fin 128, planOK j.val = true := by
  intro j
  fin_cases j <;> decide +kernel

theorem block_four (j : Nat) : block j 4 = 128 := by
  have h : ∀ i, i < 32 → ((plans.getD i []).getD 4 0) = 128 := by decide
  exact h (j % 32) (Nat.mod_lt _ (by decide))

/-- C1: `skips′`, the elided `addi a2` words of a child routine: the levels whose output address equals the
previous one. The final jump to block 832 cannot reuse the output address. -/
def saves (j : Nat) : Nat :=
  ((List.range 4).map fun l => if outO j (l + 1) = outO j l then 1 else 0).sum

/-- The per-class table of `saves` (`2 - saves` is the accounting correction). -/
def savesTable : List Nat :=
  [0,1,1,1,1,2,2,1,1,2,2,2,2,2,2,1,0,1,1,2,1,2,2,1,1,2,2,1,1,1,1,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem saves_table : ∀ j : Fin 128, saves j.val = savesTable.getD (j.val % 32) 0 := by
  intro j; fin_cases j <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem saves_bounds : ∀ j : Fin 128, saves j.val ≤ 2 := by
  intro j; fin_cases j <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem total_saves : ((List.range 32).map saves).sum = 42 := by decide +kernel

end SigGolfCandidate.Research.SharedPathPacking

/-!
Private shared-path construction under development. The executable source
model below is separate from `SigGolf.Challenge.submission`: its machine
refinement and security certificate are not yet installed.

Each pair has two 64-child branches. Both coordinates select the same
branch. The first coordinate supplies a pair of nodes inside that branch;
the second binds those nodes through its leaf and level-four padding and
supplies the outer authentication sibling. This removes one digest per
pair while retaining the original degree-53 private seed families.
-/
namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.WCT9

abbrev PairRoot := Digest × Digest

/-- B tables enumerate physical leaves by rotating the raw child field.
Private seed and chain/leaf addresses retain the original raw child. -/
def rawChild (first : Bool) (physical : Nat) : Nat :=
  if first then physical else 2 * (physical % 64) + physical / 64

def physicalChild (first : Bool) (raw : Nat) : Nat :=
  if first then raw else raw / 2 + 64 * (raw % 2)

theorem physicalChild_lt (first : Bool) (raw : Nat) (h : raw < 128) :
    physicalChild first raw < 128 := by
  cases first <;> simp only [physicalChild, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem raw_physical_child (first : Bool) (raw : Nat) (h : raw < 128) :
    rawChild first (physicalChild first raw) = raw := by
  cases first <;> simp only [rawChild, physicalChild, Bool.false_eq_true, ↓reduceIte] <;> omega

structure Selection where
  branch : Fin 2
  first : Fin 64
  second : Fin 64

def firstChild (s : Selection) : Child :=
  ⟨64 * s.branch.val + s.first.val, by have := s.branch.isLt; have := s.first.isLt; omega⟩

def secondChild (s : Selection) : Child :=
  ⟨64 * s.branch.val + s.second.val, by have := s.branch.isLt; have := s.second.isLt; omega⟩

theorem selected_branch (s : Selection) :
    (firstChild s).val / 64 = (secondChild s).val / 64 := by
  have hb := s.branch.isLt
  have ha := s.first.isLt
  have hc := s.second.isLt
  simp only [firstChild, secondChild]
  omega

structure PairOpening where
  firstValues : Fin 6 → Digest
  firstPath : Fin 6 → Digest
  secondValues : Fin 6 → Digest
  secondPath : Fin 7 → Digest

def nodesPair (nodes : Array Digest) (branch : Nat) : PairRoot :=
  (nodes.getD (4 + 2 * branch) 0, nodes.getD (5 + 2 * branch) 0)

/-- The final singleton writes its top node directly into the layer-three
encoding input: the right top node (heap 3) as the low hash half at `WIT + 48`,
the left top node (heap 2) as the HIGH hash half at `WIT + 0` (stage 2, merged
singleton "Cm": the junk low half lands below the witness, so the C3 row pad at
`WIT + 24` stays witness memory). Paired B coordinates keep the high outer half. -/
def sharedOuterHash (coord index heap : Nat) (left right : Digest) : M Digest :=
  let input := wctTopInput coord index heap left 0 right
  if coord = 8 ∧ heap = 3 then shortHash input else highHash input

/-- Level four carries the preceding right node. An A coordinate uses the
high hash half there; a B coordinate uses the low half and one additional
outer fold. The half choice permits contiguous 32-byte machine writes.
C1 (FTS Merkle half-swap): the packed nodes `8..127` follow `ftsHighHeap`
(`wctNodeHashH`), i.e. the even heaps `16..127` use the high half. -/
def sharedNode (first : Bool) (coord index heap : Nat)
    (pads : Nat → PairRoot) (left right : Digest) : M Digest :=
  if heap < 4 then sharedOuterHash coord index heap left right
  else if heap < 8 then
    let input := wctTopInput coord index heap left (pads (heap / 2 - 2)).2 right
    if first then highHash input else shortHash input
  else wctNodeHashH coord index heap left right

def sharedHeap (first : Bool) (index coord : Nat) (pads : Nat → PairRoot)
    (leaves : List Digest) : M (Array Digest) :=
  (List.range' (if first then 4 else 2) (if first then 124 else 126)).reverse.foldlM
    (fun nodes heap => do
      let value ← sharedNode first coord index heap pads
        (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
      pure (nodes.set! heap value))
    ((List.replicate 128 (0 : Digest) ++ leaves).toArray)

def buildSharedCoordinate (first : Bool) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    M (Array Digest × List Digest) := do
  let coefs ← ftsCoefs index coord
  let state ← (List.range 128).foldlM
    (fun (state : List Digest × List Digest) j => do
      let (root, values) ← buildChildH (128 + j) index coord (rawChild first j) word coefs (pads (j / 64)).1
      pure (state.1 ++ [root], if j = selected.val then values else state.2)) ([], [])
  let nodes ← sharedHeap first index coord pads state.1
  pure (nodes, state.2)

def authAt (nodes : Array Digest) (selected level : Nat) : Digest :=
  nodes.getD (((128 + selected) / 2 ^ level) ^^^ 1) 0

def buildPair (index pair : Nat) (s : Selection) (aWord bWord : Rank)
    (prev : PairRoot) : M (PairOpening × PairRoot) := do
  let a ← buildSharedCoordinate true index (2 * pair) (firstChild s) aWord (fun _ => prev)
  let b ← buildSharedCoordinate false index (2 * pair + 1) (secondChild s) bWord
    (nodesPair a.1)
  pure (⟨fun i => a.2.getD i.val 0, fun i => authAt a.1 (firstChild s).val i.val,
      fun i => b.2.getD i.val 0, fun i => authAt b.1 (secondChild s).val i.val⟩,
    (b.1.getD 2 0, b.1.getD 3 0))

def recoverSharedInner (first : Bool) (index coord : Nat) (selected : Child)
    (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest)
    (prev : PairRoot) : M Digest := do
  let ends ← (List.finRange 6).mapM fun i =>
    let deficit := wordDigit word i
    chain index coord (rawChild first selected.val) i.val (4 - deficit) deficit (values i)
  let leaf ← leafHashH (128 + selected.val) index coord (rawChild first selected.val) prev.1 ends
  (List.range 5).foldlM (fun value level => do
    let other := path level
    let lr := if selected.val / 2 ^ level % 2 = 0 then (value, other) else (other, value)
    sharedNode first coord index ((128 + selected.val) / 2 ^ (level + 1))
      (fun _ => prev) lr.1 lr.2) leaf

def recoverPair (index pair : Nat) (s : Selection) (aWord bWord : Rank)
    (opened : PairOpening) (prev : PairRoot) : M PairRoot := do
  let aChild := firstChild s
  let bChild := secondChild s
  let a ← recoverSharedInner true index (2 * pair) aChild aWord opened.firstValues
    (fun i => opened.firstPath ⟨i % 6, Nat.mod_lt _ (by decide)⟩) prev
  let aPair := if aChild.val / 32 % 2 = 0 then (a, opened.firstPath 5)
    else (opened.firstPath 5, a)
  let b ← recoverSharedInner false index (2 * pair + 1) bChild bWord opened.secondValues
    (fun i => opened.secondPath ⟨i % 7, Nat.mod_lt _ (by decide)⟩) aPair
  let lr := if bChild.val / 32 % 2 = 0 then (b, opened.secondPath 5)
    else (opened.secondPath 5, b)
  let outer ← sharedOuterHash (2 * pair + 1) index (2 + bChild.val / 64) lr.1 lr.2
  pure (if bChild.val / 64 % 2 = 0 then (outer, opened.secondPath 6)
    else (opened.secondPath 6, outer))

def pairOpeningDigests : Nat := 6 + 6 + 6 + 7

theorem pair_saves_one_digest : pairOpeningDigests + 1 = 2 * (6 + 7) := by decide

theorem four_pairs_signature_size : 5310 - 4 * 16 = 5246 := by decide

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def heapCut (first : Bool) : Nat := if first then 4 else 2

def SharedHeapInv (answers : Answers) (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) (leaves : List Digest) (done : Nat) (nodes : Array Digest) : Prop :=
  nodes.size = 256 ∧
    (∀ i, 128 ≤ i → i < 256 → nodes.getD i 0 = leaves.getD (i - 128) 0) ∧
    (∀ i, heapCut first ≤ i → i < 128 → 128 - done ≤ i → nodes.getD i 0 =
      evalWithAnswerFn answers (sharedNode first coord index i pads
        (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0)))

theorem heapCut_bounds (first : Bool) : 2 ≤ heapCut first ∧ heapCut first ≤ 4 := by
  cases first <;> decide

theorem shared_heap_order (first : Bool) (i : Nat) (hi : i < 128 - heapCut first) :
    ((List.range' (heapCut first) (128 - heapCut first)).reverse)[i]'(by simpa using hi) = 127 - i := by
  rw [List.getElem_reverse]
  simp only [List.length_range', List.getElem_range', Nat.one_mul]
  have := heapCut_bounds first
  omega

theorem shared_heap_initial (answers : Answers) (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) (leaves : List Digest) (hlen : leaves.length = 128) :
    SharedHeapInv answers first index coord pads leaves 0
      ((List.replicate 128 (0 : Digest) ++ leaves).toArray) := by
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro i hlo hhi
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      ← List.getD_eq_getElem?_getD]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega)]
    simp only [List.length_replicate]
  · intro i _ hi hlo
    omega

theorem shared_heap_step (answers : Answers) (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) (leaves : List Digest) (done : Nat)
    (hdone : done < 128 - heapCut first) (nodes : Array Digest)
    (hinv : SharedHeapInv answers first index coord pads leaves done nodes) :
    SharedHeapInv answers first index coord pads leaves (done + 1)
      (nodes.set! (127 - done) (evalWithAnswerFn answers
        (sharedNode first coord index (127 - done) pads
          (nodes.getD (2 * (127 - done)) 0) (nodes.getD (2 * (127 - done) + 1) 0)))) := by
  let heap := 127 - done
  let v := evalWithAnswerFn answers (sharedNode first coord index heap pads
    (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0))
  change SharedHeapInv answers first index coord pads leaves (done + 1) (nodes.set! heap v)
  rcases hinv with ⟨hsize, hleaf, hnode⟩
  have hc := heapCut_bounds first
  have hh : heapCut first ≤ heap ∧ heap < 128 := by dsimp only [heap]; omega
  refine ⟨by rw [Array.size_set!, hsize], ?_, ?_⟩
  · intro i hlo hhi
    rw [getD_set_other nodes heap i v (by omega)]
    exact hleaf i hlo hhi
  · intro i hlo hhi hdone'
    have hheap : heap ≤ i := by dsimp only [heap]; omega
    have hl : (nodes.set! heap v).getD (2 * i) 0 = nodes.getD (2 * i) 0 :=
      getD_set_other nodes heap (2 * i) v (by omega)
    have hr : (nodes.set! heap v).getD (2 * i + 1) 0 = nodes.getD (2 * i + 1) 0 :=
      getD_set_other nodes heap (2 * i + 1) v (by omega)
    rw [hl, hr]
    by_cases he : i = heap
    · subst i
      rw [getD_set_self nodes heap v (by omega)]
    · rw [getD_set_other nodes heap i v (Ne.symm he)]
      exact hnode i hlo hhi (by dsimp only [heap] at he hheap; omega)

theorem shared_heap_complete (answers : Answers) (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) (leaves : List Digest) (hlen : leaves.length = 128) :
    SharedHeapInv answers first index coord pads leaves (128 - heapCut first)
      (evalWithAnswerFn answers (sharedHeap first index coord pads leaves)) := by
  have he : sharedHeap first index coord pads leaves =
      (List.range' (heapCut first) (128 - heapCut first)).reverse.foldlM
        (fun nodes heap => do
          let value ← sharedNode first coord index heap pads
            (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
          pure (nodes.set! heap value))
        ((List.replicate 128 (0 : Digest) ++ leaves).toArray) := by
    cases first <;> rfl
  rw [he]
  have h := eval_foldlM_list_inv answers (List.range' (heapCut first) (128 - heapCut first)).reverse
    (fun nodes heap => do
      let value ← sharedNode first coord index heap pads
        (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
      pure (nodes.set! heap value))
    (SharedHeapInv answers first index coord pads leaves) _
    (shared_heap_initial answers first index coord pads leaves hlen) (by
      intro done hdone nodes hinv
      have hd : done < 128 - heapCut first := by
        simpa only [List.length_reverse, List.length_range'] using hdone
      rw [shared_heap_order first done hd]
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      exact shared_heap_step answers first index coord pads leaves done hd nodes hinv)
  simpa only [List.length_reverse, List.length_range'] using h

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9

structure SingletonOpening where
  values : Fin 6 → Digest
  path : Fin 7 → Digest

structure ForestSelection where
  pairs : Fin 4 → Selection
  singleton : Child

structure ForestWords where
  first : Fin 4 → Rank
  second : Fin 4 → Rank
  singleton : Rank

structure ForestOpening where
  pairs : Fin 4 → PairOpening
  singleton : SingletonOpening

structure Signature where
  rho : Digest
  policyHints : BitVec 16
  forest : ForestOpening
  layers : (lay : Layer) → LayerSignature lay

/-- `topHigh`: the restricted top choice hint (witness byte rel 22312, bit 4): the verifier reads the HIGH half of
the top encoding answer when it is set and LOW is not forced. Honest value: the producer chose HIGH. -/
structure Witness where
  signature : Signature
  digestCounter : BitVec 32
  counters : Layer → BitVec 32
  topHigh : Bool
  /-- Top-bytes layer: the re-derived nonces of the top path nodes of heights 1..11 (witness pads). -/
  topNonces : List Nat

def emptyPairOpening : PairOpening := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- The last singleton uses the B node layout, including its level-four pad. -/
def buildSingleton (index : Nat) (selected : Child) (word : Rank) (prev : PairRoot) :
    M (SingletonOpening × PairRoot) := do
  let built ← buildSharedCoordinate false index 8 selected word (fun _ => prev)
  pure (⟨fun i => built.2.getD i.val 0, fun i => authAt built.1 selected.val i.val⟩,
    (built.1.getD 2 0, built.1.getD 3 0))

def recoverSingleton (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) : M PairRoot := do
  let inner ← recoverSharedInner false index 8 selected word opened.values
    (fun i => opened.path ⟨i % 7, Nat.mod_lt _ (by decide)⟩) prev
  let lr := if selected.val / 32 % 2 = 0 then (inner, opened.path 5)
    else (opened.path 5, inner)
  let outer ← sharedOuterHash 8 index (2 + selected.val / 64) lr.1 lr.2
  pure (if selected.val / 64 % 2 = 0 then (outer, opened.path 6)
    else (opened.path 6, outer))

def buildForest (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    M (ForestOpening × PairRoot) := do
  let state ← (List.finRange 4).foldlM
    (fun (state : List PairOpening × PairRoot) pair => do
      let built ← buildPair index pair.val (selected.pairs pair)
        (words.first pair) (words.second pair) state.2
      pure (state.1 ++ [built.1], built.2)) ([], ftsStart)
  let last ← buildSingleton index selected.singleton words.singleton state.2
  pure (⟨fun pair => state.1.getD pair.val emptyPairOpening, last.1⟩, last.2)

def recoverForest (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) : M PairRoot := do
  let prev ← (List.finRange 4).foldlM
    (fun prev pair => recoverPair index pair.val (selected.pairs pair)
      (words.first pair) (words.second pair) (opened.pairs pair) prev) ftsStart
  recoverSingleton index selected.singleton words.singleton opened.singleton prev

/-- Physical B children rotate the raw seven-bit field right by one: the
shared low bit becomes the branch bit, and the next six bits select within it. -/
def selectionFromOutput (output : HashOutput) (pair : Fin 4) : Selection where
  branch := ⟨output.toNat / 2 ^ (64 * pair.val + 6) % 2, Nat.mod_lt _ (by decide)⟩
  first := ⟨output.toNat / 2 ^ (64 * pair.val) % 64, Nat.mod_lt _ (by decide)⟩
  second := ⟨output.toNat / 2 ^ (64 * pair.val + 7) % 64, Nat.mod_lt _ (by decide)⟩

def forestSelectionFromOutput (output : HashOutput) : ForestSelection where
  pairs := selectionFromOutput output
  singleton := ⟨physicalChild false (output.toNat / 2 ^ 229 % 128),
    physicalChild_lt false _ (Nat.mod_lt _ (by decide))⟩

def rankBase (coord : Nat) : Nat := [13, 77, 89, 101, 141, 153, 165, 205, 217].getD coord 0

def rawForestRank (output : HashOutput) (coord : Nat) : Nat :=
  output.toNat / 2 ^ rankBase coord % 1024

/-- Total decoder; the digest acceptance condition separately requires each
raw rank to be below563, in which case this reduction leaves it unchanged. -/
def forestRank (output : HashOutput) (coord : Nat) : Rank :=
  ⟨rawForestRank output coord % 563, Nat.mod_lt _ (by decide)⟩

def forestWordsFromOutput (output : HashOutput) : ForestWords where
  first := fun pair => forestRank output (2 * pair.val)
  second := fun pair => forestRank output (2 * pair.val + 1)
  singleton := forestRank output 8

def forestOpeningDigests : Nat := 4 * pairOpeningDigests + (6 + 7)

theorem forest_opening_size : forestOpeningDigests = 113 := by decide

theorem forest_digest_saving : forestOpeningDigests + 4 = 9 * (6 + 7) := by decide

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def sharedLeaves (answers : Answers) (first : Bool) (index coord : Nat) (pads : Nat → PairRoot) : List Digest :=
  List.ofFn (fun j : Fin 128 =>
    childRootH answers (128 + j.val) index coord (rawChild first j.val) (pads (j.val / 64)).1)

def sharedNodes (answers : Answers) (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) : Array Digest :=
  evalWithAnswerFn answers (sharedHeap first index coord pads (sharedLeaves answers first index coord pads))

def sharedRows (first : Bool) (index coord : Nat) (selected : Child) (word : Rank)
    (coefs : List Digest) (pads : Nat → PairRoot) : M (List Digest × List Digest) :=
  (List.range 128).foldlM (fun (state : List Digest × List Digest) j => do
    let (root, values) ← buildChildH (128 + j) index coord (rawChild first j) word coefs (pads (j / 64)).1
    pure (state.1 ++ [root], if j = selected.val then values else state.2)) ([], [])

def SharedRows (answers : Answers) (first : Bool) (index coord : Nat) (selected : Child)
    (word : Rank) (pads : Nat → PairRoot) (done : Nat) (rows : List Digest × List Digest) : Prop :=
  rows.1.length = done ∧
    (∀ j, j < done → rows.1.getD j 0 =
      childRootH answers (128 + j) index coord (rawChild first j) (pads (j / 64)).1) ∧
    rows.2 = (if selected.val < done then
      List.ofFn (fun i : Fin 6 => chainValue answers index coord (rawChild first selected.val) word i) else [])

theorem shared_rows_step (answers : Answers) (first : Bool) (index coord : Nat) (selected : Child)
    (word : Rank) (pads : Nat → PairRoot) (done : Nat) (rows : List Digest × List Digest)
    (hrows : SharedRows answers first index coord selected word pads done rows) :
    SharedRows answers first index coord selected word pads (done + 1)
      (rows.1 ++ [childRootH answers (128 + done) index coord (rawChild first done) (pads (done / 64)).1],
       if done = selected.val then
         List.ofFn (fun i : Fin 6 => chainValue answers index coord (rawChild first done) word i) else rows.2) := by
  rcases hrows with ⟨hlen, hroot, hvalues⟩
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro j hj
    rw [ClaudeWCT.WCT9.getD_append_singleton, hlen]
    by_cases hjd : j < done
    · rw [if_pos hjd]; exact hroot j hjd
    · have he : j = done := by omega
      subst j
      simp
  · by_cases hs : done = selected.val
    · subst hs; simp
    · have hs' : selected.val < done + 1 ↔ selected.val < done := by omega
      simp only [if_neg hs, hvalues, hs']

theorem eval_sharedRows (answers : Answers) (first : Bool) (index coord : Nat) (selected : Child)
    (word : Rank) (pads : Nat → PairRoot) :
    SharedRows answers first index coord selected word pads 128
      (evalWithAnswerFn answers (sharedRows first index coord selected word
        (List.ofFn (ftsCoef answers index coord)) pads)) := by
  unfold sharedRows
  refine eval_foldlM_range_inv answers 128 _ (SharedRows answers first index coord selected word pads)
    ([], []) ?_ ?_
  · simp [SharedRows]
  · intro done _ rows hrows
    simp only [evalWithAnswerFn_bind, buildChildH_result, evalWithAnswerFn_pure]
    exact shared_rows_step answers first index coord selected word pads done rows hrows

theorem buildSharedCoordinate_result (answers : Answers) (first : Bool) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    evalWithAnswerFn answers (buildSharedCoordinate first index coord selected word pads) =
      (sharedNodes answers first index coord pads,
       List.ofFn (fun i : Fin 6 => chainValue answers index coord (rawChild first selected.val) word i)) := by
  let rows := evalWithAnswerFn answers (sharedRows first index coord selected word
    (List.ofFn (ftsCoef answers index coord)) pads)
  have hr : SharedRows answers first index coord selected word pads 128 rows :=
    eval_sharedRows answers first index coord selected word pads
  rcases hr with ⟨hlen, hroot, hvalues⟩
  have hroots : rows.1 = sharedLeaves answers first index coord pads := by
    apply List.ext_getElem (by simpa only [sharedLeaves, List.length_ofFn] using hlen)
    intro j hj hk
    simpa only [sharedLeaves, List.getD_eq_getElem _ _ hj, List.getElem_ofFn] using
      hroot j (by omega)
  rw [if_pos selected.isLt] at hvalues
  unfold buildSharedCoordinate
  rw [evalWithAnswerFn_bind, eval_ftsCoefs]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (evalWithAnswerFn answers (sharedHeap first index coord pads rows.1), rows.2) = _
  rw [hroots, hvalues]
  rfl

theorem sharedNodes_graph (answers : Answers) (first : Bool) (index coord : Nat)
    (pads : Nat → PairRoot) :
    SharedHeapInv answers first index coord pads (sharedLeaves answers first index coord pads)
      (128 - heapCut first) (sharedNodes answers first index coord pads) :=
  shared_heap_complete answers first index coord pads _ (by simp [sharedLeaves])

/-- All five inner steps stay in the selected64-leaf branch, so replacing
branch pads by the selected branch's pair preserves their hash inputs. -/
theorem sharedNode_selected_pad (first : Bool) (index coord selected level : Nat)
    (hselected : selected < 128) (hlevel : level < 5) (pads : Nat → PairRoot)
    (left right : Digest) :
    sharedNode first coord index ((128 + selected) / 2 ^ (level + 1))
      (fun _ => pads (selected / 64)) left right =
    sharedNode first coord index ((128 + selected) / 2 ^ (level + 1)) pads left right := by
  have hlo : 4 ≤ (128 + selected) / 2 ^ (level + 1) := by
    interval_cases level <;> norm_num <;> omega
  have hbranch : (128 + selected) / 2 ^ (level + 1) < 8 →
      (128 + selected) / 2 ^ (level + 1) / 2 - 2 = selected / 64 := by
    interval_cases level <;> norm_num <;> omega
  have hnot : ¬ (128 + selected) / 2 ^ (level + 1) < 4 := by omega
  simp only [sharedNode, if_neg hnot]
  by_cases hh : (128 + selected) / 2 ^ (level + 1) < 8
  · simp only [if_pos hh, hbranch hh]
  · simp only [if_neg hh]

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem heap_path_pair (f : Nat → Digest) (selected level : Nat)
    (hselected : selected < 128) (hlevel : level < 5) :
    (if selected / 2 ^ level % 2 = 0 then
      (f ((128 + selected) / 2 ^ level), f (((128 + selected) / 2 ^ level) ^^^ 1))
    else (f (((128 + selected) / 2 ^ level) ^^^ 1), f ((128 + selected) / 2 ^ level))) =
      (f (2 * ((128 + selected) / 2 ^ (level + 1))),
       f (2 * ((128 + selected) / 2 ^ (level + 1)) + 1)) := by
  have hp : selected / 2 ^ level % 2 = (128 + selected) / 2 ^ level % 2 := by
    interval_cases level <;> norm_num <;> omega
  rw [hp, sibling_pair f ((128 + selected) / 2 ^ level)]
  have hd : (128 + selected) / 2 ^ level / 2 = (128 + selected) / 2 ^ (level + 1) := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  rw [hd]

theorem recoverSharedInner_honest (answers : Answers) (first : Bool) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot)
    (values : Fin 6 → Digest) (path : Nat → Digest)
    (hvalues : ∀ i, values i = chainValue answers index coord (rawChild first selected.val) word i)
    (hpath : ∀ level, level < 5 → path level =
      authAt (sharedNodes answers first index coord pads) selected.val level) :
    evalWithAnswerFn answers (recoverSharedInner first index coord selected word values path
      (pads (selected.val / 64))) =
      (sharedNodes answers first index coord pads).getD ((128 + selected.val) / 32) 0 := by
  let nodes := sharedNodes answers first index coord pads
  have hg := sharedNodes_graph answers first index coord pads
  have hends : (List.finRange 6).map (fun i => evalWithAnswerFn answers
      (chain index coord (rawChild first selected.val) i.val
        (4 - wordDigit word i) (wordDigit word i) (values i))) =
      List.ofFn (fun i : Fin 6 => chainEnd answers index coord (rawChild first selected.val) i) := by
    simp_rw [hvalues, value_completes]
    exact List.ofFn_eq_map.symm
  have hleaf : evalWithAnswerFn answers
      (leafHashH (128 + selected.val) index coord (rawChild first selected.val) (pads (selected.val / 64)).1
        (List.ofFn (fun i : Fin 6 => chainEnd answers index coord (rawChild first selected.val) i))) =
      nodes.getD (128 + selected.val) 0 := by
    have hl := hg.2.1 (128 + selected.val) (by omega) (by have := selected.isLt; omega)
    rw [Nat.add_sub_cancel_left, sharedLeaves,
      List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact selected.isLt), List.getElem_ofFn] at hl
    exact hl.symm
  have hwalk := eval_foldlM_range_inv answers 5
    (fun value level => do
      let other := path level
      let lr := if selected.val / 2 ^ level % 2 = 0 then (value, other) else (other, value)
      sharedNode first coord index ((128 + selected.val) / 2 ^ (level + 1))
        (fun _ => pads (selected.val / 64)) lr.1 lr.2)
    (fun done value => value = nodes.getD ((128 + selected.val) / 2 ^ done) 0)
    (nodes.getD (128 + selected.val) 0) (by simp) (by
      intro level hlevel value hv
      have hb : 4 ≤ (128 + selected.val) / 2 ^ (level + 1) ∧
          (128 + selected.val) / 2 ^ (level + 1) < 128 := by
        have hs := selected.isLt
        interval_cases level <;> norm_num <;> omega
      change evalWithAnswerFn answers (sharedNode first coord index
        ((128 + selected.val) / 2 ^ (level + 1)) (fun _ => pads (selected.val / 64))
        (if selected.val / 2 ^ level % 2 = 0 then (value, path level) else (path level, value)).1
        (if selected.val / 2 ^ level % 2 = 0 then (value, path level) else (path level, value)).2) = _
      rw [hv, hpath level hlevel]
      unfold authAt
      rw [heap_path_pair (fun j => nodes.getD j 0) selected.val level selected.isLt hlevel,
        sharedNode_selected_pad first index coord selected.val level selected.isLt hlevel]
      have hc := heapCut_bounds first
      exact (hg.2.2 ((128 + selected.val) / 2 ^ (level + 1)) (by omega) hb.2 (by omega)).symm)
  unfold recoverSharedInner
  simp only [evalWithAnswerFn_bind, eval_mapM, evalWithAnswerFn_pure]
  rw [hends, hleaf]
  exact hwalk

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem ordered_branch_pair (nodes : Array Digest) (selected : Nat) (hs : selected < 128) :
    (if selected / 32 % 2 = 0 then
      (nodes.getD ((128 + selected) / 32) 0, authAt nodes selected 5)
    else (authAt nodes selected 5, nodes.getD ((128 + selected) / 32) 0)) =
      nodesPair nodes (selected / 64) := by
  have hp : selected / 32 % 2 = (128 + selected) / 32 % 2 := by omega
  unfold authAt nodesPair
  norm_num only [Nat.reducePow]
  rw [hp, sibling_pair (fun j => nodes.getD j 0) ((128 + selected) / 32)]
  have hd : (128 + selected) / 32 / 2 = 2 + selected / 64 := by omega
  rw [hd]
  congr 1 <;> congr 1 <;> omega

theorem ordered_top_pair (nodes : Array Digest) (selected : Nat) (hs : selected < 128) :
    (if selected / 64 % 2 = 0 then
      (nodes.getD (2 + selected / 64) 0, authAt nodes selected 6)
    else (authAt nodes selected 6, nodes.getD (2 + selected / 64) 0)) =
      (nodes.getD 2 0, nodes.getD 3 0) := by
  have hq : selected / 64 = 0 ∨ selected / 64 = 1 := by omega
  have hd : (128 + selected) / 64 = 2 + selected / 64 := by omega
  unfold authAt
  norm_num only [Nat.reducePow]
  rw [hd]
  rcases hq with h | h <;> rw [h] <;> rfl

def recoverSharedOuter (index coord : Nat) (selected : Child) (word : Rank)
    (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) : M PairRoot := do
  let inner ← recoverSharedInner false index coord selected word values path prev
  let lr := if selected.val / 32 % 2 = 0 then (inner, path 5) else (path 5, inner)
  let outer ← sharedOuterHash coord index (2 + selected.val / 64) lr.1 lr.2
  pure (if selected.val / 64 % 2 = 0 then (outer, path 6) else (path 6, outer))

theorem recoverSharedOuter_honest (answers : Answers) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot)
    (values : Fin 6 → Digest) (path : Nat → Digest)
    (hvalues : ∀ i, values i = chainValue answers index coord (rawChild false selected.val) word i)
    (hpath : ∀ level, level < 7 → path level =
      authAt (sharedNodes answers false index coord pads) selected.val level) :
    evalWithAnswerFn answers (recoverSharedOuter index coord selected word values path
      (pads (selected.val / 64))) =
      ((sharedNodes answers false index coord pads).getD 2 0,
       (sharedNodes answers false index coord pads).getD 3 0) := by
  let nodes := sharedNodes answers false index coord pads
  have hs := selected.isLt
  have hi := recoverSharedInner_honest answers false index coord selected word pads values path
    hvalues (fun level hlevel => hpath level (by omega))
  have hg := sharedNodes_graph answers false index coord pads
  have hn := hg.2.2 (2 + selected.val / 64) (by simp [heapCut]) (by omega) (by simp [heapCut])
  have hh : 2 + selected.val / 64 < 4 := by omega
  have hm : 2 * (2 + selected.val / 64) = 4 + 2 * (selected.val / 64) := by omega
  simp only [sharedNode, if_pos hh, hm] at hn
  have hm' : 4 + 2 * (selected.val / 64) + 1 = 5 + 2 * (selected.val / 64) := by omega
  rw [hm'] at hn
  unfold recoverSharedOuter
  rw [evalWithAnswerFn_bind, hi]
  rw [hpath 5 (by decide), ordered_branch_pair nodes selected.val hs]
  simp only [nodesPair]
  rw [evalWithAnswerFn_bind, ← hn]
  simp only [evalWithAnswerFn_pure]
  rw [hpath 6 (by decide), ordered_top_pair nodes selected.val hs]

theorem recoverSingleton_eq_outer (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) :
    recoverSingleton index selected word opened prev =
      recoverSharedOuter index 8 selected word opened.values
        (fun i => opened.path ⟨i % 7, Nat.mod_lt _ (by decide)⟩) prev := rfl

theorem recoverSingleton_honest (answers : Answers) (index : Nat) (selected : Child)
    (word : Rank) (prev : PairRoot) :
    let built := evalWithAnswerFn answers (buildSingleton index selected word prev)
    evalWithAnswerFn answers (recoverSingleton index selected word built.1 prev) = built.2 := by
  unfold buildSingleton
  simp only [evalWithAnswerFn_bind, buildSharedCoordinate_result, evalWithAnswerFn_pure]
  rw [recoverSingleton_eq_outer]
  apply recoverSharedOuter_honest answers index 8 selected word (fun _ => prev)
  · intro i
    change (List.ofFn _).getD i.val 0 = _
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
  · intro level hl
    simp only [Nat.mod_eq_of_lt hl]

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def firstNodes (answers : Answers) (index pair : Nat) (prev : PairRoot) : Array Digest :=
  sharedNodes answers true index (2 * pair) (fun _ => prev)

def secondNodes (answers : Answers) (index pair : Nat) (prev : PairRoot) : Array Digest :=
  sharedNodes answers false index (2 * pair + 1) (nodesPair (firstNodes answers index pair prev))

def expectedPairOpening (answers : Answers) (index pair : Nat) (s : Selection)
    (aWord bWord : Rank) (prev : PairRoot) : PairOpening where
  firstValues := fun i => (List.ofFn (fun j : Fin 6 =>
    chainValue answers index (2 * pair) (rawChild true (firstChild s).val) aWord j)).getD i.val 0
  firstPath := fun i => authAt (firstNodes answers index pair prev) (firstChild s).val i.val
  secondValues := fun i => (List.ofFn (fun j : Fin 6 =>
    chainValue answers index (2 * pair + 1) (rawChild false (secondChild s).val) bWord j)).getD i.val 0
  secondPath := fun i => authAt (secondNodes answers index pair prev) (secondChild s).val i.val

def expectedPairRoot (answers : Answers) (index pair : Nat) (prev : PairRoot) : PairRoot :=
  ((secondNodes answers index pair prev).getD 2 0, (secondNodes answers index pair prev).getD 3 0)

attribute [local irreducible] sharedNodes

theorem buildPair_result (answers : Answers) (index pair : Nat) (s : Selection)
    (aWord bWord : Rank) (prev : PairRoot) :
    evalWithAnswerFn answers (buildPair index pair s aWord bWord prev) =
      (expectedPairOpening answers index pair s aWord bWord prev,
       expectedPairRoot answers index pair prev) := by
  simp only [buildPair, evalWithAnswerFn_bind, buildSharedCoordinate_result, evalWithAnswerFn_pure]
  rfl

theorem recoverPair_expected (answers : Answers) (index pair : Nat) (s : Selection)
    (aWord bWord : Rank) (prev : PairRoot) :
    evalWithAnswerFn answers (recoverPair index pair s aWord bWord
      (expectedPairOpening answers index pair s aWord bWord prev) prev) =
      expectedPairRoot answers index pair prev := by
  let a := firstNodes answers index pair prev
  let b := secondNodes answers index pair prev
  let opened := expectedPairOpening answers index pair s aWord bWord prev
  have ha := recoverSharedInner_honest answers true index (2 * pair) (firstChild s) aWord
    (fun _ => prev) opened.firstValues
    (fun i => opened.firstPath ⟨i % 6, Nat.mod_lt _ (by decide)⟩)
    (by
      intro i
      change (List.ofFn _).getD i.val 0 = _
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt), List.getElem_ofFn])
    (by
      intro level hl
      dsimp only [opened, expectedPairOpening, firstNodes]
      rw [Nat.mod_eq_of_lt (by omega)]
      )
  unfold recoverPair
  rw [evalWithAnswerFn_bind, ha]
  change evalWithAnswerFn answers
    (recoverSharedOuter index (2 * pair + 1) (secondChild s) bWord opened.secondValues
      (fun i => opened.secondPath ⟨i % 7, Nat.mod_lt _ (by decide)⟩)
      (if (firstChild s).val / 32 % 2 = 0 then
        (a.getD ((128 + (firstChild s).val) / 32) 0, authAt a (firstChild s).val 5)
      else (authAt a (firstChild s).val 5, a.getD ((128 + (firstChild s).val) / 32) 0))) = _
  rw [ordered_branch_pair a (firstChild s).val (firstChild s).isLt, selected_branch s]
  apply recoverSharedOuter_honest answers index (2 * pair + 1) (secondChild s) bWord (nodesPair a)
  · intro i
    change (List.ofFn _).getD i.val 0 = _
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
  · intro level hl
    dsimp only [opened, expectedPairOpening, secondNodes, firstNodes]
    rw [Nat.mod_eq_of_lt hl]
    rfl

theorem recoverPair_honest (answers : Answers) (index pair : Nat) (s : Selection)
    (aWord bWord : Rank) (prev : PairRoot) :
    let built := evalWithAnswerFn answers (buildPair index pair s aWord bWord prev)
    evalWithAnswerFn answers (recoverPair index pair s aWord bWord built.1 prev) = built.2 := by
  rw [buildPair_result]
  exact recoverPair_expected answers index pair s aWord bWord prev

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] sharedNodes

/-- The complete four-pair forest and its final B singleton recover the
builder's final commitment under every fixed oracle answer function. -/
theorem recoverForest_honest (answers : Answers) (index : Nat)
    (selected : ForestSelection) (words : ForestWords) :
    let built := evalWithAnswerFn answers (buildForest index selected words)
    evalWithAnswerFn answers (recoverForest index selected words built.1) = built.2 := by
  have hfour : List.finRange 4 = [0, 1, 2, 3] := by decide
  have hv0 : (0 : Fin 4).val = 0 := rfl
  have hv1 : (1 : Fin 4).val = 1 := rfl
  have hv2 : (2 : Fin 4).val = 2 := rfl
  have hv3 : (3 : Fin 4).val = 3 := rfl
  let r0 := expectedPairRoot answers index 0 ftsStart
  let r1 := expectedPairRoot answers index 1 r0
  let r2 := expectedPairRoot answers index 2 r1
  let r3 := expectedPairRoot answers index 3 r2
  simp only [buildForest, hfour, List.foldlM_cons, List.foldlM_nil,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, buildPair_result]
  simp only [recoverForest, hfour, List.foldlM_cons, List.foldlM_nil,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  simp only [hv0, hv1, hv2, hv3, List.nil_append, List.append_assoc, List.cons_append, List.getD_cons_zero,
    List.getD_cons_succ, recoverPair_expected]
  exact recoverSingleton_honest answers index selected.singleton words.singleton r3


end SigGolfCandidate.Research.SharedForest

/-! Private roots-first canonical producer. Retained chain prefixes let the
ancestor-only search choose digits after every lower root has been fixed. -/
namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9

/-- Retain each prefix while evaluating a WOTS chain once, in its ordinary order. Stage 2 (C3, #866): each step
keeps the half `chainHigh lay i start` of its output, as `WCT9.chainW` does (the last step of chain 0 of a lower
layer keeps the HIGH half). -/
def chainPrefixes (lay : Layer) (tree leaf i start : Nat) :
    Nat → Digest → M (List Digest)
  | 0, value => pure [value]
  | count + 1, value => do
      let next ← halfHash (chainHigh lay i start) (ClaudeWCT.WCT9.chainInputW lay tree leaf i start value)
      let tail ← chainPrefixes lay tree leaf i (start + 1) count next
      pure (value :: tail)

def buildLeafPrefixes (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    M ((Digest × List (List Digest)) × List Digest) := do
  let (coefs, carry) ← lowerCoefs lay tree leaf carry
  let prefixes ← (List.range (chainCount lay)).mapM fun i =>
    chainPrefixes lay tree leaf i 0 (maxDigit lay i) (lowerFamilySeed coefs lay leaf i)
  let root ← lowerLeafHash lay tree leaf
    ((List.range (chainCount lay)).map fun i =>
      (prefixes.getD i []).getD (maxDigit lay i) 0)
  pure ((root, prefixes), carry)

structure PreparedLower where
  levels : List (List Digest)
  prefixes : List (List Digest)

/-- Only the selected leaf retains its prefixes; every other leaf uses the
existing full-chain builder. No chain is evaluated again after digit search. -/
def buildTreePrefixes (lay : Layer) (tree selected : Nat) : M PreparedLower := do
  let state ← (List.range (2 ^ height lay)).foldlM
    (fun (state : List Digest × List (List Digest) × List Digest) leaf => do
      let ((root, prefixes), carry) ←
        if leaf = selected then buildLeafPrefixes lay tree leaf state.2.2
        else do
          let ((root, _), carry) ← buildLeafPF lay tree leaf [] state.2.2
          pure ((root, []), carry)
      pure (state.1 ++ [root], if leaf = selected then prefixes else state.2.1, carry))
    ([], [], [])
  let levels ← buildLevelsBelow 3 lay.val tree (height lay) state.1
  pure ⟨levels, state.2.1⟩

def preparedPieces (lay : Layer) (leaf : Nat) (prepared : PreparedLower)
    (digits : List Nat) : Pieces :=
  ((List.range (chainCount lay)).map fun i =>
      (prepared.prefixes.getD i []).getD (digits.getD i 0) 0,
   (List.range (height lay)).map fun level =>
      (prepared.levels.getD level []).getD (leaf / 2 ^ level ^^^ 1) 0)

structure PreparedRoots where
  one : PreparedLower
  two : PreparedLower
  three : PreparedLower

def prepareRoots (index : Nat) : M PreparedRoots := do
  let one ← buildTreePrefixes 1 (route index 1).2 (route index 1).1
  let two ← buildTreePrefixes 2 (route index 2).2 (route index 2).1
  let three ← buildTreePrefixes 3 (route index 3).2 (route index 3).1
  pure ⟨one, two, three⟩

structure CanonicalLayers where
  pieces : List Pieces
  counters : List (BitVec 32)
  digits : List (List Nat)
  /-- The selected half of every layer (`true` = LOW). -/
  lows : List Bool
  residual : Nat
  policyHints : BitVec 16

/-- All thresholds are determined by the canonical ancestors. The lower
tree roots are already fixed, and lower reveals are pure prefix lookups. -/
def searchPreparedLayers (cache : SigGolfCandidate.T3.Cache) (index : Nat) (prepared : PreparedRoots)
    (forest : PairRoot) : M (Option CanonicalLayers) := do
  let pair0 := topPair 1 prepared.one.levels
  let pair1 := topPair 2 prepared.two.levels
  let pair2 := topPair 3 prepared.three.levels
  let some (counter0, digits0, low0) ← CanonicalPolicy.layerCounterSearchAt 0
    (CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit)
    (route index 0).2 (route index 0).1 (.pair pair0.1 pair0.2) 0 (searchLimit 0)
    | pure none
  let residual1 := CanonicalPolicy.nextResidual CanonicalPolicy.totalCredit 0 low0 digits0
  let floor1 := CanonicalPolicy.threshold 1 residual1
  if floor1 ≥ 16 then return none
  let some (counter1, digits1, low1) ← CanonicalPolicy.layerCounterSearchAt 1
    floor1
    (route index 1).2 (route index 1).1 (.pair pair1.1 pair1.2) 0 (searchLimit 1)
    | pure none
  let residual2 := CanonicalPolicy.nextResidual residual1 1 low1 digits1
  let floor2 := CanonicalPolicy.threshold 2 residual2
  if floor2 ≥ 22 then return none
  let some (counter2, digits2, low2) ← CanonicalPolicy.layerCounterSearchAt 2
    floor2
    (route index 2).2 (route index 2).1 (.pair pair2.1 pair2.2) 0 (searchLimit 2)
    | pure none
  let residual3 := CanonicalPolicy.nextResidual residual2 2 low2 digits2
  let floor3 := CanonicalPolicy.threshold 3 residual3
  if floor3 ≥ 22 then return none
  let some (counter3, digits3, low3) ← CanonicalPolicy.layerCounterSearchAt 3
    floor3
    (route index 3).2 (route index 3).1 (.pair forest.1 forest.2) 0 (searchLimit 3)
    | pure none
  let top ← signTop cache (route index 0).1 digits0
  pure (some ⟨[top,
      preparedPieces 1 (route index 1).1 prepared.one digits1,
      preparedPieces 2 (route index 2).1 prepared.two digits2,
      preparedPieces 3 (route index 3).1 prepared.three digits3],
    [counter0, counter1, counter2, counter3], [digits0, digits1, digits2, digits3],
    [low0, low1, low2, low3],
    CanonicalPolicy.nextResidual residual3 3 low3 digits3,
    BitVec.ofNat 16 (484 * floor1 + 22 * floor2 + floor3)⟩)

/-- Source signing continuation after the FTS digest search has selected an
output. The enclosing producer supplies the accepted output and its counter. -/
def signFromOutput (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (digestCounter : BitVec 32)
    (output : HashOutput) : M (Option Witness) := do
  let index := digestIndex output
  let forest ← buildForest index (forestSelectionFromOutput output) (forestWordsFromOutput output)
  let prepared ← prepareRoots index
  let some layers ← searchPreparedLayers cache index prepared forest.2 | pure none
  let signature : Signature := ⟨rho, layers.policyHints, forest.1,
    fun lay => piecesSignature lay (layers.pieces.getD lay.val ([], []))⟩
  pure (some ⟨signature, digestCounter, fun lay => layers.counters.getD lay.val 0, !(layers.lows.getD 0 true), []⟩)

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness

theorem lower_chain_succ_first (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    SigGolfCandidate.T3.chain lay tree leaf i start (count + 1) value = (do
      let next ← shortHash (SigGolfCandidate.T3.chainInput lay tree leaf i start value)
      SigGolfCandidate.T3.chain lay tree leaf i (start + 1) count next) := by
  rw [show count + 1 = 1 + count by omega, SigGolfCandidate.T3.Correctness.chain_add]
  rfl

/-- Stage 2 (C3): `lower_chain_succ_first` for the chain of the current scheme. -/
theorem lower_chainW_succ_first (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    ClaudeWCT.WCT9.chainW lay tree leaf i start (count + 1) value = (do
      let next ← ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i start)
        (ClaudeWCT.WCT9.chainInputW lay tree leaf i start value)
      ClaudeWCT.WCT9.chainW lay tree leaf i (start + 1) count next) := by
  rw [show count + 1 = 1 + count by omega, ClaudeWCT.WCT9.chainW_add]
  have h1 : ClaudeWCT.WCT9.chainW lay tree leaf i start 1 value =
      ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i start)
        (ClaudeWCT.WCT9.chainInputW lay tree leaf i start value) := by
    unfold ClaudeWCT.WCT9.chainW
    simp only [List.range'_one, List.foldlM_cons, List.foldlM_nil, bind_pure]
  rw [h1]

theorem eval_chainPrefixes_length (answers : Answers) (lay : Layer)
    (tree leaf i start count : Nat) (value : Digest) :
    (evalWithAnswerFn answers (chainPrefixes lay tree leaf i start count value)).length = count + 1 := by
  induction count generalizing start value with
  | zero => simp [chainPrefixes, evalWithAnswerFn_pure]
  | succ count ih =>
    simp only [chainPrefixes, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.length_cons, ih]

theorem eval_chainPrefixes_getD (answers : Answers) (lay : Layer)
    (tree leaf i start count : Nat) (value : Digest) (j : Nat) (hj : j ≤ count) :
    (evalWithAnswerFn answers (chainPrefixes lay tree leaf i start count value)).getD j 0 =
      evalWithAnswerFn answers (ClaudeWCT.WCT9.chainW lay tree leaf i start j value) := by
  induction count generalizing start value j with
  | zero =>
    have hz : j = 0 := by omega
    subst j
    rfl
  | succ count ih =>
    cases j with
    | zero =>
      simp only [chainPrefixes, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.getD_cons_zero]
      rfl
    | succ j =>
      simp only [chainPrefixes, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.getD_cons_succ]
      rw [ih _ _ _ (by omega), lower_chainW_succ_first, evalWithAnswerFn_bind]

end SigGolfCandidate.Research.SharedForest

/-! Shared-forest digest selection and the exact producer cap. The selector
bit shared by each pair does not enter either child's variable cycle count. -/
namespace SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 ClaudeWCT.WCT9

def firstCoord (coord : Nat) : Bool := decide (coord < 8 ∧ coord % 2 = 0)
def rawChildBase (coord : Nat) : Nat := [0, 6, 64, 70, 128, 134, 192, 198, 229].getD coord 0

def rawChildFromOutput (output : HashOutput) (coord : Fin 9) : Child :=
  ⟨output.toNat / 2 ^ rawChildBase coord.val % 128, Nat.mod_lt _ (by decide)⟩

def physicalChildFromOutput (output : HashOutput) (coord : Fin 9) : Child :=
  ⟨physicalChild (firstCoord coord.val) (rawChildFromOutput output coord).val,
    physicalChild_lt _ _ (rawChildFromOutput output coord).isLt⟩

/-- C1 (stage 1): the per-child cycle correction `2 - skips′` of the physical child's class (A routines fit
their 32-word slots, so there is no spill term). -/
def accountingCorrection (coord : Nat) (raw : Child) : Nat :=
  2 - SharedPathPacking.saves (physicalChild (firstCoord coord) raw.val)

def coordinateAccountingCost (output : HashOutput) (coord : Fin 9) : Nat :=
  routineCost (forestRank output coord.val) + accountingCorrection coord.val (rawChildFromOutput output coord)

def jointAccountingCost (output : HashOutput) : Nat :=
  ((List.finRange 9).map (coordinateAccountingCost output)).sum

def ranksAccepted (output : HashOutput) : Bool :=
  (List.finRange 9).all (fun coord => decide (rawForestRank output coord.val < 563))

/-- Joint cap 777 (`P(joint ≤ 777 | gate, ranks) = 0.990672`). -/
def digestAccepted (output : HashOutput) : Bool :=
  decide (output.toNat / 2 ^ 242 % 16384 < 791) && ranksAccepted output &&
    decide (jointAccountingCost output ≤ 776)

theorem firstCoord_eq_shared (coord : Nat) : firstCoord coord = decide (coord < 8 ∧ coord % 2 = 0) := rfl

theorem ranksAccepted_iff (output : HashOutput) : ranksAccepted output = true ↔
    ∀ coord : Fin 9, rawForestRank output coord.val < 563 := by
  simp [ranksAccepted, List.all_eq_true]

theorem accepted_conditions (output : HashOutput) (h : digestAccepted output = true) :
    output.toNat / 2 ^ 242 % 16384 < 791 ∧
    (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
    jointAccountingCost output ≤ 776 := by
  simpa only [digestAccepted, Bool.and_eq_true, decide_eq_true_eq, ranksAccepted_iff,
    and_assoc] using h
end SigGolfCandidate.Research.SharedForest

/-! The compact signature carries explicit canonical policy hints. All128 nonce
bits are retained; the hints are checked again after bottom-up recovery. -/
namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9

/-- Policy hint bound (img-v4/v6 mixed radix): h = 484·f1 + 22·f2 + f3 with f1 ≤ 15, f2, f3 ≤ 21, h < 7744. -/
def policyHintBound : Nat := 7744

def hintFloor (hints : BitVec 16) (lay : Layer) : Nat :=
  if lay = 0 then CanonicalPolicy.topFloor else hints.toNat / 22 ^ (3 - lay.val) % 22

def policyHintsValid (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool) : Bool :=
  let residual1 := CanonicalPolicy.nextResidual CanonicalPolicy.totalCredit 0 (lows.getD 0 true) (digits.getD 0 [])
  let residual2 := CanonicalPolicy.nextResidual residual1 1 (lows.getD 1 true) (digits.getD 1 [])
  let residual3 := CanonicalPolicy.nextResidual residual2 2 (lows.getD 2 true) (digits.getD 2 [])
  decide (hints.toNat < 7744 ∧ digits.length = 4 ∧
    hintFloor hints 1 = CanonicalPolicy.threshold 1 residual1 ∧
    hintFloor hints 2 = CanonicalPolicy.threshold 2 residual2 ∧
    hintFloor hints 3 = CanonicalPolicy.threshold 3 residual3)

/-- Adapter for the unchanged main-tree recovery kernels. The forest opening
is recovered separately; no dummy opening is inspected by those kernels. -/
def mainSignature (sig : Signature) : ClaudeWCT.WCT9.Signature :=
  ⟨sig.rho, fun _ => ⟨fun _ => 0, fun _ => 0⟩, sig.layers⟩

def fillTopSignature (sig : Signature) (c : Nat) : Signature :=
  { sig with layers := fun lay => fillLayer lay (sig.layers lay) c }

/-- Normal form of a top path node at height `j`: the compact codec does not store the zero-test bits
(`T3.topZeroOk`): T51 (5,195 bytes): the top `topZeroBits j` bits for `j = 1..10`; for the top sibling (`j = 11`) bits
104..127 (104..111 zero-test bits, 112..127 brute-forced). (#938 img-v6, 5,239 bytes: top `j` bits, sibling 98..127.) -/
def normPathD (j : Nat) (d : Digest) : Digest :=
  if 1 ≤ j ∧ j ≤ 10 then BitVec.ofNat 128 (d.toNat % 2 ^ (128 - topZeroBits j))
  else if j = 11 then BitVec.ofNat 128 (d.toNat % 2 ^ 104) else d

def normLayer (lay : Layer) (ls : LayerSignature lay) : LayerSignature lay :=
  ⟨ls.values, fun j => if lay.val = 0 then normPathD j.val (ls.path j) else ls.path j⟩

/-- What the compact codec keeps (13-bit hint, normalized top path; T51: 5,195 bytes); `expand` applies it first. -/
def normTop (sig : Signature) : Signature :=
  { sig with policyHints := BitVec.ofNat 16 (sig.policyHints.toNat % 2 ^ 13)
             layers := fun lay => normLayer lay (sig.layers lay) }

/-- The honest top path passes its zero tests (no nonce search hit its cap). -/
def TopPathOK (sig : Signature) : Prop :=
  ∀ j : Fin (height 0), 1 ≤ j.val → topZeroOk j.val ((sig.layers 0).path j) = true

structure RecoveredLayers where
  foldedTop : Digest
  root : Digest
  counters : List (BitVec 32)
  digits : List (List Nat)
  /-- The selected half of every layer (`true` = LOW), top first. -/
  lows : List Bool
  /-- Top-bytes layer: the nonces of the top path nodes of heights 1..11 (re-derived by `topFoldN`). -/
  nonces : List Nat

/-- Hints allow one bottom-up pass. The final check compares these hints with
the unique ancestor policy, so alternate hint encodings are rejected. -/
def recoverHintedLayers (sig : Signature) (index : Nat) (other : Digest) :
    Nat → LayerMsg → M (Option RecoveredLayers)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let some (counter, digits, low) ← CanonicalPolicy.layerCounterSearchAt lay
        (hintFloor sig.policyHints lay) tree leaf msg 0 (searchLimit lay) | pure none
      if n = 0 then
        let (folded, nonces) ← topFoldN (mainSignature sig) index digits
        let root ← topNode index folded other
        pure (some ⟨folded, root, [counter], [digits], [low], nonces⟩)
      else
        let pair ← recoverLayerPair (mainSignature sig) index lay digits
        let some previous ← recoverHintedLayers sig index other n (.pair pair.1 pair.2) | pure none
        pure (some { previous with
          counters := previous.counters ++ [counter]
          digits := previous.digits ++ [digits]
          lows := previous.lows ++ [low] })

def sharedDigestSearch (rho : Digest) (message : Message) (counter : Nat) :
    Nat → M (Option (BitVec 32 × HashOutput))
  | 0 => pure none
  | fuel + 1 => do
      let output ← digest rho message (BitVec.ofNat 32 counter)
      if digestAccepted output then return some (BitVec.ofNat 32 counter, output)
      sharedDigestSearch rho message (counter + 1) fuel

def signPayload (cache : SigGolfCandidate.T3.Cache) (message : Message) : M (Option Signature) := do
  let rho ← privateNonce message
  let some (counter, output) ← sharedDigestSearch rho message 0 digestAttemptLimit | pure none
  let some witness ← signFromOutput cache rho counter output | pure none
  pure (some witness.signature)

def sign (cache : SigGolfCandidate.T3.Cache) (message : Message) : M (Option Signature) := do
  let tag ← privateMac cache.region
  if tag ≠ cache.tag then return none
  signPayload cache message

/-- The pre-v6 expansion kernel (hint check, top sibling field cleared, brute force). -/
def expandFill (message : Message) (pk : Digest) (sig : Signature) : M (Option Witness) := do
  if sig.policyHints.toNat ≥ 7744 then return none
  let sig0 := fillTopSignature sig 0
  let some (counter, output) ← sharedDigestSearch sig0.rho message 0 digestAttemptLimit | pure none
  let index := digestIndex output
  let forest ← recoverForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output) sig0.forest
  let some layers ← recoverHintedLayers sig0 index ((sig0.layers 0).path topJ)
    4 (.pair forest.1 forest.2) | pure none
  if !policyHintsValid sig0.policyHints layers.digits layers.lows then return none
  if layers.root = pk then
    return some ⟨sig0, counter, fun lay => layers.counters.getD lay.val 0, !(layers.lows.getD 0 true),
      layers.nonces⟩
  let some c ← searchTop index layers.foldedTop ((sig0.layers 0).path topJ) pk searchFuel 1 | pure none
  pure (some ⟨fillTopSignature sig0 c, counter, fun lay => layers.counters.getD lay.val 0,
    !(layers.lows.getD 0 true), layers.nonces⟩)

/-- img-v6 expansion: normalize to what the 5,239-byte codec keeps, then the old kernel. -/
def expand (message : Message) (pk : Digest) (sig : Signature) : M (Option Witness) :=
  expandFill message pk (normTop sig)

theorem nonce_retained (sig : Signature) (c : Nat) :
    (fillTopSignature sig c).rho = sig.rho := rfl

theorem hints_retained (sig : Signature) (c : Nat) :
    (fillTopSignature sig c).policyHints = sig.policyHints := rfl

theorem ofNat_mod_pow_idem (n m x : Nat) (hm : m ≤ n) :
    BitVec.ofNat n ((BitVec.ofNat n (x % 2 ^ m)).toNat % 2 ^ m) = BitVec.ofNat n (x % 2 ^ m) := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hm), Nat.mod_mod]

theorem normPathD_idem (j : Nat) (d : Digest) : normPathD j (normPathD j d) = normPathD j d := by
  unfold normPathD
  by_cases h1 : 1 ≤ j ∧ j ≤ 10
  · simp only [if_pos h1]
    exact ofNat_mod_pow_idem 128 (128 - topZeroBits j) d.toNat (by omega)
  · by_cases h11 : j = 11
    · simp only [if_neg h1, if_pos h11]
      exact ofNat_mod_pow_idem 128 104 d.toNat (by omega)
    · simp only [if_neg h1, if_neg h11]

theorem normPathD_setTop (d : Digest) (c : Nat) : normPathD 11 (setTop d c) = normPathD 11 d := by
  unfold normPathD
  simp only [show ¬(1 ≤ 11 ∧ 11 ≤ 10) by omega, if_false, if_true]
  congr 1
  rw [setTop_toNat, Nat.add_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 104 ≤ 112)),
    show c % 2 ^ 16 * 2 ^ 112 % 2 ^ 104 = 0 from
      Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by norm_num)) _), add_zero, Nat.mod_mod]

/-- T51: the zero-bit allocation (`b_h = 0,0,1,1,2,3,4,5,6,7,8`; #938 had `b_h = h`). -/
theorem normZeroBits_eq (j : Nat) (hj : j ≤ 11) : topZeroBits j = topZeroAlloc.getD j 0 := by
  rfl

/-- A path node that passes its zero test is fixed by the normal form (the top sibling up to its brute-forced
bits 109..127). -/
theorem normPathD_ok (j : Nat) (hj : j < 12) (d : Digest) (hz : 1 ≤ j → topZeroOk j d = true) :
    normPathD j d = if j = 11 then setTop d 0 else d := by
  unfold normPathD
  by_cases hj0 : j = 0
  · subst hj0
    simp
  by_cases h11 : j = 11
  · subst h11
    simp only [show ¬(1 ≤ 11 ∧ 11 ≤ 10) by omega, if_false, if_true]
    have h' : d.toNat / 2 ^ 104 % 2 ^ 8 = 0 := by
      have := hz (by omega)
      unfold topZeroOk at this
      simpa using this
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, setTop_toNat, show (2 : Nat) ^ 112 = 2 ^ 104 * 2 ^ 8 by norm_num, Nat.mod_mul, h']
    simp only [mul_zero, add_zero, Nat.zero_mod, zero_mul]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) d.isLt)
  · have h1 : 1 ≤ j ∧ j ≤ 10 := by omega
    simp only [if_pos h1, if_neg h11]
    have hz' := hz (by omega)
    unfold topZeroOk at hz'
    rw [if_neg h11, beq_iff_eq] at hz'
    have hdm := Nat.div_add_mod d.toNat (2 ^ (128 - topZeroBits j))
    rw [hz', mul_zero, zero_add] at hdm
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hdm]
    exact Nat.mod_eq_of_lt d.isLt

theorem normTop_rho (sig : Signature) : (normTop sig).rho = sig.rho := rfl
theorem normTop_forest (sig : Signature) : (normTop sig).forest = sig.forest := rfl

theorem normTop_layers_ne (sig : Signature) (lay : Layer) (h : lay ≠ 0) : (normTop sig).layers lay = sig.layers lay := by
  have h0 : lay.val ≠ 0 := fun hv => h (Fin.ext hv)
  unfold normTop normLayer
  simp only [h0, if_false]

theorem normTop_hints (sig : Signature) (h : sig.policyHints.toNat < 2 ^ 13) :
    (normTop sig).policyHints = sig.policyHints := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 16 (sig.policyHints.toNat % 2 ^ 13)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt sig.policyHints.isLt]

theorem normTop_normTop (sig : Signature) : normTop (normTop sig) = normTop sig := by
  unfold normTop
  congr 1
  · exact ofNat_mod_pow_idem 16 13 sig.policyHints.toNat (by omega)
  · funext lay
    unfold normLayer
    congr 1
    funext j
    by_cases h0 : lay.val = 0
    · simp only [h0, if_true, normPathD_idem]
    · simp only [h0, if_false]

theorem normTop_fill (sig : Signature) (c : Nat) : normTop (fillTopSignature sig c) = normTop sig := by
  unfold normTop fillTopSignature
  congr 1
  funext lay
  unfold normLayer fillLayer
  congr 1
  funext j
  by_cases h0 : lay.val = 0
  · by_cases h11 : j.val = 11
    · simp only [h0, h11, and_self, if_true, normPathD_setTop]
    · simp only [h0, h11, and_false, true_and, if_true, if_false]
  · simp only [h0, false_and, if_false]

/-- Honest signatures (top path zero tests passed, 13-bit hint) normalize to the old `fillTopSignature sig 0`. -/
theorem normTop_eq_fill (sig : Signature) (hh : sig.policyHints.toNat < 2 ^ 13) (hz : TopPathOK sig) :
    normTop sig = fillTopSignature sig 0 := by
  unfold normTop fillTopSignature
  congr 1
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hh, Nat.mod_eq_of_lt sig.policyHints.isLt]
  · funext lay
    unfold normLayer fillLayer
    congr 1
    funext j
    by_cases h0 : lay.val = 0
    · have hl : lay = 0 := Fin.ext h0
      subst hl
      have hj : j.val < 12 := j.isLt
      rw [normPathD_ok j.val hj _ (hz j)]
      by_cases h11 : j.val = 11
      · simp [h11]
      · simp [h11]
    · simp only [h0, false_and, if_false]

theorem expand_normTop (message : Message) (pk : Digest) (sig : Signature) :
    expand message pk (normTop sig) = expand message pk sig := by
  unfold expand
  rw [normTop_normTop]

theorem fillTopSignature_fill (sig : Signature) (a b : Nat) :
    fillTopSignature (fillTopSignature sig a) b = fillTopSignature sig b := by
  unfold fillTopSignature
  simp only [Signature.mk.injEq, true_and]
  funext lay
  exact fillLayer_fillLayer lay (sig.layers lay) a b

theorem expandFill_fill (message : Message) (pk : Digest) (sig : Signature) (c : Nat) :
    expandFill message pk (fillTopSignature sig c) = expandFill message pk sig := by
  simp only [expandFill, hints_retained, fillTopSignature_fill]

/-- On an honest signature (13-bit hint, top path zero tests passed) `expand` is the old kernel. -/
theorem expand_eq_expandFill (message : Message) (pk : Digest) (sig : Signature)
    (hh : sig.policyHints.toNat < 2 ^ 13) (htop : TopPathOK sig) :
    expand message pk sig = expandFill message pk sig := by
  unfold expand
  rw [normTop_eq_fill sig hh htop, expandFill_fill]


theorem canonical_fts_window : CanonicalPolicy.ftsSearchLimit = digestAttemptLimit := rfl

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 ClaudeWCT.WCT9

def aCorrection (low : Nat) : Nat := 2 - SharedPathPacking.saves low
def bCorrection (low : Nat) : Nat := 2 - SharedPathPacking.saves low

/-- C1 (stage 1): the correction `2 - skips′` of each low-field class (13 classes 0, 16 classes 1, 3 classes 2). -/
def correctionTable : List Nat :=
  [2,1,1,1,1,0,0,1,1,0,0,0,0,0,0,1,2,1,1,0,1,0,0,1,1,0,0,1,1,1,1,2]

set_option maxRecDepth 100000 in
theorem aCorrection_table : ∀ c : Fin 32, aCorrection c.val = correctionTable.getD c.val 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem bCorrection_table : ∀ c : Fin 32, bCorrection c.val = correctionTable.getD c.val 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Only five unshared selector bits influence a coordinate's accounting
cost. The shared pair-branch bit is absent from this formula. -/
theorem accountingCorrection_low (coord : Fin 9) (raw : Child) :
    accountingCorrection coord.val raw =
      if firstCoord coord.val then aCorrection (raw.val % 32)
      else bCorrection (raw.val / 2 % 32) := by
  fin_cases coord <;> fin_cases raw <;> decide +kernel

def costFieldBase (coord : Nat) : Nat := rawChildBase coord + (if firstCoord coord then 0 else 1)
def costField (output : HashOutput) (coord : Fin 9) : Fin 32 :=
  ⟨output.toNat / 2 ^ costFieldBase coord.val % 32, Nat.mod_lt _ (by decide)⟩

theorem accountingCorrection_field (output : HashOutput) (coord : Fin 9) :
    accountingCorrection coord.val (rawChildFromOutput output coord) =
      if firstCoord coord.val then aCorrection (costField output coord).val
      else bCorrection (costField output coord).val := by
  rw [accountingCorrection_low]
  unfold rawChildFromOutput costField costFieldBase
  split
  · rename_i h
    simp only [h, ↓reduceIte, Nat.add_zero]
    congr 1
    omega
  · rename_i h
    simp only [h, ↓reduceIte, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    congr 1
    omega

theorem costFieldBases : (List.range 9).map costFieldBase =
    [0, 7, 64, 71, 128, 135, 192, 199, 230] := by decide +kernel

/-- All nine5-bit cost fields, nine10-bit rank fields, the31-bit index,
and14-bit gate occupy disjoint ranges of the256-bit digest. -/
def countingFields : List (Nat × Nat) :=
  ((List.range 9).map fun k => (costFieldBase k, 5)) ++
  ((List.range 9).map fun k => (rankBase k, 10)) ++ [(33,31), (242,14)]

def countingFieldsOK : Bool :=
  countingFields.all (fun a => decide (a.1 + a.2 ≤ 256)) &&
    (countingFields.zipIdx).all (fun ai =>
      (countingFields.zipIdx).all (fun bj =>
        decide (ai.2 = bj.2 ∨ ai.1.1 + ai.1.2 ≤ bj.1.1 ∨ bj.1.1 + bj.1.2 ≤ ai.1.1)))

theorem countingFields_disjoint : countingFieldsOK = true := by decide +kernel
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness

def prefixRows (answers : Answers) (lay : Layer) (tree leaf : Nat) : List (List Digest) :=
  (List.range (chainCount lay)).map fun i =>
    evalWithAnswerFn answers (chainPrefixes lay tree leaf i 0 (maxDigit lay i)
      (wotsSeed answers lay tree leaf i))

theorem prefixRows_getD (answers : Answers) (lay : Layer) (tree leaf i j : Nat)
    (hi : i < chainCount lay) (hj : j ≤ maxDigit lay i) :
    ((prefixRows answers lay tree leaf).getD i []).getD j 0 =
      evalWithAnswerFn answers (chainW lay tree leaf i 0 j
        (wotsSeed answers lay tree leaf i)) := by
  unfold prefixRows
  rw [List.getD_eq_getElem _ [] (by simpa)]
  simp only [List.getElem_map, List.getElem_range]
  exact eval_chainPrefixes_getD answers lay tree leaf i 0 _ _ j hj

theorem buildLeafPrefixes_result (answers : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree leaf : Nat) (carry : List Digest)
    (hcarry : leaf % famGrp lay ≠ 0 → carry = famCoefL answers lay tree (famOf lay leaf)) :
    evalWithAnswerFn answers (buildLeafPrefixes lay tree leaf carry) =
      ((wotsRoot answers lay tree leaf, prefixRows answers lay tree leaf),
       leafCarryOut answers lay tree leaf) := by
  simp only [buildLeafPrefixes, evalWithAnswerFn_bind,
    eval_lowerCoefs answers hlay tree leaf carry hcarry, evalWithAnswerFn_pure, eval_mapM,
    lowerFamilySeed_eq answers hlay]
  change ((evalWithAnswerFn answers (lowerLeafHash lay tree leaf
    ((List.range (chainCount lay)).map fun i =>
      ((prefixRows answers lay tree leaf).getD i []).getD (maxDigit lay i) 0)),
    prefixRows answers lay tree leaf), _) = _
  have he : (List.range (chainCount lay)).map (fun i =>
      ((prefixRows answers lay tree leaf).getD i []).getD (maxDigit lay i) 0) =
      (List.range (chainCount lay)).map (wotsEnd answers lay tree leaf) := by
    apply List.map_congr_left
    intro i hi
    exact prefixRows_getD answers lay tree leaf i _ (List.mem_range.mp hi) (by omega)
  rw [he]
  rfl

def prefixTreeRows (lay : Layer) (tree selected : Nat) :
    M (List Digest × List (List Digest) × List Digest) :=
  (List.range (2 ^ height lay)).foldlM
    (fun (state : List Digest × List (List Digest) × List Digest) leaf => do
      let ((root, prefixes), carry) ←
        if leaf = selected then buildLeafPrefixes lay tree leaf state.2.2
        else do
          let ((root, _), carry) ← buildLeafPF lay tree leaf [] state.2.2
          pure ((root, []), carry)
      pure (state.1 ++ [root], if leaf = selected then prefixes else state.2.1, carry))
    ([], [], [])

def PrefixTreeRows (answers : Answers) (lay : Layer) (tree selected done : Nat)
    (rows : List Digest × List (List Digest) × List Digest) : Prop :=
  rows.1.length = done ∧
    (∀ j, j < done → rows.1.getD j 0 = wotsRoot answers lay tree j) ∧
    rows.2.1 = (if selected < done then prefixRows answers lay tree selected else []) ∧
    rows.2.2 = treeCarry answers lay tree done

theorem eval_prefixTreeRows (answers : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree selected : Nat) :
    PrefixTreeRows answers lay tree selected (2 ^ height lay)
      (evalWithAnswerFn answers (prefixTreeRows lay tree selected)) := by
  unfold prefixTreeRows
  refine eval_foldlM_range_inv answers (2 ^ height lay) _
    (PrefixTreeRows answers lay tree selected) ([], [], [])
    (by simp [PrefixTreeRows, treeCarry]) ?_
  intro done _ rows hrows
  rcases hrows with ⟨hlen, hroot, hvalues, hc⟩
  have hstep : evalWithAnswerFn answers (do
      let ((root, prefixes), carry) ←
        if done = selected then buildLeafPrefixes lay tree done rows.2.2
        else do
          let ((root, _), carry) ← buildLeafPF lay tree done [] rows.2.2
          pure ((root, []), carry)
      pure (rows.1 ++ [root], if done = selected then prefixes else rows.2.1, carry)) =
      (rows.1 ++ [wotsRoot answers lay tree done],
       if done = selected then prefixRows answers lay tree done else rows.2.1,
       leafCarryOut answers lay tree done) := by
    by_cases hs : done = selected
    · subst selected
      simp only [↓reduceIte, evalWithAnswerFn_bind, hc,
        buildLeafPrefixes_result answers hlay tree done _
          (carryOk_treeCarry answers lay tree done), evalWithAnswerFn_pure]
    · simp only [hs, ↓reduceIte, evalWithAnswerFn_bind, hc,
        buildLeafPF_result answers hlay tree done [] (Cost.validDigits_nil lay) _
          (carryOk_treeCarry answers lay tree done), evalWithAnswerFn_pure]
  rw [hstep]
  refine ⟨by simp [hlen], ?_, ?_, ?_⟩
  · intro j hj
    rw [ClaudeWCT.WCT9.getD_append_singleton, hlen]
    by_cases hjd : j < done
    · rw [if_pos hjd]; exact hroot j hjd
    · have he : j = done := by omega
      subst j
      simp
  · by_cases hs : done = selected
    · subst hs; simp
    · have hs' : selected < done + 1 ↔ selected < done := by omega
      simp only [if_neg hs, hvalues, hs']
  · show leafCarryOut answers lay tree done = treeCarry answers lay tree (done + 1)
    unfold treeCarry
    rw [if_neg (show done + 1 ≠ 0 by omega), Nat.add_sub_cancel]

theorem buildTreePrefixes_factor (lay : Layer) (tree selected : Nat) :
    buildTreePrefixes lay tree selected = (do
      let rows ← prefixTreeRows lay tree selected
      let levels ← buildLevelsBelow 3 lay.val tree (height lay) rows.1
      pure ⟨levels, rows.2.1⟩) := rfl

theorem eval_buildTreePrefixes_result (answers : Answers) {lay : Layer}
    (hlay : lay ≠ 0) (tree selected : Nat) (hsel : selected < 2 ^ height lay) :
    evalWithAnswerFn answers (buildTreePrefixes lay tree selected) =
      ⟨(wotsTree answers lay tree).take (height lay),
        prefixRows answers lay tree selected⟩ := by
  let rows := evalWithAnswerFn answers (prefixTreeRows lay tree selected)
  have hr : PrefixTreeRows answers lay tree selected (2 ^ height lay) rows :=
    eval_prefixTreeRows answers hlay tree selected
  rcases hr with ⟨hlen, hroot, hvalues, -⟩
  have hroots : rows.1 = (List.range (2 ^ height lay)).map (wotsRoot answers lay tree) :=
    list_eq_range_map _ _ _ hlen hroot
  rw [if_pos hsel] at hvalues
  rw [buildTreePrefixes_factor, evalWithAnswerFn_bind]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (⟨evalWithAnswerFn answers (buildLevelsBelow 3 lay.val tree (height lay) rows.1),
    rows.2.1⟩ : PreparedLower) = _
  rw [hroots, hvalues, eval_buildLevelsBelow answers 3 lay.val tree (height lay) _ (by simp)
    (by fin_cases lay <;> decide)]
  simp only [wotsTree, if_neg hlay]

theorem preparedPieces_result (answers : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree selected : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (hsel : selected < 2 ^ height lay) :
    preparedPieces lay selected
      (evalWithAnswerFn answers (buildTreePrefixes lay tree selected)) digits =
      wotsPieces answers lay tree selected digits := by
  rw [eval_buildTreePrefixes_result answers hlay tree selected hsel]
  unfold preparedPieces wotsPieces
  apply Prod.ext
  · apply List.map_congr_left
    intro i hi
    exact prefixRows_getD answers lay tree selected i _ (List.mem_range.mp hi)
      (hvalid i (List.mem_range.mp hi))
  · exact map_range_take_path _ _ _

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 ClaudeWCT.WCT9

theorem base22_unique {x y : Nat} (hx : x < 7744) (hy : y < 7744)
    (h1 : x / 484 % 22 = y / 484 % 22) (h2 : x / 22 % 22 = y / 22 % 22)
    (h3 : x % 22 = y % 22) : x = y := by
  omega

theorem hintFloor_unique {a b : BitVec 16} (ha : a.toNat < 7744) (hb : b.toNat < 7744)
    (h1 : hintFloor a 1 = hintFloor b 1)
    (h2 : hintFloor a 2 = hintFloor b 2)
    (h3 : hintFloor a 3 = hintFloor b 3) : a = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [hintFloor, show (1 : Layer) ≠ 0 by decide, show (2 : Layer) ≠ 0 by decide,
    show (3 : Layer) ≠ 0 by decide, if_false] at h1 h2 h3
  norm_num at h1 h2 h3
  exact base22_unique ha hb h1 h2 h3

theorem policyHintsValid_unique {a b : BitVec 16} {digits : List (List Nat)} {lows : List Bool}
    (ha : policyHintsValid a digits lows = true) (hb : policyHintsValid b digits lows = true) : a = b := by
  simp only [policyHintsValid, decide_eq_true_eq] at ha hb
  exact hintFloor_unique ha.1 hb.1 (ha.2.2.1.trans hb.2.2.1.symm)
    (ha.2.2.2.1.trans hb.2.2.2.1.symm) (ha.2.2.2.2.trans hb.2.2.2.2.symm)

theorem encodedHints_spec (a b c : Nat) (ha : a < 16) (hb : b < 22) (hc : c < 22) :
    let code := BitVec.ofNat 16 (484 * a + 22 * b + c)
    code.toNat < 7744 ∧ hintFloor code 1 = a ∧
      hintFloor code 2 = b ∧ hintFloor code 3 = c := by
  dsimp only
  simp only [hintFloor, show (1 : Layer) ≠ 0 by decide,
    show (2 : Layer) ≠ 0 by decide, show (3 : Layer) ≠ 0 by decide, if_false]
  norm_num [BitVec.toNat_ofNat]
  have hn : 484 * a + 22 * b + c < 65536 := by omega
  rw [Nat.mod_eq_of_lt hn]
  omega

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 ClaudeWCT.WCT9

theorem firstThreshold_window : ∀ r : Fin 56,
    CanonicalPolicy.threshold 1 r.val < 16 ∧
      r.val - CanonicalPolicy.threshold 1 r.val ≤ 40 := by
  decide +kernel

theorem secondThreshold_window : ∀ r : Fin 41,
    CanonicalPolicy.threshold 2 r.val < 22 ∧
      r.val - CanonicalPolicy.threshold 2 r.val ≤ 21 := by
  decide +kernel

theorem thirdThreshold_window (r : Nat) (hr : r ≤ 21) :
    CanonicalPolicy.threshold 3 r = r := by
  simp [CanonicalPolicy.threshold, hr]

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Cost ClaudeWCT.WCT9.Cost

theorem bound_chainPrefixes (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    CBound (fun xs => xs.length = count + 1) count
      (chainPrefixes lay tree leaf i start count value) := by
  induction count generalizing start value with
  | zero => exact .pure [value] 0 rfl
  | succ count ih =>
    unfold chainPrefixes
    have hs : CBound (fun _ => True) 1
        (halfHash (chainHigh lay i start)
          (ClaudeWCT.WCT9.chainInputW lay tree leaf i start value)) := by
      apply bound_halfHash <;>
        simp [ClaudeWCT.WCT9.chainInputW_length, pad64_length]
    refine hs.bind' (l := count) (fun next _ => ?_) (by omega)
    refine (ih (start + 1) next).bind' (l := 0) (n := count)
      (fun tail ht => .pure (value :: tail) 0 (by simp [ht])) (by omega)

theorem sum_map_range_eq (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem bound_buildLeafPrefixes (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    CBound (fun result => result.1.2.length = chainCount lay) (leafCostP lay leaf)
      (buildLeafPrefixes lay tree leaf carry) := by
  unfold buildLeafPrefixes
  refine (bound_lowerCoefs lay tree leaf carry).bind' (l := digitTotal lay + leafHashCost lay)
    (fun res _ => ?_) (by unfold leafCostP; omega)
  refine (Bound.mapM_list (P := GoodQuery) (List.range (chainCount lay)) _
    (fun i => maxDigit lay i) (fun i _ =>
      (bound_chainPrefixes lay tree leaf i 0 (maxDigit lay i) (lowerFamilySeed res.1 lay leaf i)).mono
        (fun _ h => h) (fun _ _ => trivial))).bind' (l := leafHashCost lay)
    (fun prefixes hprefixes => ?_) ?_
  · refine (bound_lowerLeafHash lay tree leaf _ (by simp only [List.length_map, List.length_range])).bind' (l := 0) (n := leafHashCost lay)
      (fun root _ => .pure _ 0 (by simpa using hprefixes)) (by omega)
  · unfold digitTotal
    simp only [sum_map_range_eq]
    exact le_rfl

theorem bound_buildTreePrefixes (lay : Layer) (tree selected : Nat) :
    CBound (fun result => LevelShape (height lay) (height lay - 1) result.levels)
      (treeCostP lay) (buildTreePrefixes lay tree selected) := by
  unfold buildTreePrefixes
  refine Bound.bind' (l := 2 ^ height lay - 2) (Bound.foldlM_range (2 ^ height lay) _
    (fun i (state : List Digest × List (List Digest) × List Digest) => state.1.length = i)
    (leafCostP lay) ([], [], []) rfl (fun leaf _ state hstate => ?_))
    (fun state hstate => ?_) le_rfl
  · by_cases hs : leaf = selected
    · simp only [if_pos hs]
      refine (bound_buildLeafPrefixes lay tree leaf state.2.2).bind' (l := 0)
        (fun result _ => .pure _ 0 (by simp [hstate])) (by omega)
    · simp only [if_neg hs]
      refine (bound_buildLeafPF lay tree leaf [] (validDigits_nil lay) state.2.2).bind' (l := 0)
        (fun result _ => ?_) (by omega)
      exact .pure _ 0 (by simp [hstate])
  · refine (bound_buildLevelsBelow 3 lay.val tree (height lay) state.1 hstate
      (by fin_cases lay <;> decide)).bind' (l := 0)
      (fun levels hlevels => .pure (PreparedLower.mk levels state.2.1) 0 hlevels) (by omega)

theorem bound_prepareRoots (index : Nat) :
    CBound (fun _ => True) (treeCostP 1 + treeCostP 2 + treeCostP 3) (prepareRoots index) := by
  unfold prepareRoots
  refine (bound_buildTreePrefixes 1 (route index 1).2 (route index 1).1).bind'
    (l := treeCostP 2 + treeCostP 3) (fun one _ => ?_) (by omega)
  refine (bound_buildTreePrefixes 2 (route index 2).2 (route index 2).1).bind'
    (l := treeCostP 3) (fun two _ => ?_) (by omega)
  exact (bound_buildTreePrefixes 3 (route index 3).2 (route index 3).1).bind'
    (l := 0) (fun three _ => .pure (PreparedRoots.mk one two three) 0 trivial) (by omega)

/-- v6 lower families: 81146 − 325 (L1 349 + L2/L3 175 family pairs instead of 4 per leaf). -/
theorem prepared_roots_cost : treeCostP 1 + treeCostP 2 + treeCostP 3 = 80821 := by
  rw [treeCostP_one, treeCostP_two, treeCostP_three]

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Cost ClaudeWCT.WCT9.Cost

theorem rawChild_lt (first : Bool) (physical : Nat) (h : physical < 128) :
    rawChild first physical < 128 := by
  cases first <;> simp only [rawChild, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem bound_highHash64 (input : HashInput) (hlen : input.length = 64) :
    CBound (fun _ => True) 1 (highHash input) := by
  apply bound_highHashP
  · simp only [GoodQuery, pad64_length, hlen]
    norm_num
  · simp only [pad64_length, hlen]
    norm_num

theorem bound_sharedOuterHash (coord index heap : Nat) (left right : Digest) :
    CBound (fun _ => True) 1 (sharedOuterHash coord index heap left right) := by
  unfold sharedOuterHash
  split
  · apply bound_shortHash <;> simp [wctTopInput_length, pad64_length]
  · exact bound_highHash64 _ (wctTopInput_length ..)

theorem bound_sharedNode (first : Bool) (coord index heap : Nat) (pads : Nat → PairRoot)
    (left right : Digest) :
    CBound (fun _ => True) 1 (sharedNode first coord index heap pads left right) := by
  unfold sharedNode
  split
  · exact bound_sharedOuterHash ..
  · split
    · split
      · exact bound_highHash64 _ (wctTopInput_length ..)
      · apply bound_shortHash <;> simp [wctTopInput_length, pad64_length]
    · rw [nodeHashH_eq, ftsHash_eq]
      split
      · exact bound_highHash64 _ (nodeInput_length ..)
      · apply bound_shortHash <;> simp [nodeInput_length, pad64_length]

theorem bound_sharedHeap (first : Bool) (index coord : Nat) (pads : Nat → PairRoot)
    (leaves : List Digest) :
    CBound (fun _ => True) (if first then 124 else 126) (sharedHeap first index coord pads leaves) := by
  unfold sharedHeap
  apply (Bound.foldlM_list (P := GoodQuery)
    (List.range' (if first then 4 else 2) (if first then 124 else 126)).reverse
    (fun (nodes : Array Digest) heap => do
      let value ← sharedNode first coord index heap pads
        (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
      pure (nodes.set! heap value)) (fun _ _ => True) (fun _ => 1) _
    trivial (fun i hi nodes _ =>
      (bound_sharedNode first coord index _ pads _ _).bind' (l := 0)
        (fun value _ => .pure (nodes.set! _ value) 0 trivial) (by omega))).mono_k
  simp

theorem bound_buildSharedCoordinate (first : Bool) (index coord : Nat)
    (hcoord : coord < 9) (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    CBound (fun _ => True) (if first then 3479 else 3481)
      (buildSharedCoordinate first index coord selected word pads) := by
  unfold buildSharedCoordinate
  refine (cbound_of_ftsBound (ftsBound_ftsCoefs index coord hcoord)).bind'
    (l := 3328 + if first then 124 else 126) (fun coefs _ => ?_) ?_
  · refine (Bound.foldlM_range_le 128 _ (fun _ _ => True) (fun _ => 26) ([], [])
      trivial (fun j hj state _ => ?_) (fun _ _ => trivial) (by simp)).bind'
      (l := if first then 124 else 126) (fun state _ => ?_) le_rfl
    · refine (bound_buildChildH (128 + j) index coord (rawChild first j) word coefs (pads (j / 64)).1
        hcoord (rawChild_lt first j hj)).bind' (l := 0)
        (fun child _ => .pure _ 0 trivial) (by simp [ClaudeWCT.WCT9.childCost])
    · exact (bound_sharedHeap first index coord pads state.1).bind' (l := 0)
        (fun nodes _ => .pure (nodes, state.2) 0 trivial) (by omega)
  · cases first <;> decide

theorem bound_buildPair (index pair : Nat) (hpair : pair < 4) (s : Selection)
    (aWord bWord : Rank) (prev : PairRoot) :
    CBound (fun _ => True) 6960 (buildPair index pair s aWord bWord prev) := by
  unfold buildPair
  refine (bound_buildSharedCoordinate true index (2 * pair) (by omega)
    (firstChild s) aWord (fun _ => prev)).bind' (l := 3481) (fun a _ => ?_) (by decide)
  exact (bound_buildSharedCoordinate false index (2 * pair + 1) (by omega)
    (secondChild s) bWord (nodesPair a.1)).bind' (l := 0)
    (fun b _ => .pure _ 0 trivial) (by decide)

theorem bound_buildSingleton (index : Nat) (selected : Child) (word : Rank) (prev : PairRoot) :
    CBound (fun _ => True) 3481 (buildSingleton index selected word prev) := by
  unfold buildSingleton
  exact (bound_buildSharedCoordinate false index 8 (by decide) selected word (fun _ => prev)).bind'
    (l := 0) (fun built _ => .pure _ 0 trivial) (by decide)

theorem bound_buildForest (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    CBound (fun _ => True) 31321 (buildForest index selected words) := by
  unfold buildForest
  refine (Bound.foldlM_list (P := GoodQuery) (List.finRange 4) _ (fun _ _ => True)
    (fun _ => 6960) ([], ftsStart) trivial (fun i hi state _ => ?_)).bind'
    (l := 3481) (fun state _ => ?_) (by simp)
  · exact (bound_buildPair index _ ((List.finRange 4)[i]'hi).isLt _ _ _ state.2).bind'
      (l := 0) (fun built _ => .pure _ 0 trivial) (by decide)
  · exact (bound_buildSingleton index selected.singleton words.singleton state.2).bind'
      (l := 0) (fun last _ => .pure _ 0 trivial) (by decide)

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem canonical_decode_valid {lay : Layer} {answer : Digest} {digits : List Nat}
    (h : CanonicalPolicy.decode lay answer = some digits) :
    Cost.ValidDigits lay digits := by
  have hv := Cost.validDigits_decode h
  fin_cases lay <;> simpa [CanonicalPolicy.normalLayer, Cost.ValidDigits, chainCount, maxDigit] using hv

theorem canonical_search_some (answers : Answers) (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) : ∀ fuel counter found digits low, counter + fuel ≤ 2 ^ 32 →
      evalWithAnswerFn answers
        (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) = some (found, digits, low) →
      counter ≤ found.toNat ∧ found.toNat < counter + fuel ∧
        CanonicalPolicy.producerDecodeOut lay floor
          (evalWithAnswerFn answers (publicHash (layerEncodingInput lay tree leaf msg found))) =
            some (digits, low) := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter found digits low _ he
      simp [CanonicalPolicy.layerCounterSearchAt] at he
  | succ fuel ih =>
      intro counter found digits low hlimit he
      simp only [CanonicalPolicy.layerCounterSearchAt, evalWithAnswerFn_bind] at he
      cases hd : CanonicalPolicy.producerDecodeOut lay floor (evalWithAnswerFn answers
        (publicHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)))) with
      | none =>
          simp only [hd] at he
          obtain ⟨hlo, hhi, hgood⟩ := ih (counter + 1) found digits low (by omega) he
          exact ⟨by omega, by omega, hgood⟩
      | some values =>
          simp only [hd, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          have hcount : (BitVec.ofNat 32 counter).toNat = counter := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact ⟨by rw [hcount], by rw [hcount]; omega, hd⟩

/-- `canonical_search_some` unpacked: the returned half is the canonical one and the producer accepted the
canonical word (`encodingHash`) with that half. -/
theorem canonical_search_some' (answers : Answers) (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) (fuel counter : Nat) (found : BitVec 32) (digits : List Nat) (low : Bool)
    (hlimit : counter + fuel ≤ 2 ^ 32)
    (he : evalWithAnswerFn answers
        (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) = some (found, digits, low)) :
    counter ≤ found.toNat ∧ found.toNat < counter + fuel ∧
      low = lowSelected lay (evalWithAnswerFn answers (publicHash (layerEncodingInput lay tree leaf msg found))) ∧
      CanonicalPolicy.producerDecodeAt lay floor low
        (evalWithAnswerFn answers (encodingHash lay (layerEncodingInput lay tree leaf msg found))) = some digits := by
  obtain ⟨h1, h2, h3⟩ := canonical_search_some answers lay floor tree leaf msg fuel counter found digits low hlimit he
  obtain ⟨hl, hd⟩ := CanonicalPolicy.producerDecodeOut_spec h3
  exact ⟨h1, h2, hl, hd⟩

theorem canonical_search_valid_credit (answers : Answers) (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) (fuel counter : Nat) (found : BitVec 32) (digits : List Nat) (low : Bool)
    (hlimit : counter + fuel ≤ 2 ^ 32)
    (he : evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) = some (found, digits, low)) :
    Cost.ValidDigits lay digits ∧ floor ≤ CanonicalPolicy.credit lay low digits := by
  have hd := (canonical_search_some' answers lay floor tree leaf msg fuel counter found digits low hlimit he).2.2.2
  exact ⟨canonical_decode_valid (CanonicalPolicy.producerDecodeAt_spec hd).1,
    CanonicalPolicy.producerDecodeAt_credit hd⟩

theorem canonical_four_residual (d0 d1 d2 d3 : List Nat) (l0 l1 l2 l3 : Bool)
    (h0 : 14 ≤ CanonicalPolicy.credit 0 l0 d0)
    (h1 : CanonicalPolicy.threshold 1 (CanonicalPolicy.nextResidual 69 0 l0 d0) ≤
      CanonicalPolicy.credit 1 l1 d1)
    (h2 : CanonicalPolicy.threshold 2
      (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual 69 0 l0 d0) 1 l1 d1) ≤
      CanonicalPolicy.credit 2 l2 d2)
    (h3 : CanonicalPolicy.threshold 3
      (CanonicalPolicy.nextResidual
        (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual 69 0 l0 d0) 1 l1 d1) 2 l2 d2) ≤
      CanonicalPolicy.credit 3 l3 d3) :
    CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual
      (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual 69 0 l0 d0) 1 l1 d1) 2 l2 d2) 3 l3 d3 = 0 := by
  let r1 := CanonicalPolicy.nextResidual 69 0 l0 d0
  have hr1 : r1 < 56 := by dsimp [r1, CanonicalPolicy.nextResidual]; omega
  have hw1 := firstThreshold_window ⟨r1, hr1⟩
  change CanonicalPolicy.threshold 1 r1 < 16 ∧ r1 - CanonicalPolicy.threshold 1 r1 ≤ 40 at hw1
  let r2 := CanonicalPolicy.nextResidual r1 1 l1 d1
  have hr2 : r2 < 41 := by
    change CanonicalPolicy.threshold 1 r1 ≤ CanonicalPolicy.credit 1 l1 d1 at h1
    dsimp [r2, CanonicalPolicy.nextResidual]; omega
  have hw2 := secondThreshold_window ⟨r2, hr2⟩
  change CanonicalPolicy.threshold 2 r2 < 22 ∧ r2 - CanonicalPolicy.threshold 2 r2 ≤ 21 at hw2
  let r3 := CanonicalPolicy.nextResidual r2 2 l2 d2
  have hr3 : r3 ≤ 21 := by
    change CanonicalPolicy.threshold 2 r2 ≤ CanonicalPolicy.credit 2 l2 d2 at h2
    dsimp [r3, CanonicalPolicy.nextResidual]; omega
  change CanonicalPolicy.threshold 3 r3 ≤ CanonicalPolicy.credit 3 l3 d3 at h3
  rw [thirdThreshold_window r3 hr3] at h3
  change r3 - CanonicalPolicy.credit 3 l3 d3 = 0
  omega

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9

def verifyDigestAccepted (output : HashOutput) : Bool :=
  decide (output.toNat / 2 ^ 242 % 16384 < 791) && ranksAccepted output

theorem digestAccepted_implies_verify {output : HashOutput} (h : digestAccepted output = true) :
    verifyDigestAccepted output = true := by
  simp only [digestAccepted, Bool.and_eq_true] at h
  simpa only [verifyDigestAccepted, Bool.and_eq_true] using h.1

/-- Broad normalized verification retains the machine's early abort ordering.
Canonical producer floors and hints are checked by the signer and expander. -/
def verifyLayers (w : Witness) (index : Nat) : Nat → LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := w.counters lay
      if counter.toNat ≥ verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← verificationHash lay w.topHigh (layerEncodingInput lay tree leaf msg counter)
      if n = 0 then verifyTopN (mainSignature w.signature) w.topNonces index answer
      else
        let some digits := CanonicalPolicy.decode lay answer | pure none
        let some pair ← recoverLayerPairGuard (mainSignature w.signature) index lay answer digits | pure none
        verifyLayers w index n (.pair pair.1 pair.2)

def verify (message : Message) (pk : Digest) (w : Witness) : M Bool := do
  if w.digestCounter.toNat ≥ digestVerifyWindow then return false
  let output ← digest w.signature.rho message w.digestCounter
  if !verifyDigestAccepted output then return false
  let index := digestIndex output
  let forest ← recoverForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output) w.signature.forest
  let some root ← verifyLayers w index 4 (.pair forest.1 forest.2) | pure false
  pure (root == pk)

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem recoverHintedLayers_verified (answers : Answers) (sig : Signature) (index : Nat) :
    ∀ n, n ≤ 4 → ∀ msg result,
      evalWithAnswerFn answers (recoverHintedLayers sig index ((sig.layers 0).path topJ) n msg) = some result →
      result.counters.length = n ∧ result.digits.length = n ∧ result.lows.length = n ∧
        ∀ w : Witness, w.signature = sig →
          (∀ lay : Layer, lay.val < n → w.counters lay = result.counters.getD lay.val 0) →
          w.topHigh = !(result.lows.getD 0 true) → w.topNonces = result.nonces →
          evalWithAnswerFn answers (verifyLayers w index n msg) = some result.root := by
  intro n
  induction n with
  | zero =>
      intro _ msg result he
      simp [recoverHintedLayers] at he
  | succ n ih =>
      intro hn msg result he
      simp only [recoverHintedLayers, evalWithAnswerFn_bind] at he
      split at he
      ·
          rename_i counter digits low hs
          have hlim := searchLimit_le (Fin.ofNat 4 n)
          obtain ⟨_, hbound, hlow, hproducer⟩ := canonical_search_some' answers _ _ _ _ _
            _ 0 counter digits low (by unfold counterLimit at hlim; omega) hs
          have hdecode := (CanonicalPolicy.producerDecodeAt_spec hproducer).1
          have hnot : ¬counter.toNat ≥ verifyWindow := ctr_not_ge_verifyWindow counter
          have hlay := ofNat_layer_val n (by omega)
          by_cases hn0 : n = 0
          · subst n
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at he
            subst result
            refine ⟨rfl, rfl, rfl, fun w hw hc hh hnon => ?_⟩
            have hcounter : w.counters (Fin.ofNat 4 0) = counter := by
              rw [hc _ (by rw [hlay]; omega), hlay]; rfl
            have hdecode0 : SigGolfCandidate.T3.decode 0
                (evalWithAnswerFn answers (encodingHash 0
                  (layerEncodingInput 0 (route index 0).2 (route index 0).1 msg counter))) = some digits := hdecode
            have hv : evalWithAnswerFn answers (verificationHash 0 w.topHigh
                (layerEncodingInput 0 (route index 0).2 (route index 0).1 msg counter)) =
                evalWithAnswerFn answers (encodingHash 0
                  (layerEncodingInput 0 (route index 0).2 (route index 0).1 msg counter)) := by
              apply eval_verificationHash_honest
              rw [hh, encodingHigh_top]
              simp only [List.getD_cons_zero]
              exact congrArg (fun b => !b) hlow
            simp only [verifyLayers, hcounter, hnot, ite_false, evalWithAnswerFn_bind, if_true, hw]
            simp only [show (Fin.ofNat 4 0 : Layer) = 0 from rfl]
            rw [hv, hnon]
            exact eval_verifyTopN_topFoldN answers _ index hdecode0
          · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
            split at he
            rotate_left
            · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
            ·
                rename_i previous hr
                simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
                subst result
                obtain ⟨hlen, hdlen, hllen, hverify⟩ := ih (by omega) _ _ hr
                refine ⟨by simp [hlen], by simp [hdlen], by simp [hllen], fun w hw hc hh => ?_⟩
                have hcounter : w.counters (Fin.ofNat 4 n) = counter := by
                  rw [hc _ (by rw [hlay]; omega), hlay,
                    List.getD_append_right previous.counters [counter] 0 n (by omega), hlen]
                  simp
                have hnonzero : (Fin.ofNat 4 n : Layer) ≠ 0 := by
                  intro h; have := congrArg Fin.val h; rw [hlay] at this; exact hn0 this
                have hgood : lowerRankGood (evalWithAnswerFn answers (encodingHash (Fin.ofNat 4 n)
                    (layerEncodingInput (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
                      (route index (Fin.ofNat 4 n)).1 msg counter))) :=
                  (CanonicalPolicy.producerDecodeAt_spec hproducer).2.2.2.resolve_left hnonzero
                simp only [verifyLayers, hcounter, hnot, ite_false, evalWithAnswerFn_bind,
                  verificationHash_lower (Fin.ofNat 4 n) hnonzero,
                  hdecode, hn0, hw, recoverLayerPairGuard_of_good _ _ _ _ _ hgood, evalWithAnswerFn_map]
                apply hverify w hw
                · intro lay hsmall
                  rw [hc lay (by omega), List.getD_append previous.counters [counter] 0 lay.val (by omega)]
                · rw [hh, List.getD_append previous.lows [low] true 0 (by omega)]
      · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 ClaudeWCT.WCT9

/-- The paired table selector is exactly the canonical A leaf position. -/
theorem physicalFromOutput_first (output : HashOutput) (pair : Fin 4) :
    physicalChildFromOutput output ⟨2 * pair.val, by have := pair.isLt; omega⟩ =
      firstChild ((forestSelectionFromOutput output).pairs pair) := by
  apply Fin.ext
  fin_cases pair <;>
    simp [physicalChildFromOutput, firstCoord, physicalChild, rawChildFromOutput, rawChildBase,
      forestSelectionFromOutput, selectionFromOutput, firstChild] <;> omega

/-- The rotated B selector shares A's branch and retains six independent path bits. -/
theorem physicalFromOutput_second (output : HashOutput) (pair : Fin 4) :
    physicalChildFromOutput output ⟨2 * pair.val + 1, by have := pair.isLt; omega⟩ =
      secondChild ((forestSelectionFromOutput output).pairs pair) := by
  apply Fin.ext
  fin_cases pair <;>
    simp [physicalChildFromOutput, firstCoord, physicalChild, rawChildFromOutput, rawChildBase,
      forestSelectionFromOutput, selectionFromOutput, secondChild] <;> omega

theorem physicalFromOutput_singleton (output : HashOutput) :
    physicalChildFromOutput output 8 = (forestSelectionFromOutput output).singleton := by
  rfl

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem mainSignature_fill (sig : Signature) (c : Nat) :
    mainSignature (fillTopSignature sig c) = fillTop (mainSignature sig) c := rfl

theorem topFold_fill_signature (sig : Signature) (index : Nat) (digits : List Nat) (c : Nat) :
    topFold (mainSignature (fillTopSignature sig c)) index digits =
      topFold (mainSignature sig) index digits := by
  rw [mainSignature_fill]
  have h := topFold_fill (mainSignature sig) index digits c
    ((topSib (mainSignature sig)).toNat / 2 ^ 112)
  rw [fillTop_self] at h
  exact h

theorem topFoldN_fill_signature (sig : Signature) (index : Nat) (digits : List Nat) (c : Nat) :
    topFoldN (mainSignature (fillTopSignature sig c)) index digits =
      topFoldN (mainSignature sig) index digits := by
  rw [mainSignature_fill]
  have h := topFoldN_fill (mainSignature sig) index digits c
    ((topSib (mainSignature sig)).toNat / 2 ^ 112)
  rw [fillTop_self] at h
  exact h

theorem recoverHintedLayers_fill (sig : Signature) (index : Nat) (other : Digest) (c : Nat) :
    ∀ n, n ≤ 4 → ∀ msg,
      recoverHintedLayers (fillTopSignature sig c) index other n msg =
        recoverHintedLayers sig index other n msg := by
  intro n
  induction n with
  | zero => intro _ msg; rfl
  | succ n ih =>
      intro hn msg
      simp only [recoverHintedLayers, hints_retained]
      apply bind_congr
      intro found
      cases found with
      | none => rfl
      | some found =>
          obtain ⟨counter, digits, low⟩ := found
          cases n with
          | zero =>
              simp only [if_true, topFoldN_fill_signature]
          | succ k =>
              have hne := fin_ofNat_succ_ne k (by omega)
              simp only [Nat.succ_ne_zero, if_false, mainSignature_fill,
                recoverLayerPair_fill _ _ _ _ _ hne]
              apply bind_congr
              intro pair
              rw [ih (by omega)]

theorem eval_recoverHintedLayers_other (answers : Answers) (sig : Signature)
    (index : Nat) (other other' : Digest) :
    ∀ n msg, evalWithAnswerFn answers (recoverHintedLayers sig index other' n msg) =
      (evalWithAnswerFn answers (recoverHintedLayers sig index other n msg)).map
        (fun result => {result with root := evalWithAnswerFn answers (topNode index result.foldedTop other')}) := by
  intro n
  induction n with
  | zero => intro msg; simp [recoverHintedLayers]
  | succ n ih =>
      intro msg
      simp only [recoverHintedLayers, evalWithAnswerFn_bind]
      split
      ·
          rename_i counter digits low _
          by_cases hn : n = 0
          · simp [hn]
          · simp only [hn, if_false, evalWithAnswerFn_bind, ih]
            cases evalWithAnswerFn answers (recoverHintedLayers sig index other n _) with
            | none => simp
            | some previous => simp
      · simp

theorem sharedDigestSearch_some (answers : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter found output, counter + fuel ≤ 2 ^ 32 →
      evalWithAnswerFn answers (sharedDigestSearch rho message counter fuel) = some (found, output) →
      counter ≤ found.toNat ∧ found.toNat < counter + fuel ∧ digestAccepted output = true ∧
        evalWithAnswerFn answers (digest rho message found) = output := by
  intro fuel
  induction fuel with
  | zero => intro counter found output _ he; simp [sharedDigestSearch] at he
  | succ fuel ih =>
      intro counter found output hlimit he
      simp only [sharedDigestSearch, evalWithAnswerFn_bind] at he
      split_ifs at he with hg
      · simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hc : (BitVec.ofNat 32 counter).toNat = counter := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact ⟨by rw [hc], by rw [hc]; omega, hg, rfl⟩
      · obtain ⟨hlo, hhi, hg, ho⟩ := ih (counter + 1) found output (by omega) he
        exact ⟨by omega, by omega, hg, ho⟩

theorem verify_from_recovered (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (counter : BitVec 32) (output : HashOutput) (result : RecoveredLayers)
    (ho : evalWithAnswerFn answers (digest sig.rho message counter) = output)
    (ha : verifyDigestAccepted output = true)
    (hr : evalWithAnswerFn answers (recoverHintedLayers sig (digestIndex output)
      ((sig.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
        (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)) = some result)
    (hpk : result.root = pk) :
    evalWithAnswerFn answers (verify message pk
      ⟨sig, counter, fun lay => result.counters.getD lay.val 0, !(result.lows.getD 0 true), result.nonces⟩) = true := by
  have hc : ¬counter.toNat ≥ digestVerifyWindow := Nat.not_le.mpr counter.isLt
  have hv := (recoverHintedLayers_verified answers sig (digestIndex output) 4 le_rfl _ _ hr).2.2.2
    ⟨sig, counter, fun lay => result.counters.getD lay.val 0, !(result.lows.getD 0 true), result.nonces⟩ rfl (by intros; rfl) rfl
  simp only [verify, hc, if_false, evalWithAnswerFn_bind, ho, ha, Bool.not_true,
    Bool.false_eq_true, hv, evalWithAnswerFn_pure, hpk, beq_self_eq_true]

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- The forest commitment depends only on the signing index and oracle answers;
selector and rank choices determine its opening, but not its value. -/
def forestCommitment (answers : Answers) (index : Nat) : PairRoot :=
  let first := expectedPairRoot answers index 0 ftsStart
  let second := expectedPairRoot answers index 1 first
  let third := expectedPairRoot answers index 2 second
  let fourth := expectedPairRoot answers index 3 third
  let nodes := sharedNodes answers false index 8 (fun _ => fourth)
  (nodes.getD 2 0, nodes.getD 3 0)

attribute [local irreducible] sharedNodes

theorem buildForest_commitment (answers : Answers) (index : Nat)
    (selected : ForestSelection) (words : ForestWords) :
    (evalWithAnswerFn answers (buildForest index selected words)).2 = forestCommitment answers index := by
  have hfour : List.finRange 4 = [0, 1, 2, 3] := by decide
  simp only [buildForest, hfour, List.foldlM_cons, List.foldlM_nil,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, buildPair_result,
    buildSingleton, buildSharedCoordinate_result]
  rfl

theorem recoverForest_commitment (answers : Answers) (index : Nat)
    (selected : ForestSelection) (words : ForestWords) :
    evalWithAnswerFn answers (recoverForest index selected words
      (evalWithAnswerFn answers (buildForest index selected words)).1) = forestCommitment answers index :=
  (recoverForest_honest answers index selected words).trans (buildForest_commitment answers index selected words)

def fixedPrepared (answers : Answers) (index : Nat) (lay : Layer) : PreparedLower :=
  ⟨(wotsTree answers lay (route index lay).2).take (height lay),
    prefixRows answers lay (route index lay).2 (route index lay).1⟩

theorem prepareRoots_result (answers : Answers) (index : Nat) :
    evalWithAnswerFn answers (prepareRoots index) =
      ⟨fixedPrepared answers index 1, fixedPrepared answers index 2, fixedPrepared answers index 3⟩ := by
  simp only [prepareRoots, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [eval_buildTreePrefixes_result answers (by decide) _ _ (route_leaf_bound index 1),
    eval_buildTreePrefixes_result answers (by decide) _ _ (route_leaf_bound index 2),
    eval_buildTreePrefixes_result answers (by decide) _ _ (route_leaf_bound index 3)]
  rfl

theorem fixedPrepared_pair (answers : Answers) (index : Nat) (lay : Layer) :
    topPair lay (fixedPrepared answers index lay).levels = builtPair answers lay (route index lay).2 :=
  topPair_take lay _

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem topPath_fill_signature (sig : Signature) (c : Nat) :
    ((fillTopSignature sig c).layers 0).path topJ = setTop ((sig.layers 0).path topJ) c :=
  topSib_fillTop (mainSignature sig) c

theorem expandFill_verified (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (w : Witness)
    (he : evalWithAnswerFn answers (expandFill message pk sig) = some w) :
    evalWithAnswerFn answers (verify message pk w) = true := by
  unfold expandFill at he
  by_cases hh : sig.policyHints.toNat ≥ 7744
  · simp only [hh, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he
  simp only [hh, if_false, evalWithAnswerFn_bind] at he
  let sig0 := fillTopSignature sig 0
  cases hd : evalWithAnswerFn answers (sharedDigestSearch sig0.rho message 0 digestAttemptLimit) with
  | none =>
      dsimp only [sig0] at hd
      simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      have hdlim : 0 + digestAttemptLimit ≤ 2 ^ 32 := by simpa using digestAttemptLimit_le
      obtain ⟨_, _, haccept, houtput⟩ := sharedDigestSearch_some answers sig0.rho message
        digestAttemptLimit 0 counter output hdlim hd
      have ha := digestAccepted_implies_verify haccept
      dsimp only [sig0] at hd
      simp only [hd, evalWithAnswerFn_bind] at he
      let index := digestIndex output
      let forest := evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
        (forestWordsFromOutput output) sig0.forest)
      cases hr : evalWithAnswerFn answers (recoverHintedLayers sig0 index ((sig0.layers 0).path topJ)
        4 (.pair forest.1 forest.2)) with
      | none =>
          dsimp only [index, forest, sig0] at hr
          simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some result =>
          dsimp only [index, forest, sig0] at hr
          simp only [hr] at he
          cases hp : policyHintsValid sig0.policyHints result.digits result.lows with
          | false =>
              dsimp only [sig0] at hp
              simp only [hp, Bool.not_false, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he
          | true =>
              dsimp only [sig0] at hp
              simp only [hp, Bool.not_true, Bool.false_eq_true, if_false] at he
              by_cases hpk : result.root = pk
              · simp only [hpk, if_true, evalWithAnswerFn_pure, Option.some.injEq] at he
                subst w
                exact verify_from_recovered answers message pk sig0 counter output result houtput ha hr hpk
              · simp only [hpk, if_false, evalWithAnswerFn_bind] at he
                cases hs : evalWithAnswerFn answers
                  (searchTop index result.foldedTop ((sig0.layers 0).path topJ) pk searchFuel 1) with
                | none =>
                    dsimp only [index, sig0] at hs
                    simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
                | some c =>
                    dsimp only [index, sig0] at hs
                    simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
                    subst w
                    have hc := (eval_searchTop answers index result.foldedTop ((sig0.layers 0).path topJ)
                      pk searchFuel 1 c hs).2.2
                    let completed : RecoveredLayers := {result with
                      root := evalWithAnswerFn answers
                        (topNode index result.foldedTop (((fillTopSignature sig0 c).layers 0).path topJ))}
                    have hcompleted : completed.root = pk := by
                      dsimp only [completed]
                      rw [topPath_fill_signature]
                      exact hc
                    have hr' : evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig0 c) index
                        (((fillTopSignature sig0 c).layers 0).path topJ) 4 (.pair forest.1 forest.2)) =
                        some completed := by
                      rw [recoverHintedLayers_fill _ _ _ _ _ le_rfl]
                      rw [eval_recoverHintedLayers_other answers sig0 index ((sig0.layers 0).path topJ)]
                      rw [hr]
                      rfl
                    exact verify_from_recovered answers message pk (fillTopSignature sig0 c)
                      counter output completed houtput ha hr' hcompleted

theorem expand_verified (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (w : Witness)
    (he : evalWithAnswerFn answers (expand message pk sig) = some w) :
    evalWithAnswerFn answers (verify message pk w) = true :=
  expandFill_verified answers message pk (normTop sig) w he

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def preparedResidual1 (result : CanonicalLayers) : Nat :=
  CanonicalPolicy.nextResidual (CanonicalPolicy.totalCredit) 0 (result.lows.getD 0 true) (result.digits.getD 0 [])

def preparedResidual2 (result : CanonicalLayers) : Nat :=
  CanonicalPolicy.nextResidual (preparedResidual1 result) 1 (result.lows.getD 1 true) (result.digits.getD 1 [])

def preparedResidual3 (result : CanonicalLayers) : Nat :=
  CanonicalPolicy.nextResidual (preparedResidual2 result) 2 (result.lows.getD 2 true) (result.digits.getD 2 [])

/-- The successful source program exposes exactly the four canonical searches,
with every lower threshold determined by its already selected ancestors. -/
structure PreparedSearchFacts (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) (result : CanonicalLayers) : Prop where
  pieces_length : result.pieces.length = 4
  counters_length : result.counters.length = 4
  digits_length : result.digits.length = 4
  lows_length : result.lows.length = 4
  search0 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 0
    (CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit) (route index 0).2 (route index 0).1
    (.pair (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2) 0 (searchLimit 0)) =
      some (result.counters.getD 0 0, result.digits.getD 0 [], result.lows.getD 0 true)
  search1 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 1
    (CanonicalPolicy.threshold 1 (preparedResidual1 result)) (route index 1).2 (route index 1).1
    (.pair (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2) 0 (searchLimit 1)) =
      some (result.counters.getD 1 0, result.digits.getD 1 [], result.lows.getD 1 true)
  search2 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 2
    (CanonicalPolicy.threshold 2 (preparedResidual2 result)) (route index 2).2 (route index 2).1
    (.pair (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2) 0 (searchLimit 2)) =
      some (result.counters.getD 2 0, result.digits.getD 2 [], result.lows.getD 2 true)
  search3 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 3
    (CanonicalPolicy.threshold 3 (preparedResidual3 result)) (route index 3).2 (route index 3).1
    (.pair (forest).1 (forest).2) 0 (searchLimit 3)) =
      some (result.counters.getD 3 0, result.digits.getD 3 [], result.lows.getD 3 true)
  floor1_lt : CanonicalPolicy.threshold 1 (preparedResidual1 result) < 16
  floor2_lt : CanonicalPolicy.threshold 2 (preparedResidual2 result) < 22
  floor3_lt : CanonicalPolicy.threshold 3 (preparedResidual3 result) < 22
  residual_eq : result.residual = CanonicalPolicy.nextResidual (preparedResidual3 result) 3
    (result.lows.getD 3 true) (result.digits.getD 3 [])
  hints_eq : result.policyHints = BitVec.ofNat 16
    (484 * CanonicalPolicy.threshold 1 (preparedResidual1 result) +
     22 * CanonicalPolicy.threshold 2 (preparedResidual2 result) +
     CanonicalPolicy.threshold 3 (preparedResidual3 result))
  pieces_eq : result.pieces = [
    evalWithAnswerFn answers (signTop cache (route index 0).1 (result.digits.getD 0 [])),
    preparedPieces 1 (route index 1).1 prepared.one (result.digits.getD 1 []),
    preparedPieces 2 (route index 2).1 prepared.two (result.digits.getD 2 []),
    preparedPieces 3 (route index 3).1 prepared.three (result.digits.getD 3 [])]

theorem searchPreparedLayers_some (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) (result : CanonicalLayers)
    (he : evalWithAnswerFn answers (searchPreparedLayers cache index prepared forest) = some result) :
    PreparedSearchFacts answers cache index prepared forest result := by
  unfold searchPreparedLayers at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs0 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 0
    (CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit) (route index 0).2 (route index 0).1
    (.pair (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2) 0 (searchLimit 0)) with
  | none => simp only [hs0, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found0 =>
      obtain ⟨c0, d0, l0⟩ := found0
      simp only [hs0, evalWithAnswerFn_bind] at he
      let r1 := CanonicalPolicy.nextResidual CanonicalPolicy.totalCredit 0 l0 d0
      let f1 := CanonicalPolicy.threshold 1 r1
      by_cases hf1 : f1 ≥ 16
      · dsimp only [r1, f1] at hf1
        simp only [hf1, if_true,
          evalWithAnswerFn_pure, reduceCtorEq] at he
      dsimp only [r1, f1] at hf1
      simp only [hf1, if_false,
        evalWithAnswerFn_bind] at he
      cases hs1 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 1
        f1 (route index 1).2 (route index 1).1
        (.pair (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2) 0 (searchLimit 1)) with
      | none =>
          dsimp only [r1, f1] at hs1
          simp only [hs1, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some found1 =>
          obtain ⟨c1, d1, l1⟩ := found1
          dsimp only [r1, f1] at hs1
          simp only [hs1, evalWithAnswerFn_bind] at he
          let r2 := CanonicalPolicy.nextResidual r1 1 l1 d1
          let f2 := CanonicalPolicy.threshold 2 r2
          by_cases hf2 : f2 ≥ 22
          · dsimp only [r1, f1, r2, f2] at hf2
            simp only [hf2, if_true,
              evalWithAnswerFn_pure, reduceCtorEq] at he
          dsimp only [r1, f1, r2, f2] at hf2
          simp only [hf2, if_false,
            evalWithAnswerFn_bind] at he
          cases hs2 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 2
            f2 (route index 2).2 (route index 2).1
            (.pair (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2) 0 (searchLimit 2)) with
          | none =>
              dsimp only [r1, f1, r2, f2] at hs2
              simp only [hs2, evalWithAnswerFn_pure, reduceCtorEq] at he
          | some found2 =>
              obtain ⟨c2, d2, l2⟩ := found2
              dsimp only [r1, f1, r2, f2] at hs2
              simp only [hs2, evalWithAnswerFn_bind] at he
              let r3 := CanonicalPolicy.nextResidual r2 2 l2 d2
              let f3 := CanonicalPolicy.threshold 3 r3
              by_cases hf3 : f3 ≥ 22
              · dsimp only [r1, f1, r2, f2, r3, f3] at hf3
                simp only [hf3, if_true,
                  evalWithAnswerFn_pure, reduceCtorEq] at he
              dsimp only [r1, f1, r2, f2, r3, f3] at hf3
              simp only [hf3, if_false,
                evalWithAnswerFn_bind] at he
              cases hs3 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 3
                f3 (route index 3).2 (route index 3).1
                (.pair (forest).1 (forest).2) 0 (searchLimit 3)) with
              | none =>
                  dsimp only [r1, f1, r2, f2, r3, f3] at hs3
                  simp only [hs3, evalWithAnswerFn_pure, reduceCtorEq] at he
              | some found3 =>
                  obtain ⟨c3, d3, l3⟩ := found3
                  dsimp only [r1, f1, r2, f2, r3, f3] at hs3
                  simp only [hs3, evalWithAnswerFn_bind] at he
                  simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
                  subst result
                  constructor
                  · rfl
                  · rfl
                  · rfl
                  · rfl
                  · exact hs0
                  · exact hs1
                  · exact hs2
                  · exact hs3
                  · exact Nat.lt_of_not_ge hf1
                  · exact Nat.lt_of_not_ge hf2
                  · exact Nat.lt_of_not_ge hf3
                  · rfl
                  · rfl
                  · rfl

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem recoverLayerPair_wotsPieces (answers : Answers) (sig : Signature) (index : Nat)
    (lay : Layer) (hl : lay ≠ 0) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (hpieces : sig.layers lay = piecesSignature lay
      (wotsPieces answers lay (route index lay).2 (route index lay).1 digits)) :
    evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index lay digits) =
      builtPair answers lay (route index lay).2 := by
  apply eval_recoverLayerPair_honest answers (mainSignature sig) index lay hl digits hvalid
  · intro i
    change (sig.layers lay).values i = _
    rw [hpieces]
    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, i.isLt]
  · intro j
    change (sig.layers lay).path j = _
    rw [hpieces]
    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, j.isLt]

theorem topNode_wotsPieces (answers : Answers) (sig : Signature) (index : Nat)
    (hindex : index < 2 ^ 31) (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (hpieces : sig.layers 0 = piecesSignature 0
      (wotsPieces answers 0 (route index 0).2 (route index 0).1 digits)) :
    evalWithAnswerFn answers (topNode index
      (evalWithAnswerFn answers (topFoldN (mainSignature sig) index digits)).1
      ((sig.layers 0).path topJ)) = treeValue (builtTree answers 0 0) 12 0 := by
  have ht : (route index 0).2 = 0 := route_top_tree index hindex
  have hp : sig.layers 0 = piecesSignature 0 (honestPieces answers 0 0 (route index 0).1 digits) := by
    rw [hpieces, ht, wotsPieces_top]
  exact eval_topNode_topFoldN_honest answers (mainSignature sig) index hindex digits hvalid
    (fun i => by
      change (sig.layers 0).values i = _
      rw [hp]
      simp [piecesSignature, honestPieces, List.getD_eq_getElem, i.isLt])
    (fun j => by
      change (sig.layers 0).path j = _
      rw [hp]
      simp [piecesSignature, honestPieces, List.getD_eq_getElem, j.isLt])

theorem recoverHintedLayers_replay (answers : Answers) (sig : Signature) (index : Nat)
    (other : Digest) (forest : PairRoot)
    (counter : Layer → BitVec 32) (digits : Layer → List Nat) (lows : Layer → Bool)
    (hs : ∀ lay, evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay
      (hintFloor sig.policyHints lay) (route index lay).2 (route index lay).1
      (if lay = 3 then .pair forest.1 forest.2 else
        let lower : Layer := Fin.ofNat 4 (lay.val + 1)
        .pair (builtPair answers lower (route index lower).2).1
          (builtPair answers lower (route index lower).2).2)
      0 (searchLimit lay)) = some (counter lay, digits lay, lows lay))
    (hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
      (recoverLayerPair (mainSignature sig) index lay (digits lay)) =
      builtPair answers lay (route index lay).2) :
    evalWithAnswerFn answers (recoverHintedLayers sig index other 4 (.pair forest.1 forest.2)) =
      some ⟨(evalWithAnswerFn answers (topFoldN (mainSignature sig) index (digits 0))).1,
        evalWithAnswerFn answers (topNode index
          (evalWithAnswerFn answers (topFoldN (mainSignature sig) index (digits 0))).1 other),
        [counter 0, counter 1, counter 2, counter 3],
        [digits 0, digits 1, digits 2, digits 3],
        [lows 0, lows 1, lows 2, lows 3],
        (evalWithAnswerFn answers (topFoldN (mainSignature sig) index (digits 0))).2⟩ := by
  have hs0 := hs 0
  have hs1 := hs 1
  have hs2 := hs 2
  have hs3 := hs 3
  have hp1 := hp 1 (by decide)
  have hp2 := hp 2 (by decide)
  have hp3 := hp 3 (by decide)
  simp only [show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
    show (2 : Layer) ≠ 3 by decide, if_false, if_true,
    show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
    show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
    show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl] at hs0 hs1 hs2 hs3
  simp only [recoverHintedLayers, evalWithAnswerFn_bind,
    show (Fin.ofNat 4 0 : Layer) = 0 from rfl,
    show (Fin.ofNat 4 1 : Layer) = 1 from rfl,
    show (Fin.ofNat 4 2 : Layer) = 2 from rfl,
    show (Fin.ofNat 4 3 : Layer) = 3 from rfl,
    hs0, hs1, hs2, hs3, hp1, hp2, hp3,
    Nat.reduceEqDiff, if_false, if_true, evalWithAnswerFn_pure]
  rfl

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem layer_four_cases (lay : Layer) : lay = 0 ∨ lay = 1 ∨ lay = 2 ∨ lay = 3 := by
  fin_cases lay <;> decide

@[simp] theorem layer_val_0 : (0 : Layer).val = 0 := rfl
@[simp] theorem layer_val_1 : (1 : Layer).val = 1 := rfl
@[simp] theorem layer_val_2 : (2 : Layer).val = 2 := rfl
@[simp] theorem layer_val_3 : (3 : Layer).val = 3 := rfl

theorem PreparedSearchFacts.validDigits {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result) (lay : Layer) :
    Cost.ValidDigits lay (result.digits.getD lay.val []) := by
  rcases layer_four_cases lay with rfl | rfl | rfl | rfl
  · exact (canonical_search_valid_credit answers 0 _ _ _ _ _ _ _ _ _
      (by have hb := searchLimit_le (0 : Layer); unfold counterLimit at hb; omega) h.search0).1
  · exact (canonical_search_valid_credit answers 1 _ _ _ _ _ _ _ _ _
      (by have hb := searchLimit_le (1 : Layer); unfold counterLimit at hb; omega) h.search1).1
  · exact (canonical_search_valid_credit answers 2 _ _ _ _ _ _ _ _ _
      (by have hb := searchLimit_le (2 : Layer); unfold counterLimit at hb; omega) h.search2).1
  · exact (canonical_search_valid_credit answers 3 _ _ _ _ _ _ _ _ _
      (by have hb := searchLimit_le (3 : Layer); unfold counterLimit at hb; omega) h.search3).1

theorem PreparedSearchFacts.hints_spec {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result) :
    result.policyHints.toNat < 7744 ∧
      hintFloor result.policyHints 1 = CanonicalPolicy.threshold 1 (preparedResidual1 result) ∧
      hintFloor result.policyHints 2 = CanonicalPolicy.threshold 2 (preparedResidual2 result) ∧
      hintFloor result.policyHints 3 = CanonicalPolicy.threshold 3 (preparedResidual3 result) := by
  rw [h.hints_eq]
  exact encodedHints_spec _ _ _ h.floor1_lt h.floor2_lt h.floor3_lt

theorem PreparedSearchFacts.hints_valid {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result) :
    policyHintsValid result.policyHints result.digits result.lows = true := by
  simp only [policyHintsValid, decide_eq_true_eq]
  exact ⟨h.hints_spec.1, h.digits_length, h.hints_spec.2⟩

theorem preparedPieces_fixed (answers : Answers) (index : Nat) {lay : Layer}
    (hlay : lay ≠ 0) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits) :
    preparedPieces lay (route index lay).1 (fixedPrepared answers index lay) digits =
      wotsPieces answers lay (route index lay).2 (route index lay).1 digits := by
  have h := preparedPieces_result answers hlay (route index lay).2 (route index lay).1
    digits hvalid (route_leaf_bound index lay)
  rw [eval_buildTreePrefixes_result answers hlay _ _ (route_leaf_bound index lay)] at h
  exact h

theorem PreparedSearchFacts.honest_pieces {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index (evalWithAnswerFn answers (prepareRoots index)) forest result)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (hindex : index < 2 ^ 31)
    (lay : Layer) :
    result.pieces.getD lay.val ([], []) =
      wotsPieces answers lay (route index lay).2 (route index lay).1 (result.digits.getD lay.val []) := by
  have hv := h.validDigits lay
  rw [h.pieces_eq, prepareRoots_result]
  rcases layer_four_cases lay with rfl | rfl | rfl | rfl <;>
    simp only [layer_val_0, layer_val_1, layer_val_2, layer_val_3] at hv ⊢
  · simp only [Fin.val_zero, List.getD_cons_zero]
    rw [eval_signTop_honest answers cache _ _ hcache (route_leaf_bound index 0) hv,
      route_top_tree index hindex, wotsPieces_top]
  · simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      preparedPieces_fixed answers index (lay := 1) (by decide) _ hv
  · simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      preparedPieces_fixed answers index (lay := 2) (by decide) _ hv
  · simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      preparedPieces_fixed answers index (lay := 3) (by decide) _ hv

theorem list_four_getD {α : Type} (xs : List α) (zero : α) (hlen : xs.length = 4) :
    [xs.getD 0 zero, xs.getD 1 zero, xs.getD 2 zero, xs.getD 3 zero] = xs := by
  apply List.ext_getElem (by simpa using hlen.symm)
  intro i hi hj
  have hi4 : i < 4 := by simpa using hi
  interval_cases i <;> simp_all [List.getD_eq_getElem]

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem PreparedSearchFacts.recover_honest {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index (evalWithAnswerFn answers (prepareRoots index)) forest result)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (hindex : index < 2 ^ 31)
    (sig : Signature) (hhints : sig.policyHints = result.policyHints)
    (hpieces : ∀ lay, sig.layers lay = piecesSignature lay (result.pieces.getD lay.val ([], []))) :
    ∃ folded nonces, evalWithAnswerFn answers (recoverHintedLayers sig index ((sig.layers 0).path topJ)
      4 (.pair forest.1 forest.2)) = some ⟨folded,
        treeValue (builtTree answers 0 0) 12 0, result.counters, result.digits, result.lows, nonces⟩ := by
  have hpiece : ∀ lay, sig.layers lay = piecesSignature lay
      (wotsPieces answers lay (route index lay).2 (route index lay).1 (result.digits.getD lay.val [])) := by
    intro lay
    rw [hpieces lay, h.honest_pieces hcache hindex lay]
  have hs0 := h.search0
  have hs1 := h.search1
  have hs2 := h.search2
  have hs3 := h.search3
  simp only [prepareRoots_result, fixedPrepared_pair] at hs0 hs1 hs2
  have hs : ∀ lay, evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay
      (hintFloor sig.policyHints lay) (route index lay).2 (route index lay).1
      (if lay = 3 then .pair forest.1 forest.2 else
        let lower : Layer := Fin.ofNat 4 (lay.val + 1)
        .pair (builtPair answers lower (route index lower).2).1
          (builtPair answers lower (route index lower).2).2)
      0 (searchLimit lay)) = some (result.counters.getD lay.val 0, result.digits.getD lay.val [],
        result.lows.getD lay.val true) := by
    intro lay
    rw [hhints]
    rcases layer_four_cases lay with rfl | rfl | rfl | rfl <;>
      simp only [layer_val_0, layer_val_1, layer_val_2, layer_val_3,
        show (Fin.ofNat 4 1 : Layer) = 1 from rfl,
        show (Fin.ofNat 4 2 : Layer) = 2 from rfl,
        show (Fin.ofNat 4 3 : Layer) = 3 from rfl, Nat.reduceAdd, show (0 : Layer) ≠ 3 by decide,
        show (1 : Layer) ≠ 3 by decide, show (2 : Layer) ≠ 3 by decide, if_false, if_true]
    · exact hs0
    · simpa only [h.hints_spec.2.1] using hs1
    · simpa only [h.hints_spec.2.2.1] using hs2
    · simpa only [h.hints_spec.2.2.2] using hs3
  have hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
      (recoverLayerPair (mainSignature sig) index lay (result.digits.getD lay.val [])) =
      builtPair answers lay (route index lay).2 := by
    intro lay hl
    exact recoverLayerPair_wotsPieces answers sig index lay hl _ (h.validDigits lay) (hpiece lay)
  have hr := recoverHintedLayers_replay answers sig index ((sig.layers 0).path topJ) forest
    (fun lay => result.counters.getD lay.val 0) (fun lay => result.digits.getD lay.val [])
    (fun lay => result.lows.getD lay.val true) hs hp
  simp only [layer_val_0, layer_val_1, layer_val_2, layer_val_3] at hr
  have ht := topNode_wotsPieces answers sig index hindex _ (h.validDigits 0) (hpiece 0)
  simp only [layer_val_0] at ht
  rw [ht,
    list_four_getD result.counters 0 h.counters_length,
    list_four_getD result.digits [] h.digits_length,
    list_four_getD result.lows true h.lows_length] at hr
  exact ⟨_, _, hr⟩

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem expand_complete_of_recovered (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (counter : BitVec 32) (output : HashOutput) (result : RecoveredLayers)
    (hd : evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 digestAttemptLimit) =
      some (counter, output))
    (hr : evalWithAnswerFn answers (recoverHintedLayers sig (digestIndex output)
      ((sig.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
        (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)) = some result)
    (hh : policyHintsValid sig.policyHints result.digits result.lows = true) (hpk : result.root = pk)
    (htop : TopPathOK sig) :
    ∃ w, evalWithAnswerFn answers (expand message pk sig) = some w := by
  have hhbound' : sig.policyHints.toNat < 2 ^ 13 := by
    simp only [policyHintsValid, decide_eq_true_eq] at hh
    have := hh.1
    omega
  rw [expand_eq_expandFill message pk sig hhbound' htop]
  have hhbound : sig.policyHints.toNat < 7744 := by
    simp only [policyHintsValid, decide_eq_true_eq] at hh
    exact hh.1
  let index := digestIndex output
  let forest := evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output) sig.forest)
  let sig0 := fillTopSignature sig 0
  let result0 : RecoveredLayers := {result with
    root := evalWithAnswerFn answers (topNode index result.foldedTop ((sig0.layers 0).path topJ))}
  have hr0 : evalWithAnswerFn answers (recoverHintedLayers sig0 index
      ((sig0.layers 0).path topJ) 4 (.pair forest.1 forest.2)) = some result0 := by
    dsimp only [sig0]
    rw [recoverHintedLayers_fill _ _ _ _ _ le_rfl,
      eval_recoverHintedLayers_other answers sig index ((sig.layers 0).path topJ)]
    rw [hr]
    rfl
  have hroot : evalWithAnswerFn answers (topNode index result.foldedTop ((sig.layers 0).path topJ)) = pk := by
    have he := eval_recoverHintedLayers_other answers sig index ((sig.layers 0).path topJ)
      ((sig.layers 0).path topJ) 4 (.pair forest.1 forest.2)
    rw [hr] at he
    simp only [Option.map_some, Option.some.injEq] at he
    have he' := congrArg RecoveredLayers.root he
    exact he'.symm.trans hpk
  unfold expandFill
  simp only [show ¬sig.policyHints.toNat ≥ 7744 by omega, if_false, evalWithAnswerFn_bind]
  simp only [nonce_retained, hd, evalWithAnswerFn_bind]
  dsimp only [sig0, index, forest] at hr0
  simp only [show (fillTopSignature sig 0).forest = sig.forest from rfl]
  rw [hr0]
  simp only [result0, sig0, hints_retained, hh, Bool.not_true, Bool.false_eq_true, if_false]
  by_cases hzero : result0.root = pk
  · dsimp only [result0, sig0] at hzero
    rw [if_pos hzero, evalWithAnswerFn_pure]
    exact ⟨_, rfl⟩
  · have hz : evalWithAnswerFn answers (topNode index result.foldedTop ((sig0.layers 0).path topJ)) ≠ pk := hzero
    have hcompletion : evalWithAnswerFn answers (topNode index result.foldedTop
        (setTop ((sig0.layers 0).path topJ) (((sig.layers 0).path topJ).toNat / 2 ^ 112))) = pk := by
      rw [topPath_fill_signature, setTop_setTop, setTop_self]
      exact hroot
    have hn : ((sig.layers 0).path topJ).toNat / 2 ^ 112 ≠ 0 := by
      intro he
      rw [he, topPath_fill_signature, setTop_setTop] at hcompletion
      exact hz hcompletion
    obtain ⟨c, hc⟩ := searchTop_complete answers index result.foldedTop ((sig0.layers 0).path topJ)
      pk searchFuel 1 (((sig.layers 0).path topJ).toNat / 2 ^ 112) (by omega)
      (by have ht := top_lt ((sig.layers 0).path topJ); unfold searchFuel; omega) hcompletion
    dsimp only [sig0] at hz
    dsimp only [sig0, index] at hc
    rw [if_neg hz, evalWithAnswerFn_bind, hc, evalWithAnswerFn_pure]
    exact ⟨_, rfl⟩

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signFromOutput_recovery (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    w.signature.rho = rho ∧ ∃ result : RecoveredLayers,
      evalWithAnswerFn answers (recoverHintedLayers w.signature (digestIndex output)
        ((w.signature.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1
          (evalWithAnswerFn answers (recoverForest (digestIndex output)
            (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2)) = some result ∧
      result.root = treeValue (builtTree answers 0 0) 12 0 ∧
      policyHintsValid w.signature.policyHints result.digits result.lows = true ∧
      w.topHigh = !(result.lows.getD 0 true) := by
  let index := digestIndex output
  let built := evalWithAnswerFn answers (buildForest index
    (forestSelectionFromOutput output) (forestWordsFromOutput output))
  let prepared := evalWithAnswerFn answers (prepareRoots index)
  unfold signFromOutput at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs : evalWithAnswerFn answers (searchPreparedLayers cache index prepared built.2) with
  | none =>
      dsimp only [index, prepared, built] at hs
      simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some layers =>
      have hf := searchPreparedLayers_some answers cache index prepared built.2 layers hs
      dsimp only [index, prepared, built] at hs
      simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
      subst w
      let sig : Signature := ⟨rho, layers.policyHints, built.1,
        fun lay => piecesSignature lay (layers.pieces.getD lay.val ([], []))⟩
      obtain ⟨folded, nonces, hr⟩ := hf.recover_honest hcache (digestIndex_lt output) sig rfl (by intro lay; rfl)
      refine ⟨rfl, ⟨folded, _, layers.counters, layers.digits, layers.lows, nonces⟩, ?_, rfl, hf.hints_valid, rfl⟩
      change evalWithAnswerFn answers (recoverHintedLayers sig index ((sig.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
          (forestWordsFromOutput output) built.1)).1
          (evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
            (forestWordsFromOutput output) built.1)).2)) = _
      have hforest : evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
          (forestWordsFromOutput output) built.1) = built.2 :=
        recoverForest_honest answers index _ _
      rw [hforest]
      exact hr

/-- img-v6 completeness event: every node of the keygen top tree (heights 1..11) passes its zero test, i.e. no
top nonce search hit its cap (probability ≥ 1 − 2^−143). -/
def TopTreeOK (answers : Answers) : Prop :=
  ∀ j : Nat, 1 ≤ j → j ≤ 11 → ∀ i, i < 2 ^ (12 - j) →
    topZeroOk j (treeValue (builtTree answers 0 0) j i) = true

theorem route0_tree (index : Nat) (h : index < 2 ^ 31) : (route index 0).2 = 0 := by
  simp only [route]
  apply Nat.div_eq_of_lt
  simpa [height] using h

theorem route0_leaf_lt (index : Nat) : (route index 0).1 < 2 ^ 12 := by
  simp only [route]
  exact Nat.mod_lt _ (by simp [height])

theorem sibling_lt (leaf j : Nat) (hleaf : leaf < 2 ^ 12) (hj : j ≤ 11) : leaf / 2 ^ j ^^^ 1 < 2 ^ (12 - j) := by
  apply Nat.xor_lt_two_pow
  · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show 12 - j + j = 12 by omega]
    exact hleaf
  · exact Nat.one_lt_two_pow (by omega)

/-- The signer's top path node at height `j` is the keygen's node next to the signed leaf's ancestor. -/
theorem signFromOutput_path (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) (j : Fin (height 0)) :
    (w.signature.layers 0).path j =
      treeValue (builtTree answers 0 0) j.val ((route (digestIndex output) 0).1 / 2 ^ j.val ^^^ 1) := by
  let index := digestIndex output
  let built := evalWithAnswerFn answers (buildForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output))
  let prepared := evalWithAnswerFn answers (prepareRoots index)
  unfold signFromOutput at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs : evalWithAnswerFn answers (searchPreparedLayers cache index prepared built.2) with
  | none =>
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some layers =>
    have hf := searchPreparedLayers_some answers cache index prepared built.2 layers hs
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
    subst w
    have hp := hf.honest_pieces hcache (digestIndex_lt output) 0
    change (piecesSignature 0 (layers.pieces.getD (0 : Layer).val ([], []))).path j = _
    have hj : j.val < 12 := j.isLt
    rw [hp, route0_tree _ (digestIndex_lt output)]
    simp [piecesSignature, wotsPieces, wotsTree_top, height, index, hj]

theorem signFromOutput_topPathOK (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (htree : TopTreeOK answers) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    TopPathOK w.signature := by
  intro j hj
  have hj11 : j.val ≤ 11 := Nat.le_of_lt_succ j.isLt
  rw [signFromOutput_path answers cache hcache rho counter output w he j]
  exact htree j.val hj hj11 _ (sibling_lt _ _ (route0_leaf_lt _) hj11)

theorem signPayload_expands (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (htree : TopTreeOK answers)
    (message : Message) (sig : Signature)
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) :
    ∃ w, evalWithAnswerFn answers (expand message (treeValue (builtTree answers 0 0) 12 0) sig) = some w ∧
      evalWithAnswerFn answers (verify message (treeValue (builtTree answers 0 0) 12 0) w) = true := by
  unfold signPayload at he
  simp only [evalWithAnswerFn_bind] at he
  let rho := evalWithAnswerFn answers (privateNonce message)
  cases hd : evalWithAnswerFn answers (sharedDigestSearch rho message 0 digestAttemptLimit) with
  | none =>
      dsimp only [rho] at hd
      simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      dsimp only [rho] at hd
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (signFromOutput cache rho counter output) with
      | none =>
          dsimp only [rho] at hs
          simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some original =>
          have hh := signFromOutput_recovery answers cache hcache rho counter output original hs
          have htop := signFromOutput_topPathOK answers cache hcache htree rho counter output original hs
          dsimp only [rho] at hs
          simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
          subst sig
          obtain ⟨hrho, result, hr, hpk, hp, _⟩ := hh
          have hd' : evalWithAnswerFn answers
              (sharedDigestSearch original.signature.rho message 0 digestAttemptLimit) = some (counter, output) := by
            rw [hrho]
            exact hd
          obtain ⟨w, hw⟩ := expand_complete_of_recovered answers message _ original.signature
            counter output result hd' hr hp hpk htop
          exact ⟨w, hw, expand_verified answers message _ original.signature w hw⟩

theorem sign_expands (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (htree : TopTreeOK answers)
    (message : Message) (sig : Signature)
    (he : evalWithAnswerFn answers (sign cache message) = some sig) :
    ∃ w, evalWithAnswerFn answers (expand message (treeValue (builtTree answers 0 0) 12 0) sig) = some w ∧
      evalWithAnswerFn answers (verify message (treeValue (builtTree answers 0 0) 12 0) w) = true := by
  unfold sign at he
  simp only [evalWithAnswerFn_bind] at he
  split_ifs at he with htag
  · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
  · exact signPayload_expands answers cache hcache htree message sig he

end SigGolfCandidate.Research.SharedForest

/-! Exact relevant-bit product law for the shared forest producer. -/
namespace SigGolfCandidate.Research.SharedDigestFields

def fromBits (n : Nat) (f : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem fromBits_get (n : Nat) (f : Fin n → Bool) (i : Fin n) :
    (fromBits n f).getLsbD i.val = f i := by
  simp only [fromBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]

def bitsEquiv (n : Nat) : BitVec n ≃ (Fin n → Bool) where
  toFun v i := v.getLsbD i.val
  invFun := fromBits n
  left_inv v := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact fromBits_get n (fun j => v.getLsbD j.val) ⟨i, hi⟩
  right_inv f := by
    funext i
    exact fromBits_get n f i


set_option maxRecDepth 10000
set_option maxHeartbeats 0
def costBase (k : Nat) : Nat := [0, 7, 64, 71, 128, 135, 192, 199, 230].getD k 0
def rankBase (k : Nat) : Nat := [13, 77, 89, 101, 141, 153, 165, 205, 217].getD k 0
def spareBase (k : Nat) : Nat := [5, 6, 12, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 69, 70, 76, 87, 88, 99, 100, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 133, 134, 140, 151, 152, 163, 164, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 197, 198, 204, 215, 216, 227, 228, 229, 235, 236, 237, 238, 239, 240, 241].getD k 0
def position (i : Nat) : Nat :=
  if i < 45 then costBase (i / 5) + i % 5
  else if i < 135 then rankBase ((i-45)/10) + (i-45)%10
  else if i < 166 then 33 + (i-135)
  else if i < 180 then 242 + (i-166)
  else spareBase (i-180)
def inversePosition (i : Nat) : Nat := [0, 1, 2, 3, 4, 180, 181, 5, 6, 7, 8, 9, 182, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 10, 11, 12, 13, 14, 193, 194, 15, 16, 17, 18, 19, 195, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 196, 197, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 198, 199, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 20, 21, 22, 23, 24, 217, 218, 25, 26, 27, 28, 29, 219, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 220, 221, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 222, 223, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 30, 31, 32, 33, 34, 241, 242, 35, 36, 37, 38, 39, 243, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 244, 245, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 246, 247, 248, 40, 41, 42, 43, 44, 249, 250, 251, 252, 253, 254, 255, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179].getD i 0
theorem inversePosition_bound : ∀ i : Fin 256, inversePosition i.val < 256 := by decide +kernel
theorem inversePosition_correct : ∀ i : Fin 256, position (inversePosition i.val) = i.val := by decide +kernel
abbrev Fields := (Fin 9 → BitVec 5) × (Fin 9 → BitVec 10) × BitVec 31 × BitVec 14
def fields (a : BitVec 256) : Fields :=
  (fun k => a.extractLsb' (costBase k.val) 5,
   fun k => a.extractLsb' (rankBase k.val) 10,
   a.extractLsb' 33 31, a.extractLsb' 242 14)
def decompose (a : BitVec 256) : Fields × BitVec 76 :=
  (fields a, fromBits 76 (fun i => a.getLsbD (spareBase i.val)))
theorem decompose_injective : Function.Injective decompose := by
  intro a b h
  have hb : ∀ i : Fin 256, a.getLsbD (position i.val) = b.getLsbD (position i.val) := by
    intro i
    unfold position
    split_ifs with h0 h1 h2 h3
    · have hk : i.val / 5 < 9 := by omega
      have e := congrArg (fun v : Fields × BitVec 76 => (v.1.1 ⟨i.val / 5,hk⟩).getLsbD (i.val % 5)) h
      simpa only [decompose, fields, BitVec.getLsbD_extractLsb',
        Nat.mod_lt _ (by decide : 0 < 5), decide_true, Bool.true_and] using e
    · have hk : (i.val-45)/10 < 9 := by omega
      have e := congrArg (fun v : Fields × BitVec 76 => (v.1.2.1 ⟨(i.val-45)/10,hk⟩).getLsbD ((i.val-45)%10)) h
      simpa only [decompose, fields, BitVec.getLsbD_extractLsb',
        Nat.mod_lt _ (by decide : 0 < 10), decide_true, Bool.true_and] using e
    · have hk : i.val-135 < 31 := by omega
      have e := congrArg (fun v : Fields × BitVec 76 => v.1.2.2.1.getLsbD (i.val-135)) h
      simpa only [decompose, fields, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and] using e
    · have hk : i.val-166 < 14 := by omega
      have e := congrArg (fun v : Fields × BitVec 76 => v.1.2.2.2.getLsbD (i.val-166)) h
      simpa only [decompose, fields, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and] using e
    · have hk : i.val-180 < 76 := by omega
      have e := congrArg (fun v : Fields × BitVec 76 => v.2.getLsbD (i.val-180)) h
      simpa only [decompose, fromBits_get 76 _ ⟨i.val-180,hk⟩] using e
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have e := hb ⟨inversePosition k, inversePosition_bound ⟨k,hk⟩⟩
  simpa only [inversePosition_correct ⟨k,hk⟩] using e

theorem decompose_bijective : Function.Bijective decompose := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨decompose_injective, ?_⟩
  simp only [Fields, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bitVec]
  norm_num
noncomputable def decomposeEquiv : BitVec 256 ≃ Fields × BitVec 76 :=
  Equiv.ofBijective decompose decompose_bijective
end SigGolfCandidate.Research.SharedDigestFields
namespace SigGolfCandidate.Research.SharedDigestFields
noncomputable def fiberEquiv (f : Fields) : {a : BitVec 256 // fields a = f} ≃ BitVec 76 where
  toFun a := (decompose a.val).2
  invFun spare := ⟨decomposeEquiv.symm (f, spare),
    congrArg Prod.fst (decomposeEquiv.apply_symm_apply (f,spare))⟩
  left_inv a := by
    apply Subtype.ext
    apply decomposeEquiv.injective
    change decomposeEquiv (decomposeEquiv.symm (f, (decompose a.val).2)) = decompose a.val
    rw [decomposeEquiv.apply_symm_apply]
    exact Prod.ext a.property.symm rfl
  right_inv spare := congrArg Prod.snd (decomposeEquiv.apply_symm_apply (f,spare))
theorem fiber_card (f : Fields) : Fintype.card {a : BitVec 256 // fields a = f} = 2^76 :=
  (Fintype.card_congr (fiberEquiv f)).trans (Fintype.card_bitVec 76)
end SigGolfCandidate.Research.SharedDigestFields
namespace SigGolfCandidate.Research.SharedDigestFields
open OracleComp OracleSpec ENNReal
 theorem fields_uniform :
    𝒮[fields <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      𝒮[($ᵗ Fields : ProbComp Fields)] := by
  have hm : fields <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256)) =
      Prod.fst <$> (decompose <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256))) := by
    simp only [Functor.map_map]
    rfl
  have hd : 𝒮[decompose <$> ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      𝒮[($ᵗ (Fields × BitVec 76) : ProbComp (Fields × BitVec 76))] :=
    evalSPMF_map_bijective_uniform_cross (α := BitVec 256) (β := Fields × BitVec 76) decompose decompose_bijective
  rw [hm, evalSPMF_map, hd, ← evalSPMF_map]
  exact evalSPMF_map_fst_uniformSample_prod
end SigGolfCandidate.Research.SharedDigestFields
namespace SigGolfCandidate.Research.SharedDigestFields
open SigGolfCandidate.T3

theorem costBase_source (k : Fin 9) : costBase k.val = SharedForest.costFieldBase k.val := by
  fin_cases k <;> rfl

theorem rankBase_source (k : Nat) : rankBase k = SharedForest.rankBase k := rfl

theorem fields_cost (a : HashOutput) (k : Fin 9) :
    ((fields a).1 k).toNat = (SharedForest.costField a k).val := by
  simp only [fields, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, costBase_source]
  rfl

theorem fields_rank (a : HashOutput) (k : Fin 9) :
    ((fields a).2.1 k).toNat = SharedForest.rawForestRank a k.val := by
  simp only [fields, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, rankBase_source]
  rfl

theorem fields_index (a : HashOutput) : (fields a).2.2.1.toNat = ClaudeWCT.WCT9.digestIndex a := by
  simp only [fields, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rfl

theorem fields_gate (a : HashOutput) : (fields a).2.2.2.toNat = a.toNat / 2^242 % 16384 := by
  simp only [fields, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
end SigGolfCandidate.Research.SharedDigestFields

namespace SigGolfCandidate.Research.SharedDigestFields
open SigGolfCandidate.T3 ClaudeWCT.WCT9 OracleComp OracleSpec

def decodedRank (f : Fields) (k : Fin 9) : Fin 563 :=
  ⟨(f.2.1 k).toNat % 563, Nat.mod_lt _ (by decide)⟩
def coordinateCost (f : Fields) (k : Fin 9) : Nat :=
  routineCost (decodedRank f k) +
    (if SharedForest.firstCoord k.val then SharedForest.aCorrection (f.1 k).toNat
     else SharedForest.bCorrection (f.1 k).toNat)
def cost (f : Fields) : Nat := ((List.finRange 9).map (coordinateCost f)).sum
def accepted (f : Fields) : Bool :=
  decide (f.2.2.2.toNat < 791) &&
    (List.finRange 9).all (fun k => decide ((f.2.1 k).toNat < 563)) && decide (cost f ≤ 776)

theorem decodedRank_fields (a : HashOutput) (k : Fin 9) :
    decodedRank (fields a) k = SharedForest.forestRank a k.val := by
  apply Fin.ext
  simp only [decodedRank, fields_rank]
  rfl

theorem coordinateCost_fields (a : HashOutput) (k : Fin 9) :
    coordinateCost (fields a) k = SharedForest.coordinateAccountingCost a k := by
  simp only [coordinateCost, decodedRank_fields, fields_cost,
    SharedForest.coordinateAccountingCost, SharedForest.accountingCorrection_field]

theorem cost_fields (a : HashOutput) : cost (fields a) = SharedForest.jointAccountingCost a := by
  have hc : coordinateCost (fields a) = SharedForest.coordinateAccountingCost a :=
    funext (coordinateCost_fields a)
  simp only [cost, SharedForest.jointAccountingCost, hc]

theorem accepted_fields (a : HashOutput) : accepted (fields a) = SharedForest.digestAccepted a := by
  simp only [accepted, SharedForest.digestAccepted, SharedForest.ranksAccepted,
    fields_gate, fields_rank, cost_fields]

theorem accepted_uniform :
    𝒮[SharedForest.digestAccepted <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒮[accepted <$> ($ᵗ Fields : ProbComp Fields)] := by
  have h : SharedForest.digestAccepted = accepted ∘ fields := by
    funext a
    exact (accepted_fields a).symm
  have hm : SharedForest.digestAccepted <$> ($ᵗ HashOutput : ProbComp HashOutput) =
      accepted <$> (fields <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
    rw [Functor.map_map]
    exact congrArg (fun f => f <$> ($ᵗ HashOutput : ProbComp HashOutput)) h
  rw [hm, evalSPMF_map, fields_uniform, ← evalSPMF_map]

noncomputable def predicateEquiv (p : Fields → Prop) :
    {a : HashOutput // p (fields a)} ≃ {f : Fields // p f} × BitVec 76 where
  toFun a := (⟨fields a.val, a.property⟩, (decompose a.val).2)
  invFun v := ⟨decomposeEquiv.symm (v.1.val, v.2), by
    have h := congrArg Prod.fst (decomposeEquiv.apply_symm_apply (v.1.val,v.2))
    change fields (decomposeEquiv.symm (v.1.val,v.2)) = v.1.val at h
    rw [h]
    exact v.1.property⟩
  left_inv a := by
    apply Subtype.ext
    exact decomposeEquiv.symm_apply_apply a.val
  right_inv v := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (decomposeEquiv.apply_symm_apply (v.1.val,v.2))
    · change (decompose (decomposeEquiv.symm (v.1.val,v.2))).2 = v.2
      exact congrArg Prod.snd (decomposeEquiv.apply_symm_apply (v.1.val,v.2))

theorem predicate_card (p : Fields → Prop) [DecidablePred p] :
    Fintype.card {a : HashOutput // p (fields a)} = Fintype.card {f : Fields // p f} * 2^76 := by
  rw [Fintype.card_congr (predicateEquiv p), Fintype.card_prod, Fintype.card_bitVec]
end SigGolfCandidate.Research.SharedDigestFields

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem recoverHintedLayers_credit (answers : Answers) (sig : Signature) (index : Nat) (other : Digest) :
    ∀ n, n ≤ 4 → ∀ msg result,
      evalWithAnswerFn answers (recoverHintedLayers sig index other n msg) = some result →
      result.digits.length = n ∧ result.lows.length = n ∧ ∀ lay : Layer, lay.val < n →
        hintFloor sig.policyHints lay ≤
          CanonicalPolicy.credit lay (result.lows.getD lay.val true) (result.digits.getD lay.val []) := by
  intro n
  induction n with
  | zero =>
      intro _ msg result he
      simp [recoverHintedLayers] at he
  | succ n ih =>
      intro hn msg result he
      simp only [recoverHintedLayers, evalWithAnswerFn_bind] at he
      split at he
      ·
          rename_i counter digits low hs
          have hlim := searchLimit_le (Fin.ofNat 4 n)
          have hd := (canonical_search_valid_credit answers _ _ _ _ _ _ 0 counter digits low
            (by unfold counterLimit at hlim; omega) hs).2
          have hlay := ofNat_layer_val n (by omega)
          by_cases hn0 : n = 0
          · subst n
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at he
            subst result
            refine ⟨rfl, rfl, fun lay hsmall => ?_⟩
            have heq : lay = 0 := Fin.ext (by omega)
            subst lay
            exact hd
          · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
            split at he
            rotate_left
            · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
            ·
                rename_i previous hr
                simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
                subst result
                obtain ⟨hlen, hllen, hprevious⟩ := ih (by omega) _ _ hr
                refine ⟨by simp [hlen], by simp [hllen], fun lay hsmall => ?_⟩
                by_cases htop : lay.val = n
                · have heq : lay = Fin.ofNat 4 n := Fin.ext (htop.trans hlay.symm)
                  subst lay
                  simp only [hlay, List.getD_append_right previous.digits [digits] [] n (by omega), hlen,
                    List.getD_append_right previous.lows [low] true n (by omega), hllen,
                    Nat.sub_self, List.getD_cons_zero]
                  exact hd
                · rw [List.getD_append previous.digits [digits] [] lay.val (by omega),
                    List.getD_append previous.lows [low] true lay.val (by omega)]
                  exact hprevious lay (by omega)
      · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he

theorem policyHints_credit_sum (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool)
    (hh : policyHintsValid hints digits lows = true)
    (hc : ∀ lay : Layer, hintFloor hints lay ≤
      CanonicalPolicy.credit lay (lows.getD lay.val true) (digits.getD lay.val [])) :
    69 ≤ ((List.finRange 4).map fun lay =>
      CanonicalPolicy.credit lay (lows.getD lay.val true) (digits.getD lay.val [])).sum := by
  simp only [policyHintsValid, decide_eq_true_eq] at hh
  have h0 : 14 ≤ CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 []) := by
    simpa [hintFloor, CanonicalPolicy.topFloor] using hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  rw [hh.2.2.1] at h1
  rw [hh.2.2.2.1] at h2
  rw [hh.2.2.2.2] at h3
  have hz := canonical_four_residual (digits.getD 0 []) (digits.getD 1 []) (digits.getD 2 [])
    (digits.getD 3 []) (lows.getD 0 true) (lows.getD 1 true) (lows.getD 2 true) (lows.getD 3 true) h0 h1 h2 h3
  simp only [CanonicalPolicy.nextResidual] at hz
  change 69 ≤ CanonicalPolicy.credit 0 (lows.getD 0 true) (digits.getD 0 []) +
    (CanonicalPolicy.credit 1 (lows.getD 1 true) (digits.getD 1 []) +
      (CanonicalPolicy.credit 2 (lows.getD 2 true) (digits.getD 2 []) +
      (CanonicalPolicy.credit 3 (lows.getD 3 true) (digits.getD 3 []) + 0)))
  omega
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Cost
open ClaudeWCT.WCT9.Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem maxDigit_le_seven (lay : Layer) (i : Nat) : maxDigit lay i ≤ 7 := by
  unfold maxDigit
  split_ifs <;> omega

/-- Coarse unconditional main-tree recovery bound; no old local credit floor
or old layer-two/three target is used. -/
theorem bound_recoverLayerPair_coarse (sig : ClaudeWCT.WCT9.Signature) (index : Nat)
    (lay : Layer) (digits : List Nat) :
    CBound (fun _ => True) 404 (recoverLayerPair sig index lay digits) := by
  unfold recoverLayerPair
  dsimp only
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount lay)) _
    (fun _ => 7) (fun i _ => (bound_chainW _ _ _ _ _ _ _).mono_k
      (Nat.sub_le _ _ |>.trans (maxDigit_le_seven lay i.val)))).bind'
    (l := leafHashCost lay + (height lay - 1)) (fun ends hends => ?_) ?_
  · refine (bound_lowerLeafHash lay _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine ((Bound.foldlM_list (P := GoodQuery) (List.finRange (height lay - 1)) _
      (fun _ _ => True) (fun _ => 1) root trivial (fun i hi value _ => ?_)).bind' (l := 0)
      (fun _ _ => .pure _ 0 trivial) (by simp))
    exact bound_lowerNodeHash _ _ _ _ _
  · fin_cases lay <;> decide

theorem bound_topFold_coarse (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (digits : List Nat) :
    CBound (fun _ => True) 403 (topFold sig index digits) := by
  unfold topFold topEnds
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount 0)) _
    (fun _ => 7) (fun i _ => (bound_layChain _ _ _ _ _ _ _).mono_k
      (Nat.sub_le _ _ |>.trans (maxDigit_le_seven 0 i.val)))).bind'
    (l := leafHashCost 0 + 11) (fun ends hends => ?_) ?_
  · refine (bound_leafHash 0 _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine (Bound.foldlM_list (P := GoodQuery) ((List.finRange (height 0)).take 11) _
      (fun _ _ => True) (fun _ => 1) root trivial (fun i hi value _ => ?_)).mono_k
        (by rw [take_top_length]; simp)
    unfold topStep
    exact bound_nodeHash _ _ _ _ _ _
  · decide

/-- Top-bytes layer: the expander's nonce re-derivation costs at most `topNonceCap h = 104·2^h` per path node of
height `h = 1..11` (Σ = 425,776), on top of the 392 chain/leaf compressions. -/
def topFoldNCost : Nat := 392 + 425776
theorem bound_topFoldN_coarse (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (digits : List Nat) :
    CBound (fun _ => True) topFoldNCost (topFoldN sig index digits) := by
  unfold topFoldN topEnds topFoldNCost
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount 0)) _
    (fun _ => 7) (fun i _ => (bound_layChain _ _ _ _ _ _ _).mono_k
      (Nat.sub_le _ _ |>.trans (maxDigit_le_seven 0 i.val)))).bind'
    (l := leafHashCost 0 + 425776) (fun ends hends => ?_) ?_
  · refine (bound_leafHash 0 _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine (Bound.foldlM_list (P := GoodQuery) ((List.finRange (height 0)).take 11) _
      (fun _ _ => True) (fun i => topNonceCap (i + 1)) (root, []) trivial (fun i hi st _ => ?_)).mono_k
        (by decide +kernel)
    have hjv : (((List.finRange (height 0)).take 11)[i]'hi).val = i := by simp [List.getElem_take]
    unfold topStepN
    exact (Cost.bound_topNodeAt _ _ _ _).bind' (l := 0) (fun _ _ => .pure _ 0 trivial) (by rw [hjv]; simp)
  · decide

theorem bound_recoverSharedInner (first : Bool) (index coord : Nat) (hc : coord<9)
    (selected : Child) (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) :
    CBound (fun _ => True) 31 (recoverSharedInner first index coord selected word values path prev) := by
  unfold recoverSharedInner
  have hj := rawChild_lt first selected.val selected.isLt
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange 6) _ (fun _ => 4)
    (fun i _ => (cbound_of_ftsBound (ftsBound_chain index coord (rawChild first selected.val)
      i.val (4-wordDigit word i) (wordDigit word i) (values i) hc hj i.isLt
      (by have h := wordDigit_le_four word i; omega))).mono_k (wordDigit_le_four word i))).bind'
      (l := 7) (fun ends hends => ?_) (by decide)
  refine (cbound_of_ftsBound (ftsBound_leafHashH index (128 + selected.val) coord (rawChild first selected.val)
    prev.1 ends hc hj (by simpa using hends))).bind'
      (l := 5) (fun leaf _ => ?_) (by decide)
  exact (Bound.foldlM_list (P := GoodQuery) (List.range 5) _ (fun _ _ => True) (fun _ => 1)
    leaf trivial (fun i hi value _ => bound_sharedNode ..)).mono_k (by simp)

theorem bound_recoverPair (index pair : Nat) (hp : pair<4) (selected : Selection)
    (aWord bWord : Rank) (opened : PairOpening) (prev : PairRoot) :
    CBound (fun _ => True) 63 (recoverPair index pair selected aWord bWord opened prev) := by
  unfold recoverPair
  refine (bound_recoverSharedInner true index (2*pair) (by omega) _ _ _ _ _).bind'
    (l := 32) (fun a _ => ?_) (by decide)
  refine (bound_recoverSharedInner false index (2*pair+1) (by omega) _ _ _ _ _).bind'
    (l := 1) (fun b _ => ?_) (by decide)
  exact (bound_sharedOuterHash ..).bind' (l := 0) (fun outer _ => .pure _ 0 trivial) (by decide)

theorem bound_recoverSingleton (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (prev : PairRoot) :
    CBound (fun _ => True) 32 (recoverSingleton index selected word opened prev) := by
  unfold recoverSingleton
  refine (bound_recoverSharedInner false index 8 (by decide) _ _ _ _ _).bind'
    (l := 1) (fun inner _ => ?_) (by decide)
  exact (bound_sharedOuterHash ..).bind' (l := 0) (fun outer _ => .pure _ 0 trivial) (by decide)

theorem bound_recoverForest (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) :
    CBound (fun _ => True) 284 (recoverForest index selected words opened) := by
  unfold recoverForest
  refine (Bound.foldlM_list (P := GoodQuery) (List.finRange 4) _ (fun _ _ => True) (fun _ => 63)
    ftsStart trivial (fun i hi prev _ => bound_recoverPair index ((List.finRange 4)[i]).val ((List.finRange 4)[i]).isLt _ _ _ _ _)).bind'
      (l := 32) (fun prev _ => bound_recoverSingleton ..) (by decide)

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def recoverySearch (answers : Answers) (sig : Signature) (index : Nat) (forest : PairRoot) (lay : Layer) :
    M (Option (BitVec 32 × List Nat × Bool)) :=
  CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
    (route index lay).2 (route index lay).1
    (if lay = 3 then .pair forest.1 forest.2 else
      let lower : Layer := Fin.ofNat 4 (lay.val + 1)
      .pair (builtPair answers lower (route index lower).2).1
        (builtPair answers lower (route index lower).2).2) 0 (searchLimit lay)

def recoverySearchCost (answers : Answers) (sig : Signature) (index : Nat) (forest : PairRoot) : Nat :=
  cost answers (recoverySearch answers sig index forest 0) +
  cost answers (recoverySearch answers sig index forest 1) +
  cost answers (recoverySearch answers sig index forest 2) +
  cost answers (recoverySearch answers sig index forest 3)

theorem recoverHintedLayers_cost_replay (answers : Answers) (sig : Signature) (index : Nat)
    (other : Digest) (forest : PairRoot) (counter : Layer → BitVec 32) (digits : Layer → List Nat)
    (lows : Layer → Bool)
    (hs : ∀ lay, evalWithAnswerFn answers (recoverySearch answers sig index forest lay) =
      some (counter lay, digits lay, lows lay))
    (hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
      (recoverLayerPair (mainSignature sig) index lay (digits lay)) =
      builtPair answers lay (route index lay).2) :
    cost answers (recoverHintedLayers sig index other 4 (.pair forest.1 forest.2)) ≤
      recoverySearchCost answers sig index forest + (1616 + 425765) := by
  have hs0 := hs 0
  have hs1 := hs 1
  have hs2 := hs 2
  have hs3 := hs 3
  have hp1 := hp 1 (by decide)
  have hp2 := hp 2 (by decide)
  have hp3 := hp 3 (by decide)
  have hc1 := cost_bound answers (bound_recoverLayerPair_coarse (mainSignature sig) index 1 (digits 1))
  have hc2 := cost_bound answers (bound_recoverLayerPair_coarse (mainSignature sig) index 2 (digits 2))
  have hc3 := cost_bound answers (bound_recoverLayerPair_coarse (mainSignature sig) index 3 (digits 3))
  have hct := cost_bound answers (bound_topFoldN_coarse (mainSignature sig) index (digits 0))
  have hcn := cost_bound answers (ClaudeWCT.WCT9.Cost.bound_topNode index
    (evalWithAnswerFn answers (topFoldN (mainSignature sig) index (digits 0))).1 other)
  simp only [recoverySearch, show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
    show (2 : Layer) ≠ 3 by decide, if_false, if_true,
    show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
    show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
    show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl] at hs0 hs1 hs2 hs3 ⊢
  simp only [recoverySearchCost, recoverySearch,
    show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
    show (2 : Layer) ≠ 3 by decide, if_false, if_true,
    show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
    show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
    show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl]
  simp only [recoverHintedLayers, cost_bind, evalWithAnswerFn_bind,
    show (Fin.ofNat 4 0 : Layer) = 0 from rfl,
    show (Fin.ofNat 4 1 : Layer) = 1 from rfl,
    show (Fin.ofNat 4 2 : Layer) = 2 from rfl,
    show (Fin.ofNat 4 3 : Layer) = 3 from rfl,
    hs0, hs1, hs2, hs3, hp1, hp2, hp3,
    Nat.reduceEqDiff, if_false, if_true, evalWithAnswerFn_pure, cost_pure]
  simp only [topFoldNCost] at hct
  omega

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem PreparedSearchFacts.cost_eq {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result)
    (sig : Signature) (hh : sig.policyHints = result.policyHints)
    (hm0 : topPair 1 prepared.one.levels = builtPair answers 1 (route index 1).2)
    (hm1 : topPair 2 prepared.two.levels = builtPair answers 2 (route index 2).2)
    (hm2 : topPair 3 prepared.three.levels = builtPair answers 3 (route index 3).2) :
    cost answers (searchPreparedLayers cache index prepared forest) =
      recoverySearchCost answers sig index forest +
        cost answers (signTop cache (route index 0).1 (result.digits.getD 0 [])) := by
  have hs0 := h.search0
  have hs1 := h.search1
  have hs2 := h.search2
  have hs3 := h.search3
  have hf1 := Nat.not_le.mpr h.floor1_lt
  have hf2 := Nat.not_le.mpr h.floor2_lt
  have hf3 := Nat.not_le.mpr h.floor3_lt
  dsimp only [preparedResidual1, preparedResidual2, preparedResidual3] at hs1 hs2 hs3 hf1 hf2 hf3
  simp only [searchPreparedLayers, cost_bind, hs0, hs1, hs2, hs3,
    hf1, hf2, hf3, if_false, cost_pure, Nat.add_zero]
  simp only [recoverySearchCost, recoverySearch, hh, h.hints_spec.2.1,
    h.hints_spec.2.2.1, h.hints_spec.2.2.2, hm0, hm1, hm2,
    show hintFloor result.policyHints 0 = CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit from rfl,
    show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
    show (2 : Layer) ≠ 3 by decide, if_false, if_true,
    show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
    show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
    show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl,
    preparedResidual1, preparedResidual2, preparedResidual3]
  omega

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp SigGolfCandidate.T3 ClaudeWCT.WCT9

theorem expand_fillTopSignature (message : Message) (pk : Digest) (sig : Signature) (c : Nat) :
    expand message pk (fillTopSignature sig c) = expand message pk sig := by
  rw [← expand_normTop message pk (fillTopSignature sig c), normTop_fill, expand_normTop]

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem PreparedSearchFacts.recovery_cost_le {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result)
    (sig : Signature) (other : Digest) (hh : sig.policyHints = result.policyHints)
    (hm0 : topPair 1 prepared.one.levels = builtPair answers 1 (route index 1).2)
    (hm1 : topPair 2 prepared.two.levels = builtPair answers 2 (route index 2).2)
    (hm2 : topPair 3 prepared.three.levels = builtPair answers 3 (route index 3).2)
    (hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
      (recoverLayerPair (mainSignature sig) index lay (result.digits.getD lay.val [])) =
      builtPair answers lay (route index lay).2) :
    cost answers (recoverHintedLayers sig index other 4 (.pair forest.1 forest.2)) ≤
      cost answers (searchPreparedLayers cache index prepared forest) + (1616 + 425765) := by
  have hs0 := h.search0
  have hs1 := h.search1
  have hs2 := h.search2
  have hs3 := h.search3
  rw [hm0] at hs0
  rw [hm1] at hs1
  rw [hm2] at hs2
  have hs : ∀ lay, evalWithAnswerFn answers (recoverySearch answers sig index forest lay) =
      some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true) := by
    intro lay
    rcases layer_four_cases lay with rfl | rfl | rfl | rfl <;>
      simp only [recoverySearch, hh, h.hints_spec.2.1, h.hints_spec.2.2.1, h.hints_spec.2.2.2,
        show hintFloor result.policyHints 0 = CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit from rfl,
        show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
        show (2 : Layer) ≠ 3 by decide, if_false, if_true,
        show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
        show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
        show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl]
    · exact hs0
    · exact hs1
    · exact hs2
    · exact hs3
  have hc := recoverHintedLayers_cost_replay answers sig index other forest
    (fun lay => result.counters.getD lay.val 0) (fun lay => result.digits.getD lay.val [])
    (fun lay => result.lows.getD lay.val true) hs hp
  have he := h.cost_eq sig hh hm0 hm1 hm2
  omega

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem policyHintsValid_congr_lows (hints : BitVec 16) (digits : List (List Nat)) {lowsA lowsB : List Bool}
    (h0 : lowsA.getD 0 true = lowsB.getD 0 true) (h1 : lowsA.getD 1 true = lowsB.getD 1 true)
    (h2 : lowsA.getD 2 true = lowsB.getD 2 true) :
    policyHintsValid hints digits lowsA = policyHintsValid hints digits lowsB := by
  simp only [policyHintsValid, h0, h1, h2]

theorem hintedSelections_unique (answers : Answers) (index : Nat) (messages : Layer → LayerMsg)
    (hintsA hintsB : BitVec 16) (countersA countersB : Layer → BitVec 32)
    (digitsA digitsB : List (List Nat)) (lowsA lowsB : List Bool)
    (hvalidA : policyHintsValid hintsA digitsA lowsA = true)
    (hvalidB : policyHintsValid hintsB digitsB lowsB = true)
    (hsearchA : ∀ lay, evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay (hintFloor hintsA lay) (route index lay).2
        (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (countersA lay, digitsA.getD lay.val [], lowsA.getD lay.val true))
    (hsearchB : ∀ lay, evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay (hintFloor hintsB lay) (route index lay).2
        (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (countersB lay, digitsB.getD lay.val [], lowsB.getD lay.val true)) :
    hintsA = hintsB ∧ countersA = countersB ∧ digitsA = digitsB ∧
      ∀ lay : Layer, lowsA.getD lay.val true = lowsB.getD lay.val true := by
  have hA := hvalidA
  have hB := hvalidB
  simp only [policyHintsValid, decide_eq_true_eq] at hA hB
  have same (lay : Layer) (hf : hintFloor hintsA lay = hintFloor hintsB lay) :
      (countersA lay, digitsA.getD lay.val [], lowsA.getD lay.val true) =
        (countersB lay, digitsB.getD lay.val [], lowsB.getD lay.val true) := by
    have ha := hsearchA lay
    rw [hf] at ha
    exact Option.some.inj (ha.symm.trans (hsearchB lay))
  have h0 := same 0 (by rfl)
  have hd0 : digitsA.getD 0 [] = digitsB.getD 0 [] := congrArg (fun x => x.2.1) h0
  have hl0 : lowsA.getD 0 true = lowsB.getD 0 true := congrArg (fun x => x.2.2) h0
  have h1 := same 1 (by rw [hA.2.2.1, hB.2.2.1, hd0, hl0])
  have hd1 : digitsA.getD 1 [] = digitsB.getD 1 [] := congrArg (fun x => x.2.1) h1
  have hl1 : lowsA.getD 1 true = lowsB.getD 1 true := congrArg (fun x => x.2.2) h1
  have h2 := same 2 (by rw [hA.2.2.2.1, hB.2.2.2.1, hd0, hd1, hl0, hl1])
  have hd2 : digitsA.getD 2 [] = digitsB.getD 2 [] := congrArg (fun x => x.2.1) h2
  have hl2 : lowsA.getD 2 true = lowsB.getD 2 true := congrArg (fun x => x.2.2) h2
  have h3 := same 3 (by rw [hA.2.2.2.2, hB.2.2.2.2, hd0, hd1, hd2, hl0, hl1, hl2])
  have hd3 : digitsA.getD 3 [] = digitsB.getD 3 [] := congrArg (fun x => x.2.1) h3
  have hl3 : lowsA.getD 3 true = lowsB.getD 3 true := congrArg (fun x => x.2.2) h3
  have hd : digitsA = digitsB := by
    apply List.ext_getElem (hA.2.1.trans hB.2.1.symm)
    intro i hi hj
    have hi4 : i < 4 := by omega
    have he : digitsA.getD i [] = digitsB.getD i [] := by
      interval_cases i <;> assumption
    simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using he
  have hvB : policyHintsValid hintsB digitsA lowsA = true := by
    rw [policyHintsValid_congr_lows hintsB digitsA hl0 hl1 hl2, hd]; exact hvalidB
  refine ⟨policyHintsValid_unique hvalidA hvB, ?_, hd, ?_⟩
  · funext lay
    fin_cases lay
    · exact congrArg Prod.fst h0
    · exact congrArg Prod.fst h1
    · exact congrArg Prod.fst h2
    · exact congrArg Prod.fst h3
  · intro lay
    fin_cases lay
    · exact hl0
    · exact hl1
    · exact hl2
    · exact hl3
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def recoveredMessage (answers : Answers) (sig : Signature) (index n : Nat)
    (message : LayerMsg) (digits : List (List Nat)) (lay : Layer) : LayerMsg :=
  if lay.val + 1 = n then message else
    let next : Layer := Fin.ofNat 4 (lay.val + 1)
    let pair := evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index next
      (digits.getD (lay.val + 1) []))
    .pair pair.1 pair.2

theorem recoverHintedLayers_selections (answers : Answers) (sig : Signature) (index : Nat)
    (other : Digest) : ∀ n, n ≤ 4 → ∀ message result,
    evalWithAnswerFn answers (recoverHintedLayers sig index other n message) = some result →
    result.counters.length = n ∧ result.digits.length = n ∧ result.lows.length = n ∧
      ∀ lay : Layer, lay.val < n → evalWithAnswerFn answers
        (CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
          (route index lay).2 (route index lay).1
          (recoveredMessage answers sig index n message result.digits lay) 0 (searchLimit lay)) =
            some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true) := by
  intro n
  induction n with
  | zero => intro _ message result he; simp [recoverHintedLayers] at he
  | succ n ih =>
      intro hn message result he
      have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
      simp only [recoverHintedLayers, evalWithAnswerFn_bind] at he
      split at he
      ·
          rename_i counter digits low hs
          by_cases hn0 : n = 0
          · subst n
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at he
            subst result
            refine ⟨rfl, rfl, rfl, ?_⟩
            intro lay hlay
            have hl : lay = 0 := Fin.ext (by omega)
            subst lay
            simp only [show (Fin.ofNat 4 0 : Layer) = 0 from rfl] at hs
            simpa only [recoveredMessage, Fin.val_zero, Nat.zero_add, if_true, List.getD_cons_zero] using hs
          · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
            let pair := evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index
              (Fin.ofNat 4 n) digits)
            split at he
            rotate_left
            · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
            ·
                rename_i previous hr
                simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
                subst result
                obtain ⟨hcl, hdl, hll, hsel⟩ := ih (by omega) _ _ hr
                refine ⟨by simp [hcl], by simp [hdl], by simp [hll], ?_⟩
                intro lay hlay
                by_cases hlt : lay.val < n
                · have hcounter : (previous.counters ++ [counter]).getD lay.val 0 =
                      previous.counters.getD lay.val 0 := List.getD_append _ _ _ _ (by omega)
                  have hdigit : (previous.digits ++ [digits]).getD lay.val [] =
                      previous.digits.getD lay.val [] := List.getD_append _ _ _ _ (by omega)
                  have hlow : (previous.lows ++ [low]).getD lay.val true =
                      previous.lows.getD lay.val true := List.getD_append _ _ _ _ (by omega)
                  rw [hcounter, hdigit, hlow]
                  have hm : recoveredMessage answers sig index (n + 1) message
                        (previous.digits ++ [digits]) lay =
                      recoveredMessage answers sig index n (.pair pair.1 pair.2) previous.digits lay := by
                    unfold recoveredMessage
                    rw [if_neg (by omega)]
                    by_cases hnxt : lay.val + 1 = n
                    · rw [if_pos hnxt, hnxt, List.getD_append_right _ _ _ _ (by omega), hdl]
                      simp only [Nat.sub_self, List.getD_cons_zero]
                      rfl
                    · rw [if_neg hnxt, List.getD_append _ _ _ _ (by omega)]
                  rw [hm]
                  exact hsel lay hlt
                · have hl : lay = Fin.ofNat 4 n := Fin.ext (by rw [hv]; omega)
                  subst lay
                  simp only [recoveredMessage, hv, if_true]
                  rw [List.getD_append_right _ _ _ _ (by omega), hcl,
                    List.getD_append_right _ _ _ _ (by omega), hdl,
                    List.getD_append_right _ _ _ _ (by omega), hll]
                  simpa only [Nat.sub_self, List.getD_cons_zero] using hs
      · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
theorem fillTopSignature_fillTopSignature (sig : Signature) (a b : Nat) :
    fillTopSignature (fillTopSignature sig a) b = fillTopSignature sig b := by
  unfold fillTopSignature
  simp only [Signature.mk.injEq, true_and]
  funext lay
  exact fillLayer_fillLayer lay (sig.layers lay) a b
end SigGolfCandidate.Research.SharedForest


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem recoveredMessage_fill (answers : Answers) (sig : Signature) (index n : Nat)
    (hn : n ≤ 4) (message : LayerMsg) (digits : List (List Nat)) (lay : Layer)
    (hlay : lay.val < n) (c : Nat) :
    recoveredMessage answers (fillTopSignature sig c) index n message digits lay =
      recoveredMessage answers sig index n message digits lay := by
  unfold recoveredMessage
  split_ifs with htop
  · rfl
  · have hnext : (Fin.ofNat 4 (lay.val + 1) : Layer).val ≠ 0 := by
      rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hmain : mainSignature (fillTopSignature sig c) = fillTop (mainSignature sig) c := rfl
    dsimp only
    rw [hmain, recoverLayerPair_fill _ _ _ _ c hnext]

theorem recoveredPair_of_pieces (answers : Answers) (sig : Signature) (index : Nat)
    (lay : Layer) (hl : lay ≠ 0) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (hlayer : sig.layers lay = piecesSignature lay
      (wotsPieces answers lay (route index lay).2 (route index lay).1 digits)) :
    evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index lay digits) =
      builtPair answers lay (route index lay).2 := by
  apply eval_recoverLayerPair_honest answers (mainSignature sig) index lay hl digits hvalid
  · intro i
    change (sig.layers lay).values i = _
    rw [hlayer]
    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, i.isLt]
  · intro j
    change (sig.layers lay).path j = _
    rw [hlayer]
    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, j.isLt]

theorem recoveredSelections_canonical (answers : Answers) (sig : Signature) (index : Nat)
    (input : LayerMsg) (result : RecoveredLayers) (messages : Layer → LayerMsg)
    (hinput : input = messages 3)
    (hlower : ∀ n, n < 3 → messages (Fin.ofNat 4 n) =
      .pair (builtPair answers (Fin.ofNat 4 (n+1)) (route index (Fin.ofNat 4 (n+1))).2).1
        (builtPair answers (Fin.ofNat 4 (n+1)) (route index (Fin.ofNat 4 (n+1))).2).2)
    (hselections : ∀ lay : Layer, evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
        (route index lay).2 (route index lay).1
        (recoveredMessage answers sig index 4 input result.digits lay) 0 (searchLimit lay)) =
          some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true))
    (hshape : ∀ lay : Layer, ∃ digits,
      CanonicalPolicy.decode lay (evalWithAnswerFn answers (encodingHash lay
        (layerEncodingInput lay (route index lay).2 (route index lay).1 (messages lay)
          (result.counters.getD lay.val 0)))) = some digits ∧
      sig.layers lay = piecesSignature lay
        (wotsPieces answers lay (route index lay).2 (route index lay).1 digits)) :
    ∀ lay : Layer,
      evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
        (route index lay).2 (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true) ∧
      sig.layers lay = piecesSignature lay
        (wotsPieces answers lay (route index lay).2 (route index lay).1 (result.digits.getD lay.val [])) := by
  have step (lay : Layer)
      (hm : recoveredMessage answers sig index 4 input result.digits lay = messages lay) :
      evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
        (route index lay).2 (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true) ∧
      sig.layers lay = piecesSignature lay
        (wotsPieces answers lay (route index lay).2 (route index lay).1 (result.digits.getD lay.val [])) ∧
      Cost.ValidDigits lay (result.digits.getD lay.val []) := by
    have hs := hselections lay
    rw [hm] at hs
    have hlim := searchLimit_le lay
    have hp := (canonical_search_some' answers lay (hintFloor sig.policyHints lay)
      (route index lay).2 (route index lay).1 (messages lay) (searchLimit lay) 0
      (result.counters.getD lay.val 0) (result.digits.getD lay.val []) (result.lows.getD lay.val true)
      (by unfold counterLimit at hlim; omega) hs).2.2.2
    have hd := (CanonicalPolicy.producerDecodeAt_spec hp).1
    obtain ⟨ds, hds, hfields⟩ := hshape lay
    have heq := Option.some.inj (hds.symm.trans hd)
    subst ds
    exact ⟨hs, hfields, canonical_decode_valid hd⟩
  have h3 := step 3 (by change input = messages 3; exact hinput)
  have h2 := step 2 (by
    change LayerMsg.pair
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 3 (result.digits.getD 3 []))).1
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 3 (result.digits.getD 3 []))).2 = messages 2
    have hp := recoveredPair_of_pieces answers sig index 3 (by decide) _ h3.2.2 h3.2.1
    change evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 3
      (result.digits.getD 3 [])) = builtPair answers 3 (route index 3).2 at hp
    rw [hp]
    exact (hlower 2 (by decide)).symm)
  have h1 := step 1 (by
    change LayerMsg.pair
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 2 (result.digits.getD 2 []))).1
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 2 (result.digits.getD 2 []))).2 = messages 1
    have hp := recoveredPair_of_pieces answers sig index 2 (by decide) _ h2.2.2 h2.2.1
    change evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 2
      (result.digits.getD 2 [])) = builtPair answers 2 (route index 2).2 at hp
    rw [hp]
    exact (hlower 1 (by decide)).symm)
  have h0 := step 0 (by
    change LayerMsg.pair
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 1 (result.digits.getD 1 []))).1
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 1 (result.digits.getD 1 []))).2 = messages 0
    have hp := recoveredPair_of_pieces answers sig index 1 (by decide) _ h1.2.2 h1.2.1
    change evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 1
      (result.digits.getD 1 [])) = builtPair answers 1 (route index 1).2 at hp
    rw [hp]
    exact (hlower 0 (by decide)).symm)
  intro lay
  fin_cases lay
  · exact ⟨h0.1,h0.2.1⟩
  · exact ⟨h1.1,h1.2.1⟩
  · exact ⟨h2.1,h2.2.1⟩
  · exact ⟨h3.1,h3.2.1⟩
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signature_unique_of_selections (answers : Answers) (index : Nat)
    (messages : Layer → LayerMsg) (a b : Signature)
    (ca cb : Layer → BitVec 32) (da db : List (List Nat)) (la lb : List Bool)
    (hrho : a.rho = b.rho) (hforest : a.forest = b.forest)
    (ha : policyHintsValid a.policyHints da la = true)
    (hb : policyHintsValid b.policyHints db lb = true)
    (hsa : ∀ lay, evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay (hintFloor a.policyHints lay)
        (route index lay).2 (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (ca lay, da.getD lay.val [], la.getD lay.val true))
    (hsb : ∀ lay, evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay (hintFloor b.policyHints lay)
        (route index lay).2 (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (cb lay, db.getD lay.val [], lb.getD lay.val true))
    (hla : ∀ lay, a.layers lay = piecesSignature lay
      (wotsPieces answers lay (route index lay).2 (route index lay).1 (da.getD lay.val [])))
    (hlb : ∀ lay, b.layers lay = piecesSignature lay
      (wotsPieces answers lay (route index lay).2 (route index lay).1 (db.getD lay.val []))) : a = b := by
  obtain ⟨hh, -, hd, -⟩ := hintedSelections_unique answers index messages a.policyHints b.policyHints
    ca cb da db la lb ha hb hsa hsb
  have hl : a.layers = b.layers := by
    funext lay
    rw [hla, hlb, hd]
  cases a
  cases b
  simp only [Signature.mk.injEq]
  exact ⟨hrho, hh, hforest, hl⟩
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signFromOutput_components (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    ∃ result : CanonicalLayers,
      evalWithAnswerFn answers (searchPreparedLayers cache (digestIndex output)
        (evalWithAnswerFn answers (prepareRoots (digestIndex output)))
        (evalWithAnswerFn answers (buildForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output))).2) = some result ∧
      w.signature.rho = rho ∧ w.signature.policyHints = result.policyHints ∧
      w.signature.forest = (evalWithAnswerFn answers (buildForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output))).1 ∧
      (∀ lay, w.signature.layers lay = piecesSignature lay (result.pieces.getD lay.val ([],[]))) ∧
      w.digestCounter = counter ∧ ∀ lay, w.counters lay = result.counters.getD lay.val 0 := by
  unfold signFromOutput at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs : evalWithAnswerFn answers (searchPreparedLayers cache (digestIndex output)
    (evalWithAnswerFn answers (prepareRoots (digestIndex output)))
    (evalWithAnswerFn answers (buildForest (digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output))).2) with
  | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some result =>
      simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
      subst w
      exact ⟨result, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, fun _ => rfl⟩

theorem signPayload_components (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (sig : Signature)
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) :
    ∃ counter output w,
      evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
        message 0 digestAttemptLimit) = some (counter, output) ∧
      evalWithAnswerFn answers (signFromOutput cache (evalWithAnswerFn answers (privateNonce message))
        counter output) = some w ∧ w.signature = sig := by
  unfold signPayload at he
  simp only [evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
    message 0 digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (signFromOutput cache (evalWithAnswerFn answers (privateNonce message))
        counter output) with
      | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some w =>
          simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
          exact ⟨counter,output,w,rfl,hs,he⟩
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem PreparedSearchFacts.hinted_searches {answers : Answers} {cache : SigGolfCandidate.T3.Cache}
    {index : Nat} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index (evalWithAnswerFn answers (prepareRoots index)) forest result) :
    ∀ lay, evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay
      (hintFloor result.policyHints lay) (route index lay).2 (route index lay).1
      (if lay=3 then .pair forest.1 forest.2 else
        let lower : Layer := Fin.ofNat 4 (lay.val+1)
        .pair (builtPair answers lower (route index lower).2).1
          (builtPair answers lower (route index lower).2).2)
      0 (searchLimit lay)) = some (result.counters.getD lay.val 0,result.digits.getD lay.val [],result.lows.getD lay.val true) := by
  have hs0 := h.search0
  have hs1 := h.search1
  have hs2 := h.search2
  have hs3 := h.search3
  simp only [prepareRoots_result,fixedPrepared_pair] at hs0 hs1 hs2
  intro lay
  rcases layer_four_cases lay with rfl | rfl | rfl | rfl <;>
    simp only [layer_val_0,layer_val_1,layer_val_2,layer_val_3,
      show (Fin.ofNat 4 1 : Layer)=1 from rfl,
      show (Fin.ofNat 4 2 : Layer)=2 from rfl,
      show (Fin.ofNat 4 3 : Layer)=3 from rfl, Nat.reduceAdd,
      show (0 : Layer)≠3 by decide,show (1 : Layer)≠3 by decide,
      show (2 : Layer)≠3 by decide,if_false,if_true]
  · exact hs0
  · simpa only [h.hints_spec.2.1] using hs1
  · simpa only [h.hints_spec.2.2.1] using hs2
  · simpa only [h.hints_spec.2.2.2] using hs3
end SigGolfCandidate.Research.SharedForest
end
-- ==== merged from ClaudeWCT_Bank_WCTSpec ====
section

namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete (uniformWordAverage)
open ClaudeWCT.WCT9 (Coord Child Rank child rank wordDigit)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev WProposal := Fin (2 ^ 31) × (Coord → Child × Rank)
def outIdx (x : HashOutput) : Fin (2 ^ 31) := ⟨WCT9.digestIndex x, WCT9.digestIndex_lt x⟩
def proposal (x : HashOutput) : WProposal := (outIdx x, fun k => (child x k, rank x k))
def SlotCovered (X : List HashOutput) (N : HashOutput) (k : Coord) (t : Fin 6) : Prop :=
  ∃ x ∈ X, outIdx x = outIdx N ∧ child x k = child N k ∧ wordDigit (rank N k) t ≤ wordDigit (rank x k) t
def Covered (X : List HashOutput) (N : HashOutput) : Prop := ∀ k t, SlotCovered X N k t
def SlotCoveredP (W : List WProposal) (N : HashOutput) (k : Coord) (t : Fin 6) : Prop :=
  ∃ p ∈ W, p.1 = outIdx N ∧ (p.2 k).1 = child N k ∧ wordDigit (rank N k) t ≤ wordDigit (p.2 k).2 t
def CoveredP (W : List WProposal) (N : HashOutput) : Prop := ∀ k t, SlotCoveredP W N k t
theorem slotCovered_iff (X : List HashOutput) (N : HashOutput) (k : Coord) (t : Fin 6) :
    SlotCovered X N k t ↔ SlotCoveredP (X.map proposal) N k t := by
  constructor
  · rintro ⟨x, hx, h1, h2, h3⟩
    exact ⟨proposal x, List.mem_map_of_mem hx, h1, h2, h3⟩
  · rintro ⟨p, hp, h1, h2, h3⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    exact ⟨x, hx, h1, h2, h3⟩
theorem covered_iff (X : List HashOutput) (N : HashOutput) : Covered X N ↔ CoveredP (X.map proposal) N :=
  forall_congr' fun k => forall_congr' fun t => slotCovered_iff X N k t
theorem coveredP_append (W V : List WProposal) (N : HashOutput) (h : CoveredP W N) : CoveredP (W ++ V) N := by
  intro k t
  obtain ⟨p, hp, h1, h2, h3⟩ := h k t
  exact ⟨p, List.mem_append_left V hp, h1, h2, h3⟩
noncomputable def scoreP (W : List WProposal) (N : HashOutput) : ENNReal :=
  if WCT9.admissible N = true ∧ CoveredP W N then 1 else 0
noncomputable def score (X : List HashOutput) (N : HashOutput) : ENNReal := scoreP (X.map proposal) N
noncomputable def price (W : List WProposal) : ENNReal := 2 ^ 128 * BPORS.finiteAverage (fun N => scoreP W N)
theorem one_le_score (X : List HashOutput) (N : HashOutput) (hadm : WCT9.admissible N = true)
    (hcov : Covered X N) : 1 ≤ score X N := by
  unfold score scoreP
  rw [if_pos ⟨hadm, (covered_iff X N).mp hcov⟩]
theorem scoreP_append_mono (W V : List WProposal) (N : HashOutput) : scoreP W N ≤ scoreP (W ++ V) N := by
  unfold scoreP
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, coveredP_append W V N h1.2⟩ h2
  · exact bot_le
  · exact le_rfl
theorem score_append_mono (X Y : List HashOutput) (N : HashOutput) : score X N ≤ score (X ++ Y) N := by
  unfold score
  rw [List.map_append]
  exact scoreP_append_mono _ _ N
theorem average_score (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => score X N) = price (X.map proposal) / 2 ^ 128 := by
  unfold price score
  rw [mul_comm, ENNReal.mul_div_cancel_right (by positivity) (by finiteness)]
theorem admissible_zero : WCT9.admissible 0 = true := by decide
def AcceptedProposalUniform : Prop :=
  ∀ g : WProposal → ENNReal,
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun x => if WCT9.admissible x = true then g (proposal x) else 0) =
      BPORS.finiteAverage g *
        Pr[fun x : HashOutput => WCT9.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)]
def AcceptanceBound : Prop :=
  Pr[fun x : HashOutput => WCT9.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / 64
abbrev Coords := Coord → Child × Rank
def capOkC (c : Coords) : Bool :=
  decide ((∑ k, (WCT9.routineCost (c k).2 + WCT9.childExtra (c k).1)) ≤ WCT9.jointCap)
noncomputable def capSet : Finset Coords := Finset.univ.filter fun c => capOkC c = true
noncomputable def honestCoordLaw (c : Coords) : ENNReal :=
  if capOkC c = true then (capSet.card : ENNReal)⁻¹ else 0
noncomputable def honestLaw : WProposal → ENNReal :=
  ClaudeWCT.Numerics.Law.marked (α := Fin (2 ^ 31)) honestCoordLaw
def HonestLawSum : Prop := ∑ p, honestLaw p = 1
def AcceptedProposalHonest : Prop :=
  ∀ g : WProposal → ENNReal,
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun x => if WCT9.producerAdmissible x = true then g (proposal x) else 0) =
      (∑ p, honestLaw p * g p) *
        Pr[fun x : HashOutput => WCT9.producerAdmissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)]
def ProducerAcceptanceBound : Prop :=
  Pr[fun x : HashOutput => WCT9.producerAdmissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / 1024
def ExcessBound (horizon : Nat) (rate : ENNReal) : Prop :=
  ClaudeWCT.Numerics.Law.lawAvg honestLaw horizon (fun W : List WProposal => price W - 1023 / 1024) ≤ rate
noncomputable def wctSpec (hsum : HonestLawSum) (hacc : AcceptedProposalHonest) (hle : ProducerAcceptanceBound)
    (hprod : ∃ x, WCT9.producerAdmissible x = true) (horizon : Nat) (rate : ENNReal)
    (hexc : ExcessBound horizon rate) : FtsBankSpec WProposal where
  specTheta := 1023 / 1024
  admBound := 1 / 1024
  theta_add_admBound := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by unfold CaseC.theta; finiteness)).mp
    unfold CaseC.theta
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_inv,
      ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num
  admissible := WCT9.admissible
  producer := WCT9.producerAdmissible
  exists_producer := hprod
  acceptance_le := hle
  proposal := proposal
  law := honestLaw
  law_sum := hsum
  accepted_proposal := hacc
  score := score
  covered := Covered
  one_le_score := one_le_score
  score_append_mono := score_append_mono
  price := price
  average_score := average_score
  horizon := horizon
  excessRate := rate
  excess_le := hexc
end ClaudeWCT.Bank.WCT

namespace ClaudeWCT.Bank.WCT
/-- A stop-loss certificate at a chosen bank threshold. -/
def ExcessBoundAt (horizon : Nat) (threshold rate : ENNReal) : Prop :=
  ClaudeWCT.Numerics.Law.lawAvg honestLaw horizon
    (fun W : List WProposal => price W - threshold) ≤ rate

theorem excessBoundAt_mono {horizon : Nat} {threshold threshold' rate : ENNReal}
    (h : ExcessBoundAt horizon threshold rate) (ht : threshold ≤ threshold') :
    ExcessBoundAt horizon threshold' rate := by
  refine le_trans ?_ h
  exact ClaudeWCT.Numerics.Law.lawAvg_mono honestLaw horizon
    (fun W => tsub_le_tsub_left ht (price W))
end ClaudeWCT.Bank.WCT
end
-- ==== merged from ClaudeWCT_Bank_WCTAccept ====
section

section
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev DigestCoordinates := Fin (2 ^ 31) × (Coord → Fin 128 × Fin 1024) × (Fin 58 → Bool) × Fin (2 ^ 14)
def unusedBits : List Nat :=
  (List.range 16).map (· + 17) ++ (List.range 4).map (· + 81) ++ (List.range 5).map (· + 102) ++
    (List.range 4).map (· + 117) ++ (List.range 4).map (· + 145) ++ (List.range 5).map (· + 166) ++
    (List.range 4).map (· + 181) ++ (List.range 4).map (· + 209) ++ (List.range 12).map (· + 230)
def unusedPos (i : Fin 58) : Nat := unusedBits.getD i.val 0
def digestCoordinates (output : HashOutput) : DigestCoordinates :=
  ((output.extractLsb' 33 31).toFin,
    (fun coord => ((output.extractLsb' (childBase coord.val) 7).toFin,
      (output.extractLsb' (fieldBase coord.val) 10).toFin)),
    (fun i => output.getLsbD (unusedPos i)),
    (output.extractLsb' 242 14).toFin)
def admissibleView (view : DigestCoordinates) : Bool :=
  decide (view.2.2.2.val < WCT9.gateLimit) &&
    (List.finRange 9).all (fun coord => decide ((view.2.1 coord).2.val < 563))
theorem bit_cover : ∀ position, position < 256 →
    (33 ≤ position ∧ position < 64) ∨ 242 ≤ position ∨
      (∃ coord : Coord, childBase coord.val ≤ position ∧ position < childBase coord.val + 7) ∨
      (∃ coord : Coord, fieldBase coord.val ≤ position ∧ position < fieldBase coord.val + 10) ∨
      ∃ i : Fin 58, unusedPos i = position := by
  decide +kernel
theorem digestCoordinates_injective : Function.Injective digestCoordinates := by
  intro left right he
  apply BitVec.eq_of_getLsbD_eq
  intro position hp
  rcases bit_cover position hp with hindex | hgate | ⟨coord, hlo, hhi⟩ | ⟨coord, hlo, hhi⟩ | ⟨i, hi⟩
  · have hc := congrArg (fun x : DigestCoordinates => (BitVec.ofFin x.1 : BitVec 31)) he
    change left.extractLsb' 33 31 = right.extractLsb' 33 31 at hc
    have hb := congrArg (fun bits : BitVec 31 => bits.getLsbD (position - 33)) hc
    have hbit : position - 33 < 31 := by omega
    have hoff : 33 + (position - 33) = position := by omega
    simpa only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and, hoff] using hb
  · have hc := congrArg (fun x : DigestCoordinates => (BitVec.ofFin x.2.2.2 : BitVec 14)) he
    change left.extractLsb' 242 14 = right.extractLsb' 242 14 at hc
    have hb := congrArg (fun bits : BitVec 14 => bits.getLsbD (position - 242)) hc
    have hbit : position - 242 < 14 := by omega
    have hoff : 242 + (position - 242) = position := by omega
    simpa only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and, hoff] using hb
  · let within := position - childBase coord.val
    have hbit : within < 7 := by dsimp only [within]; omega
    have hoff : childBase coord.val + within = position := by dsimp only [within]; omega
    have hc := congrArg (fun x : DigestCoordinates =>
      (BitVec.ofFin (x.2.1 coord).1 : BitVec 7)) he
    change left.extractLsb' (childBase coord.val) 7 =
      right.extractLsb' (childBase coord.val) 7 at hc
    have hb := congrArg (fun bits : BitVec 7 => bits.getLsbD within) hc
    simpa only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and, hoff] using hb
  · let within := position - fieldBase coord.val
    have hbit : within < 10 := by dsimp only [within]; omega
    have hoff : fieldBase coord.val + within = position := by dsimp only [within]; omega
    have hc := congrArg (fun x : DigestCoordinates =>
      (BitVec.ofFin (x.2.1 coord).2 : BitVec 10)) he
    change left.extractLsb' (fieldBase coord.val) 10 =
      right.extractLsb' (fieldBase coord.val) 10 at hc
    have hb := congrArg (fun bits : BitVec 10 => bits.getLsbD within) hc
    simpa only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and, hoff] using hb
  · have hc := congrArg (fun x : DigestCoordinates => x.2.2.1 i) he
    change left.getLsbD (unusedPos i) = right.getLsbD (unusedPos i) at hc
    rw [hi] at hc
    exact hc
theorem digestCoordinates_bijective : Function.Bijective digestCoordinates := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨digestCoordinates_injective, ?_⟩
  simp only [DigestCoordinates, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bitVec, Fintype.card_bool]
  norm_num
theorem index_decode (output : HashOutput) :
    (digestCoordinates output).1.val = digestIndex output := by
  simp only [digestCoordinates, digestIndex, BitVec.val_toFin, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
theorem gate_decode (output : HashOutput) :
    (digestCoordinates output).2.2.2.val = output.toNat / 2 ^ 242 % 2 ^ 14 := by
  simp only [digestCoordinates, BitVec.val_toFin, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
theorem child_decode (output : HashOutput) (coord : Coord) :
    ((digestCoordinates output).2.1 coord).1 = child output coord := by
  apply Fin.ext
  simp only [digestCoordinates, child, BitVec.val_toFin, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
theorem field_decode (output : HashOutput) (coord : Coord) :
    ((digestCoordinates output).2.1 coord).2.val = field output coord := by
  simp only [digestCoordinates, field, BitVec.val_toFin, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
theorem rank_decode (output : HashOutput) (coord : Coord) :
    (rank output coord).val = ((digestCoordinates output).2.1 coord).2.val % 563 := by
  rw [field_decode, rank_val]
theorem admissible_decode (output : HashOutput) :
    admissibleView (digestCoordinates output) = admissible output := by
  rw [Bool.eq_iff_iff, admissible_iff]
  unfold admissibleView
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    forall_true_left, gate_decode, field_decode, gateLimit]
theorem uniform_coordinates :
    𝒮[digestCoordinates <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒮[($ᵗ DigestCoordinates : ProbComp DigestCoordinates)] := by
  exact evalSPMF_map_bijective_uniform_cross (α := HashOutput) (β := DigestCoordinates)
    digestCoordinates digestCoordinates_bijective
end ClaudeWCT.WCT9
end
section
namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open ClaudeWCT.WCT9 (Coord Child Rank child rank DigestCoordinates digestCoordinates admissibleView)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def viewProposal (v : DigestCoordinates) : WProposal :=
  (v.1, fun k => ((v.2.1 k).1, ⟨(v.2.1 k).2.val % 563, Nat.mod_lt _ (by decide)⟩))
theorem viewProposal_decode (x : HashOutput) : viewProposal (digestCoordinates x) = proposal x := by
  refine Prod.ext (Fin.ext ?_) (funext fun k => Prod.ext (WCT9.child_decode x k) (Fin.ext ?_))
  · exact WCT9.index_decode x
  · exact (WCT9.rank_decode x k).symm
theorem admissibleView_iff (v : DigestCoordinates) :
    admissibleView v = true ↔ v.2.2.2.val < WCT9.gateLimit ∧ ∀ k : Coord, (v.2.1 k).2.val < 563 := by
  unfold admissibleView
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange, forall_true_left]
abbrev FibreData := Fin WCT9.gateLimit × (Fin 58 → Bool)
def fibreEquiv (p : WProposal) :
    {v : DigestCoordinates // admissibleView v = true ∧ viewProposal v = p} ≃ FibreData where
  toFun v := (⟨v.1.2.2.2.val, ((admissibleView_iff v.1).1 v.2.1).1⟩, v.1.2.2.1)
  invFun s := ⟨(p.1, fun k => ((p.2 k).1, ⟨(p.2 k).2.val, by
      have h1 := (p.2 k).2.isLt
      omega⟩), s.2, ⟨s.1.val, by
        have := s.1.isLt
        have hgate : WCT9.gateLimit ≤ 2 ^ 14 := by decide
        omega⟩), by
    refine ⟨(admissibleView_iff _).2 ⟨s.1.isLt, fun k => (p.2 k).2.isLt⟩, ?_⟩
    refine Prod.ext rfl (funext fun k => Prod.ext rfl (Fin.ext ?_))
    exact Nat.mod_eq_of_lt (p.2 k).2.isLt⟩
  left_inv v := by
    obtain ⟨⟨i, f, u, g⟩, hadm, hp⟩ := v
    subst hp
    apply Subtype.ext
    refine Prod.ext rfl (Prod.ext (funext fun k => Prod.ext rfl (Fin.ext ?_)) rfl)
    exact Nat.mod_eq_of_lt (((admissibleView_iff _).1 hadm).2 k)
  right_inv s := rfl
theorem card_fibreData : Fintype.card FibreData = WCT9.gateLimit * 2 ^ 58 := by
  simp only [FibreData, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
theorem card_fibre (p : WProposal) :
    (Finset.univ.filter (fun x : HashOutput => WCT9.admissible x = true ∧ proposal x = p)).card =
      WCT9.gateLimit * 2 ^ 58 := by
  have e : {x : HashOutput // WCT9.admissible x = true ∧ proposal x = p} ≃
      {v : DigestCoordinates // admissibleView v = true ∧ viewProposal v = p} :=
    (Equiv.ofBijective digestCoordinates WCT9.digestCoordinates_bijective).subtypeEquiv
      (fun x => by
        change WCT9.admissible x = true ∧ proposal x = p ↔
          admissibleView (digestCoordinates x) = true ∧ viewProposal (digestCoordinates x) = p
        rw [WCT9.admissible_decode, viewProposal_decode])
  have hc := Fintype.card_congr (e.trans (fibreEquiv p))
  rw [card_fibreData, Fintype.card_subtype] at hc
  exact hc
theorem sum_admissible (g : WProposal → ENNReal) :
    (∑ x : HashOutput, if WCT9.admissible x = true then g (proposal x) else 0) =
      ((WCT9.gateLimit * 2 ^ 58 : Nat) : ENNReal) * ∑ p, g p := by
  rw [← Finset.sum_filter, ← Finset.sum_fiberwise _ proposal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const,
    Finset.filter_filter, card_fibre, nsmul_eq_mul]
theorem sum_admissible_one :
    (∑ x : HashOutput, if WCT9.admissible x = true then (1 : ENNReal) else 0) =
      ((WCT9.gateLimit * 2 ^ 58 : Nat) : ENNReal) * (Fintype.card WProposal : ENNReal) := by
  rw [sum_admissible (fun _ => 1), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
theorem acceptance_eq_ratio :
    Pr[fun x : HashOutput => WCT9.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ((WCT9.gateLimit * 2 ^ 58 : Nat) : ENNReal) * (Fintype.card WProposal : ENNReal) /
        (Fintype.card HashOutput : ENNReal) := by
  rw [← expectedValue_ite_one, BPORS.expected_uniform_eq_finiteAverage]
  unfold SigGolfResearch.Gate6.Moments.finiteAverage
  rw [sum_admissible_one]
theorem acceptedProposalUniform : AcceptedProposalUniform := by
  intro g
  rw [acceptance_eq_ratio, BPORS.expected_uniform_eq_finiteAverage]
  unfold SigGolfResearch.Gate6.Moments.finiteAverage
  rw [sum_admissible]
  have hP : (Fintype.card WProposal : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hP' : (Fintype.card WProposal : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  simp only [div_eq_mul_inv]
  calc ((WCT9.gateLimit * 2 ^ 58 : Nat) : ENNReal) * (∑ p, g p) * (Fintype.card HashOutput : ENNReal)⁻¹
      = ((WCT9.gateLimit * 2 ^ 58 : Nat) : ENNReal) * (∑ p, g p) * (Fintype.card HashOutput : ENNReal)⁻¹ *
          ((Fintype.card WProposal : ENNReal)⁻¹ * (Fintype.card WProposal : ENNReal)) := by
        rw [ENNReal.inv_mul_cancel hP hP', mul_one]
    _ = _ := by ring
theorem acceptance_eq :
    Pr[fun x : HashOutput => WCT9.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (WCT9.gateLimit * 563 ^ 9 : ENNReal) / 2 ^ 104 := by
  rw [acceptance_eq_ratio]
  simp only [WProposal, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bitVec]
  rw [ENNReal.div_eq_div_iff (by positivity) (by finiteness) (by positivity) (by finiteness)]
  norm_num
  ring
theorem acceptanceBound : AcceptanceBound := by
  unfold AcceptanceBound
  rw [acceptance_eq]
  have h0 : (WCT9.gateLimit * 563 ^ 9 : ENNReal) ≤ 2 ^ 98 := by
    exact_mod_cast (show (WCT9.gateLimit * 563 ^ 9 : Nat) ≤ 2 ^ 98 by norm_num [WCT9.gateLimit])
  have h : (WCT9.gateLimit * 563 ^ 9 : ENNReal) / 2 ^ 104 ≤ 2 ^ 98 / 2 ^ 104 := ENNReal.div_le_div_right h0 _
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.div_eq_div_iff (by positivity) (by finiteness) (by positivity) (by finiteness)]
  norm_num
end ClaudeWCT.Bank.WCT
end

/-! Exact digest fibers for the paired shared-path forest. -/
namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev PairSelector := Fin 2 × Fin 64 × Fin 64
abbrev Selectors := (Fin 4 → PairSelector) × Fin 128
abbrev RawFields := Selectors × (Fin 9 → Fin 1024) × Fin (2^31) × Fin (2^14)
abbrev Coordinates := RawFields × (Fin 62 → Bool)
def rankBase (k : Nat) : Nat := [13,77,89,101,141,153,165,205,217].getD k 0
def spareBase (k : Nat) : Nat := [23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 87, 88, 99, 100, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 151, 152, 163, 164, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 215, 216, 227, 228, 236, 237, 238, 239, 240, 241].getD k 0
def position (i : Nat) : Nat :=
  if i < 52 then 64*(i/13)+i%13
  else if i < 59 then 229+(i-52)
  else if i < 149 then rankBase ((i-59)/10)+(i-59)%10
  else if i < 180 then 33+(i-149)
  else if i < 194 then 242+(i-180)
  else spareBase (i-194)
def inversePosition (k : Nat) : Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 204, 205, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 206, 207, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 225, 226, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 227, 228, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 246, 247, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 248, 249, 52, 53, 54, 55, 56, 57, 58, 250, 251, 252, 253, 254, 255, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193].getD k 0
theorem inverse_bound : ∀ k : Fin 256, inversePosition k.val < 256 := by decide +kernel
theorem inverse_correct : ∀ k : Fin 256, position (inversePosition k.val) = k.val := by decide +kernel

def rawFields (a : HashOutput) : RawFields :=
  ((fun k => ((a.extractLsb' (64*k.val+6) 1).toFin,
      (a.extractLsb' (64*k.val) 6).toFin, (a.extractLsb' (64*k.val+7) 6).toFin),
    (a.extractLsb' 229 7).toFin),
    fun k => (a.extractLsb' (rankBase k.val) 10).toFin,
    (a.extractLsb' 33 31).toFin, (a.extractLsb' 242 14).toFin)
def coordinates (a : HashOutput) : Coordinates :=
  (rawFields a, fun k => a.getLsbD (spareBase k.val))

theorem coordinates_injective : Function.Injective coordinates := by
  intro a b he
  have hb : ∀ i : Fin 256, a.getLsbD (position i.val) = b.getLsbD (position i.val) := by
    intro i
    unfold position
    split_ifs with h0 h1 h2 h3 h4
    · have hk : i.val/13<4 := by omega
      by_cases hsmall : i.val%13<6
      · have e := congrArg (fun v : Coordinates =>
          (BitVec.ofFin (v.1.1.1 ⟨i.val/13,hk⟩).2.1 : BitVec 6).getLsbD (i.val%13)) he
        simpa only [coordinates, rawFields, BitVec.ofFin_toFin,
          BitVec.getLsbD_extractLsb', hsmall, decide_true, Bool.true_and] using e
      · by_cases hmid : i.val%13=6
        · have e := congrArg (fun v : Coordinates =>
            (BitVec.ofFin (v.1.1.1 ⟨i.val/13,hk⟩).1 : BitVec 1).getLsbD 0) he
          simpa only [coordinates, rawFields, BitVec.ofFin_toFin,
            BitVec.getLsbD_extractLsb', Nat.zero_lt_succ, decide_true, Bool.true_and,
            Nat.add_zero, hmid] using e
        · have hwithin : i.val%13-7<6 := by omega
          have hoff : 64*(i.val/13)+7+(i.val%13-7)=64*(i.val/13)+i.val%13 := by omega
          have e := congrArg (fun v : Coordinates =>
            (BitVec.ofFin (v.1.1.1 ⟨i.val/13,hk⟩).2.2 : BitVec 6).getLsbD (i.val%13-7)) he
          simpa only [coordinates, rawFields, BitVec.ofFin_toFin,
            BitVec.getLsbD_extractLsb', hwithin, decide_true, Bool.true_and, hoff] using e
    · have hk : i.val-52<7 := by omega
      have e := congrArg (fun v : Coordinates =>
        (BitVec.ofFin v.1.1.2 : BitVec 7).getLsbD (i.val-52)) he
      simpa only [coordinates, rawFields, BitVec.ofFin_toFin,
        BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and] using e
    · have hk : (i.val-59)/10<9 := by omega
      have e := congrArg (fun v : Coordinates =>
        (BitVec.ofFin (v.1.2.1 ⟨(i.val-59)/10,hk⟩) : BitVec 10).getLsbD ((i.val-59)%10)) he
      simpa only [coordinates, rawFields, BitVec.ofFin_toFin,
        BitVec.getLsbD_extractLsb', Nat.mod_lt _ (by decide : 0<10), decide_true, Bool.true_and] using e
    · have hk : i.val-149<31 := by omega
      have e := congrArg (fun v : Coordinates =>
        (BitVec.ofFin v.1.2.2.1 : BitVec 31).getLsbD (i.val-149)) he
      simpa only [coordinates, rawFields, BitVec.ofFin_toFin,
        BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and] using e
    · have hk : i.val-180<14 := by omega
      have e := congrArg (fun v : Coordinates =>
        (BitVec.ofFin v.1.2.2.2 : BitVec 14).getLsbD (i.val-180)) he
      simpa only [coordinates, rawFields, BitVec.ofFin_toFin,
        BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and] using e
    · have hk : i.val-194<62 := by omega
      exact congrArg (fun v : Coordinates => v.2 ⟨i.val-194,hk⟩) he
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e := hb ⟨inversePosition i,inverse_bound ⟨i,hi⟩⟩
  simpa only [inverse_correct ⟨i,hi⟩] using e

theorem coordinates_bijective : Function.Bijective coordinates := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨coordinates_injective, ?_⟩
  simp only [Coordinates, RawFields, Selectors, PairSelector,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bitVec, Fintype.card_bool]
  norm_num
noncomputable def coordinatesEquiv : HashOutput ≃ Coordinates :=
  Equiv.ofBijective coordinates coordinates_bijective

theorem uniform_coordinates :
    𝒮[coordinates <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒮[($ᵗ Coordinates : ProbComp Coordinates)] :=
  evalSPMF_map_bijective_uniform_cross (α := HashOutput) (β := Coordinates) coordinates coordinates_bijective
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev Alphabet := Selectors × (Fin 9 → Fin 563)
abbrev Proposal := Fin (2^31) × Alphabet

def viewProposal (v : Coordinates) : Proposal :=
  (v.1.2.2.1, v.1.1, fun k => ⟨(v.1.2.1 k).val % 563, Nat.mod_lt _ (by decide)⟩)
def proposal (a : HashOutput) : Proposal := viewProposal (coordinates a)
def admissibleView (v : Coordinates) : Bool :=
  decide (v.1.2.2.2.val < 791) && (List.finRange 9).all (fun k => decide ((v.1.2.1 k).val < 563))
def admissible (a : HashOutput) : Bool := admissibleView (coordinates a)

theorem admissibleView_iff (v : Coordinates) :
    admissibleView v = true ↔ v.1.2.2.2.val < 791 ∧ ∀ k : Fin 9, (v.1.2.1 k).val < 563 := by
  simp only [admissibleView, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, forall_true_left]
abbrev FibreData := Fin 791 × (Fin 62 → Bool)
def fibreEquiv (p : Proposal) :
    {v : Coordinates // admissibleView v = true ∧ viewProposal v = p} ≃ FibreData where
  toFun v := (⟨v.1.1.2.2.2.val, ((admissibleView_iff v.1).1 v.2.1).1⟩, v.1.2)
  invFun s := ⟨((p.2.1, fun k => ⟨(p.2.2 k).val, by have := (p.2.2 k).isLt; omega⟩,
    p.1, ⟨s.1.val, by have := s.1.isLt; omega⟩), s.2), by
    refine ⟨(admissibleView_iff _).2 ⟨s.1.isLt, fun k => (p.2.2 k).isLt⟩, ?_⟩
    refine Prod.ext rfl (Prod.ext rfl (funext fun k => Fin.ext ?_))
    exact Nat.mod_eq_of_lt (p.2.2 k).isLt⟩
  left_inv v := by
    obtain ⟨⟨⟨sel, ranks, i, g⟩, spare⟩, hadm, hp⟩ := v
    subst hp
    apply Subtype.ext
    refine Prod.ext (Prod.ext rfl (Prod.ext (funext fun k => Fin.ext ?_) rfl)) rfl
    exact Nat.mod_eq_of_lt (((admissibleView_iff _).1 hadm).2 k)
  right_inv s := rfl

theorem card_fibre (p : Proposal) :
    (Finset.univ.filter (fun a : HashOutput => admissible a = true ∧ proposal a = p)).card =
      791 * 2^62 := by
  have e : {a : HashOutput // admissible a = true ∧ proposal a = p} ≃
      {v : Coordinates // admissibleView v = true ∧ viewProposal v = p} :=
    coordinatesEquiv.subtypeEquiv (fun _ => Iff.rfl)
  have hc := Fintype.card_congr (e.trans (fibreEquiv p))
  simpa only [FibreData, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Fintype.card_subtype] using hc

theorem sum_admissible (g : Proposal → ENNReal) :
    (∑ a : HashOutput, if admissible a = true then g (proposal a) else 0) =
      ((791 * 2^62 : Nat) : ENNReal) * ∑ p, g p := by
  rw [← Finset.sum_filter, ← Finset.sum_fiberwise _ proposal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.1 ha).2]),
    Finset.sum_const, Finset.filter_filter, card_fibre, nsmul_eq_mul]

theorem acceptance_eq :
    Pr[fun a : HashOutput => admissible a = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (791 * 563^9 : ENNReal) / 2^104 := by
  rw [← expectedValue_ite_one, BPORS.expected_uniform_eq_finiteAverage]
  unfold SigGolfResearch.Gate6.Moments.finiteAverage
  rw [sum_admissible (fun _ => 1), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  simp only [Proposal, Alphabet, Selectors, PairSelector, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_bitVec]
  rw [ENNReal.div_eq_div_iff (by positivity) (by finiteness) (by positivity) (by finiteness)]
  norm_num

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SigGolfCandidate.Research
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def lowField (s : Selectors) (k : Fin 9) : Nat :=
  if h : k.val < 8 then
    let pair := s.1 ⟨k.val/2,by omega⟩
    if k.val % 2 = 0 then pair.2.1.val % 32 else pair.2.2.val % 32
  else s.2.val / 2 % 32

def coordinateCost (a : Alphabet) (k : Fin 9) : Nat :=
  ClaudeWCT.WCT9.routineCost (a.2 k) +
    if SharedForest.firstCoord k.val then SharedForest.aCorrection (lowField a.1 k)
    else SharedForest.bCorrection (lowField a.1 k)
def cost (a : Alphabet) : Nat := ((List.finRange 9).map (coordinateCost a)).sum
/-- The producer's joint cap 777 (`SharedForest.digestAccepted`). -/
def capOk (a : Alphabet) : Bool := decide (cost a ≤ 776)
def producer (a : HashOutput) : Bool := admissible a && capOk (proposal a).2

theorem proposal_index (a : HashOutput) : (proposal a).1.val = ClaudeWCT.WCT9.digestIndex a := by
  simp only [proposal, viewProposal, coordinates, rawFields, BitVec.val_toFin,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rfl

theorem proposal_rank (a : HashOutput) (k : Fin 9) :
    (proposal a).2.2 k = SharedForest.forestRank a k.val := by
  apply Fin.ext
  simp only [proposal, viewProposal, coordinates, rawFields, BitVec.val_toFin,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rfl

theorem proposal_lowField (a : HashOutput) (k : Fin 9) :
    lowField (proposal a).2.1 k = (SharedForest.costField a k).val := by
  fin_cases k <;>
    simp only [lowField, proposal, viewProposal, coordinates, rawFields,
      SharedForest.costField, SharedForest.costFieldBase, SharedForest.rawChildBase,
      SharedForest.firstCoord, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, BitVec.val_toFin, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  all_goals norm_num
  all_goals omega

theorem coordinateCost_source (a : HashOutput) (k : Fin 9) :
    coordinateCost (proposal a).2 k = SharedForest.coordinateAccountingCost a k := by
  rw [coordinateCost, proposal_rank, proposal_lowField]
  rw [SharedForest.coordinateAccountingCost, SharedForest.accountingCorrection_field]

theorem cost_source (a : HashOutput) : cost (proposal a).2 = SharedForest.jointAccountingCost a := by
  have h : coordinateCost (proposal a).2 = SharedForest.coordinateAccountingCost a :=
    funext (coordinateCost_source a)
  simp only [cost, SharedForest.jointAccountingCost, h]

theorem admissible_source (a : HashOutput) :
    admissible a = (decide (a.toNat/2^242%16384 < 791) && SharedForest.ranksAccepted a) := by
  simp only [admissible, admissibleView, coordinates, rawFields, BitVec.val_toFin,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rfl

theorem producer_source (a : HashOutput) : producer a = SharedForest.digestAccepted a := by
  rw [producer, admissible_source, capOk, cost_source]
  rfl

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open SigGolfCandidate.T3 SigGolfCandidate.Research
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def rawChild (s : Selectors) (k : Fin 9) : Fin 128 :=
  if hk : k.val<8 then
    let p := s.1 ⟨k.val/2,by omega⟩
    if k.val%2=0 then ⟨64*p.1.val+p.2.1.val,by have := p.1.isLt; have := p.2.1.isLt; omega⟩
    else ⟨2*p.2.2.val+p.1.val,by have := p.1.isLt; have := p.2.2.isLt; omega⟩
  else s.2

theorem proposal_child (a : HashOutput) (k : Fin 9) :
    rawChild (proposal a).2.1 k = SharedForest.rawChildFromOutput a k := by
  apply Fin.ext
  fin_cases k <;>
    simp only [rawChild, proposal, viewProposal, coordinates, rawFields,
      SharedForest.rawChildFromOutput, SharedForest.rawChildBase,
      List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, BitVec.val_toFin, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  all_goals norm_num
  all_goals omega

end ClaudeWCT.Bank.Paired
end
-- ==== merged from ClaudeWCT_Numerics_N600CapCount ====
section

namespace ClaudeWCT.Numerics.N600Cap
open Finset Polynomial
set_option maxRecDepth 100000
open ClaudeWCT.WCT9 (routineCost routineCosts routineCosts_length jointCap Coord Child Rank childExtra childSave maxChildSave)
def pairCost (c : Fin 9 → Child × Rank) : ℕ := ∑ k, (routineCost (c k).2 + childExtra (c k).1)
def J : ℕ := 51758331623566378875032754303375722573332992
noncomputable def costPoly : ℕ[X] := ∑ r : Fin 563, X ^ routineCost r
noncomputable def pairPoly : ℕ[X] := ∑ p : Child × Rank, X ^ (routineCost p.2 + childExtra p.1)
theorem sum_routineCost {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ r : Fin 563, f (routineCost r) = (routineCosts.map f).sum := by
  have h : ∀ (l : List ℕ) (n : ℕ) (hl : l.length = n),
      ∑ r : Fin n, f (l[r.val]'(by omega)) = (l.map f).sum := by
    intro l n hl
    subst hl
    rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]
  exact h routineCosts 563 routineCosts_length
theorem sum_childExtra {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ c : Child, f (childExtra c) = ((List.range 128).map fun c => f (maxChildSave - childSave c)).sum := by
  rw [← List.sum_ofFn]
  congr 1
theorem card_pairCost_eq (t : ℕ) : #{c : Fin 9 → Child × Rank | pairCost c = t} = (pairPoly ^ 9).coeff t := by
  have h := ClaudeWCT.Numerics.card_pi_sum_eq_coeff (fun _ : Fin 9 => (univ : Finset (Child × Rank)))
    (fun p => routineCost p.2 + childExtra p.1) t
  rw [Fintype.piFinset_univ, prod_const, card_univ, Fintype.card_fin] at h
  exact h
theorem pairCost_le (c : Fin 9 → Child × Rank) : pairCost c ≤ 846 := by
  unfold pairCost
  calc ∑ k, (routineCost (c k).2 + childExtra (c k).1) ≤ ∑ _k : Fin 9, 94 :=
        sum_le_sum fun k _ => by
          have h1 := (ClaudeWCT.WCT9.routineCost_bounds (c k).2).2
          have h2 : childExtra (c k).1 ≤ 5 := by unfold childExtra maxChildSave; omega
          omega
    _ = 846 := by simp
def costEval (B : ℕ) : ℕ := (routineCosts.map fun c => B ^ c).sum
def childEval (B : ℕ) : ℕ := ((List.range 128).map fun c => B ^ (maxChildSave - childSave c)).sum
def pairEval (B : ℕ) : ℕ := childEval B * costEval B
theorem eval_costPoly (B : ℕ) : costPoly.eval B = costEval B := by
  rw [costPoly, eval_finsetSum]
  simp only [eval_pow, eval_X]
  exact sum_routineCost (fun c => B ^ c)
theorem eval_pairPoly (B : ℕ) : pairPoly.eval B = pairEval B := by
  rw [pairPoly, eval_finsetSum]
  simp only [eval_pow, eval_X]
  rw [Fintype.sum_prod_type]
  simp only [pow_add]
  rw [show (∑ x : Child, ∑ y : Rank, B ^ routineCost y * B ^ childExtra x) =
      (∑ x : Child, B ^ childExtra x) * ∑ y : Rank, B ^ routineCost y by
    rw [Finset.sum_mul]; refine sum_congr rfl fun x _ => ?_; rw [Finset.mul_sum]
    refine sum_congr rfl fun y _ => ?_; ring]
  rw [sum_childExtra (fun e => B ^ e), sum_routineCost (fun c => B ^ c)]
  rfl
theorem pairEval_one : pairEval 1 = 72064 := by decide +kernel
theorem eval_one_pairPoly : pairPoly.eval 1 = 72064 := by
  rw [eval_pairPoly, pairEval_one]
def capCheck : Bool :=
  Nat.beq ((List.range 790).foldr (fun t s => pairEval (2 ^ 150) ^ 9 / (2 ^ 150) ^ t % 2 ^ 150 + s) 0) J
theorem capCheck_ok : capCheck = true := by decide +kernel
theorem range_foldr_eq_sum' (h : ℕ → ℕ) (n : ℕ) :
    (List.range n).foldr (fun r s => h r + s) 0 = ∑ r ∈ Finset.range n, h r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldr_append, Finset.sum_range_succ]
    simp only [List.foldr_cons, List.foldr_nil, Nat.add_zero]
    have hshift : ∀ (l : List ℕ) (c : ℕ), l.foldr (fun r s => h r + s) c = l.foldr (fun r s => h r + s) 0 + c := by
      intro l c
      induction l with
      | nil => simp
      | cons a l ihl => simp only [List.foldr_cons, ihl]; omega
    rw [hshift, ih]
def capSet : Finset (Coord → Child × Rank) := univ.filter fun c => pairCost c ≤ jointCap
theorem mem_capSet (c : Coord → Child × Rank) : c ∈ capSet ↔ pairCost c ≤ jointCap := by
  simp only [capSet, mem_filter, mem_univ, true_and]
set_option linter.constructorNameAsVariable false in
theorem card_capSet : capSet.card = J := by
  have hB : 0 < 2 ^ 150 := by positivity
  have hcoeff : ∀ i, (pairPoly ^ 9).coeff i < 2 ^ 150 := by
    intro i
    refine lt_of_le_of_lt (ClaudeWCT.Numerics.coeff_le_eval_one _ i) ?_
    rw [eval_pow, eval_one_pairPoly]
    norm_num
  have hext : ∀ t, (pairPoly ^ 9).coeff t = pairEval (2 ^ 150) ^ 9 / (2 ^ 150) ^ t % 2 ^ 150 := by
    intro t
    rw [← ClaudeWCT.Numerics.eval_div_pow_mod hB t _ hcoeff, eval_pow, eval_pairPoly]
  have hsplit : capSet.card = ∑ t ∈ range 790, #{c : Fin 9 → Child × Rank | pairCost c = t} := by
    have hmem : ∀ c ∈ capSet, pairCost c ∈ range 790 := by
      intro c hc
      rw [mem_capSet] at hc
      rw [mem_range]
      have h707 : ClaudeWCT.WCT9.jointCap = 789 := rfl
      omega
    rw [card_eq_sum_card_fiberwise hmem]
    unfold capSet
    refine sum_congr rfl fun t ht => ?_
    rw [filter_filter]
    exact congrArg Finset.card (filter_congr fun c _ => ⟨fun h => h.2,
      fun h => ⟨by rw [h]; have h2 := mem_range.mp ht; unfold ClaudeWCT.WCT9.jointCap; omega, h⟩⟩)
  have hc := capCheck_ok
  unfold capCheck at hc
  rw [hsplit]
  simp_rw [card_pairCost_eq, hext]
  rw [← range_foldr_eq_sum']
  exact Nat.eq_of_beq_eq_true hc
end ClaudeWCT.Numerics.N600Cap
end
