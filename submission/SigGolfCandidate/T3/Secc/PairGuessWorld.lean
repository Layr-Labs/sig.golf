import SigGolfCandidate.SphincsSecurity.Proof.Forced.SecretGuessForced
import SigGolfCandidate.T3.Secc.CanonGraph
import SigGolfCandidate.T3.Secc.WotsReference
import SigGolfCandidate.SphincsSecurity.Proof.Forced.SecretGuessErasure

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
