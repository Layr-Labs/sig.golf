import SigGolfCandidate.ClaudeWCT_W9_T3M_SigCodecC
import SigGolfCandidate.ClaudeWCT_W9_T3_Proofs
import SigGolfCandidate.ClaudeWCT_W9_T3M_Witness_Queries

namespace ClaudeWCT.W9.T3M.Final
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 (M Spec Message Digest Cache keygen privateInput)
open SigGolfCandidate.T3.Security (Request forwardWorld)
open ClaudeWCT.W9.T3.Security (Signature Requests signingOracle)
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)
noncomputable local instance instDecidableEqSignature_securityP : DecidableEq Signature := Classical.decEq _
inductive ForgeryP where
  | witness (message : Message) (witness : WBytes)
  | signature (message : Message) (signature : Signature)
abbrev AdversaryP := Digest → Cache → OracleComp (OracleWorld + Requests) (Option ForgeryP)
noncomputable def checkForgeryP (publicKey : Digest) (log : QueryLog Requests) : ForgeryP → M Bool := by
  classical
  exact fun forgery => do
    match forgery with
    | .witness message wb =>
        let verified ← verifyP message publicKey wb
        pure (decide (¬∃ entry ∈ log, entry.1.message = message ∧ entry.2.isSome = true) && verified)
    | .signature message signature =>
        let wb ← expandB message publicKey signature
        let some wb := wb | return false
        let verified ← verifyP message publicKey wb
        pure (decide (¬∃ entry ∈ log, entry.1.message = message ∧
          entry.2.map ClaudeWCT.WCT9.proj = some (ClaudeWCT.WCT9.proj signature)) && verified)
noncomputable def gameP (adversary : AdversaryP) : M Bool := do
    let (publicKey, cache) ← keygen
    let (forgery, log) ← (simulateQ
      ((fun input => liftM (forwardWorld input) : QueryImpl OracleWorld (WriterT (QueryLog Requests) M)) +
        signingOracle) (adversary publicKey cache)).run
    let some forgery := forgery | return false
    let verified ← checkForgeryP publicKey log forgery
    pure (decide (log.length ≤ 2^32) && verified)
noncomputable def realExperimentP (adversary : AdversaryP) : ProbComp (Bool × Nat) :=
  sampleMasterSeed >>= fun secret =>
    (simulateQ romImpl (SphincsSecurity.countHashQueries
      (SigGolfCandidate.T3.Derivation.realize (privateInput secret) (gameP adversary)))).run' ∅
def SecurityP : Prop := ∀ (adversary : AdversaryP) (q : Nat), 1 ≤ q →
  Pr[fun result => result.1 = true ∧ result.2 ≤ q | realExperimentP adversary] ≤ (q : ℝ≥0∞) / 2 ^ 127
end ClaudeWCT.W9.T3M.Final

namespace ClaudeWCT.W9.T3M.Final.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 (M Spec Message Digest Cache keygen privateInput)
open SigGolfCandidate.T3.Security (Request forwardWorld)
open SigGolfCandidate.Research.SharedForest (Signature)
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)

abbrev Requests := Request →ₒ Option Signature

def signingOracle : QueryImpl Requests (WriterT (QueryLog Requests) M) :=
  QueryImpl.withLogging fun request => liftM
    (SigGolfCandidate.Research.SharedForest.sign request.cache request.message)

inductive ForgeryP where
  | witness (message : Message) (witness : WBytes)
  | signature (message : Message) (signature : Signature)

abbrev AdversaryP := Digest → Cache → OracleComp (OracleWorld + Requests) (Option ForgeryP)

/-- Strong novelty compares the complete5239-byte wire signature, including
its canonical policy hints and the112-bit serialized top sibling. -/
noncomputable def checkForgeryP (publicKey : Digest) (log : QueryLog Requests) : ForgeryP → M Bool := by
  classical
  exact fun forgery => do
    match forgery with
    | .witness message wb =>
        let verified ← ClaudeWCT.W9.T3M.Paired.verifyP message publicKey wb
        pure (decide (¬∃ entry ∈ log, entry.1.message = message ∧ entry.2.isSome = true) && verified)
    | .signature message signature =>
        let wb ← ClaudeWCT.W9.T3M.Paired.expandB message publicKey signature
        let some wb := wb | return false
        let verified ← ClaudeWCT.W9.T3M.Paired.verifyP message publicKey wb
        pure (decide (¬∃ entry ∈ log, entry.1.message = message ∧
          entry.2.map SharedCodec.sigBC = some (SharedCodec.sigBC signature)) && verified)

noncomputable def gameP (adversary : AdversaryP) : M Bool := do
  let (publicKey, cache) ← keygen
  let (forgery, log) ← (simulateQ
    ((fun input => liftM (forwardWorld input) : QueryImpl OracleWorld (WriterT (QueryLog Requests) M)) +
      signingOracle) (adversary publicKey cache)).run
  let some forgery := forgery | return false
  let verified ← checkForgeryP publicKey log forgery
  pure (decide (log.length ≤ 2^32) && verified)

noncomputable def realExperimentP (adversary : AdversaryP) : ProbComp (Bool × Nat) :=
  sampleMasterSeed >>= fun secret =>
    (simulateQ romImpl (SphincsSecurity.countHashQueries
      (SigGolfCandidate.T3.Derivation.realize (privateInput secret) (gameP adversary)))).run' ∅

def SecurityP : Prop := ∀ (adversary : AdversaryP) (q : Nat), 1 ≤ q →
  Pr[fun result => result.1 = true ∧ result.2 ≤ q | realExperimentP adversary] ≤ (q : ENNReal) / 2 ^ 127

end ClaudeWCT.W9.T3M.Final.Paired

namespace ClaudeWCT.W9.T3M.Final.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def Fresh (log : QueryLog Requests) : ForgeryP → Prop
  | .witness message _ => ¬∃ entry ∈ log, entry.1.message = message ∧ entry.2.isSome = true
  | .signature message sig => ¬∃ entry ∈ log, entry.1.message = message ∧
      entry.2.map SharedCodec.sigBC = some (SharedCodec.sigBC sig)

def WitnessOf (answers : Answers) (pk : Digest) : ForgeryP → Message → WBytes → Prop
  | .witness sourceMessage sourceWitness, message, witness =>
      sourceMessage = message ∧ sourceWitness = witness
  | .signature sourceMessage sig, message, witness =>
      sourceMessage = message ∧
        evalWithAnswerFn answers (ClaudeWCT.W9.T3M.Paired.expandB message pk sig) = some witness

theorem check_accepting (answers : Answers) (pk : Digest) (log : QueryLog Requests)
    (forgery : ForgeryP) (h : evalWithAnswerFn answers (checkForgeryP pk log forgery) = true) :
    Fresh log forgery ∧ ∃ message witness,
      WitnessOf answers pk forgery message witness ∧
      evalWithAnswerFn answers (ClaudeWCT.W9.T3M.Paired.verifyP message pk witness) = true ∧
      ∀ q ∈ queried answers (ClaudeWCT.W9.T3M.Paired.verifyP message pk witness),
        q ∈ queried answers (checkForgeryP pk log forgery) := by
  cases forgery with
  | witness message witness =>
      simp only [checkForgeryP, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Bool.and_eq_true,
        decide_eq_true_eq] at h
      refine ⟨h.1, message, witness, ⟨rfl,rfl⟩, h.2, ?_⟩
      intro q hq
      simpa only [checkForgeryP, queried_bind, queried_pure, List.append_nil] using hq
  | signature message sig =>
      cases he : evalWithAnswerFn answers (ClaudeWCT.W9.T3M.Paired.expandB message pk sig) with
      | none => simp [checkForgeryP, evalWithAnswerFn_bind, he, evalWithAnswerFn_pure] at h
      | some witness =>
          simp only [checkForgeryP, evalWithAnswerFn_bind, he, evalWithAnswerFn_pure, Bool.and_eq_true,
            decide_eq_true_eq] at h
          refine ⟨h.1, message, witness, ⟨rfl, he⟩, h.2, ?_⟩
          intro q hq
          simp only [checkForgeryP, queried_bind, he, queried_pure, List.append_nil]
          exact List.mem_append_right _ hq
#print axioms check_accepting
end ClaudeWCT.W9.T3M.Final.Paired
