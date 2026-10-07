import SigGolfCandidate.T3.Secc.LargeCouplingKeygen
import SigGolfCandidate.T3.Secc.SeccSufRoute

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingShort : DecidableEq T3.Cache := Classical.decEq _
section Short
variable {A T : Answers} (hAT : Wots.Ref.ShortAgree A T)
include hAT
theorem secretsOf_short : secretsOf A = secretsOf T := by
  funext s
  cases s with
  | inl x => exact Wots.Ref.leafSeed_short hAT _ _ _ _
  | inr f =>
      change ftsSecretOf A f = ftsSecretOf T f
      unfold ftsSecretOf
      dsimp only
      rw [Wots.Ref.ShortRespects.privatePair 8 f.coord.val f.index.val 0 (f.leaf.val / 2) A T hAT]
theorem publicHash_respects (input : HashInput) (h : (pad64 input).length ≤ SeccLaw.maxInputLength) :
    Wots.Ref.ShortRespects (publicHash input) := by
  intro A' T' hAT'
  unfold publicHash
  change A' (.inl (.inr (pad64 input))) = T' (.inl (.inr (pad64 input)))
  exact hAT'.public _ h
theorem digestSearch_short (rho : Digest) (m : Message) :
    ∀ fuel c, evalWithAnswerFn A (digestSearch rho m c fuel) = evalWithAnswerFn T (digestSearch rho m c fuel) := by
  intro fuel
  induction fuel with
  | zero => intro c; rfl
  | succ fuel ih =>
      intro c
      simp only [digestSearch, digest, evalWithAnswerFn_bind]
      have hlen : (pad64 (digestInput rho m (BitVec.ofNat 32 c))).length ≤ SeccLaw.maxInputLength := by
        rw [BPB.pad64_digestInput, BPB.digestInput_length]
        unfold SeccLaw.maxInputLength
        omega
      rw [publicHash_respects hAT _ hlen A T hAT]
      split_ifs
      · rfl
      · exact ih (c + 1)
theorem signDigest_short (m : Message) : LargeResidual.signDigest A m = LargeResidual.signDigest T m := by
  unfold LargeResidual.signDigest
  have hn : evalWithAnswerFn A (T3.privateNonce m) = evalWithAnswerFn T (T3.privateNonce m) := by
    simp only [T3.privateNonce, privateHash, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    change (A (.inr (.inr (.inl m)))).extractLsb' 0 128 = (T (.inr (.inr (.inl m)))).extractLsb' 0 128
    rw [hAT.priv]
  rw [hn]
  exact digestSearch_short hAT _ _ _ _
theorem signDisclosed_short (published : T3.Cache) (request : Security.Request) :
    signDisclosed A published request = signDisclosed T published request := by
  have hd : Wots.referenceDigits A = Wots.referenceDigits T := funext (Wots.Ref.referenceDigits_short hAT)
  have hok : ∀ index, RouteOk A index ↔ RouteOk T index := by
    intro index
    unfold RouteOk
    simp only [Wots.Ref.referenceSearch_short hAT]
  unfold signDisclosed LargeResidual.signItems
  rw [signDigest_short hAT, hd]
  split_ifs
  · rcases LargeResidual.signDigest T request.message with _ | ⟨c, N⟩
    · rfl
    · simp only [hok]
  · rfl
end Short
def ContactR (adversary : AdversaryP) (q : Nat) (result : FirstHit.Recorded Bool) (A : Answers) : Prop :=
  ∀ generated tagged checked, TaggedSplit adversary result generated tagged checked →
    (monitorRun (Wots.referenceInputs adversary) A q generated.value.2 tagged.steps checked.events).contact = true
theorem contact_eq_contactR (adversary : AdversaryP) (q : Nat) (z : PaddedGame.TraceResult × Answers) :
    Contact adversary q z = ContactR adversary q (QueryRecorded.recordedTrace z.1) z.2 := rfl
end SigGolfCandidate.T3.Security.LargeCoupling
