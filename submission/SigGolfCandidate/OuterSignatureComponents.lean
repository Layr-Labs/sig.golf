import SigGolfCandidate.OuterPreparedFacts
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterSignatureComponents
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec
attribute [local irreducible] OuterForestMoment.forest
theorem signFromOutput_components (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (OuterSigning.signFromOutput cache rho counter output) = some w) :
    ∃ result : CanonicalLayers,
      evalWithAnswerFn answers (OuterSigning.searchPreparedLayers cache (digestIndex output)
        (evalWithAnswerFn answers (prepareRoots (digestIndex output)))
        (evalWithAnswerFn answers (OuterForestMoment.forest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output))).2) = some result ∧
      w.signature.rho = rho ∧ w.signature.policyHints = result.policyHints ∧
      w.signature.forest = (evalWithAnswerFn answers (OuterForestMoment.forest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output))).1 ∧
      (∀ lay, w.signature.layers lay = piecesSignature lay (result.pieces.getD lay.val ([],[]))) ∧
      w.digestCounter = counter ∧ ∀ lay, w.counters lay = result.counters.getD lay.val 0 := by
  unfold OuterSigning.signFromOutput at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs : evalWithAnswerFn answers (OuterSigning.searchPreparedLayers cache (digestIndex output)
    (evalWithAnswerFn answers (prepareRoots (digestIndex output)))
    (evalWithAnswerFn answers (OuterForestMoment.forest (digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output))).2) with
  | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some result =>
      simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
      subst w
      exact ⟨result, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, fun _ => rfl⟩

theorem signPayload_components (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (he : evalWithAnswerFn answers (OuterSigning.signPayload cache message) = some sig) :
    ∃ counter output w,
      evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
        message 0 digestAttemptLimit) = some (counter, output) ∧
      evalWithAnswerFn answers (OuterSigning.signFromOutput cache (evalWithAnswerFn answers (privateNonce message))
        counter output) = some w ∧ w.signature = sig := by
  unfold OuterSigning.signPayload at he
  simp only [evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
    message 0 digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (OuterSigning.signFromOutput cache (evalWithAnswerFn answers (privateNonce message))
        counter output) with
      | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some w =>
          simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
          exact ⟨counter,output,w,rfl,hs,he⟩
theorem rhoHintOK_signFromOutput (answers : SigGolfCandidate.T3.Correctness.Answers)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (hrho : rho.toNat < R)
    (he : evalWithAnswerFn answers (OuterSigning.signFromOutput cache rho counter output)
      = some w) :
    RhoHintOK w.signature := by
  obtain ⟨result, hres, hr, hh, -⟩ :=
    signFromOutput_components answers cache rho counter output w he
  have F := OuterPreparedFacts.searchPreparedLayers_some answers cache _ _ _ result hres
  have r1 := threshold_lt_ranges 1 _ (by decide) (lt_of_lt_of_le F.floor1_lt (by decide))
  have r2 := threshold_lt_ranges 2 _ (by decide) F.floor2_lt
  have r3 := threshold_lt_ranges 3 _ (by decide) F.floor3_lt
  simp only [if_true, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide,
    if_false] at r1 r2 r3
  refine ⟨by rw [hr]; exact hrho, ?_⟩
  rw [hh, F.hints_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
    have h1 := F.floor1_lt; have h2 := F.floor2_lt; have h3 := F.floor3_lt; omega)]
  exact hints_ok_table ⟨_, r1⟩ ⟨_, r2⟩ ⟨_, r3⟩

/-- R6 (F4): honest `signPayload` output is `RhoHintOK` (`rho = rhoMod _ < R`, admissible floors). -/
theorem rhoHintOK_signPayload (answers : SigGolfCandidate.T3.Correctness.Answers)
    (cache : SigGolfCandidate.T3.Cache) (message : Message) (sig : SharedSignature)
    (he : evalWithAnswerFn answers (OuterSigning.signPayload cache message) = some sig) :
    RhoHintOK sig := by
  obtain ⟨counter, output, w, -, hw, rfl⟩ :=
    signPayload_components answers cache message sig he
  refine rhoHintOK_signFromOutput answers cache _ counter output w ?_ hw
  simp only [privateNonce, evalWithAnswerFn_bind, evalWithAnswerFn_pure, rhoMod_toNat]
  exact rhoMod_lt _

/-- R6 (F4): every honest signature (`SharedForest.sign`) is `RhoHintOK`; feed this to the codec round trip
(`sigDecC_sigBC_normTop`, `digC_sigBC`, `sigBC_injective_normTop`). -/
theorem rhoHintOK_sign (answers : SigGolfCandidate.T3.Correctness.Answers) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (sig : SharedSignature)
    (he : evalWithAnswerFn answers (OuterSigning.sign cache message) = some sig) :
    RhoHintOK sig := by
  unfold OuterSigning.sign at he
  simp only [evalWithAnswerFn_bind] at he
  split_ifs at he with htag
  · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
  · exact rhoHintOK_signPayload answers cache message sig he

#print axioms rhoHintOK_sign
end OuterSignatureComponents
