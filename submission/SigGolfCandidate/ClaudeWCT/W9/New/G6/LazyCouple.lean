import SigGolfCandidate.T3.Secc.PairGuessLazyEager
import SigGolfCandidate.ClaudeWCT.W9.New.G6.LazyFree

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
section WorldBoundL
open SecretGuessObservation (fixedRun lazyRun)
end WorldBoundL
section Chain
end Chain
section Laws
open SecretGuessObservation (forcedRun forcedImpl runWith)
variable (slot : Nat)
theorem forcedRun_query (E : SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem)
    (input : WSpecL.Domain) (s : WStateL) :
    forcedRun E slot (liftM (WSpecL.query input)) s = (forcedImpl E slot input).run s := by
  rw [forcedRun, ← bind_pure (liftM (WSpecL.query input)), SecretGuessObservation.runWith_query_bind]
  simp only [SecretGuessObservation.runWith_pure]
  exact bind_pure _
theorem forcedRun_bind' {β γ : Type} (E : SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem)
    (first : OracleComp WSpecL β) (next : β → OracleComp WSpecL γ) (s : WStateL) :
    forcedRun E slot (first >>= next) s = forcedRun E slot first s >>= fun mid => forcedRun E slot (next mid.1) mid.2 := by
  simp only [forcedRun, SecretGuessObservation.runWith, simulateQ_bind, StateT.run_bind]
theorem ro_uniform (x : HashInput) :
    𝒮[($ᵗ (SphincsSecurity.HashSpec.Range x) : ProbComp _)] = (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) := by
  apply SPMF.ext
  intro a
  have h1 : 𝒮[($ᵗ (SphincsSecurity.HashSpec.Range x) : ProbComp _)] a =
      Pr[= a | ($ᵗ (SphincsSecurity.HashSpec.Range x) : ProbComp _)] := by
    rw [← SPMF.probOutput_eq_apply, probOutput_evalSPMF]
  have h2 := probOutput_uniformSample (α := SphincsSecurity.HashSpec.Range x) a
  have h3 : ((Fintype.card (SphincsSecurity.HashSpec.Range x) : ENNReal))⁻¹ = ((Fintype.card HashOutput : ENNReal))⁻¹ := by
    exact congrArg (fun n : ℕ => ((n : ENNReal))⁻¹)
      (Fintype.card_congr' (rfl : SphincsSecurity.HashSpec.Range x = HashOutput))
  have h4 : (PMF.uniformOfFintype HashOutput) (a : HashOutput) = ((Fintype.card HashOutput : ENNReal))⁻¹ :=
    PMF.uniformOfFintype_apply (a : HashOutput)
  exact h1.trans (h2.trans (h3.trans (h4.symm.trans (SPMF.liftM_apply _ _).symm)))
def SearchCore (s s' : WStateL) : Prop :=
  s'.allowed = s.allowed ∧ s'.retired = s.retired ∧ s'.guesses = s.guesses ∧ s'.probes = s.probes ∧
    s'.memory.nonces = s.memory.nonces ∧ s'.memory.births = s.memory.births ∧
    s'.memory.exposures = s.memory.exposures
theorem SearchCore.trans {s1 s2 s3 : WStateL} (h1 : SearchCore s1 s2) (h2 : SearchCore s2 s3) : SearchCore s1 s3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2⟩
theorem SearchCore.refl (s : WStateL) : SearchCore s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end Laws
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
section Steps
open SecretGuessObservation (fixedRun fixedImpl runWith)
variable (D : digestInputs → HashOutput) (Nn : Message → Digest) (fts : FtsCoord → Digest)
def Keeps (m m' : LazyMem) : Prop := m'.births = m.births ∧ m'.exposures = m.exposures ∧ m'.trials = m.trials
theorem Keeps.refl (m : LazyMem) : Keeps m m := ⟨rfl, rfl, rfl⟩
theorem Keeps.trans {m1 m2 m3 : LazyMem} (h1 : Keeps m1 m2) (h2 : Keeps m2 m3) : Keeps m1 m3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩
end Steps
section Programs
open SecretGuessObservation (fixedRun fixedImpl runWith)
noncomputable local instance instDecidableEqCache_pairGuessLazyCount : DecidableEq T3.Cache := Classical.decEq _
theorem queried_digestSearch_succ (A : Answers) (rho : Digest) (m : Message) (counter fuel : Nat) :
    SecurityExtraction.queried A (digestSearch rho m counter (fuel + 1)) =
      (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))) : T3.Spec.Domain) ::
        SecurityExtraction.queried A
          (if digestAdmissible (A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))))) = true
            then pure (some (BitVec.ofNat 32 counter, A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))))))
            else digestSearch rho m (counter + 1) fuel) := by
  rw [digestSearch]
  exact SecurityExtraction.queried_query_bind A _ _
end Programs
section Bank
end Bank
end SigGolfCandidate.T3.Security.BPair
end
section
namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph (WctAddr WctPoint)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem digestInputs rowVal rowStep nonceStep NotDN)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def inlineWith (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    QueryImpl WSpecL (OracleComp WSpec)
  | .inl (.coin n) => (liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1)))
  | .inl (.birth x) => pure (rowVal D x)
  | .inl (.trial x) => pure (rowVal D x)
  | .inl (.nonce m) => pure (Nn m)
  | .inl (.expose _) => pure ()
  | .inr q => liftM (WSpec.query (.inr q))
section Inline
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
noncomputable local instance instDecidableEqCache_g6LazyCouple : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
noncomputable def inlineAux (ω : CanonTable.Omega U) : QueryImpl WSpecL (OracleComp WSpec) :=
  inlineWith (digestOf ω) (nonceOf ω)
theorem inline_probeW (D : digestInputs → HashOutput) (Nn : Message → Digest)
    (step : Guess.ChainAddr → Fin 4 → Digest → HashOutput) (top : Guess.ChainAddr → HashOutput) (miss : HashOutput)
    (a : Guess.ChainAddr) (p : Fin 4) (v : Digest) :
    simulateQ (inlineWith D Nn) (Guess.probeW (auxSpec := AuxSpecL) step top miss a p v) =
      Guess.probeW (auxSpec := unifSpec) step top miss a p v := by
  unfold Guess.probeW Guess.trialQ
  rw [simulateQ_bind, simulateQ_spec_query]
  refine bind_congr fun hit => ?_
  cases hit with
  | false => simp only [Bool.false_eq_true, if_false, simulateQ_pure]
  | true =>
      simp only [if_true]
      cases Guess.succPos p with
      | none => simp only [simulateQ_pure]
      | some p' =>
          simp only
          unfold Guess.discloseQ
          rw [simulateQ_bind, simulateQ_spec_query]
          exact bind_congr fun next => by rw [simulateQ_pure]
theorem inline_discloseQ (D : digestInputs → HashOutput) (Nn : Message → Digest) (c : Guess.GCoord) :
    simulateQ (inlineWith D Nn) (Guess.discloseQ (auxSpec := AuxSpecL) (V := Digest) c) =
      Guess.discloseQ (auxSpec := unifSpec) (V := Digest) c := by
  unfold Guess.discloseQ
  rw [simulateQ_spec_query]
  rfl
theorem inline_discloseAll (D : digestInputs → HashOutput) (Nn : Message → Digest) (cs : List Guess.GCoord) :
    simulateQ (inlineWith D Nn) (Guess.discloseAll (auxSpec := AuxSpecL) (V := Digest) cs) =
      Guess.discloseAll (auxSpec := unifSpec) (V := Digest) cs := by
  induction cs with
  | nil => simp [Guess.discloseAll]
  | cons c rest ih =>
      unfold Guess.discloseAll at ih ⊢
      rw [List.mapM_cons, List.mapM_cons, simulateQ_bind, inline_discloseQ]
      refine bind_congr fun v => ?_
      rw [simulateQ_bind, ih]
      exact bind_congr fun vs => by rw [simulateQ_pure]
theorem inline_hashL (ω : CanonTable.Omega U) (x : HashInput) :
    simulateQ (inlineAux ω) (hashL hU ω x) = hashW hU ω x := by
  unfold hashL hashW Guess.ChainTable.hashW
  cases hd : Guess.decodeProbe x with
  | some q => exact inline_probeW _ _ _ _ _ _ _ _
  | none =>
      simp only
      by_cases hx : x ∈ digestInputs
      · rw [if_pos hx]
        unfold birthReq
        rw [simulateQ_spec_query]
        change pure (rowVal (digestOf ω) x) = pure (wA hU ω 0 (.inl (.inr x)))
        rw [answers_digest hU ω 0 x hx]
      · rw [if_neg hx, simulateQ_pure]
        rfl
theorem eval_wctDigestSearch_succ (A : Answers) (rho : Digest) (m : Message) (counter fuel : Nat) :
    evalWithAnswerFn A (WCT9.digestSearch rho m counter (fuel + 1)) =
      if WCT9.producerAdmissible (A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))))) = true then
        some (BitVec.ofNat 32 counter, A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter))))))
      else evalWithAnswerFn A (WCT9.digestSearch rho m (counter + 1) fuel) := by
  rw [WCT9.digestSearch, evalWithAnswerFn_bind]
  rw [show evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 counter)) =
    A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter))))) from eval_query' A _]
  by_cases h : WCT9.producerAdmissible (A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))))) = true
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
theorem inline_searchL (ω : CanonTable.Omega U) (rho : Digest) (m : Message) (counter fuel : Nat) :
    simulateQ (inlineAux ω) (searchL rho m counter fuel) =
      pure (evalWithAnswerFn (wA hU ω 0) (WCT9.digestSearch rho m counter fuel)) := by
  induction fuel generalizing counter with
  | zero => rfl
  | succ fuel ih =>
      rw [eval_wctDigestSearch_succ, answers_digest hU ω _ _ (SigGolfCandidate.T3.Security.BPair.digestInput_mem _ _ _)]
      simp only [searchL, trialReq, simulateQ_bind, simulateQ_spec_query, inlineAux, inlineWith, pure_bind]
      by_cases h : WCT9.producerAdmissible (rowVal (digestOf ω) (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))) = true
      · simp only [h, ↓reduceIte, simulateQ_pure]
      · simp only [h, ↓reduceIte, Bool.false_eq_true]
        exact ih _
theorem signerCore_neg (ω : CanonTable.Omega U) {published : SigGolfCandidate.T3.Cache} {request : Request}
    (hc : ¬request.cache = published) : signerCore hU ω published request = none := by
  unfold signerCore
  rw [if_neg hc]
theorem inline_signL (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    simulateQ (inlineAux ω) (signL hU ω published request) = signW hU ω published request := by
  unfold signW openedFor liftFor
  simp only [sign_answers]
  unfold signL
  by_cases hc : request.cache = published
  · rw [if_pos hc]
    simp only [nonceReq, exposeReq, simulateQ_bind, simulateQ_spec_query, inline_searchL hU ω]
    simp only [inlineAux, inlineWith, pure_bind]
    rw [← eval_nonce hU ω 0 request.message]
    unfold signerCore
    rw [if_pos hc]
    generalize evalWithAnswerFn (wA hU ω 0) (privateNonce request.message) = rho
    generalize evalWithAnswerFn (wA hU ω 0) (WCT9.digestSearch rho request.message 0 WCT9.digestAttemptLimit) = found
    rcases found with _ | ⟨c, output⟩
    · simp only [finishL, simulateQ_pure, Guess.discloseAll, List.mapM_nil, pure_bind, Option.map_none]
    · simp only [finishL]
      unfold signerLayersW
      generalize evalWithAnswerFn (wA hU ω 0) (WCT9.signLayersBC request.cache (WCT9.digestIndex output) 4
        (.pair (WCT9.honestTop (wA hU ω 0) (WCT9.digestIndex output)).1 (WCT9.honestTop (wA hU ω 0) (WCT9.digestIndex output)).2)) = L
      rcases L with _ | pieces
      · simp only [simulateQ_pure, Guess.discloseAll, List.mapM_nil, pure_bind, Option.map_none]
      · simp only [simulateQ_bind, simulateQ_pure]
        rw [show simulateQ (inlineWith (digestOf ω) (nonceOf ω))
            (Guess.discloseAll (auxSpec := AuxSpecL) (V := Digest) (revealedCoords output)) =
          Guess.discloseAll (auxSpec := unifSpec) (V := Digest) (revealedCoords output) from
          inline_discloseAll _ _ _]
        exact bind_congr fun values => by rw [Option.map_some]
  · rw [if_neg hc, signerCore_neg hU ω hc]
    simp only [simulateQ_pure, Guess.discloseAll, List.mapM_nil, pure_bind, Option.map_none]
theorem interactionL_pure (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    interactionL hU ω published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl
theorem interactionL_coin (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      (coinReqL n >>= fun coin => interactionL hU ω published (next coin)) := rfl
theorem interactionL_public (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (x : HashInput) (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (hashL hU ω x >>= fun answer => interactionL hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl
theorem interactionL_request (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (signL hU ω published request >>= fun signature => interactionL hU ω published (next signature) >>= fun rest =>
        pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl
theorem programL_pure (ω : CanonTable.Omega U) {β : Type} (value : β) :
    programL hU ω (pure value : M β) = pure (value, []) := rfl
theorem programL_coin (ω : CanonTable.Omega U) {β : Type} (n : Nat) (next : Fin (n + 1) → M β) :
    programL hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inl n))) >>= next) =
      (coinReqL n >>= fun coin => programL hU ω (next coin)) := rfl
theorem programL_public (ω : CanonTable.Omega U) {β : Type} (x : HashInput) (next : HashOutput → M β) :
    programL hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr x))) >>= next) =
      (hashL hU ω x >>= fun answer => programL hU ω (next answer) >>= fun rest =>
        pure (rest.1, (x, answer) :: rest.2)) := rfl
theorem programL_private (ω : CanonTable.Omega U) {β : Type} (c : Coordinate) (next : HashOutput → M β) :
    programL hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inr c)) >>= next) = programL hU ω (next 0) := rfl
theorem inline_interactionL (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    simulateQ (inlineAux ω) (interactionL hU ω published program) = interactionW hU ω published program := by
  induction program using OracleComp.inductionOn with
  | pure value => rw [interactionL_pure, interactionW_pure, simulateQ_pure]
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionL_coin, interactionW_coin, simulateQ_bind, coinReqL, simulateQ_spec_query]
        exact bind_congr fun coin => ih coin
      · rw [interactionL_public, interactionW_public, simulateQ_bind, inline_hashL]
        refine bind_congr fun answer => ?_
        rw [simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]
      · rw [interactionL_request, interactionW_request, simulateQ_bind, inline_signL]
        refine bind_congr fun signature => ?_
        rw [simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]
theorem inline_programL (ω : CanonTable.Omega U) {β : Type} (program : M β) :
    simulateQ (inlineAux ω) (programL hU ω program) = programW hU ω program := by
  induction program using OracleComp.inductionOn with
  | pure value => rw [programL_pure, programW_pure, simulateQ_pure]
  | query_bind input next ih =>
      rcases input with (n | x) | c
      · rw [programL_coin, simulateQ_bind, coinReqL, simulateQ_spec_query]
        exact bind_congr fun coin => ih coin
      · rw [programL_public, programW_public, simulateQ_bind, inline_hashL]
        refine bind_congr fun answer => ?_
        rw [simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]
      · rw [programL_private]
        exact ih (0 : HashOutput)
theorem worldGame_inline (ω : CanonTable.Omega U) (adversary : AdversaryP) :
    worldGame hU ω adversary = simulateQ (inlineAux ω) (worldGameL hU ω adversary) := by
  unfold worldGameL worldGameCore worldGame
  rw [simulateQ_bind, inline_interactionL]
  refine bind_congr fun interaction => ?_
  rw [simulateQ_bind, inline_programL]
  exact bind_congr fun verdict => by rw [simulateQ_pure]
end Inline
section Run
open SecretGuessObservation (fixedRun fixedImpl runWith)
def forget (s : WStateL) : WState := ⟨s.allowed, s.retired, s.guesses, s.probes, PUnit.unit⟩
theorem coin_spmf (n : Nat) : (liftM (liftM (coinImpl n) : PMF (Fin (n + 1))) : SPMF (Fin (n + 1))) =
    (liftM (PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) := evalSPMF_query (spec := unifSpec) n
theorem fixed_aux_pure {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest) (g : Guess.GCoord → Digest)
    (s : WStateL) (input : AuxL) (v : AuxSpecL.Range input) (mem' : LazyMem)
    (h : (envE D Nn).auxiliary s input = pure (v, mem'))
    (next : AuxSpecL.Range input → OracleComp WSpecL α) :
    runWith (fixedImpl (envE D Nn) g) (liftM (WSpecL.query (.inl input)) >>= next) s =
      runWith (fixedImpl (envE D Nn) g) (next v) { s with memory := mem' } := by
  rw [SecretGuessObservation.runWith_query_bind]
  change ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((envE D Nn).auxiliary s input) : SPMF _)) >>= _ = _
  rw [h, liftM_pure, map_pure, pure_bind]
theorem fixed_inline {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest) (g : Guess.GCoord → Digest)
    (W : OracleComp WSpecL α) (s : WStateL) (hs : SigGolfCandidate.T3.Security.BPair.Consistent D Nn s.memory) :
    (fun r => (r.1, forget r.2)) <$> fixedRun (envE D Nn) g W s =
      fixedRun env g (simulateQ (inlineWith D Nn) W) (forget s) := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure a => simp only [fixedRun, SecretGuessObservation.runWith_pure, simulateQ_pure, map_pure]
  | query_bind input next ih =>
      rcases input with input | (⟨c, v⟩ | c)
      · cases input with
        | coin n =>
            rw [fixedRun, SecretGuessObservation.runWith_query_bind, map_bind, simulateQ_bind, simulateQ_spec_query]
            change ((fun result => (result.1, { s with memory := result.2 })) <$>
              (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _)) >>= _ =
              fixedRun env g ((liftM (WSpec.query (.inl n)) : OracleComp WSpec _) >>= fun c =>
                simulateQ (inlineWith D Nn) (next c)) (forget s)
            rw [fixedRun, SecretGuessObservation.runWith_query_bind]
            change _ = ((fun result => (result.1, { forget s with memory := result.2 })) <$>
              (liftM ((fun a => (a, PUnit.unit)) <$> (liftM (coinImpl n) : PMF _)) : SPMF _)) >>= _
            have hL : ((fun result => (result.1, { s with memory := result.2 })) <$>
                (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _)) =
                (fun c => (c, s)) <$> (liftM (PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) := by
              rw [liftM_map, Functor.map_map]
            have hR : ((fun result => (result.1, { forget s with memory := result.2 })) <$>
                (liftM ((fun a => (a, PUnit.unit)) <$> (liftM (coinImpl n) : PMF _)) : SPMF _)) =
                (fun c => (c, forget s)) <$> (liftM (PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) := by
              rw [liftM_map, coin_spmf, Functor.map_map]
            rw [hL, hR]
            exact (bind_map_left _ _ _).trans ((bind_congr fun c => ih c s hs).trans
              (bind_map_left (fun c => (c, forget s)) _ (fun result =>
                runWith (fixedImpl env g) (simulateQ (inlineWith D Nn) (next result.1)) result.2)).symm)
        | birth x =>
            obtain ⟨mem', hc, h⟩ := SigGolfCandidate.T3.Security.BPair.rowStep_eager D Nn s.memory hs x true
            rw [fixedRun, fixed_aux_pure D Nn g s (.birth x) (rowVal D x) mem' h, simulateQ_bind, simulateQ_spec_query]
            change _ = fixedRun env g (pure (rowVal D x) >>= fun u => simulateQ (inlineWith D Nn) (next u)) (forget s)
            rw [pure_bind]
            exact ih _ _ hc
        | trial x =>
            obtain ⟨mem', hc, h⟩ := SigGolfCandidate.T3.Security.BPair.rowStep_eager D Nn s.memory hs x false
            rw [fixedRun, fixed_aux_pure D Nn g s (.trial x) (rowVal D x) mem' h, simulateQ_bind, simulateQ_spec_query]
            change _ = fixedRun env g (pure (rowVal D x) >>= fun u => simulateQ (inlineWith D Nn) (next u)) (forget s)
            rw [pure_bind]
            exact ih _ _ hc
        | nonce m =>
            obtain ⟨mem', hc, h⟩ := SigGolfCandidate.T3.Security.BPair.nonceStep_eager D Nn s.memory hs m
            rw [fixedRun, fixed_aux_pure D Nn g s (.nonce m) (Nn m) mem' h, simulateQ_bind, simulateQ_spec_query]
            change _ = fixedRun env g (pure (Nn m) >>= fun u => simulateQ (inlineWith D Nn) (next u)) (forget s)
            rw [pure_bind]
            exact ih _ _ hc
        | expose o =>
            rw [fixedRun, fixed_aux_pure D Nn g s (.expose o) () (s.memory.expose o) rfl, simulateQ_bind,
              simulateQ_spec_query]
            change _ = fixedRun env g (pure () >>= fun u => simulateQ (inlineWith D Nn) (next u)) (forget s)
            rw [pure_bind]
            exact ih _ _ ⟨hs.1, hs.2⟩
      · rw [fixedRun, SecretGuessObservation.runWith_query_bind, map_bind, simulateQ_bind, simulateQ_spec_query]
        change (pure (decide (g c = v), SecretGuessObservation.afterTrial (envE D Nn) s c v (decide (g c = v))) >>= _) =
          fixedRun env g ((liftM (WSpec.query (.inr (.inl (c, v)))) : OracleComp WSpec Bool) >>= fun u =>
            simulateQ (inlineWith D Nn) (next u)) (forget s)
        rw [pure_bind, fixedRun, SecretGuessObservation.runWith_query_bind]
        change _ = (pure (decide (g c = v), SecretGuessObservation.afterTrial env (forget s) c v (decide (g c = v))) >>= _)
        rw [pure_bind]
        exact ih _ _ hs
      · rw [fixedRun, SecretGuessObservation.runWith_query_bind, map_bind, simulateQ_bind, simulateQ_spec_query]
        change (pure (g c, SecretGuessObservation.afterDisclosure (envE D Nn) s c (g c)) >>= _) =
          fixedRun env g ((liftM (WSpec.query (.inr (.inr c)))  : OracleComp WSpec Digest) >>= fun u =>
            simulateQ (inlineWith D Nn) (next u)) (forget s)
        rw [pure_bind, fixedRun, SecretGuessObservation.runWith_query_bind]
        change _ = (pure (g c, SecretGuessObservation.afterDisclosure env (forget s) c (g c)) >>= _)
        rw [pure_bind]
        exact ih _ _ hs
theorem fixed_inline_nonzero {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest)
    (g : Guess.GCoord → Digest) (W : OracleComp WSpecL α) (s : WStateL)
    (hs : SigGolfCandidate.T3.Security.BPair.Consistent D Nn s.memory)
    (r : α × WStateL) (hr : fixedRun (envE D Nn) g W s r ≠ 0) :
    fixedRun env g (simulateQ (inlineWith D Nn) W) (forget s) (r.1, forget r.2) ≠ 0 := by
  rw [← fixed_inline D Nn g W s hs]
  have hm : r ∈ support (fixedRun (envE D Nn) g W s) := by
    simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr
  have h : (r.1, forget r.2) ∈ support ((fun r => (r.1, forget r.2)) <$> fixedRun (envE D Nn) g W s) := by
    rw [support_map]
    exact ⟨r, hm, rfl⟩
  simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using h
end Run
section LazyCouple
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
open SecretGuessObservation (fixedRun)
theorem forget_initL : forget initL = init := rfl
theorem fixed_worldGameL (g : CanonTable.HiddenF) (adversary : AdversaryP) :
    Prod.fst <$> fixedRun (envE (digestOf ω) (nonceOf ω)) (Guess.Fam.phi g.1 g.2) (worldGameL hU ω adversary) initL =
      𝒮[pairRun (wA hU ω g) adversary] := by
  have h := congrArg (Functor.map Prod.fst)
    (fixed_inline (digestOf ω) (nonceOf ω) (Guess.Fam.phi g.1 g.2) (worldGameL hU ω adversary) initL
      (SigGolfCandidate.T3.Security.BPair.consistent_empty _ _))
  rw [Functor.map_map] at h
  rw [show (Prod.fst <$> fixedRun (envE (digestOf ω) (nonceOf ω)) (Guess.Fam.phi g.1 g.2) (worldGameL hU ω adversary)
      initL) = (fun r => (r.1, forget r.2).1) <$> fixedRun (envE (digestOf ω) (nonceOf ω)) (Guess.Fam.phi g.1 g.2)
      (worldGameL hU ω adversary) initL from rfl, h, forget_initL, ← fixed_worldGame hU ω g adversary]
  change _ = Prod.fst <$> fixedRun env (Guess.Fam.phi g.1 g.2) (worldGame hU ω adversary) init
  rw [worldGame_inline]
  rfl
theorem worldGameL_tracking (g : CanonTable.HiddenF) (adversary : AdversaryP)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) (Guess.Fam.phi g.1 g.2) (worldGameL hU ω adversary) initL r ≠ 0) :
    r.2.probes ≤ r.1.2.2.length ∧
      ∀ c, GuessedIn (wA hU ω g) r.1.2.1 r.1.2.2 c → Guess.PrefixIn r.2.guesses c.1 c.2.val := by
  have h := fixed_inline_nonzero (digestOf ω) (nonceOf ω) (Guess.Fam.phi g.1 g.2) _ initL
    (SigGolfCandidate.T3.Security.BPair.consistent_empty _ _) r hr
  rw [forget_initL] at h
  change fixedRun env (Guess.Fam.phi g.1 g.2) (simulateQ (inlineAux ω) (worldGameL hU ω adversary)) init
    (r.1, forget r.2) ≠ 0 at h
  rw [← worldGame_inline] at h
  exact worldGame_tracking hU ω g adversary (r.1, forget r.2) h
/-- `worldGame_noBad` for the lazy-digest world. -/
theorem worldGameL_noBad (g : CanonTable.HiddenF) (adversary : AdversaryP)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) (Guess.Fam.phi g.1 g.2) (worldGameL hU ω adversary) initL r ≠ 0)
    (hno : ¬OverflowIn (wA hU ω g) r.1.2.1) : ¬Guess.Fam.Bad r.2 := by
  have h := fixed_inline_nonzero (digestOf ω) (nonceOf ω) (Guess.Fam.phi g.1 g.2) _ initL
    (SigGolfCandidate.T3.Security.BPair.consistent_empty _ _) r hr
  rw [forget_initL] at h
  change fixedRun env (Guess.Fam.phi g.1 g.2) (simulateQ (inlineAux ω) (worldGameL hU ω adversary)) init
    (r.1, forget r.2) ≠ 0 at h
  rw [← worldGame_inline] at h
  exact worldGame_noBad hU ω g adversary (r.1, forget r.2) h hno
end LazyCouple
end ClaudeWCT.W9.T3.Security.WPair
end
