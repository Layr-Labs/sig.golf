import SigGolfCandidate.T3.Secc.PairGuessLazyFree

section

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
section Table
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
theorem eval_nonce (ω : Omega U) (fts : FtsCoord → Digest) (m : Message) :
    evalWithAnswerFn (Omega.answers hU ω fts) (privateNonce m) = nonceOf ω m := by
  unfold privateNonce privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (CanonGraph.privateEquiv.symm (ω.secrets fts, ω.other) (.inr (.inl m))).extractLsb' 0 128 = _
  rw [privateEquiv_symm_apply, ChainGraph.joinOutput_low]
  exact splitEquiv_symm_other _ _ (nonceHalf m) (nonceHalf_not_secret m)
theorem signerRho_eq (ω : Omega U) (request : Request) : signerRho hU ω request = nonceOf ω request.message :=
  eval_nonce hU ω _ request.message
end Table
section Inline
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
noncomputable local instance instDecidableEqCache_pairGuessLazyCouple : DecidableEq T3.Cache := Classical.decEq _
noncomputable def inlineWith (D : digestInputs → HashOutput) (Nn : Message → Digest) : QueryImpl WSpecL (OracleComp WSpec)
  | .inl (.coin n) => (liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1)))
  | .inl (.birth x) => pure (rowVal D x)
  | .inl (.trial x) => pure (rowVal D x)
  | .inl (.nonce m) => pure (Nn m)
  | .inl (.expose _) => pure ()
  | .inr q => liftM (WSpec.query (.inr q))
noncomputable def inlineAux (ω : Omega U) : QueryImpl WSpecL (OracleComp WSpec) := inlineWith (digestOf ω) (nonceOf ω)
theorem eval_digestSearch_succ (A : Answers) (rho : Digest) (m : Message) (counter fuel : Nat) :
    evalWithAnswerFn A (digestSearch rho m counter (fuel + 1)) =
      if digestAdmissible (A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))))) = true then
        some (BitVec.ofNat 32 counter, A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter))))))
      else evalWithAnswerFn A (digestSearch rho m (counter + 1) fuel) := by
  rw [digestSearch, evalWithAnswerFn_bind]
  rw [show evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 counter)) =
    A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter))))) from eval_query' A _]
  by_cases h : digestAdmissible (A (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))))) = true
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
theorem inline_disclosures (ω : Omega U) (positions : List FtsCoord) :
    simulateQ (inlineAux ω) (positions.mapM discloseReq) =
      positions.mapM fun f => (liftM (WSpec.query (.inr (.inr f))) : OracleComp WSpec Digest) := by
  induction positions with
  | nil => rfl
  | cons first rest ih =>
      rw [List.mapM_cons, List.mapM_cons, simulateQ_bind]
      simp only [discloseReq, simulateQ_spec_query, simulateQ_bind, ih, simulateQ_pure]
      simp only [inlineAux, inlineWith]
theorem interactionL_pure (ω : Omega U) (published : T3.Cache) {α : Type} (value : α) :
    interactionL hU ω published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl
theorem interactionL_coin (ω : Omega U) (published : T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      (coinReqL n >>= fun coin => interactionL hU ω published (next coin)) := rfl
theorem interactionL_public (ω : Omega U) (published : T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (hashL hU ω x >>= fun answer => interactionL hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl
theorem interactionL_request (ω : Omega U) (published : T3.Cache) {α : Type} (request : Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (signL hU ω published request >>= fun signature => interactionL hU ω published (next signature) >>= fun rest =>
        pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl
theorem programL_pure (ω : Omega U) {β : Type} (value : β) : programL hU ω (pure value : M β) = pure (value, []) := rfl
theorem programL_coin (ω : Omega U) {β : Type} (n : Nat) (next : Fin (n + 1) → M β) :
    programL hU ω (liftM (T3.Spec.query (.inl (.inl n))) >>= next) =
      (coinReqL n >>= fun coin => programL hU ω (next coin)) := rfl
theorem programL_public (ω : Omega U) {β : Type} (x : HashInput) (next : HashOutput → M β) :
    programL hU ω (liftM (T3.Spec.query (.inl (.inr x))) >>= next) =
      (hashL hU ω x >>= fun answer => programL hU ω (next answer) >>= fun rest =>
        pure (rest.1, (x, answer) :: rest.2)) := rfl
theorem programL_private (ω : Omega U) {β : Type} (c : Coordinate) (next : HashOutput → M β) :
    programL hU ω (liftM (T3.Spec.query (.inr c)) >>= next) = programL hU ω (next 0) := rfl
noncomputable abbrev worldGameL (ω : Omega U) (adversary : AdversaryP) := worldGameCore hU ω adversary
end Inline
section Run
open SecretGuessObservation (fixedRun fixedImpl runWith)
def forget (s : WStateL) : WState := ⟨s.allowed, s.retired, s.guesses, s.probes, PUnit.unit⟩
def Consistent (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem) : Prop :=
  (∀ x a, mem.rows x = some a → a = rowVal D x) ∧ ∀ m v, mem.nonces m = some v → v = Nn m
theorem consistent_empty (D : digestInputs → HashOutput) (Nn : Message → Digest) : Consistent D Nn LazyMem.empty :=
  by
  refine ⟨fun x a h => ?_, fun m v h => ?_⟩
  · simp [LazyMem.empty] at h
  · simp [LazyMem.empty] at h
theorem rowStep_eager (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Consistent D Nn mem) (x : HashInput) (isBirth : Bool) :
    ∃ mem', Consistent D Nn mem' ∧ rowStep mem x isBirth (pure (rowVal D x)) = pure (rowVal D x, mem') := by
  have hreplay : Consistent D Nn (mem.replayRow x isBirth) := by
    unfold LazyMem.replayRow
    split
    · exact hm
    · exact hm
  unfold rowStep
  cases h : mem.rows x with
  | some a =>
      refine ⟨mem.replayRow x isBirth, hreplay, ?_⟩
      change pure (a, mem.replayRow x isBirth) = _
      rw [hm.1 x a h]
  | none =>
      by_cases hx : x ∈ digestInputs
      · refine ⟨mem.readRow x (rowVal D x) isBirth, ⟨?_, hm.2⟩, ?_⟩
        · intro y a hy
          change mem.rows.cacheQuery x (rowVal D x) y = some a at hy
          by_cases hyx : y = x
          · subst hyx
            rw [QueryCache.cacheQuery_self] at hy
            exact (Option.some.inj hy).symm
          · rw [QueryCache.cacheQuery_of_ne _ _ hyx] at hy
            exact hm.1 y a hy
        · change (if x ∈ digestInputs then _ else _) = _
          rw [if_pos hx, map_pure]
      · refine ⟨mem.replayRow x isBirth, hreplay, ?_⟩
        change (if x ∈ digestInputs then _ else _) = _
        rw [if_neg hx, rowVal, dif_neg hx]
theorem nonceStep_eager (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Consistent D Nn mem) (m : Message) :
    ∃ mem', Consistent D Nn mem' ∧ nonceStep mem m (pure (Nn m)) = pure (Nn m, mem') := by
  unfold nonceStep
  cases h : mem.nonces m with
  | some v =>
      refine ⟨mem, hm, ?_⟩
      change pure (v, mem) = _
      rw [hm.2 m v h]
  | none =>
      refine ⟨mem.drawNonce m (Nn m), ⟨hm.1, ?_⟩, map_pure _ _⟩
      intro m' v hv
      change Function.update mem.nonces m (some (Nn m)) m' = some v at hv
      by_cases hmm : m' = m
      · subst hmm
        rw [Function.update_self] at hv
        exact (Option.some.inj hv).symm
      · rw [Function.update_of_ne hmm] at hv
        exact hm.2 m' v hv
theorem coin_spmf (n : Nat) : (liftM (liftM (coinImpl n) : PMF (Fin (n + 1))) : SPMF (Fin (n + 1))) =
    (liftM (PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) := evalSPMF_query (spec := unifSpec) n
theorem fixed_aux_pure {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest) (fts : FtsCoord → Digest)
    (s : WStateL) (input : AuxL) (v : AuxSpecL.Range input) (mem' : LazyMem)
    (h : (envE D Nn).auxiliary s input = pure (v, mem'))
    (next : AuxSpecL.Range input → OracleComp WSpecL α) :
    runWith (fixedImpl (envE D Nn) fts) (liftM (WSpecL.query (.inl input)) >>= next) s =
      runWith (fixedImpl (envE D Nn) fts) (next v) { s with memory := mem' } := by
  rw [SecretGuessObservation.runWith_query_bind]
  change ((fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((envE D Nn).auxiliary s input) : SPMF _)) >>= _ = _
  rw [h, liftM_pure, map_pure, pure_bind]
theorem fixed_inline {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest) (fts : FtsCoord → Digest)
    (W : OracleComp WSpecL α) (s : WStateL) (hs : Consistent D Nn s.memory) :
    (fun r => (r.1, forget r.2)) <$> fixedRun (envE D Nn) fts W s =
      fixedRun env fts (simulateQ (inlineWith D Nn) W) (forget s) := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure a => simp only [fixedRun, SecretGuessObservation.runWith_pure, simulateQ_pure, map_pure]
  | query_bind input next ih =>
      rcases input with input | (⟨f, c⟩ | f)
      · cases input with
        | coin n =>
            rw [fixedRun, SecretGuessObservation.runWith_query_bind, map_bind, simulateQ_bind, simulateQ_spec_query]
            change ((fun result => (result.1, { s with memory := result.2 })) <$>
              (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _)) >>= _ =
              fixedRun env fts ((liftM (WSpec.query (.inl n)) : OracleComp WSpec _) >>= fun c =>
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
                runWith (fixedImpl env fts) (simulateQ (inlineWith D Nn) (next result.1)) result.2)).symm)
        | birth x =>
            obtain ⟨mem', hc, h⟩ := rowStep_eager D Nn s.memory hs x true
            rw [fixedRun, fixed_aux_pure D Nn fts s (.birth x) (rowVal D x) mem' h, simulateQ_bind, simulateQ_spec_query]
            change _ = fixedRun env fts (pure (rowVal D x) >>= fun u => simulateQ (inlineWith D Nn) (next u)) (forget s)
            rw [pure_bind]
            exact ih _ _ hc
        | trial x =>
            obtain ⟨mem', hc, h⟩ := rowStep_eager D Nn s.memory hs x false
            rw [fixedRun, fixed_aux_pure D Nn fts s (.trial x) (rowVal D x) mem' h, simulateQ_bind, simulateQ_spec_query]
            change _ = fixedRun env fts (pure (rowVal D x) >>= fun u => simulateQ (inlineWith D Nn) (next u)) (forget s)
            rw [pure_bind]
            exact ih _ _ hc
        | nonce m =>
            obtain ⟨mem', hc, h⟩ := nonceStep_eager D Nn s.memory hs m
            rw [fixedRun, fixed_aux_pure D Nn fts s (.nonce m) (Nn m) mem' h, simulateQ_bind, simulateQ_spec_query]
            change _ = fixedRun env fts (pure (Nn m) >>= fun u => simulateQ (inlineWith D Nn) (next u)) (forget s)
            rw [pure_bind]
            exact ih _ _ hc
        | expose o =>
            rw [fixedRun, fixed_aux_pure D Nn fts s (.expose o) () (s.memory.expose o) rfl, simulateQ_bind, simulateQ_spec_query]
            change _ = fixedRun env fts (pure () >>= fun u => simulateQ (inlineWith D Nn) (next u)) (forget s)
            rw [pure_bind]
            exact ih _ _ ⟨hs.1, hs.2⟩
      · rw [fixedRun, SecretGuessObservation.runWith_query_bind, map_bind, simulateQ_bind, simulateQ_spec_query]
        change (pure (decide (fts f = c), SecretGuessObservation.afterTrial (envE D Nn) s f c (decide (fts f = c))) >>= _) =
          fixedRun env fts ((liftM (WSpec.query (.inr (.inl (f, c)))) : OracleComp WSpec Bool) >>= fun u =>
            simulateQ (inlineWith D Nn) (next u)) (forget s)
        rw [pure_bind, fixedRun, SecretGuessObservation.runWith_query_bind]
        change _ = (pure (decide (fts f = c), SecretGuessObservation.afterTrial env (forget s) f c (decide (fts f = c))) >>= _)
        rw [pure_bind]
        exact ih _ _ hs
      · rw [fixedRun, SecretGuessObservation.runWith_query_bind, map_bind, simulateQ_bind, simulateQ_spec_query]
        change (pure (fts f, SecretGuessObservation.afterDisclosure (envE D Nn) s f (fts f)) >>= _) =
          fixedRun env fts ((liftM (WSpec.query (.inr (.inr f)))  : OracleComp WSpec Digest) >>= fun u =>
            simulateQ (inlineWith D Nn) (next u)) (forget s)
        rw [pure_bind, fixedRun, SecretGuessObservation.runWith_query_bind]
        change _ = (pure (fts f, SecretGuessObservation.afterDisclosure env (forget s) f (fts f)) >>= _)
        rw [pure_bind]
        exact ih _ _ hs
theorem fixed_inline_nonzero {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest)
    (fts : FtsCoord → Digest) (W : OracleComp WSpecL α) (s : WStateL) (hs : Consistent D Nn s.memory)
    (r : α × WStateL) (hr : fixedRun (envE D Nn) fts W s r ≠ 0) :
    fixedRun env fts (simulateQ (inlineWith D Nn) W) (forget s) (r.1, forget r.2) ≠ 0 := by
  rw [← fixed_inline D Nn fts W s hs]
  have hm : r ∈ support (fixedRun (envE D Nn) fts W s) := by
    simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr
  have h : (r.1, forget r.2) ∈ support ((fun r => (r.1, forget r.2)) <$> fixedRun (envE D Nn) fts W s) := by
    rw [support_map]
    exact ⟨r, hm, rfl⟩
  simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using h
end Run
section LazyCouple
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
open SecretGuessObservation (fixedRun)
theorem forget_initL : forget initL = init := rfl
end LazyCouple
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
section Ghost
open SecretGuessObservation (fixedRun fixedImpl runWith)
theorem runL_bind_nonzero {β γ : Type} (E : SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem)
    (fts : FtsCoord → Digest) (first : OracleComp WSpecL β) (next : β → OracleComp WSpecL γ) (s : WStateL)
    (r : γ × WStateL) (hr : fixedRun E fts (first >>= next) s r ≠ 0) :
    ∃ mid, fixedRun E fts first s mid ≠ 0 ∧ fixedRun E fts (next mid.1) mid.2 r ≠ 0 := by
  unfold fixedRun runWith at hr ⊢
  rw [simulateQ_bind, StateT.run_bind, RetainedObservation.bind_nonzero] at hr
  exact hr
theorem runL_pure_nonzero {β : Type} (E : SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem)
    (fts : FtsCoord → Digest) (v : β) (s : WStateL) (r : β × WStateL) (hr : fixedRun E fts (pure v) s r ≠ 0) :
    r = (v, s) := by
  unfold fixedRun at hr
  rw [SecretGuessObservation.runWith_pure] at hr
  simpa only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr
structure Grows (m m' : LazyMem) : Prop where
  rows : ∀ x a, m.rows x = some a → m'.rows x = some a
  births : ∀ a ∈ m.births, a ∈ m'.births
  trials : ∀ x ∈ m.trials, x ∈ m'.trials
  exposures : ∀ o ∈ m.exposures, o ∈ m'.exposures
theorem Grows.refl (m : LazyMem) : Grows m m := ⟨fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩
theorem Grows.trans {m1 m2 m3 : LazyMem} (h1 : Grows m1 m2) (h2 : Grows m2 m3) : Grows m1 m3 :=
  ⟨fun x a h => h2.rows x a (h1.rows x a h), fun a h => h2.births a (h1.births a h),
    fun x h => h2.trials x (h1.trials x h), fun o h => h2.exposures o (h1.exposures o h)⟩
def Good (D : digestInputs → HashOutput) (Nn : Message → Digest) (m : LazyMem) : Prop :=
  Consistent D Nn m ∧ ∀ x a, m.rows x = some a → a ∈ m.births ∨ x ∈ m.trials
theorem good_empty (D : digestInputs → HashOutput) (Nn : Message → Digest) : Good D Nn LazyMem.empty :=
  ⟨consistent_empty D Nn, fun x a h => by simp [LazyMem.empty] at h⟩
theorem replayRow_true (mem : LazyMem) (x : HashInput) : mem.replayRow x true = mem := by
  simp [LazyMem.replayRow]
theorem replayRow_false (mem : LazyMem) (x : HashInput) :
    mem.replayRow x false = { mem with trials := mem.trials ++ [x] } := by
  simp [LazyMem.replayRow]
theorem readRow_true (mem : LazyMem) (x : HashInput) (a : HashOutput) :
    mem.readRow x a true = { mem with rows := mem.rows.cacheQuery x a, births := mem.births ++ [a] } := by
  simp [LazyMem.readRow]
theorem readRow_false (mem : LazyMem) (x : HashInput) (a : HashOutput) :
    mem.readRow x a false = { mem with rows := mem.rows.cacheQuery x a, trials := mem.trials ++ [x] } := by
  simp [LazyMem.readRow]
theorem cacheQuery_good (D : digestInputs → HashOutput) (mem : LazyMem) (x : HashInput) (y : HashInput) (b : HashOutput)
    (hy : mem.rows.cacheQuery x (rowVal D x) y = some b) :
    b = rowVal D x ∧ y = x ∨ mem.rows y = some b := by
  by_cases hyx : y = x
  · subst hyx
    rw [QueryCache.cacheQuery_self] at hy
    exact Or.inl ⟨(Option.some.inj hy).symm, rfl⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ hyx] at hy
    exact Or.inr hy
theorem rowStep_ghost (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Good D Nn mem) (x : HashInput) (isBirth : Bool) :
    ∃ mem', rowStep mem x isBirth (pure (rowVal D x)) = pure (rowVal D x, mem') ∧ Good D Nn mem' ∧
      Grows mem mem' ∧ (x ∈ digestInputs → mem'.rows x = some (rowVal D x)) := by
  have hreplay : Good D Nn (mem.replayRow x isBirth) ∧ Grows mem (mem.replayRow x isBirth) := by
    cases isBirth
    · rw [replayRow_false]
      refine ⟨⟨hm.1, fun y a hy => ?_⟩, ⟨fun _ _ h => h, fun _ h => h, fun y h => List.mem_append_left _ h,
        fun _ h => h⟩⟩
      rcases hm.2 y a hy with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_append_left _ h)
    · rw [replayRow_true]
      exact ⟨hm, Grows.refl mem⟩
  unfold rowStep
  cases h : mem.rows x with
  | some a =>
      have ha := hm.1.1 x a h
      refine ⟨mem.replayRow x isBirth, ?_, hreplay.1, hreplay.2, fun _ => ?_⟩
      · change pure (a, mem.replayRow x isBirth) = _
        rw [ha]
      · rw [hreplay.2.rows x a h, ha]
  | none =>
      by_cases hx : x ∈ digestInputs
      · refine ⟨mem.readRow x (rowVal D x) isBirth, ?_, ?_, ?_, fun _ => ?_⟩
        · change (if x ∈ digestInputs then _ else _) = _
          rw [if_pos hx, map_pure]
        · cases isBirth
          · rw [readRow_false]
            refine ⟨⟨fun y b hy => ?_, hm.1.2⟩, fun y b hy => ?_⟩
            · rcases cacheQuery_good D mem x y b hy with ⟨rfl, rfl⟩ | hy
              · rfl
              · exact hm.1.1 y b hy
            · rcases cacheQuery_good D mem x y b hy with ⟨rfl, rfl⟩ | hy
              · exact Or.inr (List.mem_append_right _ (List.mem_singleton_self _))
              · rcases hm.2 y b hy with h | h
                · exact Or.inl h
                · exact Or.inr (List.mem_append_left _ h)
          · rw [readRow_true]
            refine ⟨⟨fun y b hy => ?_, hm.1.2⟩, fun y b hy => ?_⟩
            · rcases cacheQuery_good D mem x y b hy with ⟨rfl, rfl⟩ | hy
              · rfl
              · exact hm.1.1 y b hy
            · rcases cacheQuery_good D mem x y b hy with ⟨rfl, rfl⟩ | hy
              · exact Or.inl (List.mem_append_right _ (List.mem_singleton_self _))
              · rcases hm.2 y b hy with h | h
                · exact Or.inl (List.mem_append_left _ h)
                · exact Or.inr h
        · have hrows : ∀ y b, mem.rows y = some b → mem.rows.cacheQuery x (rowVal D x) y = some b := by
            intro y b hy
            have hyx : y ≠ x := by
              rintro rfl
              rw [h] at hy
              cases hy
            rw [QueryCache.cacheQuery_of_ne _ _ hyx]
            exact hy
          cases isBirth
          · rw [readRow_false]
            exact ⟨hrows, fun _ h => h, fun _ h => List.mem_append_left _ h, fun _ h => h⟩
          · rw [readRow_true]
            exact ⟨hrows, fun _ h => List.mem_append_left _ h, fun _ h => h, fun _ h => h⟩
        · cases isBirth
          · rw [readRow_false]
            exact QueryCache.cacheQuery_self _ _ _
          · rw [readRow_true]
            exact QueryCache.cacheQuery_self _ _ _
      · refine ⟨mem.replayRow x isBirth, ?_, hreplay.1, hreplay.2, fun h' => absurd h' hx⟩
        change (if x ∈ digestInputs then _ else _) = _
        rw [if_neg hx, rowVal, dif_neg hx]
theorem nonceStep_ghost (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Good D Nn mem) (m : Message) :
    ∃ mem', nonceStep mem m (pure (Nn m)) = pure (Nn m, mem') ∧ Good D Nn mem' ∧ Grows mem mem' := by
  unfold nonceStep
  cases h : mem.nonces m with
  | some v =>
      refine ⟨mem, ?_, hm, Grows.refl mem⟩
      change pure (v, mem) = _
      rw [hm.1.2 m v h]
  | none =>
      refine ⟨mem.drawNonce m (Nn m), map_pure _ _, ⟨⟨hm.1.1, ?_⟩, hm.2⟩,
        ⟨fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩⟩
      intro m' v hv
      change Function.update mem.nonces m (some (Nn m)) m' = some v at hv
      by_cases hmm : m' = m
      · subst hmm
        rw [Function.update_self] at hv
        exact (Option.some.inj hv).symm
      · rw [Function.update_of_ne hmm] at hv
        exact hm.1.2 m' v hv
theorem expose_ghost (D : digestInputs → HashOutput) (Nn : Message → Digest) (mem : LazyMem)
    (hm : Good D Nn mem) (o : Option HashOutput) : Good D Nn (mem.expose o) ∧ Grows mem (mem.expose o) :=
  ⟨hm, ⟨fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => List.mem_append_left _ h⟩⟩
theorem fixed_aux_single (D : digestInputs → HashOutput) (Nn : Message → Digest) (fts : FtsCoord → Digest)
    (s : WStateL) (input : AuxL) (v : AuxSpecL.Range input) (mem' : LazyMem)
    (h : (envE D Nn).auxiliary s input = pure (v, mem')) :
    fixedRun (envE D Nn) fts (liftM (WSpecL.query (.inl input))) s = pure (v, { s with memory := mem' }) := by
  rw [fixedRun, ← bind_pure (liftM (WSpecL.query (.inl input))), fixed_aux_pure D Nn fts s input v mem' h,
    SecretGuessObservation.runWith_pure]
theorem run_good {α : Type} (D : digestInputs → HashOutput) (Nn : Message → Digest) (fts : FtsCoord → Digest)
    (W : OracleComp WSpecL α) (s : WStateL) (hs : Good D Nn s.memory) (r : α × WStateL)
    (hr : fixedRun (envE D Nn) fts W s r ≠ 0) : Good D Nn r.2.memory ∧ Grows s.memory r.2.memory := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure a =>
      rw [runL_pure_nonzero _ fts a s r hr]
      exact ⟨hs, Grows.refl _⟩
  | query_bind input next ih =>
      rcases input with input | (⟨f, c⟩ | f)
      · cases input with
        | coin n =>
            unfold fixedRun at hr
            rw [SecretGuessObservation.runWith_query_bind, RetainedObservation.bind_nonzero] at hr
            obtain ⟨mid, hm, hr⟩ := hr
            have hmid : mid.2 = s := by
              change ((fun result => (result.1, { s with memory := result.2 })) <$>
                (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _)) mid ≠ 0 at hm
              rw [liftM_map, Functor.map_map] at hm
              simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
                SPMF.pure_apply_eq_zero_iff, not_not] at hm
              obtain ⟨c, _, rfl⟩ := hm
              rfl
            obtain ⟨h1, h2⟩ := ih mid.1 mid.2 (by rw [hmid]; exact hs) hr
            rw [hmid] at h2
            exact ⟨h1, h2⟩
        | birth x =>
            obtain ⟨mem', heq, hg, hgr, -⟩ := rowStep_ghost D Nn s.memory hs x true
            rw [fixedRun, fixed_aux_pure D Nn fts s (.birth x) (rowVal D x) mem' heq] at hr
            obtain ⟨h1, h2⟩ := ih _ _ hg hr
            exact ⟨h1, hgr.trans h2⟩
        | trial x =>
            obtain ⟨mem', heq, hg, hgr, -⟩ := rowStep_ghost D Nn s.memory hs x false
            rw [fixedRun, fixed_aux_pure D Nn fts s (.trial x) (rowVal D x) mem' heq] at hr
            obtain ⟨h1, h2⟩ := ih _ _ hg hr
            exact ⟨h1, hgr.trans h2⟩
        | nonce m =>
            obtain ⟨mem', heq, hg, hgr⟩ := nonceStep_ghost D Nn s.memory hs m
            rw [fixedRun, fixed_aux_pure D Nn fts s (.nonce m) (Nn m) mem' heq] at hr
            obtain ⟨h1, h2⟩ := ih _ _ hg hr
            exact ⟨h1, hgr.trans h2⟩
        | expose o =>
            rw [fixedRun, fixed_aux_pure D Nn fts s (.expose o) () (s.memory.expose o) rfl] at hr
            have he := expose_ghost D Nn s.memory hs o
            obtain ⟨h1, h2⟩ := ih () { s with memory := s.memory.expose o } he.1 hr
            exact ⟨h1, he.2.trans h2⟩
      · unfold fixedRun at hr
        rw [SecretGuessObservation.runWith_query_bind] at hr
        change ((pure (decide (fts f = c), SecretGuessObservation.afterTrial (envE D Nn) s f c (decide (fts f = c))) :
          SPMF (Bool × WStateL)) >>= fun mid => runWith (fixedImpl (envE D Nn) fts) (next mid.1) mid.2) r ≠ 0 at hr
        rw [pure_bind] at hr
        exact ih _ (SecretGuessObservation.afterTrial (envE D Nn) s f c (decide (fts f = c))) hs hr
      · unfold fixedRun at hr
        rw [SecretGuessObservation.runWith_query_bind] at hr
        change ((pure (fts f, SecretGuessObservation.afterDisclosure (envE D Nn) s f (fts f)) : SPMF (Digest × WStateL)) >>=
          fun mid => runWith (fixedImpl (envE D Nn) fts) (next mid.1) mid.2) r ≠ 0 at hr
        rw [pure_bind] at hr
        exact ih _ (SecretGuessObservation.afterDisclosure (envE D Nn) s f (fts f)) hs hr
end Ghost
section WorldGhost
open SecretGuessObservation (fixedRun fixedImpl runWith)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
noncomputable local instance instDecidableEqCache_pairGuessLazyGhost : DecidableEq T3.Cache := Classical.decEq _
theorem hashL_ghost (fts : FtsCoord → Digest) (x : HashInput) (s : WStateL)
    (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : HashOutput × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (hashL hU ω x) s r ≠ 0) (hx : x ∈ digestInputs) :
    r.2.memory.rows x = some r.1 := by
  have hd : decodeProbe x = none := by
    cases hd : decodeProbe x with
    | none => rfl
    | some p =>
        have hpx := eq_of_decodeProbe hd
        rw [hpx] at hx
        exact absurd hx (probeInput_not_digest p.1 p.2)
  unfold hashL at hr
  rw [hd] at hr
  dsimp only at hr
  rw [if_pos hx] at hr
  obtain ⟨mem', heq, -, -, hrow⟩ := rowStep_ghost (digestOf ω) (nonceOf ω) s.memory hs x true
  rw [birthReq, fixed_aux_single (digestOf ω) (nonceOf ω) fts s (.birth x) _ mem' heq] at hr
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  subst hr
  exact hrow hx
theorem finishL_some (fts : FtsCoord → Digest) (request : Request) (rho : Digest)
    (found : Option (BitVec 32 × HashOutput)) (s : WStateL) (r : Option Signature × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (finishL hU ω request rho found) s r ≠ 0)
    (σ : Signature) (hσ : r.1 = some σ) : ∃ c out, found = some (c, out) ∧ σ.rho = rho := by
  cases found with
  | none =>
      rw [runL_pure_nonzero _ fts _ s r hr] at hσ
      cases hσ
  | some found =>
      obtain ⟨c, out⟩ := found
      refine ⟨c, out, rfl, ?_⟩
      change fixedRun (envE (digestOf ω) (nonceOf ω)) fts (match signerLayers hU ω request out with
        | none => pure none
        | some pieces => do
            let values ← (openedPositions out).mapM discloseReq
            pure (some (Correctness.assembledSignature rho
              (openedValues (overwrite (openedPositions out) values) out,
                (signerForest hU ω out).2.1, (signerForest hU ω out).2.2) pieces))) s r ≠ 0 at hr
      cases hl : signerLayers hU ω request out with
      | none =>
          rw [hl] at hr
          rw [runL_pure_nonzero _ fts _ s r hr] at hσ
          cases hσ
      | some pieces =>
          rw [hl] at hr
          obtain ⟨mid, -, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
          rw [runL_pure_nonzero _ fts _ _ r hr] at hσ
          cases hσ
          exact Correctness.assembledSignature_rho _ _ _
theorem programL_ghost (fts : FtsCoord → Digest) {β : Type} (program : M β) (s : WStateL)
    (hs : Good (digestOf ω) (nonceOf ω) s.memory) (r : (β × List Wots.Entry) × WStateL)
    (hr : fixedRun (envE (digestOf ω) (nonceOf ω)) fts (programL hU ω program) s r ≠ 0) :
    ∀ x a, (x, a) ∈ r.1.2 → x ∈ digestInputs → r.2.memory.rows x = some a := by
  induction program using OracleComp.inductionOn generalizing s r with
  | pure value =>
      rw [programL_pure] at hr
      rw [runL_pure_nonzero _ fts _ s r hr]
      exact fun _ _ h => (by simp at h)
  | query_bind input next ih =>
      rcases input with (n | x) | c
      · rw [programL_coin] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        exact ih m1.1 m1.2 (run_good _ _ fts _ s hs m1 h1).1 r hr
      · rw [programL_public] at hr
        obtain ⟨m1, h1, hr⟩ := runL_bind_nonzero _ fts _ _ s r hr
        obtain ⟨m2, h2, hr⟩ := runL_bind_nonzero _ fts _ _ m1.2 r hr
        rw [runL_pure_nonzero _ fts _ _ r hr]
        have g1 := run_good _ _ fts _ s hs m1 h1
        have g2 := run_good _ _ fts _ m1.2 g1.1 m2 h2
        have i2 := ih m1.1 m1.2 g1.1 m2 h2
        intro y a hy hdy
        rcases List.mem_cons.mp hy with he | hy
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          exact g2.2.rows _ _ (hashL_ghost hU ω fts y s hs m1 h1 hdy)
        · exact i2 y a hy hdy
      · rw [programL_private] at hr
        exact ih (0 : HashOutput) s hs r hr
end WorldGhost
end SigGolfCandidate.T3.Security.BPair
end
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
section Uniform
theorem evalSPMF_uniform {X : Type} [Fintype X] [Nonempty X] (I : SampleableType X) :
    𝒮[(@uniformSample X I : ProbComp X)] = (liftM (PMF.uniformOfFintype X) : SPMF X) := by
  apply SPMF.ext
  intro x
  rw [SPMF.liftM_apply, PMF.uniformOfFintype_apply, ← SPMF.probOutput_eq_apply, probOutput_evalSPMF]
  exact @probOutput_uniformSample X I _ x
theorem uniform_update {ι β γ : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β] (i : ι)
    (g : β → (ι → β) → SPMF γ) (hg : ∀ a T c, g a (Function.update T i c) = g a T) :
    ((liftM (PMF.uniformOfFintype (ι → β)) : SPMF (ι → β)) >>= fun T => g (T i) T) =
      ((liftM (PMF.uniformOfFintype β) : SPMF β) >>= fun a =>
        (liftM (PMF.uniformOfFintype (ι → β)) : SPMF (ι → β)) >>= fun T => g a T) := by
  let IT : SampleableType (ι → β) := SampleableType.ofFintype _
  let Ia : SampleableType β := SampleableType.ofFintype _
  let IP : SampleableType ((ι → β) × β) := SampleableType.ofFintype _
  let f : (ι → β) × β → (ι → β) × β := fun p => (Function.update p.1 i p.2, p.1 i)
  have hinv : ∀ p, f (f p) = p := by
    rintro ⟨T, a⟩
    simp only [f, Function.update_self, Function.update_idem, Function.update_eq_self]
  have hf : Function.Bijective f := ⟨fun p q h => by rw [← hinv p, ← hinv q, h], fun p => ⟨f p, hinv p⟩⟩
  have hb := @evalSPMF_map_bijective_uniform_cross ((ι → β) × β) IP ((ι → β) × β) IP _ f hf
  have hp := @FullGame.uniform_product (ι → β) β _ _ IT Ia IP
  rw [← evalSPMF_uniform IT, ← evalSPMF_uniform Ia]
  calc (𝒮[(@uniformSample _ IT : ProbComp (ι → β))] >>= fun T => g (T i) T)
      = (𝒮[(@uniformSample _ IT : ProbComp (ι → β))] >>= fun T =>
          𝒮[(@uniformSample _ Ia : ProbComp β)] >>= fun _ => g (T i) T) := by
        simp only [evalSPMF_uniform Ia, RetainedObservation.lift_bind_const]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (ι → β)) >>= fun T => (@uniformSample _ Ia : ProbComp β) >>= fun a =>
          pure (T, a)] >>= fun p => g (p.1 i) p.1) := by
        simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((ι → β) × β))] >>= fun p => g (p.1 i) p.1) := by rw [hp]
    _ = (𝒮[f <$> (@uniformSample _ IP : ProbComp ((ι → β) × β))] >>= fun p => g (p.1 i) p.1) := by rw [hb]
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((ι → β) × β))] >>= fun p => g p.2 (Function.update p.1 i p.2)) := by
        rw [evalSPMF_map, bind_map_left]
        simp only [f, Function.update_self]
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((ι → β) × β))] >>= fun p => g p.2 p.1) := by simp only [hg]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (ι → β)) >>= fun T => (@uniformSample _ Ia : ProbComp β) >>= fun a =>
          pure (T, a)] >>= fun p => g p.2 p.1) := by rw [hp]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (ι → β))] >>= fun T =>
          𝒮[(@uniformSample _ Ia : ProbComp β)] >>= fun a => g a T) := by
        simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
    _ = _ := RetainedObservation.bind_comm _ _ _
noncomputable def patch {α σ β : Type} (e : σ → α) (T : α → β) (D : σ → β) (a : α) : β :=
  @dite _ (∃ s, e s = a) (Classical.propDecidable _) (fun h => D (Classical.choose h)) (fun _ => T a)
theorem patch_e {α σ β : Type} {e : σ → α} (he : Function.Injective e) (T : α → β) (D : σ → β) (s : σ) :
    patch e T D (e s) = D s := by
  have h : ∃ s', e s' = e s := ⟨s, rfl⟩
  rw [patch, dif_pos h]
  exact congrArg D (he (Classical.choose_spec h))
theorem patch_of {α σ β : Type} (e : σ → α) (T : α → β) (D : σ → β) (a : α) (ha : ∀ s, e s ≠ a) :
    patch e T D a = T a := by
  rw [patch, dif_neg (fun h => ha _ (Classical.choose_spec h))]
theorem patch_uniform {α σ β γ : Type} [Fintype α] [Fintype σ] [Fintype β] [Nonempty β] [DecidableEq α]
    [DecidableEq σ] {e : σ → α} (he : Function.Injective e) (IT : SampleableType (α → β))
    (ID : SampleableType (σ → β)) (k : (α → β) → SPMF γ) :
    (𝒮[(@uniformSample _ IT : ProbComp (α → β))] >>= fun T => 𝒮[(@uniformSample _ ID : ProbComp (σ → β))] >>=
      fun D => k (patch e T D)) = 𝒮[(@uniformSample _ IT : ProbComp (α → β))] >>= k := by
  let IP : SampleableType ((α → β) × (σ → β)) := SampleableType.ofFintype _
  let Φ : (α → β) × (σ → β) → (α → β) × (σ → β) := fun p => (patch e p.1 p.2, p.1 ∘ e)
  have hinv : ∀ p, Φ (Φ p) = p := by
    rintro ⟨T, D⟩
    refine Prod.ext (funext fun a => ?_) (funext fun s => ?_)
    · change patch e (patch e T D) (T ∘ e) a = T a
      by_cases h : ∃ s, e s = a
      · obtain ⟨s, rfl⟩ := h
        rw [patch_e he]
        rfl
      · have h' : ∀ s, e s ≠ a := fun s hs => h ⟨s, hs⟩
        rw [patch_of e _ _ a h', patch_of e _ _ a h']
    · exact patch_e he T D s
  have hΦ : Function.Bijective Φ := ⟨fun p q h => by rw [← hinv p, ← hinv q, h], fun p => ⟨Φ p, hinv p⟩⟩
  have hb := @evalSPMF_map_bijective_uniform_cross ((α → β) × (σ → β)) IP ((α → β) × (σ → β)) IP _ Φ hΦ
  have hp := @FullGame.uniform_product (α → β) (σ → β) _ _ IT ID IP
  calc _ = (𝒮[(@uniformSample _ IT : ProbComp (α → β)) >>= fun T => (@uniformSample _ ID : ProbComp (σ → β)) >>= fun D =>
          pure (T, D)] >>= fun p => k (Φ p).1) := by
        simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
        rfl
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((α → β) × (σ → β)))] >>= fun p => k (Φ p).1) := by rw [hp]
    _ = (𝒮[Φ <$> (@uniformSample _ IP : ProbComp ((α → β) × (σ → β)))] >>= fun p => k p.1) := by
        rw [evalSPMF_map, bind_map_left]
    _ = (𝒮[(@uniformSample _ IP : ProbComp ((α → β) × (σ → β)))] >>= fun p => k p.1) := by rw [hb]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (α → β)) >>= fun T => (@uniformSample _ ID : ProbComp (σ → β)) >>= fun D =>
          pure (T, D)] >>= fun p => k p.1) := by rw [hp]
    _ = (𝒮[(@uniformSample _ IT : ProbComp (α → β))] >>= fun T =>
          𝒮[(@uniformSample _ ID : ProbComp (σ → β))] >>= fun _ => k T) := by
        simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
    _ = _ := by simp only [evalSPMF_uniform ID, RetainedObservation.lift_bind_const]
end Uniform
noncomputable instance instSampleableDigestRows : SampleableType (digestInputs → HashOutput) :=
  SampleableType.ofFintype _
noncomputable instance instSampleableNonceTables : SampleableType (Message → Digest) := SampleableType.ofFintype _
section OmegaPatch
variable {U : Finset HashInput} (hsub : digestInputs ⊆ U)
def digestEmb : digestInputs → U := fun x => ⟨x.1, hsub x.2⟩
theorem digestEmb_injective : Function.Injective (digestEmb hsub) :=
  fun x y h => Subtype.ext (by have h' := congrArg Subtype.val h; exact h')
theorem nonceOther_injective : Function.Injective nonceOther := by
  intro m m' h
  have h1 := congrArg (fun o : CanonGraph.OtherHalf => o.1.1) h
  change (Sum.inr (Sum.inl m) : Coordinate) = Sum.inr (Sum.inl m') at h1
  exact Sum.inl.inj (Sum.inr.inj h1)
noncomputable def patchOmega (ω : Omega U) (D : digestInputs → HashOutput) (Nn : Message → Digest) : Omega U :=
  ⟨ω.seeds, patch nonceOther ω.other Nn, ω.labels, patch (digestEmb hsub) ω.residual D⟩
theorem digestOf_patch (ω : Omega U) (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    digestOf (patchOmega hsub ω D Nn) = D := by
  funext x
  change finiteHashAnswer ∅ U (patch (digestEmb hsub) ω.residual D) x.1 = D x
  rw [finiteHashAnswer_none ∅ U _ _ (hsub x.2) rfl]
  exact patch_e (digestEmb_injective hsub) _ _ x
theorem nonceOf_patch (ω : Omega U) (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    nonceOf (patchOmega hsub ω D Nn) = Nn :=
  funext fun m => patch_e nonceOther_injective ω.other Nn m
theorem sameRest_patch (ω : Omega U) (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    SameRest ω (patchOmega hsub ω D Nn) := by
  refine ⟨rfl, rfl, fun x hx => (patch_of (digestEmb hsub) ω.residual D x ?_).symm,
    fun h hh => (patch_of nonceOther ω.other Nn h ?_).symm⟩
  · intro y hy
    apply hx
    rw [← hy]
    exact y.2
  · intro m hm
    exact hh m hm.symm
end OmegaPatch
section OmegaLaw
attribute [local instance] instSampleableTypeSeeds_pairGuessFinal instSampleableTypeForallFtsCoordDigest_pairGuessFinal
  CanonGraph.instSampleableTypeSecrets CanonGraph.instSampleableTypeOtherHalves CanonGraph.instSampleableTypeLabels_1
theorem digest_subset (adversary : AdversaryP) : digestInputs ⊆ Wots.referenceInputs adversary :=
  digestInputs_subset_publicUniverse.trans (referenceInputs_universe' adversary)
theorem omegaLaw_patch (adversary : AdversaryP) {γ : Type} (k : Omega (Wots.referenceInputs adversary) → SPMF γ) :
    (𝒮[omegaLaw adversary] >>= fun ω => 𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D =>
      𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn => k (patchOmega (digest_subset adversary) ω D Nn)) =
      𝒮[omegaLaw adversary] >>= k := by
  unfold omegaLaw
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  refine bind_congr fun seeds => ?_
  have step1 : ∀ (other : CanonGraph.OtherHalves) (labels : CanonGraph.Labels),
      (𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput)
        (CanonGraph.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _) : ProbComp _)] >>=
        fun residual => 𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D =>
        𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          k (patchOmega (digest_subset adversary) ⟨seeds, other, labels, residual⟩ D Nn)) =
      (𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput)
        (CanonGraph.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _) : ProbComp _)] >>=
        fun residual => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          k ⟨seeds, patch nonceOther other Nn, labels, residual⟩) := by
    intro other labels
    exact patch_uniform (digestEmb_injective (digest_subset adversary)) _ _
      (fun residual => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
        k ⟨seeds, patch nonceOther other Nn, labels, residual⟩)
  simp only [step1]
  have step2 : ∀ other : CanonGraph.OtherHalves,
      (𝒮[($ᵗ CanonGraph.Labels : ProbComp _)] >>= fun labels =>
        𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput)
          (CanonGraph.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _) : ProbComp _)] >>=
        fun residual => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          k ⟨seeds, patch nonceOther other Nn, labels, residual⟩) =
      (𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn => 𝒮[($ᵗ CanonGraph.Labels : ProbComp _)] >>= fun labels =>
        𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput)
          (CanonGraph.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _) : ProbComp _)] >>=
        fun residual => k ⟨seeds, patch nonceOther other Nn, labels, residual⟩) := by
    intro other
    calc _ = (𝒮[($ᵗ CanonGraph.Labels : ProbComp _)] >>= fun labels =>
          𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput)
            (CanonGraph.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _) : ProbComp _)] >>=
          fun residual => k ⟨seeds, patch nonceOther other Nn, labels, residual⟩) :=
          bind_congr fun labels => RetainedObservation.bind_comm _ _ _
      _ = _ := RetainedObservation.bind_comm _ _ _
  simp only [step2]
  exact patch_uniform nonceOther_injective _ _ (fun other => 𝒮[($ᵗ CanonGraph.Labels : ProbComp _)] >>= fun labels =>
    𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput)
      (CanonGraph.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _) : ProbComp _)] >>=
    fun residual => k ⟨seeds, other, labels, residual⟩)
end OmegaLaw
section Steps
open SecretGuessObservation (forcedRun forcedImpl lazyImpl runWith afterTrial afterDisclosure forcedTrial)
variable (slot : Nat)
theorem rowStep_some (mem : LazyMem) (x : HashInput) (b : Bool) (src : PMF HashOutput) (a : HashOutput)
    (h : mem.rows x = some a) : rowStep mem x b src = pure (a, mem.replayRow x b) := by
  unfold rowStep
  rw [h]
theorem rowStep_out (mem : LazyMem) (x : HashInput) (b : Bool) (src : PMF HashOutput) (h : mem.rows x = none)
    (hx : x ∉ digestInputs) : rowStep mem x b src = pure (0, mem.replayRow x b) := by
  unfold rowStep
  rw [h, if_neg hx]
theorem rowStep_in (mem : LazyMem) (x : HashInput) (b : Bool) (src : PMF HashOutput) (h : mem.rows x = none)
    (hx : x ∈ digestInputs) : rowStep mem x b src = (fun a => (a, mem.readRow x a b)) <$> src := by
  unfold rowStep
  rw [h, if_pos hx]
theorem nonceStep_some (mem : LazyMem) (m : Message) (src : PMF Digest) (v : Digest) (h : mem.nonces m = some v) :
    nonceStep mem m src = pure (v, mem) := by
  unfold nonceStep
  rw [h]
theorem nonceStep_none (mem : LazyMem) (m : Message) (src : PMF Digest) (h : mem.nonces m = none) :
    nonceStep mem m src = (fun v => (v, mem.drawNonce m v)) <$> src := by
  unfold nonceStep
  rw [h]
variable (rs : HashInput → PMF HashOutput) (ns : Message → PMF Digest)
theorem step_aux (s : WStateL) (input : AuxL) :
    (forcedImpl (envWith rs ns) slot (.inl input)).run s =
      (fun result => (result.1, { s with memory := result.2 })) <$>
        (liftM (auxWith rs ns s input) : SPMF (AuxSpecL.Range input × LazyMem)) := rfl
theorem step_coin (s : WStateL) (n : Nat) :
    (forcedImpl (envWith rs ns) slot (.inl (.coin n))).run s =
      (fun c => (c, s)) <$> (liftM (PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) := by
  rw [step_aux]
  change (fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM ((fun c => (c, s.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))) : SPMF _) = _
  rw [liftM_map, Functor.map_map]
theorem step_expose (s : WStateL) (o : Option HashOutput) :
    (forcedImpl (envWith rs ns) slot (.inl (.expose o))).run s = pure ((), { s with memory := s.memory.expose o }) := by
  rw [step_aux]
  change (fun result => (result.1, { s with memory := result.2 })) <$>
    (liftM (pure ((), s.memory.expose o) : PMF _) : SPMF _) = _
  rw [liftM_pure, map_pure]
theorem step_birth (s : WStateL) (x : HashInput) :
    (forcedImpl (envWith rs ns) slot (.inl (.birth x))).run s =
      (fun result => (result.1, { s with memory := result.2 })) <$>
        (liftM (rowStep s.memory x true (rs x)) : SPMF (HashOutput × LazyMem)) := rfl
theorem step_trial (s : WStateL) (x : HashInput) :
    (forcedImpl (envWith rs ns) slot (.inl (.trial x))).run s =
      (fun result => (result.1, { s with memory := result.2 })) <$>
        (liftM (rowStep s.memory x false (rs x)) : SPMF (HashOutput × LazyMem)) := rfl
theorem step_nonce (s : WStateL) (m : Message) :
    (forcedImpl (envWith rs ns) slot (.inl (.nonce m))).run s =
      (fun result => (result.1, { s with memory := result.2 })) <$>
        (liftM (nonceStep s.memory m (ns m)) : SPMF (Digest × LazyMem)) := rfl
theorem step_guess (s : WStateL) (f : FtsCoord) (c : Digest) :
    (forcedImpl (envWith rs ns) slot (.inr (.inl (f, c)))).run s =
      (fun hit => (hit, { afterTrial (envWith rs ns) s f c hit with memory := s.memory })) <$> forcedTrial slot s f c := rfl
theorem step_disclose (s : WStateL) (f : FtsCoord) :
    (forcedImpl (envWith rs ns) slot (.inr (.inr f))).run s =
      (fun v => (v, { afterDisclosure (envWith rs ns) s f v with memory := s.memory })) <$>
        UniformTableCompletion.cell (s.allowed f) := rfl
theorem afterTrial_sources (rs' : HashInput → PMF HashOutput) (ns' : Message → PMF Digest) (s : WStateL)
    (f : FtsCoord) (c : Digest) (hit : Bool) :
    afterTrial (envWith rs ns) s f c hit = afterTrial (envWith rs' ns') s f c hit := rfl
theorem afterDisclosure_sources (rs' : HashInput → PMF HashOutput) (ns' : Message → PMF Digest) (s : WStateL)
    (f : FtsCoord) (v : Digest) :
    afterDisclosure (envWith rs ns) s f v = afterDisclosure (envWith rs' ns') s f v := rfl
end Steps
section Congr
open SecretGuessObservation (forcedRun forcedImpl runWith)
def Agree (D D' : digestInputs → HashOutput) (Nn Nn' : Message → Digest) (mem : LazyMem) : Prop :=
  (∀ y : digestInputs, mem.rows y.1 = none → D y = D' y) ∧ ∀ m, mem.nonces m = none → Nn m = Nn' m
theorem rowVal_agree {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (x : HashInput) (hx : mem.rows x = none) : rowVal D x = rowVal D' x := by
  unfold rowVal
  by_cases hd : x ∈ digestInputs
  · rw [dif_pos hd, dif_pos hd]
    exact h.1 ⟨x, hd⟩ hx
  · rw [dif_neg hd, dif_neg hd]
theorem agree_replay {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (x : HashInput) (b : Bool) : Agree D D' Nn Nn' (mem.replayRow x b) := by
  cases b
  · rw [replayRow_false]
    exact h
  · rw [replayRow_true]
    exact h
theorem agree_read {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (x : HashInput) (a : HashOutput) (b : Bool) :
    Agree D D' Nn Nn' (mem.readRow x a b) := by
  have hrows : ∀ y : digestInputs, (mem.rows.cacheQuery x a) y.1 = none → D y = D' y := by
    intro y hy
    by_cases hyx : y.1 = x
    · rw [hyx, QueryCache.cacheQuery_self] at hy
      cases hy
    · rw [QueryCache.cacheQuery_of_ne _ _ hyx] at hy
      exact h.1 y hy
  cases b
  · rw [readRow_false]
    exact ⟨hrows, h.2⟩
  · rw [readRow_true]
    exact ⟨hrows, h.2⟩
theorem agree_draw {D D' : digestInputs → HashOutput} {Nn Nn' : Message → Digest} {mem : LazyMem}
    (h : Agree D D' Nn Nn' mem) (m : Message) (v : Digest) : Agree D D' Nn Nn' (mem.drawNonce m v) := by
  refine ⟨h.1, fun m' hm' => ?_⟩
  change Function.update mem.nonces m (some v) m' = none at hm'
  by_cases hmm : m' = m
  · rw [hmm, Function.update_self] at hm'
    cases hm'
  · rw [Function.update_of_ne hmm] at hm'
    exact h.2 m' hm'
theorem forced_congr {α : Type} (D D' : digestInputs → HashOutput) (Nn Nn' : Message → Digest) (slot : Nat)
    (W : OracleComp WSpecL α) (s : WStateL) (h : Agree D D' Nn Nn' s.memory) :
    forcedRun (envE D Nn) slot W s = forcedRun (envE D' Nn') slot W s := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind input next ih =>
      simp only [forcedRun, SecretGuessObservation.runWith_query_bind]
      rcases input with input | (⟨f, c⟩ | f)
      · cases input with
        | coin n =>
            rw [envE, envE, step_coin, step_coin, bind_map_left, bind_map_left]
            exact bind_congr fun c => ih c s h
        | birth x =>
            rw [envE, envE, step_birth, step_birth]
            cases hc : s.memory.rows x with
            | some a =>
                rw [rowStep_some _ _ _ _ a hc, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure, pure_bind, pure_bind]
                exact ih a _ (agree_replay h x true)
            | none =>
                rw [rowVal_agree h x hc]
                by_cases hx : x ∈ digestInputs
                · rw [rowStep_in _ _ _ _ hc hx, liftM_map, liftM_pure, map_pure, map_pure, pure_bind, pure_bind]
                  exact ih (rowVal D' x) { s with memory := s.memory.readRow x (rowVal D' x) true }
                    (agree_read h x _ true)
                · rw [rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure, pure_bind, pure_bind]
                  exact ih _ _ (agree_replay h x true)
        | trial x =>
            rw [envE, envE, step_trial, step_trial]
            cases hc : s.memory.rows x with
            | some a =>
                rw [rowStep_some _ _ _ _ a hc, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure, pure_bind, pure_bind]
                exact ih a _ (agree_replay h x false)
            | none =>
                rw [rowVal_agree h x hc]
                by_cases hx : x ∈ digestInputs
                · rw [rowStep_in _ _ _ _ hc hx, liftM_map, liftM_pure, map_pure, map_pure, pure_bind, pure_bind]
                  exact ih (rowVal D' x) { s with memory := s.memory.readRow x (rowVal D' x) false }
                    (agree_read h x _ false)
                · rw [rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure, pure_bind, pure_bind]
                  exact ih _ _ (agree_replay h x false)
        | nonce m =>
            rw [envE, envE, step_nonce, step_nonce]
            cases hc : s.memory.nonces m with
            | some v =>
                rw [nonceStep_some _ _ _ v hc, nonceStep_some _ _ _ v hc, liftM_pure, map_pure, pure_bind, pure_bind]
                exact ih v _ h
            | none =>
                rw [nonceStep_none _ _ _ hc, nonceStep_none _ _ _ hc, liftM_map, liftM_map, liftM_pure, liftM_pure,
                  map_pure, map_pure, map_pure, map_pure, pure_bind, pure_bind, h.2 m hc]
                exact ih _ _ (agree_draw h m _)
        | expose o =>
            rw [envE, envE, step_expose, step_expose, pure_bind, pure_bind]
            exact ih () _ h
      · rw [envE, envE, step_guess, step_guess, bind_map_left, bind_map_left]
        refine bind_congr fun hit => ?_
        rw [afterTrial_sources _ _ (fun x => pure (rowVal D' x)) (fun m => pure (Nn' m))]
        exact ih hit _ h
      · rw [envE, envE, step_disclose, step_disclose, bind_map_left, bind_map_left]
        refine bind_congr fun v => ?_
        rw [afterDisclosure_sources _ _ (fun x => pure (rowVal D' x)) (fun m => pure (Nn' m))]
        exact ih v _ h
end Congr
section EagerLazy
open SecretGuessObservation (forcedRun forcedImpl runWith)
noncomputable def rowsLaw : SPMF (digestInputs → HashOutput) := liftM (PMF.uniformOfFintype (digestInputs → HashOutput))
noncomputable def noncesLaw : SPMF (Message → Digest) := liftM (PMF.uniformOfFintype (Message → Digest))
theorem avg_indep {α : Type} (slot : Nat) (input : WSpecL.Domain) (next : WSpecL.Range input → OracleComp WSpecL α)
    (s : WStateL)
    (ih : ∀ u s', (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next u) s') =
      forcedRun envL slot (next u) s')
    (X : SPMF (WSpecL.Range input × WStateL)) (hE : ∀ D Nn, (forcedImpl (envE D Nn) slot input).run s = X)
    (hL : (forcedImpl envL slot input).run s = X) :
    (rowsLaw >>= fun D => noncesLaw >>= fun Nn => (forcedImpl (envE D Nn) slot input).run s >>= fun mid =>
        runWith (forcedImpl (envE D Nn) slot) (next mid.1) mid.2) =
      ((forcedImpl envL slot input).run s >>= fun mid => runWith (forcedImpl envL slot) (next mid.1) mid.2) := by
  simp only [hE, hL]
  calc _ = (rowsLaw >>= fun D => X >>= fun mid => noncesLaw >>= fun Nn =>
        runWith (forcedImpl (envE D Nn) slot) (next mid.1) mid.2) :=
        bind_congr fun D => RetainedObservation.bind_comm _ _ _
    _ = (X >>= fun mid => rowsLaw >>= fun D => noncesLaw >>= fun Nn =>
        runWith (forcedImpl (envE D Nn) slot) (next mid.1) mid.2) := RetainedObservation.bind_comm _ _ _
    _ = _ := bind_congr fun mid => ih mid.1 mid.2
theorem avg_fresh_row {α : Type} (slot : Nat) (x : HashInput) (hx : x ∈ digestInputs) (s : WStateL) (b : Bool) (next : HashOutput → OracleComp WSpecL α)
    (ih : ∀ u s', (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next u) s') =
      forcedRun envL slot (next u) s') :
    (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next (rowVal D x))
        { s with memory := s.memory.readRow x (rowVal D x) b }) =
      ((liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) >>= fun a =>
        forcedRun envL slot (next a) { s with memory := s.memory.readRow x a b }) := by
  have hrv : ∀ D : digestInputs → HashOutput, rowVal D x = D ⟨x, hx⟩ := fun D => by rw [rowVal, dif_pos hx]
  simp only [hrv]
  rw [rowsLaw, uniform_update (⟨x, hx⟩ : digestInputs) (fun a D => noncesLaw >>= fun Nn =>
    forcedRun (envE D Nn) slot (next a) { s with memory := s.memory.readRow x a b })]
  · refine bind_congr fun a => ?_
    rw [← rowsLaw]
    exact ih a _
  · intro a T c
    refine bind_congr fun Nn => forced_congr _ _ _ _ slot _ _ ⟨fun y hy => ?_, fun _ _ => rfl⟩
    have hyx : y ≠ ⟨x, hx⟩ := by
      rintro rfl
      have hcached : (s.memory.readRow x a b).rows x = some a := by
        cases b
        · rw [readRow_false]
          exact QueryCache.cacheQuery_self _ _ _
        · rw [readRow_true]
          exact QueryCache.cacheQuery_self _ _ _
      change (s.memory.readRow x a b).rows x = none at hy
      rw [hcached] at hy
      cases hy
    exact Function.update_of_ne hyx _ _
theorem avg_fresh_nonce {α : Type} (slot : Nat) (m : Message) (s : WStateL)
    (next : Digest → OracleComp WSpecL α)
    (ih : ∀ u s', (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next u) s') =
      forcedRun envL slot (next u) s') :
    (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next (Nn m))
        { s with memory := s.memory.drawNonce m (Nn m) }) =
      ((liftM (PMF.uniformOfFintype Digest) : SPMF Digest) >>= fun v =>
        forcedRun envL slot (next v) { s with memory := s.memory.drawNonce m v }) := by
  have step : ∀ D : digestInputs → HashOutput,
      (noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next (Nn m)) { s with memory := s.memory.drawNonce m (Nn m) }) =
      ((liftM (PMF.uniformOfFintype Digest) : SPMF Digest) >>= fun v => noncesLaw >>= fun Nn =>
        forcedRun (envE D Nn) slot (next v) { s with memory := s.memory.drawNonce m v }) := by
    intro D
    rw [noncesLaw]
    refine uniform_update m (fun v Nn => forcedRun (envE D Nn) slot (next v) { s with memory := s.memory.drawNonce m v })
      fun v T c => forced_congr _ _ _ _ slot _ _ ⟨fun _ _ => rfl, fun m' hm' => ?_⟩
    have hmm : m' ≠ m := by
      rintro rfl
      change Function.update s.memory.nonces m' (some v) m' = none at hm'
      rw [Function.update_self] at hm'
      cases hm'
    exact Function.update_of_ne hmm _ _
  simp only [step]
  rw [RetainedObservation.bind_comm]
  exact bind_congr fun v => ih v _
theorem eager_lazy_core {α : Type} (slot : Nat) (W : OracleComp WSpecL α) (s : WStateL) :
    (rowsLaw >>= fun D => noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot W s) = forcedRun envL slot W s := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure a =>
      simp only [forcedRun, SecretGuessObservation.runWith_pure, rowsLaw, noncesLaw, RetainedObservation.lift_bind_const]
  | query_bind input next ih =>
      simp only [forcedRun, SecretGuessObservation.runWith_query_bind]
      rcases input with input | (⟨f, c⟩ | f)
      · cases input with
        | coin n =>
            exact avg_indep slot _ next s ih _ (fun D Nn => by rw [envE, step_coin]) (by rw [envL, step_coin])
        | expose o =>
            exact avg_indep slot _ next s ih _ (fun D Nn => by rw [envE, step_expose]) (by rw [envL, step_expose])
        | birth x =>
            cases hc : s.memory.rows x with
            | some a =>
                exact avg_indep slot _ next s ih (pure (a, { s with memory := s.memory.replayRow x true }))
                  (fun D Nn => by rw [envE, step_birth, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure])
                  (by rw [envL, step_birth, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure])
            | none =>
                by_cases hx : x ∈ digestInputs
                · have hE : ∀ D Nn, (forcedImpl (envE D Nn) slot (.inl (.birth x))).run s =
                      pure (rowVal D x, { s with memory := s.memory.readRow x (rowVal D x) true }) := fun D Nn => by
                    rw [envE, step_birth, rowStep_in _ _ _ _ hc hx, liftM_map, liftM_pure, map_pure, map_pure]
                  have hL : (forcedImpl envL slot (.inl (.birth x))).run s =
                      (fun a => (a, { s with memory := s.memory.readRow x a true })) <$>
                        (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) := by
                    rw [envL, step_birth, rowStep_in _ _ _ _ hc hx, liftM_map, Functor.map_map]
                  simp only [hE, hL, pure_bind, bind_map_left]
                  exact avg_fresh_row slot x hx s true next ih
                · exact avg_indep slot _ next s ih (pure ((0 : HashOutput), { s with memory := s.memory.replayRow x true }))
                    (fun D Nn => by rw [envE, step_birth, rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure])
                    (by rw [envL, step_birth, rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure])
        | trial x =>
            cases hc : s.memory.rows x with
            | some a =>
                exact avg_indep slot _ next s ih (pure (a, { s with memory := s.memory.replayRow x false }))
                  (fun D Nn => by rw [envE, step_trial, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure])
                  (by rw [envL, step_trial, rowStep_some _ _ _ _ a hc, liftM_pure, map_pure])
            | none =>
                by_cases hx : x ∈ digestInputs
                · have hE : ∀ D Nn, (forcedImpl (envE D Nn) slot (.inl (.trial x))).run s =
                      pure (rowVal D x, { s with memory := s.memory.readRow x (rowVal D x) false }) := fun D Nn => by
                    rw [envE, step_trial, rowStep_in _ _ _ _ hc hx, liftM_map, liftM_pure, map_pure, map_pure]
                  have hL : (forcedImpl envL slot (.inl (.trial x))).run s =
                      (fun a => (a, { s with memory := s.memory.readRow x a false })) <$>
                        (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput) := by
                    rw [envL, step_trial, rowStep_in _ _ _ _ hc hx, liftM_map, Functor.map_map]
                  simp only [hE, hL, pure_bind, bind_map_left]
                  exact avg_fresh_row slot x hx s false next ih
                · exact avg_indep slot _ next s ih (pure ((0 : HashOutput), { s with memory := s.memory.replayRow x false }))
                    (fun D Nn => by rw [envE, step_trial, rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure])
                    (by rw [envL, step_trial, rowStep_out _ _ _ _ hc hx, liftM_pure, map_pure])
        | nonce m =>
            cases hc : s.memory.nonces m with
            | some v =>
                exact avg_indep slot _ next s ih (pure (v, { s with memory := s.memory }))
                  (fun D Nn => by rw [envE, step_nonce, nonceStep_some _ _ _ v hc, liftM_pure, map_pure])
                  (by rw [envL, step_nonce, nonceStep_some _ _ _ v hc, liftM_pure, map_pure])
            | none =>
                have hE : ∀ D Nn, (forcedImpl (envE D Nn) slot (.inl (.nonce m))).run s =
                    pure (Nn m, { s with memory := s.memory.drawNonce m (Nn m) }) := fun D Nn => by
                  rw [envE, step_nonce, nonceStep_none _ _ _ hc, liftM_map, liftM_pure, map_pure, map_pure]
                have hL : (forcedImpl envL slot (.inl (.nonce m))).run s =
                    (fun v => (v, { s with memory := s.memory.drawNonce m v })) <$>
                      (liftM (PMF.uniformOfFintype Digest) : SPMF Digest) := by
                  rw [envL, step_nonce, nonceStep_none _ _ _ hc, liftM_map, Functor.map_map]
                simp only [hE, hL, pure_bind, bind_map_left]
                exact avg_fresh_nonce slot m s next ih
      · refine avg_indep slot _ next s ih _ (fun D Nn => ?_) rfl
        rw [envE, envL, step_guess, step_guess]
        have hfun : (fun hit => (hit, { SecretGuessObservation.afterTrial
              (envWith (fun x => pure (rowVal D x)) (fun m => pure (Nn m))) s f c hit with memory := s.memory })) =
            (fun hit => (hit, { SecretGuessObservation.afterTrial
              (envWith (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)) s f c hit with
                memory := s.memory })) := by
          funext hit
          rw [afterTrial_sources (fun x => pure (rowVal D x)) (fun m => pure (Nn m))
            (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)]
        rw [hfun]
      · refine avg_indep slot _ next s ih _ (fun D Nn => ?_) rfl
        rw [envE, envL, step_disclose, step_disclose]
        have hfun : (fun v => (v, { SecretGuessObservation.afterDisclosure
              (envWith (fun x => pure (rowVal D x)) (fun m => pure (Nn m))) s f v with memory := s.memory })) =
            (fun v => (v, { SecretGuessObservation.afterDisclosure
              (envWith (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)) s f v with
                memory := s.memory })) := by
          funext v
          rw [afterDisclosure_sources (fun x => pure (rowVal D x)) (fun m => pure (Nn m))
            (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)]
        rw [hfun]
theorem eager_lazy {α : Type} (W : OracleComp WSpecL α) (slot : Nat) (s : WStateL) :
    (𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
      forcedRun (envE D Nn) slot W s) = forcedRun envL slot W s := by
  rw [evalSPMF_uniform, evalSPMF_uniform]
  exact eager_lazy_core slot W s
end EagerLazy
section Avg
open SecretGuessObservation (forcedRun)
attribute [local instance] instSampleableTypeSeeds_pairGuessFinal instSampleableTypeForallFtsCoordDigest_pairGuessFinal
  CanonGraph.instSampleableTypeSecrets CanonGraph.instSampleableTypeOtherHalves CanonGraph.instSampleableTypeLabels_1
end Avg
end SigGolfCandidate.T3.Security.BPair
end
