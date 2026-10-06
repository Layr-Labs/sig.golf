import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCNearSearch
import SigGolfCandidate.ClaudeWCT.W9.New.G6.LazyCount
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsSmallContract
import SigGolfCandidate.ClaudeWCT.W9.New.C2.SignerCompleteBound

section


namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem digestInputs rowVal rowStep nonceStep patch patch_e
  patch_of patch_uniform digestEmb digestEmb_injective evalSPMF_uniform uniform_update rowStep_some rowStep_out
  rowStep_in nonceStep_some nonceStep_none rowsLaw noncesLaw replayRow_true replayRow_false readRow_true readRow_false
  digestInputs_subset_publicUniverse)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section OmegaPatch
variable {U : Finset HashInput} (hsub : digestInputs ⊆ U)
noncomputable def patchOmega (ω : CanonTable.Omega U) (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    CanonTable.Omega U :=
  ⟨ω.secrets, patch nonceOther ω.other Nn, ω.low, ω.high, patch (digestEmb hsub) ω.residual D⟩
theorem digestOf_patch (ω : CanonTable.Omega U) (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    digestOf (patchOmega hsub ω D Nn) = D := by
  funext x
  change finiteHashAnswer ∅ U (patch (digestEmb hsub) ω.residual D) x.1 = D x
  rw [finiteHashAnswer_none ∅ U _ _ (hsub x.2) rfl]
  exact patch_e (digestEmb_injective hsub) _ _ x
theorem nonceOf_patch (ω : CanonTable.Omega U) (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    nonceOf (patchOmega hsub ω D Nn) = Nn :=
  funext fun m => patch_e nonceOther_injective ω.other Nn m
theorem sameRest_patch (ω : CanonTable.Omega U) (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    SameRest ω (patchOmega hsub ω D Nn) := by
  refine ⟨rfl, rfl, rfl, fun x hx => (patch_of (digestEmb hsub) ω.residual D x ?_).symm,
    fun h hh => (patch_of nonceOther ω.other Nn h ?_).symm⟩
  · intro y hy
    apply hx
    rw [← hy]
    exact y.2
  · intro m hm
    exact hh m hm.symm
end OmegaPatch
section OmegaLaw
attribute [local instance] instFintypeCoordinate_canonGraph instSampleableTypeFullTable_canonGraph
  instSampleableTypeHashOutput_canonGraph_1 instSampleableTypeLabels_1 instSampleableTypeSecrets
  instSampleableTypeOtherHalves instFintypeSecrets_canonGraph instFintypeOtherHalves_canonGraph
  instSampleableTypeProdSecretsOtherHalves instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1
  instSampleableTypeLowLabels instSampleableTypeProdLowLabels CanonTable.instSampleableTypeHidden
theorem digest_subset (adversary : AdversaryP) : digestInputs ⊆ Wots.referenceInputs adversary :=
  digestInputs_subset_publicUniverse.trans (Wots.Ref.referenceInputs_universe adversary)
noncomputable def omegaLaw (adversary : AdversaryP) : ProbComp (CanonTable.Omega (Wots.referenceInputs adversary)) :=
  ($ᵗ Secrets : ProbComp _) >>= fun secrets =>
    ($ᵗ OtherHalves : ProbComp _) >>= fun other =>
    ($ᵗ LowLabels : ProbComp _) >>= fun low =>
    ($ᵗ LowLabels : ProbComp _) >>= fun high =>
    ($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun residual =>
      pure ⟨secrets, other, low, high, residual⟩
noncomputable def ftsPart (adversary : AdversaryP) (ω : CanonTable.Omega (Wots.referenceInputs adversary)) :
    ProbComp (Answers × QueryLog Requests × List Wots.Entry) :=
  ($ᵗ (WctPoint → Digest) : ProbComp _) >>= fun g =>
    (fun (run : Bool × QueryLog Requests × List Wots.Entry) => (wA (canon_subset adversary) ω g, run.2.1, run.2.2)) <$>
      pairRun (wA (canon_subset adversary) ω g) adversary
theorem pairExperiment_omega (adversary : AdversaryP) :
    𝒮[pairExperiment adversary] = 𝒮[omegaLaw adversary >>= ftsPart adversary] := by
  rw [pairExperiment_eq]
  unfold omegaLaw ftsPart
  simp only [bind_assoc, pure_bind]
theorem pairExperiment_avg (adversary : AdversaryP) (E : Answers × QueryLog Requests × List Wots.Entry → Prop) :
    Pr[E | pairExperiment adversary] = ∑' ω, Pr[= ω | omegaLaw adversary] *
      Pr[fun x => E (wA (canon_subset adversary) ω x.1, x.2.2.1, x.2.2.2) |
        ftsRun (canon_subset adversary) ω adversary] := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (pairExperiment_omega adversary), probEvent_bind_eq_tsum]
  apply tsum_congr
  intro ω
  rw [← inner_fts_eq (canon_subset adversary) ω adversary _ E]
  rfl
theorem omegaLaw_patch (adversary : AdversaryP) {γ : Type}
    (k : CanonTable.Omega (Wots.referenceInputs adversary) → SPMF γ) :
    (𝒮[omegaLaw adversary] >>= fun ω => 𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D =>
      𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn => k (patchOmega (digest_subset adversary) ω D Nn)) =
      𝒮[omegaLaw adversary] >>= k := by
  unfold omegaLaw
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  refine bind_congr fun secrets => ?_
  have step1 : ∀ (other : OtherHalves) (low high : LowLabels),
      (𝒮[($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)] >>=
        fun residual => 𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D =>
        𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          k (patchOmega (digest_subset adversary) ⟨secrets, other, low, high, residual⟩ D Nn)) =
      (𝒮[($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)] >>=
        fun residual => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          k ⟨secrets, patch nonceOther other Nn, low, high, residual⟩) := by
    intro other low high
    exact patch_uniform (digestEmb_injective (digest_subset adversary)) _ _
      (fun residual => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
        k ⟨secrets, patch nonceOther other Nn, low, high, residual⟩)
  simp only [step1]
  have step2 : ∀ other : OtherHalves,
      (𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun low => 𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
        𝒮[($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)] >>=
        fun residual => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          k ⟨secrets, patch nonceOther other Nn, low, high, residual⟩) =
      (𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
        𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun low => 𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
        𝒮[($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)] >>=
        fun residual => k ⟨secrets, patch nonceOther other Nn, low, high, residual⟩) := by
    intro other
    calc _ = (𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun low => 𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
          𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          𝒮[($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)] >>=
          fun residual => k ⟨secrets, patch nonceOther other Nn, low, high, residual⟩) :=
          bind_congr fun low => bind_congr fun high => RetainedObservation.bind_comm _ _ _
      _ = (𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun low => 𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
          𝒮[($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)] >>=
          fun residual => k ⟨secrets, patch nonceOther other Nn, low, high, residual⟩) :=
          bind_congr fun low => RetainedObservation.bind_comm _ _ _
      _ = _ := RetainedObservation.bind_comm _ _ _
  simp only [step2]
  exact patch_uniform nonceOther_injective _ _ (fun other =>
    𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun low => 𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
      𝒮[($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _)] >>=
      fun residual => k ⟨secrets, other, low, high, residual⟩)
end OmegaLaw
section Steps
open SecretGuessObservation (forcedRun forcedImpl lazyImpl runWith afterTrial afterDisclosure forcedTrial)
variable (slot : Nat) (rs : HashInput → PMF HashOutput) (ns : Message → PMF Digest)
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
theorem step_guess (s : WStateL) (f : Guess.GCoord) (c : Digest) :
    (forcedImpl (envWith rs ns) slot (.inr (.inl (f, c)))).run s =
      (fun hit => (hit, { afterTrial (envWith rs ns) s f c hit with memory := s.memory })) <$>
        forcedTrial slot s f c := rfl
theorem step_disclose (s : WStateL) (f : Guess.GCoord) :
    (forcedImpl (envWith rs ns) slot (.inr (.inr f))).run s =
      (fun v => (v, { afterDisclosure (envWith rs ns) s f v with memory := s.memory })) <$>
        UniformTableCompletion.cell (s.allowed f) := rfl
theorem afterTrial_sources (rs' : HashInput → PMF HashOutput) (ns' : Message → PMF Digest) (s : WStateL)
    (f : Guess.GCoord) (c : Digest) (hit : Bool) :
    afterTrial (envWith rs ns) s f c hit = afterTrial (envWith rs' ns') s f c hit := rfl
theorem afterDisclosure_sources (rs' : HashInput → PMF HashOutput) (ns' : Message → PMF Digest) (s : WStateL)
    (f : Guess.GCoord) (v : Digest) :
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
theorem avg_fresh_row {α : Type} (slot : Nat) (x : HashInput) (hx : x ∈ digestInputs) (s : WStateL) (b : Bool)
    (next : HashOutput → OracleComp WSpecL α)
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
      (noncesLaw >>= fun Nn => forcedRun (envE D Nn) slot (next (Nn m))
        { s with memory := s.memory.drawNonce m (Nn m) }) =
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
      simp only [forcedRun, SecretGuessObservation.runWith_pure, rowsLaw, noncesLaw,
        RetainedObservation.lift_bind_const]
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
                · exact avg_indep slot _ next s ih
                    (pure ((0 : HashOutput), { s with memory := s.memory.replayRow x true }))
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
                · exact avg_indep slot _ next s ih
                    (pure ((0 : HashOutput), { s with memory := s.memory.replayRow x false }))
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
theorem forced_avg_law (adversary : AdversaryP) (slot : Nat) :
    (𝒮[omegaLaw adversary] >>= fun ω => forcedRun (envE (digestOf ω) (nonceOf ω)) slot
        (worldGameL (canon_subset adversary) ω adversary) initL) =
      (𝒮[omegaLaw adversary] >>= fun ω =>
        forcedRun envL slot (worldGameL (canon_subset adversary) ω adversary) initL) := by
  symm
  calc (𝒮[omegaLaw adversary] >>= fun ω =>
        forcedRun envL slot (worldGameL (canon_subset adversary) ω adversary) initL)
      = (𝒮[omegaLaw adversary] >>= fun ω => 𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D =>
          𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          forcedRun (envE D Nn) slot (worldGameL (canon_subset adversary) ω adversary) initL) :=
        bind_congr fun ω => (eager_lazy _ slot initL).symm
    _ = (𝒮[omegaLaw adversary] >>= fun ω => 𝒮[($ᵗ (digestInputs → HashOutput) : ProbComp _)] >>= fun D =>
          𝒮[($ᵗ (Message → Digest) : ProbComp _)] >>= fun Nn =>
          (fun ω' : CanonTable.Omega (Wots.referenceInputs adversary) =>
            forcedRun (envE (digestOf ω') (nonceOf ω')) slot
              (worldGameL (canon_subset adversary) ω' adversary) initL)
            (patchOmega (digest_subset adversary) ω D Nn)) := by
        refine bind_congr fun ω => bind_congr fun D => bind_congr fun Nn => ?_
        dsimp only
        rw [digestOf_patch, nonceOf_patch]
        exact congrArg (fun W => forcedRun (envE D Nn) slot W initL)
          (worldGameL_congr (canon_subset adversary) (sameRest_patch (digest_subset adversary) ω D Nn) adversary)
    _ = _ := omegaLaw_patch adversary (fun ω' => forcedRun (envE (digestOf ω') (nonceOf ω')) slot
          (worldGameL (canon_subset adversary) ω' adversary) initL)
theorem forced_avg_eq_lazy (adversary : AdversaryP) (slot : Nat)
    (payoff : (Bool × QueryLog Requests × List Wots.Entry) × WStateL → ENNReal) :
    ∑' ω, Pr[= ω | omegaLaw adversary] * ∑' r, Pr[= r | forcedRun (envE (digestOf ω) (nonceOf ω)) slot
        (worldGameL (canon_subset adversary) ω adversary) initL] * payoff r =
      ∑' ω, Pr[= ω | omegaLaw adversary] * ∑' r, Pr[= r | forcedRun envL slot
        (worldGameL (canon_subset adversary) ω adversary) initL] * payoff r := by
  have h := congrArg (fun X => expectedValue X payoff) (forced_avg_law adversary slot)
  rw [expectedValue_bind, expectedValue_bind] at h
  simp only [expectedValue_def, probOutput_evalSPMF] at h
  exact h
end Avg
end ClaudeWCT.W9.T3.Security.WPair
end

section











section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (LazyMem)
open SphincsSecurity.Concrete
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def Extends (rows rows' : Sampling.RCache) : Prop := ∀ x a, rows x = some a → rows' x = some a
theorem Extends.refl (rows : Sampling.RCache) : Extends rows rows := fun _ _ h => h
theorem Extends.trans {r1 r2 r3 : Sampling.RCache} (h1 : Extends r1 r2) (h2 : Extends r2 r3) : Extends r1 r3 :=
  fun x a h => h2 x a (h1 x a h)
theorem search_replays_gen {β γ : Type} (secret : BitVec 256) (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (result : Nat → β → γ) :
    ∀ fuel counter (cache : Sampling.RCache) r,
      r ∈ support (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache) →
      Extends cache r.2 ∧ ∀ cache', Extends r.2 cache' → ∀ r' ∈ support (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache'),
          r' = (r.1, cache') := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter cache r hr
      simp only [searchLoop, Sampling.publicProgram, simulateQ_pure] at hr
      change r ∈ support (Sampling.roRun secret (pure none) cache) at hr
      rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨Extends.refl _, fun cache' _ r' hr' => ?_⟩
      simp only [searchLoop, Sampling.publicProgram, simulateQ_pure] at hr'
      change r' ∈ support (Sampling.roRun secret (pure none) cache') at hr'
      rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr'
      exact hr'
  | succ fuel ih =>
      intro counter cache r hr
      rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr
      obtain ⟨first, hfirst, hr⟩ := hr
      have hfirst' : Extends cache first.2 ∧ first.2 (inputs counter) = some first.1 := by
        rw [randomOracle.run_eq] at hfirst
        cases hc : cache (inputs counter) with
        | some a =>
            rw [hc, support_pure, Set.mem_singleton_iff] at hfirst
            subst hfirst
            exact ⟨Extends.refl _, hc⟩
        | none =>
            rw [hc, mem_support_bind_iff] at hfirst
            obtain ⟨a, -, hfa⟩ := hfirst
            rw [support_pure, Set.mem_singleton_iff] at hfa
            subst hfa
            refine ⟨fun x b hx => ?_, QueryCache.cacheQuery_self _ _ _⟩
            have hne : x ≠ inputs counter := fun he => by rw [he, hc] at hx; cases hx
            exact (QueryCache.cacheQuery_of_ne cache a hne).trans hx
      cases hd : decoder first.1 with
      | none =>
          rw [hd] at hr
          obtain ⟨h1, h2⟩ := ih (counter + 1) first.2 r hr
          refine ⟨hfirst'.1.trans h1, fun cache' hc' r' hr' => ?_⟩
          rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr'
          obtain ⟨first', hf'', hr'⟩ := hr'
          have hq : cache' (inputs counter) = some first.1 := hc' _ _ (h1 _ _ hfirst'.2)
          rw [randomOracle.run_eq, hq, support_pure, Set.mem_singleton_iff] at hf''
          subst hf''
          simp only [hd] at hr'
          exact h2 cache' hc' r' hr'
      | some value =>
          rw [hd] at hr
          simp only at hr
          rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr
          refine ⟨hfirst'.1, fun cache' hc' r' hr' => ?_⟩
          rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr'
          obtain ⟨first', hf'', hr'⟩ := hr'
          have hq : cache' (inputs counter) = some first.1 := hc' _ _ hfirst'.2
          rw [randomOracle.run_eq, hq, support_pure, Set.mem_singleton_iff] at hf''
          subst hf''
          simp only [hd] at hr'
          rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr'
          exact hr'
def Replays (rows : Sampling.RCache) (rho : Digest) (m : Message) (found : Option (BitVec 32 × HashOutput)) : Prop :=
  ∀ cache', Extends rows cache' →
    ∀ r' ∈ support (Sampling.roRun 0 (nearSpec.search rho m 0 WCT9.digestAttemptLimit) cache'), r' = (found, cache')
theorem Replays.mono {rows rows' : Sampling.RCache} {rho : Digest} {m : Message} {found}
    (h : Replays rows rho m found) (hext : Extends rows rows') : Replays rows' rho m found :=
  fun cache' hc => h cache' (hext.trans hc)
theorem replays_of_search (rho : Digest) (m : Message) (rows : Sampling.RCache) (r)
    (hr : r ∈ support (Sampling.roRun 0 (nearSpec.search rho m 0 WCT9.digestAttemptLimit) rows)) :
    Extends rows r.2 ∧ Replays r.2 rho m r.1 := by
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr
  obtain ⟨h1, h2⟩ := search_replays_gen 0 (Sampling.digestTrial rho m) nearSpec.decode _ _ 0 rows r hr
  refine ⟨h1, fun cache' hc r' hr' => ?_⟩
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr'
  exact h2 cache' hc r' hr'
def InvM (M : LazyMem × NearGhost) : Prop :=
  (∀ v ∈ M.1.exposures, v ∈ M.2.fresh) ∧ M.2.fresh.length ≤ M.1.exposures.length ∧
    ∀ m rho, M.1.nonces m = some rho → ∃ found, Replays M.1.rows rho m found ∧
      ∀ v ∈ (found.map Prod.snd).toList, v ∈ M.2.fresh
theorem invM_empty : InvM (LazyMem.empty, NearGhost.empty) := by
  refine ⟨fun v hv => by simp [LazyMem.empty] at hv, by simp [LazyMem.empty, NearGhost.empty], ?_⟩
  intro m rho h
  simp [LazyMem.empty] at h
noncomputable def ghostPot (q : Nat) (M : LazyMem × NearGhost) : ENNReal :=
  nearMemPotential q M.1.births M.2.fresh M.2.reused M.1.rows M.1.nonces
noncomputable def ΦI (q : Nat) (s : GState) : ENNReal := if InvM s.memory then ghostPot q s.memory else ⊤
theorem ΦI_initial (q : Nat) : ΦI q initG ≤ (q : ENNReal) * 404 / 2 ^ 128 := by
  unfold ΦI
  rw [if_pos (show InvM initG.memory from invM_empty)]
  exact mem_initial q
theorem nearCoveredBy_mono {X Y : List HashOutput} (h : ∀ v ∈ X, v ∈ Y) {N : HashOutput}
    (hN : Guess.NearCoveredBy X N) : Guess.NearCoveredBy Y N := by
  obtain ⟨k, t, hkt⟩ := hN
  exact ⟨k, t, hkt.mono_log h⟩
theorem payoff_le_ΦI (q : Nat) (r : (Bool × QueryLog Requests × List Wots.Entry) × GState) :
    WPair.nearPayoff q (r.1, projS r.2) ≤ ΦI q r.2 := by
  unfold ΦI
  split_ifs with hinv
  · unfold WPair.nearPayoff
    split_ifs with hp
    · obtain ⟨hb, hl, N, hN, hadm, hcov⟩ := hp
      exact mem_win q _ _ _ _ _ hb (hinv.2.1.trans hl) (Or.inr ⟨N, hN, hadm, nearCoveredBy_mono hinv.1 hcov⟩)
    · exact bot_le
  · exact le_top
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem spmf_ev_mono {α : Type} (p : SPMF α) {f g : α → ENNReal} (h : ∀ x, p x ≠ 0 → f x ≤ g x) :
    expectedValue p f ≤ expectedValue p g := by
  unfold expectedValue
  apply ENNReal.tsum_le_tsum
  intro x
  rw [SPMF.probOutput_eq_apply]
  by_cases hx : p x = 0
  · simp [hx]
  · exact mul_le_mul' le_rfl (h x hx)
theorem spmf_ev_le {α : Type} (p : SPMF α) {f : α → ENNReal} {c : ENNReal} (h : ∀ x, p x ≠ 0 → f x ≤ c) :
    expectedValue p f ≤ c :=
  (spmf_ev_mono p h).trans (expectedValue_le_of_le p fun _ => le_rfl)
theorem spmf_ev_congr {α : Type} (p : SPMF α) {f g : α → ENNReal} (h : ∀ x, p x ≠ 0 → f x = g x) :
    expectedValue p f = expectedValue p g :=
  le_antisymm (spmf_ev_mono p fun x hx => (h x hx).le) (spmf_ev_mono p fun x hx => (h x hx).ge)
theorem superProg_of_memory {β : Type} (slot q : Nat) (W : OracleComp WPair.WSpecL β)
    (h : ∀ s r, SecretGuessObservation.runWith (implG slot) W s r ≠ 0 → r.2.memory = s.memory) :
    SuperProg (implG slot) (ΦI q) W := by
  intro s
  apply spmf_ev_le
  intro r hr
  unfold ΦI
  rw [h s r hr]
theorem coin_memory (slot n : Nat) (s : GState) (r : Fin (n + 1) × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (WPair.coinReqL n) s r ≠ 0) : r.2.memory = s.memory := by
  obtain ⟨res, hres, rfl⟩ := aux_nonzero slot (.coin n) s r hr
  have hres' : res ∈ (WPair.envL.auxiliary (projS s) (.coin n)).support := (PMF.mem_support_iff _ _).mpr hres
  change res ∈ ((fun c => (c, (projS s).memory)) <$> PMF.uniformOfFintype (Fin (n + 1))).support at hres'
  rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hres'
  obtain ⟨c, -, rfl⟩ := hres'
  rfl
theorem secret_memory {β : Type} (slot : Nat) (p : (Guess.GCoord × Digest) ⊕ Guess.GCoord)
    (s : GState) (r : (WPair.WSpecL.Range (.inr p)) × GState)
    (hr : SecretGuessObservation.runWith (implG slot) (liftM (WPair.WSpecL.query (.inr p))) s r ≠ 0) :
    r.2.memory = s.memory := by
  unfold SecretGuessObservation.runWith at hr
  rw [simulateQ_spec_query] at hr
  rcases p with ⟨c, v⟩ | c
  · simp only [SecretGuessObservation.forcedImpl, StateT.run_mk, map_eq_bind_pure_comp,
      RetainedObservation.bind_nonzero, Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨hit, -, rfl⟩ := hr
    rfl
  · simp only [SecretGuessObservation.forcedImpl, SecretGuessObservation.lazyImpl, StateT.run_mk,
      map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def, ne_eq,
      SPMF.pure_apply_eq_zero_iff, not_not] at hr
    obtain ⟨value, -, rfl⟩ := hr
    rfl
theorem coin_ΦI (slot q n : Nat) : SuperProg (implG slot) (ΦI q) (WPair.coinReqL n) :=
  superProg_of_memory slot q _ fun s r hr => coin_memory slot n s r hr
theorem guess_ΦI (slot q : Nat) (c : Guess.GCoord) (v : Digest) :
    SuperProg (implG slot) (ΦI q) (Guess.trialQ (auxSpec := AuxSpecL) c v) :=
  superProg_of_memory slot q _ fun s r hr => secret_memory (β := Bool) slot (.inl (c, v)) s r hr
theorem disclose_ΦI (slot q : Nat) (c : Guess.GCoord) :
    SuperProg (implG slot) (ΦI q) (Guess.discloseQ (auxSpec := AuxSpecL) (V := Digest) c) :=
  superProg_of_memory slot q _ fun s r hr => secret_memory (β := Digest) slot (.inr c) s r hr
theorem mapM_ΦI {α β : Type} (slot q : Nat) (f : α → OracleComp WPair.WSpecL β)
    (hf : ∀ a, SuperProg (implG slot) (ΦI q) (f a)) :
    ∀ l : List α, SuperProg (implG slot) (ΦI q) (l.mapM f)
  | [] => superProg_pure _ _ _
  | a :: l => by
      rw [List.mapM_cons]
      exact superProg_bind _ _ (hf a) fun _ => superProg_bind _ _ (mapM_ΦI slot q f hf l) fun _ => superProg_pure _ _ _
theorem discloseAll_ΦI (slot q : Nat) (cs : List Guess.GCoord) :
    SuperProg (implG slot) (ΦI q) (Guess.discloseAll (auxSpec := AuxSpecL) (V := Digest) cs) :=
  mapM_ΦI slot q _ (fun c => disclose_ΦI slot q c) cs
theorem probeW_ΦI (slot q : Nat) {R : Type} (step : Guess.ChainAddr → Fin 3 → Digest → R)
    (top : Guess.ChainAddr → R) (miss : R) (a : Guess.ChainAddr) (p : Fin 3) (v : Digest) :
    SuperProg (implG slot) (ΦI q) (Guess.probeW (auxSpec := AuxSpecL) step top miss a p v) := by
  unfold Guess.probeW
  refine superProg_bind _ _ (guess_ΦI slot q (a, p) v) fun hit => ?_
  split
  · split
    · exact superProg_bind _ _ (disclose_ΦI slot q _) fun _ => superProg_pure _ _ _
    · exact superProg_pure _ _ _
  · exact superProg_pure _ _ _
theorem finishL_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat) (ω : CanonTable.Omega U)
    (request : Request) (rho : Digest) (found : Option (BitVec 32 × HashOutput)) :
    SuperProg (implG slot) (ΦI q) (WPair.finishL hU ω request rho found) := by
  rcases found with _ | ⟨c, output⟩
  · exact superProg_pure _ _ _
  · simp only [WPair.finishL]
    generalize WPair.signerLayersW hU ω request output = g
    cases g with
    | none => exact superProg_pure _ _ _
    | some pieces =>
        refine superProg_bind _ _ (discloseAll_ΦI slot q _) ?_
        intro values
        exact superProg_pure _ _ _
theorem ev_uniform_digest (g : Digest → ENNReal) :
    expectedValue (PMF.uniformOfFintype Digest) g = expectedValue ($ᵗ Digest : ProbComp Digest) g := by
  rw [expectedValue_uniformOfFintype, BPORS.expected_uniform_eq_finiteAverage]
theorem ev_single_aux (slot : Nat) (i : AuxL) (s : GState) (G : AuxSpecL.Range i × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (liftM (WPair.WSpecL.query (.inl i))) s) G =
      expectedValue (WPair.envL.auxiliary (projS s) i) (fun r =>
        G (r.1, { s with memory := (r.2, ghostStep s.memory.1 i r.1 s.memory.2) })) := by
  have h := ev_aux_bind slot i pure s G
  rw [bind_pure] at h
  rw [h]
  apply congrArg
  funext r
  rw [runWith_pure', expectedValue_pure]
theorem birth_ΦI (slot q : Nat) (x : HashInput) : SuperProg (implG slot) (ΦI q) (WPair.birthReq x) := by
  intro s
  by_cases hinv : InvM s.memory
  swap
  · unfold ΦI; rw [if_neg hinv]; exact le_top
  unfold WPair.birthReq
  rw [ev_single_aux]
  change expectedValue (BPair.rowStep s.memory.1 x true (PMF.uniformOfFintype HashOutput)) _ ≤ _
  unfold BPair.rowStep
  cases hx : s.memory.1.rows x with
  | some a =>
      simp only
      rw [expectedValue_pure]
      exact le_of_eq rfl
  | none =>
      simp only
      split_ifs with hd
      · rw [expectedValue_map, ev_uniform_eq]
        have hpt : ∀ a : HashOutput, ΦI q { s with memory := (s.memory.1.readRow x a true,
            ghostStep s.memory.1 (.birth x) a s.memory.2) } =
            nearMemPotential q (s.memory.1.births ++ [a]) s.memory.2.fresh s.memory.2.reused
              (s.memory.1.rows.cacheQuery x a) s.memory.1.nonces := by
          intro a
          have hext : Extends s.memory.1.rows (s.memory.1.rows.cacheQuery x a) := by
            intro y b hy
            have hne : y ≠ x := fun he => by rw [he, hx] at hy; cases hy
            exact (QueryCache.cacheQuery_of_ne s.memory.1.rows a hne).trans hy
          have hinv' : InvM (s.memory.1.readRow x a true, ghostStep s.memory.1 (.birth x) a s.memory.2) := by
            obtain ⟨h1, h2, h3⟩ := hinv
            refine ⟨h1, h2, fun m rho hm => ?_⟩
            obtain ⟨found, hrep, hf⟩ := h3 m rho hm
            exact ⟨found, hrep.mono hext, hf⟩
          unfold ΦI
          rw [if_pos hinv']
          rfl
        simp_rw [hpt]
        unfold ΦI
        rw [if_pos hinv]
        exact mem_birth q _ _ _ _ _ x hx
      · rw [expectedValue_pure]
        exact le_of_eq rfl
theorem hashL_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat) (ω : CanonTable.Omega U)
    (x : HashInput) : SuperProg (implG slot) (ΦI q) (WPair.hashL hU ω x) := by
  unfold WPair.hashL
  cases Guess.decodeProbe x with
  | some p => exact probeW_ΦI slot q _ _ _ _ _ _
  | none =>
      simp only
      split_ifs
      · exact birth_ΦI slot q x
      · exact superProg_pure _ _ _
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem spmf_ev_zero {α : Type} (p : SPMF α) {f : α → ENNReal} (h : expectedValue p f = 0) :
    ∀ x, p x ≠ 0 → f x = 0 := by
  intro x hx
  unfold expectedValue at h
  have h0 := ENNReal.tsum_eq_zero.mp h x
  rw [SPMF.probOutput_eq_apply] at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd h1 hx
  · exact h1
theorem pc_ev_offsupport {α : Type} (p : ProbComp α) :
    expectedValue p (fun r => if r ∈ support p then 0 else 1) = 0 := by
  unfold expectedValue
  apply ENNReal.tsum_eq_zero.mpr
  intro r
  by_cases hr : r ∈ support p
  · simp [hr]
  · simp [hr, probOutput_eq_zero_of_not_mem_support hr]
theorem search_support (slot : Nat) (rho : Digest) (m : Message) (s : GState) (r)
    (hr : SecretGuessObservation.runWith (implG slot) (WPair.searchL rho m 0 WCT9.digestAttemptLimit) s r ≠ 0) :
    (r.1, r.2.memory.1.rows) ∈
      support (Sampling.roRun 0 (nearSpec.search rho m 0 WCT9.digestAttemptLimit) s.memory.1.rows) := by
  have hlaw := search_law slot rho m (fun f rows =>
    if (f, rows) ∈ support (Sampling.roRun 0 (nearSpec.search rho m 0 WCT9.digestAttemptLimit) s.memory.1.rows)
    then 0 else 1) WCT9.digestAttemptLimit 0 s
  simp only [Prod.mk.eta] at hlaw
  rw [pc_ev_offsupport] at hlaw
  have h0 := spmf_ev_zero _ hlaw r hr
  by_contra hc
  rw [if_neg hc] at h0
  exact one_ne_zero h0
theorem ev_nonce_cached {β : Type} (slot : Nat) (m : Message) (rho : Digest)
    (k : Digest → OracleComp WPair.WSpecL β) (s : GState) (hn : s.memory.1.nonces m = some rho)
    (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (WPair.nonceReq m >>= k) s) G =
      expectedValue (SecretGuessObservation.runWith (implG slot) (k rho)
        ⟨s.allowed, s.retired, s.guesses, s.probes, (s.memory.1, ghostStep s.memory.1 (.nonce m) rho s.memory.2)⟩) G := by
  unfold WPair.nonceReq
  rw [ev_aux_bind]
  change expectedValue (BPair.nonceStep s.memory.1 m (PMF.uniformOfFintype Digest)) _ = _
  unfold BPair.nonceStep
  rw [hn]
  simp only
  rw [expectedValue_pure]
theorem ev_nonce_fresh {β : Type} (slot : Nat) (m : Message) (k : Digest → OracleComp WPair.WSpecL β)
    (s : GState) (hn : s.memory.1.nonces m = none) (G : β × GState → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (implG slot) (WPair.nonceReq m >>= k) s) G =
      expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        expectedValue (SecretGuessObservation.runWith (implG slot) (k v)
          ⟨s.allowed, s.retired, s.guesses, s.probes,
            (s.memory.1.drawNonce m v, ghostStep s.memory.1 (.nonce m) v s.memory.2)⟩) G) := by
  unfold WPair.nonceReq
  rw [ev_aux_bind]
  change expectedValue (BPair.nonceStep s.memory.1 m (PMF.uniformOfFintype Digest)) _ = _
  unfold BPair.nonceStep
  rw [hn]
  simp only
  rw [expectedValue_map, ev_uniform_digest]
theorem ev_expose_finish_le {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat)
    (ω : CanonTable.Omega U) (request : Request) (rho : Digest) (found : Option (BitVec 32 × HashOutput))
    (s2 : GState) :
    expectedValue (SecretGuessObservation.runWith (implG slot)
      (WPair.exposeReq (found.map Prod.snd) >>= fun _ => WPair.finishL hU ω request rho found) s2)
      (fun r => ΦI q r.2) ≤
    ΦI q ⟨s2.allowed, s2.retired, s2.guesses, s2.probes, (s2.memory.1.expose (found.map Prod.snd),
      ghostStep s2.memory.1 (.expose (found.map Prod.snd)) () s2.memory.2)⟩ := by
  unfold WPair.exposeReq
  rw [ev_aux_bind]
  change expectedValue (pure ((), s2.memory.1.expose (found.map Prod.snd)) : PMF _) _ ≤ _
  rw [expectedValue_pure]
  exact finishL_ΦI hU slot q ω request rho found _
theorem signL_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (slot q : Nat) (ω : CanonTable.Omega U)
    (published : SigGolfCandidate.T3.Cache) (request : Request) :
    SuperProg (implG slot) (ΦI q) (WPair.signL hU ω published request) := by
  unfold WPair.signL
  rcases Classical.em (request.cache = published) with hc | hc
  swap
  · simp only [hc, ↓reduceIte]
    exact superProg_pure _ _ _
  simp only [hc, ↓reduceIte]
  intro s
  by_cases hinv : InvM s.memory
  swap
  · unfold ΦI; rw [if_neg hinv]; exact le_top
  set m := request.message with hm
  obtain ⟨hI1, hI2, hI3⟩ := hinv
  have hΦs : ΦI q s = ghostPot q s.memory := by unfold ΦI; rw [if_pos ⟨hI1, hI2, hI3⟩]
  cases hn : s.memory.1.nonces m with
  | some rho =>
      rw [ev_nonce_cached slot m rho _ s hn, runWith_bind', expectedValue_bind]
      apply spmf_ev_le
      intro r hr
      refine (ev_expose_finish_le hU slot q ω request rho r.1 r.2).trans ?_
      obtain ⟨found0, hrep, hf0⟩ := hI3 m rho hn
      have hsupp := search_support slot rho m _ r hr
      obtain ⟨-, -, -, -, hg, hnon, hbir, hexp⟩ := search_frame slot rho m WCT9.digestAttemptLimit 0 _ r hr
      have hrr := hrep s.memory.1.rows (Extends.refl _) _ hsupp
      simp only [Prod.mk.injEq] at hrr
      obtain ⟨hfound, hrows⟩ := hrr
      have hg' : r.2.memory.2 = ⟨s.memory.2.reused, false, s.memory.2.fresh⟩ := by
        rw [hg]
        simp only [ghostStep, hn, reduceCtorEq, decide_false, Bool.false_and, Bool.or_false]
      have hnon' : r.2.memory.1.nonces = s.memory.1.nonces := hnon
      have hbir' : r.2.memory.1.births = s.memory.1.births := hbir
      have hexp' : r.2.memory.1.exposures = s.memory.1.exposures := hexp
      have hinv' : InvM (r.2.memory.1.expose (r.1.map Prod.snd),
          ghostStep r.2.memory.1 (.expose (r.1.map Prod.snd)) () r.2.memory.2) := by
        rw [hg']
        simp only [ghostStep, Bool.false_eq_true, if_false]
        refine ⟨fun v hv => ?_, ?_, fun m' rho' hm' => ?_⟩
        · simp only [LazyMem.expose, List.mem_append] at hv
          rcases hv with hv | hv
          · rw [hexp'] at hv; exact hI1 v hv
          · rw [hfound] at hv; exact hf0 v hv
        · simp only [LazyMem.expose, List.length_append]
          rw [hexp']
          exact hI2.trans (Nat.le_add_right _ _)
        · simp only [LazyMem.expose] at hm' ⊢
          rw [hnon'] at hm'
          rw [hrows]
          exact hI3 m' rho' hm'
      rw [hΦs]
      unfold ΦI
      dsimp only
      rw [if_pos hinv']
      apply le_of_eq
      unfold ghostPot
      rw [hg']
      simp only [ghostStep, Bool.false_eq_true, if_false, LazyMem.expose]
      rw [hbir', hrows, hnon']
  | none =>
      rw [ev_nonce_fresh slot m _ s hn, hΦs]
      refine le_trans ?_ (mem_sign_fresh q _ _ _ _ _ m hn 0 WCT9.digestAttemptLimit WCT9.digestAttemptLimit_le)
      apply expectedValue_mono
      intro v
      rw [runWith_bind', expectedValue_bind]
      set s1 : GState := ⟨s.allowed, s.retired, s.guesses, s.probes, (s.memory.1.drawNonce m v,
        ghostStep s.memory.1 (.nonce m) v s.memory.2)⟩ with hs1
      have hg1 : s1.memory.2 = ⟨(s.memory.2.reused || decide (nearSpec.Reuse s.memory.1.rows v m)), true,
          s.memory.2.fresh⟩ := by
        simp only [hs1, ghostStep, hn, decide_true, Bool.true_and]
      refine le_of_le_of_eq ?_ (search_law slot v m (fun found rows' =>
        nearMemPotential q s.memory.1.births (s.memory.2.fresh ++ (found.map Prod.snd).toList)
          (s.memory.2.reused || decide (nearSpec.Reuse s.memory.1.rows v m)) rows'
          (Function.update s.memory.1.nonces m (some v))) WCT9.digestAttemptLimit 0 s1)
      apply spmf_ev_mono
      intro r hr
      refine (ev_expose_finish_le hU slot q ω request v r.1 r.2).trans (le_of_eq ?_)
      have hsupp := search_support slot v m s1 r hr
      obtain ⟨hext, hrep⟩ := replays_of_search v m _ _ hsupp
      obtain ⟨-, -, -, -, hg, hnon, hbir, hexp⟩ := search_frame slot v m WCT9.digestAttemptLimit 0 s1 r hr
      have hnon1 : r.2.memory.1.nonces = Function.update s.memory.1.nonces m (some v) := hnon
      have hbir1 : r.2.memory.1.births = s.memory.1.births := hbir
      have hexp1 : r.2.memory.1.exposures = s.memory.1.exposures := hexp
      have hext1 : Extends s.memory.1.rows r.2.memory.1.rows := hext
      have hgr : r.2.memory.2 = ⟨(s.memory.2.reused || decide (nearSpec.Reuse s.memory.1.rows v m)), true,
          s.memory.2.fresh⟩ := hg.trans hg1
      have hinv' : InvM (r.2.memory.1.expose (r.1.map Prod.snd),
          ghostStep r.2.memory.1 (.expose (r.1.map Prod.snd)) () r.2.memory.2) := by
        rw [hgr]
        simp only [ghostStep, if_true]
        refine ⟨fun x hx => ?_, ?_, fun m' rho' hm' => ?_⟩
        · simp only [LazyMem.expose, List.mem_append] at hx ⊢
          rcases hx with hx | hx
          · rw [hexp1] at hx; exact Or.inl (hI1 x hx)
          · exact Or.inr hx
        · simp only [LazyMem.expose, List.length_append]
          rw [hexp1]
          exact Nat.add_le_add_right hI2 _
        · simp only [LazyMem.expose] at hm' ⊢
          rw [hnon1] at hm'
          by_cases he : m' = m
          · subst he
            simp only [Function.update_self, Option.some.injEq] at hm'
            subst hm'
            exact ⟨r.1, hrep, fun x hx => List.mem_append_right _ hx⟩
          · rw [Function.update_of_ne he] at hm'
            obtain ⟨f', hrep', hf'⟩ := hI3 m' rho' hm'
            exact ⟨f', hrep'.mono hext1, fun x hx => List.mem_append_left _ (hf' x hx)⟩
      unfold ΦI
      dsimp only
      rw [if_pos hinv']
      unfold ghostPot
      rw [hgr]
      simp only [ghostStep, if_true, LazyMem.expose]
      rw [hbir1, hnon1]
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem honestMsg_short {A T : Correctness.Answers} (h : Wots.Ref.ShortAgree A T) (index : Nat) (lay : Layer) :
    Extract.honestMsg A index lay = Extract.honestMsg T index lay := by
  unfold Extract.honestMsg
  split_ifs
  · exact Wots.Ref.honestRoot_short h _ _
  · exact Wots.Ref.honestForest_short h _
theorem good_short {A T : Correctness.Answers} (h : Wots.Ref.ShortAgree A T) (w : WBytes) (index : Nat) (lay : Layer)
    (hg : Extract.Good A w index lay) : Extract.Good T w index lay := by
  obtain ⟨digits, ⟨hctr, hdec⟩, hpath, hchain⟩ := hg
  refine ⟨digits, ⟨hctr, ?_⟩, ?_, ?_⟩
  · rw [← honestMsg_short h]
    rw [← Wots.Ref.ShortRespects.shortHash _ (Wots.Ref.short_of_le _ (by simp [encodingInput, SphincsSecurity.bytesLE_length])) A T h]
    exact hdec
  · intro j hj
    obtain ⟨h1, h2⟩ := hpath j hj
    exact ⟨by rw [h1, Wots.Ref.builtTree_short h], h2⟩
  · intro i hi
    obtain ⟨h1, h2⟩ := hchain i hi
    refine ⟨?_, h2⟩
    rw [h1]
    unfold Correctness.leafValue
    rw [Wots.Ref.leafSeed_short h, Wots.Ref.chainValue_short h]
def NearIn (A : Correctness.Answers) (log : QueryLog Requests) (entries : List Wots.Entry) : Prop :=
  ∃ (m : Message) (w : WBytes) (N : HashOutput) (f : BPair.FtsCoord),
    (pad64 (digestInput (wrho w) m (wdc w)), N) ∈ entries ∧
    evalWithAnswerFn A (digest (wrho w) m (wdc w)) = N ∧ Shaped N w ∧ digestGate N=true ∧
    (∀ lay : Layer, Extract.Good A w (N.toNat % 2 ^ 31) lay) ∧ ¬BPB.SignedDigest log m w ∧ log.length ≤ 2 ^ 32 ∧
    f ∈ BPair.openedPositions N ∧ BPair.GuessedIn A log entries f ∧
    ∀ g ∈ BPair.openedPositions N, g ≠ f → BPair.Disclosed A log g
theorem nearIn_short (A T : Correctness.Answers) (log : QueryLog Requests) (entries : List Wots.Entry)
    (h : Wots.Ref.ShortAgree A T) (hn : NearIn A log entries) : NearIn T log entries := by
  obtain ⟨m, w, N, f, hx, hN, hS, hgate, hgood, hsd, hlen, hf, hguess, hdis⟩ := hn
  refine ⟨m, w, N, f, hx, ?_, hS, hgate, fun lay => good_short h w _ lay (hgood lay), hsd, hlen, hf,
    BPair.guessedIn_short h log entries f hguess, fun g hg hne => BPair.disclosed_short h log g (hdis g hg hne)⟩
  rw [← BPair.eval_congr_allowed (BPair.digest_short _ _ _) h]
  exact hN
theorem nearIn_mono (A : Correctness.Answers) (log : QueryLog Requests) (entries entries' : List Wots.Entry)
    (hsub : ∀ e ∈ entries, e ∈ entries') (hn : NearIn A log entries) : NearIn A log entries' := by
  obtain ⟨m, w, N, f, hx, hN, hS, hgate, hgood, hsd, hlen, hf, hguess, hdis⟩ := hn
  exact ⟨m, w, N, f, hsub _ hx, hN, hS, hgate, hgood, hsd, hlen, hf, BPair.guessedIn_mono A log entries entries' hsub f hguess,
    hdis⟩
theorem near_shared (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) (hnear : PinnedC adversary NearQ z) :
    ∀ generated interaction checked, Wots.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction
      checked → NearIn z.2 interaction.value.2 (BPair.publicEntries checked.events) := by
  obtain ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hCat, hQ⟩ := hnear
  intro g' i' c' hs'
  obtain ⟨hg', hi', hce⟩ := split_events_unique adversary _ g i c g' i' c' hs hs'
  rw [hce, hi']
  have hagree := (SeccLaw.completed_agrees adversary q hq z hz).2
  have hstate : c.state = z.1.2.2.base.source.2 := (congrArg FirstHit.Recorded.state hs.2.2.2).symm
  have hvalue : c.value = true := (congrArg FirstHit.Recorded.value hs.2.2.2).symm.trans hclean.1
  have ha : ∀ input answer, SourceReplay.known c.state input = some answer → z.2 input = answer :=
    fun input answer hk => hagree input answer (by rw [← hstate]; exact hk)
  obtain ⟨N, -, hN, -, hS, hgate, hgood, -⟩ := hCat
  obtain ⟨check, hcheck, hev, hst, m', w', hof', hv, hsub⟩ :=
    verdict_accepting g.value.1 i.value i.state c hs.2.2.1 z.2 ha hvalue f hf
  obtain ⟨rfl, rfl⟩ := witnessOf_unique hof hof'
  obtain ⟨N', -, hN', hdq, -⟩ := WotsExtract.verifyP_walk_wots_route z.2 m g.value.1 w hpk hv
  have hNN : N' = N := hN'.symm.trans hN
  subst hNN
  obtain ⟨prior, hevent⟩ := PaddedExtraction.public_occurrence _ (PaddedExtraction.check_hashOnly _ _ f) _ check hcheck
    z.2 (by rw [hst]; exact ha) _ (hsub _ hdq)
  rw [hev] at hevent
  have hans : z.2 (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w))))) = N' := hN'
  rw [hans] at hevent
  obtain ⟨f0, hf0, hguess, hdis⟩ := hQ
  rw [hN'] at hf0 hdis
  exact ⟨m, w, N', f0, mem_publicEntries hevent, hN', hS, hgate, hgood, hsd, hlen, hf0, hguess, hdis⟩
theorem caseC_not_signer_eval (answers : Correctness.Answers) (published : T3.Cache) (log : QueryLog Requests)
    (hsig : ∀ entry ∈ log, entry.2 = evalWithAnswerFn answers (FullGame.authenticatedSign published entry.1))
    (m : Message) (w : WBytes) (N : HashOutput)
    (hN : evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N) (hS : Shaped N w) (hgate : digestGate N=true)
    (hgood : ∀ lay : Layer, Extract.Good answers w (N.toNat % 2 ^ 31) lay)
    (hfresh : ¬BPB.SignedDigest log m w) :
    ∀ entry ∈ log, (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : T3.Spec.Domain) ∉
      queried answers (FullGame.authenticatedSign published entry.1) := by
  intro entry he hq
  obtain ⟨hc, hm, hrho, hq'⟩ := BPB.signer_digest_query answers published entry.1 _ _ _ hq
  rw [← BPB.ofNat_toNat32 (wdc w)] at hq'
  have hacc := BPB.rejected_trial_inadmissible answers (wrho w) m (wdc w).toNat hq'
    (by rw [BPB.ofNat_toNat32, hN]; simp [digestAdmissible,hS.2.1,hgate])
  rw [BPB.ofNat_toNat32, hN] at hacc
  have hsel : (evalWithAnswerFn answers (payloadRecordForNonce published (wrho w) m)).2 = some N := by
    unfold payloadRecordForNonce
    simp only [evalWithAnswerFn_bind, hacc, evalWithAnswerFn_pure]
  obtain ⟨sig, hsig', hsrho⟩ := BPB.selected_payload_succeeds answers published (wrho w) m N w hsel hgood
  apply hfresh
  refine ⟨entry, he, hm, sig, ?_, hsrho⟩
  rw [hsig entry he, BPB.eval_authenticatedSign, if_pos hc, hm, ← hm, ← hrho, hm]
  exact hsig'
end SigGolfCandidate.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M (wrho wdc)
open ClaudeWCT.W9.T3M (WBytes Shaped)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem honestMsg_short {A T : Correctness.Answers} (h : SigGolfCandidate.T3.Security.Wots.Ref.ShortAgree A T)
    (index : Nat) (lay : Layer) :
    ClaudeWCT.W9.T3M.Extract.honestMsg A index lay = ClaudeWCT.W9.T3M.Extract.honestMsg T index lay := by
  unfold ClaudeWCT.W9.T3M.Extract.honestMsg
  split_ifs
  · unfold ClaudeWCT.W9.T3M.Extract.honestPair
    rw [ClaudeWCT.W9.T3.Security.Wots.Ref.wotsTree_short h]
  · rw [ClaudeWCT.W9.T3.Security.Wots.Ref.honestForest_short h _]
theorem good_short {A T : Correctness.Answers} (h : SigGolfCandidate.T3.Security.Wots.Ref.ShortAgree A T) (w : WBytes)
    (index : Nat) (lay : Layer) (hg : ClaudeWCT.W9.T3M.Extract.Good A w index lay) :
    ClaudeWCT.W9.T3M.Extract.Good T w index lay := by
  obtain ⟨digits, ⟨hctr, hdec⟩, hpath, hchain⟩ := hg
  refine ⟨digits, ⟨hctr, ?_⟩, ?_, ?_⟩
  · rw [← honestMsg_short h]
    rw [← SigGolfCandidate.T3.Security.Wots.Ref.ShortRespects.shortHash _
      (by rw [ClaudeWCT.W9.T3M.BC.layerEncodingRow_length]; unfold SeccLaw.maxInputLength; omega) A T h]
    exact hdec
  · intro j hj
    obtain ⟨h1, h2⟩ := hpath j hj
    exact ⟨by rw [h1, ClaudeWCT.W9.T3.Security.Wots.Ref.wotsTree_short h], h2⟩
  · intro i hi
    obtain ⟨h1, h2⟩ := hchain i hi
    refine ⟨?_, h2⟩
    rw [h1]
    unfold WCT9.wotsValue
    rw [ClaudeWCT.W9.T3.Security.Wots.Ref.wotsSeed_short h, SigGolfCandidate.T3.Security.Wots.Ref.chainValue_short h]
theorem goodZ_short {A T : Correctness.Answers} (h : SigGolfCandidate.T3.Security.Wots.Ref.ShortAgree A T)
    (w : WBytes) (index : Nat) (lay : Layer) (hg : ClaudeWCT.W9.T3M.BC.GoodZ A w index lay) :
    ClaudeWCT.W9.T3M.BC.GoodZ T w index lay :=
  ⟨good_short h w index lay hg.1, hg.2⟩
theorem slotDisclosed_short {A T : Correctness.Answers} (h : SigGolfCandidate.T3.Security.Wots.Ref.ShortAgree A T)
    (log : QueryLog Requests) (N : HashOutput) (k : WCT9.Coord) (t : Fin 7) (hd : SlotDisclosed A log N k t) :
    SlotDisclosed T log N k t := by
  obtain ⟨entry, he, signature, output, hs, ho, h1, h2, h3⟩ := hd
  exact ⟨entry, he, signature, output, hs, by rw [← WPair.signedOutput_short h]; exact ho, h1, h2, h3⟩
def NearIn (A : Correctness.Answers) (log : QueryLog Requests) (entries : List Wots.Entry) : Prop :=
  ∃ (m : Message) (w : WBytes) (N : HashOutput) (k : WCT9.Coord) (t : Fin 7) (c : Guess.GCoord),
    (pad64 (digestInput (wrho w) m (wdc w)), N) ∈ entries ∧
    evalWithAnswerFn A (digest (wrho w) m (wdc w)) = N ∧ Shaped N w ∧
    (∀ lay : Layer, ClaudeWCT.W9.T3M.BC.GoodZ A w (N.toNat % 2 ^ 31) lay) ∧ ¬SignedDigest log m w ∧
    log.length ≤ 2 ^ 32 ∧
    c.1 = Guess.chainOf N k t ∧ c.2.val = 3 - Guess.deficit N k t ∧ WPair.GuessedIn A log entries c ∧
    (∀ k' t', (k', t') ≠ (k, t) → SlotDisclosed A log N k' t') ∧ BPB.SignerComplete A
theorem nearIn_short (A T : Correctness.Answers) (log : QueryLog Requests) (entries : List Wots.Entry)
    (h : SigGolfCandidate.T3.Security.Wots.Ref.ShortAgree A T) (hn : NearIn A log entries) : NearIn T log entries := by
  obtain ⟨m, w, N, k, t, c, hx, hN, hS, hgood, hsd, hlen, h1, h2, hguess, hdis, hcomp⟩ := hn
  refine ⟨m, w, N, k, t, c, hx, ?_, hS, fun lay => goodZ_short h w _ lay (hgood lay), hsd, hlen, h1, h2,
    WPair.guessedIn_short h log entries c hguess, fun k' t' hne => slotDisclosed_short h log N k' t' (hdis k' t' hne),
    BPB.signerComplete_short h hcomp⟩
  rw [← WPair.eval_congr_allowed (WPair.digest_short _ _ _) h]
  exact hN
theorem nearIn_mono (A : Correctness.Answers) (log : QueryLog Requests) (entries entries' : List Wots.Entry)
    (hsub : ∀ e ∈ entries, e ∈ entries') (hn : NearIn A log entries) : NearIn A log entries' := by
  obtain ⟨m, w, N, k, t, c, hx, hN, hS, hgood, hsd, hlen, h1, h2, hguess, hdis, hcomp⟩ := hn
  exact ⟨m, w, N, k, t, c, hsub _ hx, hN, hS, hgood, hsd, hlen, h1, h2,
    WPair.guessedIn_mono A log entries entries' hsub c hguess, hdis, hcomp⟩
theorem near_shared (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) (hnear : PinnedC caseCExtraction adversary NearQ z) :
    ∀ generated interaction checked, GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction
      checked → NearIn z.2 interaction.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries checked.events) := by
  obtain ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hCat, hQ⟩ := hnear
  intro g' i' c' hs'
  obtain ⟨hg', hi', hce⟩ := split_events_unique adversary _ g i c g' i' c' hs hs'
  rw [hce, hi']
  have hagree := (SeccLaw.completed_agrees adversary q hq z hz).2
  have hstate : c.state = z.1.2.2.base.source.2 := (congrArg FirstHit.Recorded.state hs.2.2.2).symm
  have hvalue : c.value = true := (congrArg FirstHit.Recorded.value hs.2.2.2).symm.trans hclean.1
  have ha : ∀ input answer, SourceReplay.known c.state input = some answer → z.2 input = answer :=
    fun input answer hk => hagree input answer (by rw [← hstate]; exact hk)
  obtain ⟨N, -, hN, -, hS, hgood, -, hcomp⟩ := (show BPB.CaseCAt z.2 m w _ from hCat)
  obtain ⟨check, hcheck, hev, hst, m', w', hof', hv, hsub⟩ :=
    verdict_accepting g.value.1 i.value i.state c hs.2.2.1 z.2 ha hvalue f hf
  obtain ⟨rfl, rfl⟩ := witnessOf_unique hof hof'
  obtain ⟨N', -, hN', hdq, -⟩ := ClaudeWCT.W9.T3M.WctExtract.verifyP_walk_wct z.2 m g.value.1 w hv
  have hNN : N' = N := hN'.symm.trans hN
  subst hNN
  obtain ⟨prior, hevent⟩ := SigGolfCandidate.T3.Security.PaddedExtraction.public_occurrence _
    (PaddedExtraction.check_hashOnly _ _ f) _ check hcheck z.2 (by rw [hst]; exact ha) _ (hsub _ hdq)
  rw [hev] at hevent
  have hans : z.2 (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w))))) = N' := hN'
  rw [hans] at hevent
  obtain ⟨k, t, c0, h1, h2, hguess, hdis⟩ := hQ
  rw [hN'] at h1 h2 hdis
  exact ⟨m, w, N', k, t, c0, SigGolfCandidate.T3.Security.CaseC.mem_publicEntries hevent, hN', hS, hgood, hsd, hlen,
    h1, h2, hguess, hdis, hcomp⟩
theorem caseC_not_signer_eval (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (log : QueryLog Requests)
    (hsig : ∀ entry ∈ log, entry.2 = evalWithAnswerFn answers (FullGame.authenticatedSign published entry.1))
    (m : Message) (w : WBytes) (hcomp : BPB.SignerComplete answers) (hfresh : ¬SignedDigest log m w) :
    ∀ entry ∈ log, (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : SigGolfCandidate.T3.Spec.Domain) ∉
      queried answers (FullGame.authenticatedSign published entry.1) := by
  intro entry he hq
  obtain ⟨hc, hm, hrho, -⟩ := BPB.signer_digest_query answers published entry.1 _ _ _ hq
  obtain ⟨sig, hsig', hsrho⟩ := BPB.payload_succeeds_of_complete answers hcomp published (wrho w) m
  apply hfresh
  refine ⟨entry, he, hm, sig, ?_, hsrho⟩
  rw [hsig entry he, BPB.eval_authenticatedSign, if_pos hc, ← hrho, hm]
  exact hsig'
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SigGolfCandidate.T3.Security.BPair (LazyMem)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section WorldBoundL
open SecretGuessObservation (fixedRun lazyRun)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
theorem fts_event_le_worldL (adversary : AdversaryP)
    (event : (Guess.GCoord → Digest) → (Bool × QueryLog Requests × List Wots.Entry) → Prop)
    (wevent : (Bool × QueryLog Requests × List Wots.Entry) × WStateL → Prop)
    (himp : ∀ g result, fixedRun (envE (digestOf ω) (nonceOf ω)) g (worldGameL hU ω adversary) initL result ≠ 0 →
      event g result.1 → wevent result) :
    Pr[fun x => event x.1 x.2 | ftsRun hU ω adversary] ≤
      Pr[wevent | lazyRun (envE (digestOf ω) (nonceOf ω)) (worldGameL hU ω adversary) initL] := by
  rw [← SecretGuessObservation.run_erasure _ (worldGameL hU ω adversary) initL (fun _ => Finset.univ_nonempty)]
  unfold ftsRun secretsLaw
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro g
  apply mul_le_mul' le_rfl
  rw [probEvent_map, ← fixed_worldGameL hU ω g adversary, probEvent_map]
  apply probEvent_mono
  intro result hr he
  exact himp g result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr) he
end WorldBoundL
section Chain
theorem near_chain (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (P : Answers → QueryLog Requests → List Wots.Entry → Prop)
    (hshort : ∀ A T log entries, Wots.Ref.ShortAgree A T → P A log entries → P T log entries)
    (hmono : ∀ A log entries entries', (∀ e ∈ entries, e ∈ entries') → P A log entries → P A log entries')
    (payoff : (Bool × QueryLog Requests × List Wots.Entry) × WStateL → ENNReal)
    (hevent : ∀ ω g r, SecretGuessObservation.fixedRun (envE (digestOf ω) (nonceOf ω)) g
        (worldGameL (canon_subset adversary) ω adversary) initL r ≠ 0 →
      r.1.2.2.length ≤ q → P (wA (canon_subset adversary) ω g) r.1.2.1 r.1.2.2 →
      r.2.guesses.Nonempty ∧ 1 ≤ payoff r) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ∀ generated interaction checked,
        CaseC.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
          P z.2 interaction.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries checked.events) |
        SeccLaw.completedExperiment adversary q hq] ≤
      ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' ω, Pr[= ω | omegaLaw adversary] *
        ∑' r, Pr[= r | SecretGuessObservation.forcedRun envL slot (worldGameL (canon_subset adversary) ω adversary)
          initL] * payoff r := by
  refine (shared_le_pair adversary q hq P hshort hmono).trans ?_
  rw [pairExperiment_avg]
  have hω : ∀ ω : CanonTable.Omega (Wots.referenceInputs adversary),
      Pr[fun x => x.2.2.2.length ≤ q ∧ P (wA (canon_subset adversary) ω x.1) x.2.2.1 x.2.2.2 |
        ftsRun (canon_subset adversary) ω adversary] ≤
      ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' r,
        Pr[= r | SecretGuessObservation.forcedRun (envE (digestOf ω) (nonceOf ω)) slot
          (worldGameL (canon_subset adversary) ω adversary) initL] * payoff r := by
    intro ω
    refine (fts_event_le_worldL (canon_subset adversary) ω adversary
      (fun g run => run.2.2.length ≤ q ∧ P (wA (canon_subset adversary) ω g) run.2.1 run.2.2)
      (fun r => r.2.guesses.Nonempty ∧ r.2.probes ≤ q ∧ 1 ≤ payoff r) ?_).trans ?_
    · rintro g r hr ⟨hlen, hP⟩
      obtain ⟨hg, hp⟩ := hevent ω g r hr hlen hP
      exact ⟨hg, (worldGameL_tracking (canon_subset adversary) ω g adversary r hr).1.trans hlen, hp⟩
    · have h := SigGolfCandidate.T3.Security.BPair.lazyRun_event_le_forced_of (envE (digestOf ω) (nonceOf ω))
        (worldGameL (canon_subset adversary) ω adversary) LazyMem.empty q
        (fun r => r.2.guesses.Nonempty ∧ r.2.probes ≤ q ∧ 1 ≤ payoff r) payoff (fun _ _ h => h)
      rw [card_digest] at h
      exact h
  calc (∑' ω, Pr[= ω | omegaLaw adversary] *
        Pr[fun x => x.2.2.2.length ≤ q ∧ P (wA (canon_subset adversary) ω x.1) x.2.2.1 x.2.2.2 |
          ftsRun (canon_subset adversary) ω adversary])
      ≤ ∑' ω, Pr[= ω | omegaLaw adversary] * (((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' r,
          Pr[= r | SecretGuessObservation.forcedRun (envE (digestOf ω) (nonceOf ω)) slot
            (worldGameL (canon_subset adversary) ω adversary) initL] * payoff r) :=
        ENNReal.tsum_le_tsum fun ω => mul_le_mul' le_rfl (hω ω)
    _ = ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' ω, Pr[= ω | omegaLaw adversary] *
          ∑' r, Pr[= r | SecretGuessObservation.forcedRun (envE (digestOf ω) (nonceOf ω)) slot
            (worldGameL (canon_subset adversary) ω adversary) initL] * payoff r := by
        simp only [Finset.mul_sum, mul_left_comm (Pr[= _ | omegaLaw adversary])]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        exact Finset.sum_congr rfl fun slot _ => ENNReal.tsum_mul_left
    _ = _ := congrArg (fun t => ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * t)
        (Finset.sum_congr rfl fun slot _ => forced_avg_eq_lazy adversary slot payoff)
end Chain
end ClaudeWCT.W9.T3.Security.WPair
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M (wrho wdc)
open ClaudeWCT.W9.T3M (WBytes Shaped)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem interactionT_honest (T : Correctness.Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (oa : OracleComp LazyPrivate.Interaction α) (r : α × QueryLog Requests × List Wots.Entry)
    (hr : r ∈ support (WPair.interactionT T published oa)) :
    (∀ e ∈ r.2.1, e.2 = evalWithAnswerFn T (FullGame.authenticatedSign published e.1)) ∧
      ∀ e ∈ r.2.2, e.2 = T (.inl (.inr e.1)) := by
  induction oa using OracleComp.inductionOn generalizing r with
  | pure value =>
      rw [WPair.interactionT_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [WPair.interactionT_coin, mem_support_bind_iff] at hr
        obtain ⟨coin, -, hr⟩ := hr
        exact ih coin r hr
      · rw [WPair.interactionT_public, mem_support_bind_iff] at hr
        obtain ⟨rest, hrest, hr⟩ := hr
        rw [support_pure, Set.mem_singleton_iff] at hr
        subst hr
        obtain ⟨h1, h2⟩ := ih _ rest hrest
        refine ⟨h1, fun e he => ?_⟩
        rcases List.mem_cons.mp he with he | he
        · subst he; rfl
        · exact h2 e he
      · rw [WPair.interactionT_request, mem_support_bind_iff] at hr
        obtain ⟨rest, hrest, hr⟩ := hr
        rw [support_pure, Set.mem_singleton_iff] at hr
        subst hr
        obtain ⟨h1, h2⟩ := ih _ rest hrest
        refine ⟨fun e he => ?_, h2⟩
        rcases List.mem_cons.mp he with he | he
        · subst he; rfl
        · exact h1 e he
theorem entriesOf_honest (T : Correctness.Answers) (qs : List SigGolfCandidate.T3.Spec.Domain) :
    ∀ e ∈ Wots.entriesOf T qs, e.2 = T (.inl (.inr e.1)) := by
  intro e he
  unfold Wots.entriesOf at he
  rw [List.mem_filterMap] at he
  obtain ⟨q, -, hq⟩ := he
  rcases q with (c | input) | p
  · cases hq
  · cases hq; rfl
  · cases hq
theorem pairRun_honest (T : Correctness.Answers) (adversary : AdversaryP)
    (r : Bool × QueryLog Requests × List Wots.Entry) (hr : r ∈ support (WPair.pairRun T adversary)) :
    (∀ e ∈ r.2.1, e.2 = evalWithAnswerFn T (FullGame.authenticatedSign
        (evalWithAnswerFn T SigGolfCandidate.T3.keygen).2 e.1)) ∧
      ∀ e ∈ r.2.2, e.2 = T (.inl (.inr e.1)) := by
  unfold WPair.pairRun at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨interaction, hi, hr⟩ := hr
  rw [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  obtain ⟨h1, h2⟩ := interactionT_honest T _ _ interaction hi
  refine ⟨h1, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact h2 e he
  · exact entriesOf_honest T _ e he
theorem payoff_of_ghosts (q : Nat) (T : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (r : (Bool × QueryLog Requests × List Wots.Entry) × WPair.WStateL)
    (hlog : ∀ e ∈ r.1.2.1, e.2 = evalWithAnswerFn T (FullGame.authenticatedSign published e.1))
    (hexp : ∀ entry ∈ r.1.2.1, ∀ σ output, entry.2 = some σ →
      signedOutput T entry.1.message σ = some output → output ∈ r.2.memory.exposures)
    (hrows : ∀ x a, (x, a) ∈ r.1.2.2 → x ∈ SigGolfCandidate.T3.Security.BPair.digestInputs →
      a ∈ r.2.memory.births ∨ x ∈ r.2.memory.trials)
    (htrials : ∀ x ∈ r.2.memory.trials, ∃ entry ∈ r.1.2.1,
      (.inl (.inr x) : SigGolfCandidate.T3.Spec.Domain) ∈ queried T (FullGame.authenticatedSign published entry.1))
    (hbirths : r.2.memory.births.length ≤ r.1.2.2.length)
    (hexplen : r.2.memory.exposures.length ≤ r.1.2.1.length)
    (hq : r.1.2.2.length ≤ q) (hP : NearIn T r.1.2.1 r.1.2.2) : 1 ≤ WPair.nearPayoff q r := by
  obtain ⟨m, w, N, k, t, c, hx, hN, hS, hgood, hsd, hlen, -, -, -, hdis, hcomp⟩ := hP
  have hbirth : N ∈ r.2.memory.births := by
    rcases hrows _ N hx (SigGolfCandidate.T3.Security.BPair.digestInput_mem _ _ _) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨entry, he, hqe⟩ := htrials _ ht
      exact caseC_not_signer_eval T published r.1.2.1 hlog m w hcomp hsd entry he hqe
  have hcov : Guess.NearCoveredBy r.2.memory.exposures N := by
    refine ⟨k, t, fun k' t' hne => ?_⟩
    obtain ⟨entry, he, σ, output, hσ, hout, h1, h2, h3⟩ := hdis k' t' hne
    exact ⟨output, hexp entry he σ output hσ hout, congrArg Fin.val h1, h2, h3⟩
  unfold WPair.nearPayoff
  rw [if_pos ⟨hbirths.trans hq, hexplen.trans hlen, N, hbirth, hS, hcov⟩]
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem worldGame_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
    (adversary : AdversaryP) (slot q : Nat) :
    SuperProg (implG slot) (ΦI q) (WPair.worldGameCore hU ω adversary) :=
  worldGameCore_super hU (implG slot) (ΦI q) ω adversary (coin_ΦI slot q) (hashL_ΦI hU slot q ω)
    (fun published request => signL_ΦI hU slot q ω published request)
theorem forced_payoff_le {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
    (adversary : AdversaryP) (slot q : Nat) :
    expectedValue (SecretGuessObservation.forcedRun WPair.envL slot (WPair.worldGameCore hU ω adversary) WPair.initL)
      (WPair.nearPayoff q) ≤ (q : ENNReal) * 404 / 2 ^ 128 := by
  unfold SecretGuessObservation.forcedRun
  rw [← projS_initG, expectedValue_project WPair.envL slot _ initG (WPair.nearPayoff q)]
  calc
    _ ≤ expectedValue (SecretGuessObservation.runWith (implG slot) (WPair.worldGameCore hU ω adversary) initG)
        (fun r => ΦI q r.2) := expectedValue_mono _ fun r => payoff_le_ΦI q r
    _ ≤ ΦI q initG := worldGame_ΦI hU ω adversary slot q initG
    _ ≤ _ := ΦI_initial q
theorem forced_payoff_sum_le {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
    (adversary : AdversaryP) (slot q : Nat) :
    ∑' r, Pr[= r | SecretGuessObservation.forcedRun WPair.envL slot (WPair.worldGameCore hU ω adversary)
      WPair.initL] * WPair.nearPayoff q r ≤ (q : ENNReal) * 404 / 2 ^ 128 :=
  forced_payoff_le hU ω adversary slot q
end ClaudeWCT.W9.T3.Security.CaseC
end
section
namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M (WBytes Shaped)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP)
open SigGolfCandidate.T3.Security.CaseC (pmf_probEvent_mono_support)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def NearAll (adversary : AdversaryP) (q : Nat) (z : PaddedGame.TraceResult × Correctness.Answers) : Prop :=
  QueryRecorded.CleanWin q z.1 ∧ ∀ generated interaction checked,
    GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
      NearIn z.2 interaction.value.2 (SigGolfCandidate.T3.Security.BPair.publicEntries checked.events)
theorem near_le_all (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC caseCExtraction adversary NearQ z |
        SeccLaw.completedExperiment adversary q hq] ≤
      Pr[NearAll adversary q | SeccLaw.completedExperiment adversary q hq] := by
  apply pmf_probEvent_mono_support
  intro z hz h
  exact ⟨h.1, near_shared adversary q hq z hz h.1 h.2⟩
theorem omega_avg_le {Ω : Type} (L : ProbComp Ω) (f : Ω → ENNReal) (B : ENNReal) (h : ∀ ω, f ω ≤ B) :
    ∑' ω, Pr[= ω | L] * f ω ≤ B :=
  calc
    _ ≤ ∑' ω, Pr[= ω | L] * B := ENNReal.tsum_le_tsum fun ω => mul_le_mul' le_rfl (h ω)
    _ = (∑' ω, Pr[= ω | L]) * B := ENNReal.tsum_mul_right
    _ ≤ 1 * B := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = B := one_mul B
theorem fixed_support_pairRun (adversary : AdversaryP) (ω : CanonTable.Omega (Wots.referenceInputs adversary))
    (g : Guess.GCoord → Digest) (r : (Bool × QueryLog Requests × List Wots.Entry) × WPair.WStateL)
    (hr : SphincsSecurity.Concrete.SecretGuessObservation.fixedRun (WPair.envE (WPair.digestOf ω) (WPair.nonceOf ω)) g
      (WPair.worldGameL (WPair.canon_subset adversary) ω adversary) WPair.initL r ≠ 0) :
    r.1 ∈ support (WPair.pairRun (WPair.wA (WPair.canon_subset adversary) ω g) adversary) := by
  rw [mem_support_iff, probOutput_def, ← WPair.fixed_worldGameL (WPair.canon_subset adversary) ω g adversary,
    map_eq_bind_pure_comp]
  rw [SphincsSecurity.Concrete.RetainedObservation.bind_nonzero]
  refine ⟨r, hr, ?_⟩
  simp only [Function.comp_apply, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]
theorem near_event (adversary : AdversaryP) (q : Nat) (ω : CanonTable.Omega (Wots.referenceInputs adversary))
    (g : Guess.GCoord → Digest) (r : (Bool × QueryLog Requests × List Wots.Entry) × WPair.WStateL)
    (hr : SphincsSecurity.Concrete.SecretGuessObservation.fixedRun (WPair.envE (WPair.digestOf ω) (WPair.nonceOf ω)) g
      (WPair.worldGameL (WPair.canon_subset adversary) ω adversary) WPair.initL r ≠ 0)
    (hq : r.1.2.2.length ≤ q) (hP : NearIn (WPair.wA (WPair.canon_subset adversary) ω g) r.1.2.1 r.1.2.2) :
    r.2.guesses.Nonempty ∧ 1 ≤ WPair.nearPayoff q r := by
  obtain ⟨hexp, hrows, -, htrack, hbirths, htrials, hexplen⟩ :=
    WPair.worldGameL_bank (WPair.canon_subset adversary) ω g adversary r hr
  obtain ⟨hlog, -⟩ := pairRun_honest _ adversary r.1 (fixed_support_pairRun adversary ω g r hr)
  refine ⟨?_, payoff_of_ghosts q _ _ r hlog hexp (fun x a hx hd => (hrows x a hx hd).2) htrials hbirths
    hexplen hq hP⟩
  obtain ⟨-, -, -, -, -, c, -, -, -, -, -, -, -, -, hguess, -⟩ := hP
  exact Guess.nonempty_of_prefixIn (htrack c hguess)
noncomputable def nearTermTight (q : Nat) : ENNReal :=
  (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * (404 * q / 2 ^ 128)
theorem nearBoundTight : NearBound caseCExtraction NearQ nearTermTight := by
  intro adversary q hq _ _
  have hchain := WPair.near_chain adversary q hq NearIn nearIn_short nearIn_mono (WPair.nearPayoff q)
    (fun ω g r hr hlen hP => near_event adversary q ω g r hr hlen hP)
  have hslot : ∀ slot, (∑' ω, Pr[= ω | WPair.omegaLaw adversary] *
      ∑' r, Pr[= r | SphincsSecurity.Concrete.SecretGuessObservation.forcedRun WPair.envL slot
        (WPair.worldGameL (WPair.canon_subset adversary) ω adversary) WPair.initL] * WPair.nearPayoff q r) ≤
      (q : ENNReal) * 404 / 2 ^ 128 :=
    fun slot => omega_avg_le _ _ _ fun ω => forced_payoff_sum_le (WPair.canon_subset adversary) ω adversary slot q
  calc
    _ ≤ Pr[NearAll adversary q | SeccLaw.completedExperiment adversary q hq] := near_le_all adversary q hq
    _ ≤ _ := hchain
    _ ≤ ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ _slot ∈ Finset.range q, (q : ENNReal) * 404 / 2 ^ 128 :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun slot _ => hslot slot)
    _ = nearTermTight q := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      unfold nearTermTight
      simp only [div_eq_mul_inv]
      ring
theorem nearTermTight_le (q : Nat) : nearTermTight q ≤ Wots.nearTerm q := by
  unfold nearTermTight Wots.nearTerm
  apply mul_le_mul' le_rfl
  refine le_trans (le_of_eq ?_) (le_self_add.trans le_self_add)
  rfl
theorem nearBound : NearBound caseCExtraction NearQ Wots.nearTerm :=
  fun adversary q hq h1 h2 => (nearBoundTight adversary q hq h1 h2).trans (nearTermTight_le q)
theorem excessBound_horizon : ClaudeWCT.Bank.WCT.ExcessBound horizon (12500 / 100000000) :=
  ClaudeWCT.Numerics.WCTPrice.wct_excessBound_2_32
theorem caseC_small_bound_wct :
    CaseCSmallBound CaseCFreshPinned Wots.nearTerm WPair.pairTerm :=
  caseC_small_bound caseCExtraction (caseCSplitInterface WPair.pairTerm WPair.pair_guess_bound) Wots.nearTerm
    excessBound_horizon nearBound
theorem wots_caseCSmallBound : Wots.CaseCSmallBound :=
  Wots.caseCSmallBound_iff.mpr caseC_small_bound_wct
end ClaudeWCT.W9.T3.Security.CaseC
end
end
