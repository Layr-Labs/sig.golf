import SigGolfCandidate.OuterAuthenticatedSign
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
namespace OuterGameWith
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.FullGame
open ClaudeWCT.W9.T3.Security.PairedOuter
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq SiggolfT3Mac4.Cache := Classical.decEq _
noncomputable local instance : DecidableEq Region := Classical.decEq _
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : Fintype OtherCoordinate := otherFintype
noncomputable local instance : Fintype Region := CacheAuthentication.regionFintype
noncomputable local instance : SampleableType FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : SampleableType OtherTable := otherSampler
noncomputable local instance : SampleableType MacTable := CacheAuthentication.macTableSampler
structure Checker (Forgery : Type) where
  check : Digest → QueryLog ClaudeWCT.W9.T3.Security.PairedOuter.Requests → Forgery → M Bool
  nonMac : ∀ pk log forgery, NonMac (check pk log forgery)
variable {Forgery : Type}
abbrev AdversaryFor (Forgery : Type) :=
  Digest → SigGolfCandidate.T3.Cache → OracleComp ClaudeWCT.W9.T3.Security.PairedOuter.LazyPrivate.Interaction (Option Forgery)
noncomputable def verdict (checker : Checker Forgery) (publicKey : Digest)
    (result : Option Forgery × QueryLog ClaudeWCT.W9.T3.Security.PairedOuter.Requests) : M Bool := do
  let some forgery := result.1 | return false
  let verified ← checker.check publicKey result.2 forgery
  pure (decide (result.2.length ≤ 2^32) && verified)
theorem verdict_nonMac (checker : Checker Forgery) (publicKey : Digest)
    (result : Option Forgery × QueryLog ClaudeWCT.W9.T3.Security.PairedOuter.Requests) : NonMac (verdict checker publicKey result) := by
  unfold verdict
  cases result.1 with
  | none => exact SourceQueries.pure_allowed _ _
  | some forgery =>
      exact SourceQueries.bind_allowed _ (checker.nonMac publicKey result.2 forgery)
        (fun _ => SourceQueries.pure_allowed _ _)
noncomputable def game (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : M Bool := do
  let generated ← keygen
  let result ← ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.loggedWith (fun request => OuterSigning.sign request.cache request.message)
    (adversary generated.1 generated.2)
  verdict checker generated.1 result
noncomputable def realExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    ProbComp (Bool × Nat) :=
  sampleMasterSeed >>= fun secret =>
    (simulateQ romImpl (SphincsSecurity.countHashQueries
      (Derivation.realize (privateInput secret) (game checker adversary)))).run' ∅
noncomputable def tableExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (q : Nat) : ProbComp (Option (Bool × Nat)) :=
  ($ᵗ FullTable : ProbComp _) >>= fun outputs =>
    (simulateQ romImpl (Derivation.tableRun outputs (Derivation.cap (game checker adversary) q))).run' ∅
theorem private_derivation_event_bound (checker : Checker Forgery)
    (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2 ≤ q | realExperiment checker adversary] ≤
      Pr[fun outcome => ∃ result, outcome=some result ∧ result.1=true |
        tableExperiment checker adversary q] + q / ((2^256 : Nat) : ENNReal) :=
  Derivation.event_game_hop privateInput privateInput_injective
    privateInput_hit (game checker adversary) q hq (· = true)
noncomputable def countedTableExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let table ← ($ᵗ FullTable : ProbComp _)
  run table (game checker adversary) (0,∅)
theorem counted_table_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment checker adversary]=
      Pr[fun outcome => ∃ result,outcome=some result ∧ result.1=true | tableExperiment checker adversary q] := by
  unfold countedTableExperiment tableExperiment
  simp only [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro table
  apply congrArg
  exact table_cap_event table (game checker adversary) ∅ q (·=true)
theorem real_to_counted_table (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment checker adversary]+
        q/((2^256 : Nat) : ENNReal) := by
  rw [counted_table_event]
  exact private_derivation_event_bound checker adversary q hq
noncomputable def splitTableExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let other ← ($ᵗ OtherTable : ProbComp _)
  let mac ← ($ᵗ MacTable : ProbComp _)
  run (joinTable other mac) (game checker adversary) (0,∅)
theorem table_experiment_split (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    𝒮[countedTableExperiment checker adversary]=𝒮[splitTableExperiment checker adversary] :=
  uniform_table_split_bind (fun table => run table (game checker adversary) (0,∅))
noncomputable def checkContinuation (checker : Checker Forgery) (other : OtherTable) (publicKey : Digest)
    (result : (Option Forgery × QueryLog ClaudeWCT.W9.T3.Security.PairedOuter.Requests) × CountState) : ProbComp (Bool × CountState) :=
  (simulateQ (baseHandler other) (verdict checker publicKey result.1)).run result.2
noncomputable def realRest (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) (state : CountState) : ProbComp (Bool × CountState) :=
  ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run (worldHandler other) (OuterMacGame.realSigner (baseHandler other) mac)
    (adversary publicKey published) state >>= checkContinuation checker other publicKey
noncomputable def idealRest (checker : Checker Forgery) (other : OtherTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) (state : CountState) : ProbComp (Bool × CountState) :=
  ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run (worldHandler other) (OuterMacGame.idealSigner (baseHandler other) published)
    (adversary publicKey published) state >>= checkContinuation checker other publicKey
theorem logged_source_run (other : OtherTable) (mac : MacTable)
    (program : OracleComp ClaudeWCT.W9.T3.Security.PairedOuter.LazyPrivate.Interaction (Option Forgery)) (state : CountState) :
    (simulateQ (SigGolfCandidate.T3.Security.MacGame.sourceHandler (baseHandler other) mac) (ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.loggedWith (fun request => OuterSigning.sign request.cache request.message) program)).run state=
      ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run (worldHandler other) (OuterMacGame.realSigner (baseHandler other) mac) program state := by
  rw [ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.loggedWith_interpretation]
  change ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run (worldHandler other)
    (fun request => simulateQ (SigGolfCandidate.T3.Security.MacGame.sourceHandler (baseHandler other) mac)
      (OuterSigning.sign request.cache request.message)) program state=_
  exact congrArg (fun signer => ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run (worldHandler other) signer program state)
    (funext fun request => OuterMacGame.source_signer_eq (baseHandler other) mac request)
theorem source_rest_run (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) (state : CountState) :
    (simulateQ (SigGolfCandidate.T3.Security.MacGame.sourceHandler (baseHandler other) mac) (do
      let result ← ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.loggedWith (fun request => OuterSigning.sign request.cache request.message) (adversary publicKey published)
      verdict checker publicKey result)).run state=
      realRest checker other mac adversary publicKey published state := by
  rw [simulateQ_bind,StateT.run_bind,logged_source_run]
  unfold realRest
  apply bind_congr
  intro result
  rw [SigGolfCandidate.T3.Security.MacGame.simulate_no_mac _ _ _ (verdict_nonMac checker publicKey result.1)]
  rfl
theorem fixed_game_expansion (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery) :
    run (joinTable other mac) (game checker adversary) (0,∅)=
      (do
        let generated ← (simulateQ (baseHandler other) keygenPayload).run (0,∅)
        realRest checker other mac adversary generated.1.1 ⟨SigGolfCandidate.T3.Security.MacGame.tagAt mac generated.1.2,generated.1.2⟩
          (generated.2.1+2,generated.2.2)) := by
  rw [run,tableHandler_split,game]
  simp only [keygen,bind_assoc,pure_bind,simulateQ_bind,StateT.run_bind]
  rw [SigGolfCandidate.T3.Security.MacGame.simulate_no_mac _ _ _ keygenPayload_nonMac]
  apply bind_congr
  intro generated
  rw [source_mac_run,pure_bind]
  simpa only [simulateQ_bind,StateT.run_bind] using
    source_rest_run checker other mac adversary generated.1.1
      ⟨SigGolfCandidate.T3.Security.MacGame.tagAt mac generated.1.2,generated.1.2⟩ (generated.2.1+2,generated.2.2)
theorem refresh_published_mac (checker : Checker Forgery) (other : OtherTable) (adversary : AdversaryFor Forgery)
    (generated : (Digest × Region) × CountState) :
    𝒮[do
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest checker other mac adversary generated.1.1 ⟨SigGolfCandidate.T3.Security.MacGame.tagAt mac generated.1.2,generated.1.2⟩
        (generated.2.1+2,generated.2.2)]=
    𝒮[do
      let tag ← ($ᵗ HashOutput : ProbComp _)
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest checker other (SigGolfCandidate.T3.Security.MacGame.retag mac ⟨tag,generated.1.2⟩) adversary
        generated.1.1 ⟨tag,generated.1.2⟩ (generated.2.1+2,generated.2.2)] := by
  exact MacGame.refresh_published generated.1.2 (fun tag mac =>
    realRest checker other mac adversary generated.1.1 ⟨tag,generated.1.2⟩
      (generated.2.1+2,generated.2.2))
noncomputable def preparedExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let prepared ← setup
  let mac ← ($ᵗ MacTable : ProbComp _)
  realRest checker prepared.other (SigGolfCandidate.T3.Security.MacGame.retag mac prepared.published)
    adversary prepared.publicKey prepared.published prepared.state
noncomputable def authenticatedExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let prepared ← setup
  idealRest checker prepared.other adversary prepared.publicKey prepared.published prepared.state
theorem split_experiment_prepared (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    𝒮[splitTableExperiment checker adversary]=𝒮[preparedExperiment checker adversary] := by
  unfold splitTableExperiment preparedExperiment setup
  simp only [bind_assoc,pure_bind]
  apply evalSPMF_bind_congr'
  intro other
  simp_rw [fixed_game_expansion]
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro generated
  exact refresh_published_mac checker other adversary generated
theorem checkContinuation_long (checker : Checker Forgery) (other : OtherTable) (publicKey : Digest)
    (result : (Option Forgery × QueryLog ClaudeWCT.W9.T3.Security.PairedOuter.Requests) × CountState)
    (hlong : 2^32 < result.1.2.length) (q : Nat) :
    Pr[fun outcome => outcome.1=true ∧ outcome.2.1≤q | checkContinuation checker other publicKey result]=0 := by
  have hn : ¬result.1.2.length≤2^32 := Nat.not_le.mpr hlong
  unfold checkContinuation verdict
  cases result.1.1 with
  | none => simp [StateT.run_pure]
  | some forgery =>
      simp
      intro count cache _ hshort
      exact False.elim (hn hshort)
theorem rest_authentication_bound (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (prepared : Setup) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | do
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest checker prepared.other (SigGolfCandidate.T3.Security.MacGame.retag mac prepared.published)
        adversary prepared.publicKey prepared.published prepared.state] ≤
    Pr[fun result => result.1=true ∧ result.2.1≤q |
      idealRest checker prepared.other adversary prepared.publicKey prepared.published prepared.state]+
      ((2 : ENNReal)^152)⁻¹ := by
  have h := OuterMacGame.authentication_hop (worldHandler prepared.other) (baseHandler prepared.other)
    prepared.published (adversary prepared.publicKey prepared.published) (2^32) prepared.state
    (checkContinuation checker prepared.other prepared.publicKey) (fun result => result.1=true ∧ result.2.1≤q)
    (fun result hlong => checkContinuation_long checker prepared.other prepared.publicKey result hlong q)
  refine h.trans (add_le_add le_rfl ?_)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow]
theorem prepared_authentication_bound (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | preparedExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹ :=
  probEvent_bind_le_add setup _ _ _ _ (fun prepared => rest_authentication_bound checker adversary prepared q)
theorem real_to_authenticated (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  have h := real_to_counted_table checker adversary q hq
  have he := (table_experiment_split checker adversary).trans (split_experiment_prepared checker adversary)
  have hp : Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment checker adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | preparedExperiment checker adversary] :=
    probEvent_congr' (fun _ _ => Iff.rfl) he
  rw [hp] at h
  exact h.trans (add_le_add (prepared_authentication_bound checker adversary q) le_rfl)
noncomputable def idealGame (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : M Bool := do
  let generated ← keygen
  let result ← ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.loggedWith (OuterAuthenticatedSign.authenticatedSign generated.2) (adversary generated.1 generated.2)
  verdict checker generated.1 result
theorem ideal_rest_run (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) (state : CountState) :
    (simulateQ (SigGolfCandidate.T3.Security.MacGame.sourceHandler (baseHandler other) mac) (do
      let result ← ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.loggedWith (OuterAuthenticatedSign.authenticatedSign published) (adversary publicKey published)
      verdict checker publicKey result)).run state=idealRest checker other adversary publicKey published state := by
  rw [simulateQ_bind,StateT.run_bind,ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.loggedWith_interpretation]
  have hs : (fun request => simulateQ (SigGolfCandidate.T3.Security.MacGame.sourceHandler (baseHandler other) mac)
      (OuterAuthenticatedSign.authenticatedSign published request))=OuterMacGame.idealSigner (baseHandler other) published :=
    funext fun request => OuterAuthenticatedSign.interpretation other mac published request
  rw [hs]
  change ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run (worldHandler other) (OuterMacGame.idealSigner (baseHandler other) published)
    (adversary publicKey published) state >>= _ = _
  unfold idealRest
  apply bind_congr
  intro result
  rw [SigGolfCandidate.T3.Security.MacGame.simulate_no_mac _ _ _ (verdict_nonMac checker publicKey result.1)]
  rfl
theorem fixed_ideal_expansion (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery) :
    run (joinTable other mac) (idealGame checker adversary) (0,∅)=
      (do
        let generated ← (simulateQ (baseHandler other) keygenPayload).run (0,∅)
        idealRest checker other adversary generated.1.1 ⟨SigGolfCandidate.T3.Security.MacGame.tagAt mac generated.1.2,generated.1.2⟩
          (generated.2.1+2,generated.2.2)) := by
  rw [run,tableHandler_split,idealGame]
  simp only [keygen,bind_assoc,pure_bind,simulateQ_bind,StateT.run_bind]
  rw [SigGolfCandidate.T3.Security.MacGame.simulate_no_mac _ _ _ keygenPayload_nonMac]
  apply bind_congr
  intro generated
  rw [source_mac_run,pure_bind]
  simpa only [simulateQ_bind,StateT.run_bind] using
    ideal_rest_run checker other mac adversary generated.1.1
      ⟨SigGolfCandidate.T3.Security.MacGame.tagAt mac generated.1.2,generated.1.2⟩ (generated.2.1+2,generated.2.2)
noncomputable def idealTableExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let table ← ($ᵗ FullTable : ProbComp _)
  run table (idealGame checker adversary) (0,∅)
theorem ideal_table_authenticated (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    𝒮[idealTableExperiment checker adversary]=𝒮[authenticatedExperiment checker adversary] := by
  unfold idealTableExperiment
  rw [uniform_table_split_bind]
  unfold authenticatedExperiment setup
  simp only [bind_assoc,pure_bind]
  apply evalSPMF_bind_congr'
  intro other
  simp_rw [fixed_ideal_expansion]
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro generated
  exact sample_mac_at_bind generated.1.2 (fun tag =>
    idealRest checker other adversary generated.1.1 ⟨tag,generated.1.2⟩ (generated.2.1+2,generated.2.2))
noncomputable def idealLazyExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    ProbComp ((Bool × Nat) × SigGolfCandidate.T3.Security.LazyPrivate.State) :=
  SigGolfCandidate.T3.Security.LazyPrivate.run (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame checker adversary)) (∅,∅)
theorem ideal_lazy_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1.1=true ∧ result.1.2≤q | idealLazyExperiment checker adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment checker adversary] := by
  have h := SigGolfCandidate.T3.Security.LazyPrivate.run_eq_table
    (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame checker adversary)) ∅
  have hp : Pr[fun result => result.1.1=true ∧ result.1.2≤q |
      Prod.map id Prod.snd <$> idealLazyExperiment checker adversary]=
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | do
        let table ← ($ᵗ FullTable : ProbComp _)
        (simulateQ romImpl (Derivation.tableRun table
          (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame checker adversary)))).run ∅] :=
    probEvent_congr' (fun _ _ => Iff.rfl) h
  simp only [probEvent_map,Prod.map,id_eq,Function.comp_def] at hp
  rw [hp]
  have he : Pr[fun result => result.1=true ∧ result.2.1≤q | idealTableExperiment checker adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment checker adversary] :=
    probEvent_congr' (fun _ _ => Iff.rfl) (ideal_table_authenticated checker adversary)
  rw [← he]
  unfold idealTableExperiment
  simp only [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro table
  apply congrArg
  rw [run,tableHandler,countHandler_run,probEvent_map]
  simp only [plain_run,Function.comp_def,Nat.zero_add]
theorem real_to_ideal_lazy (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | idealLazyExperiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [ideal_lazy_event]
  exact real_to_authenticated checker adversary q hq

#print axioms real_to_ideal_lazy
end OuterGameWith
