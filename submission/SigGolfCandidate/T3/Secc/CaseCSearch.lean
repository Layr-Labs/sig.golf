import SigGolfCandidate.T3.Secc.CaseCForecast

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
