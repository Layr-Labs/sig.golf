import SigGolfCandidate.T3.Secc.CaseCBankMain

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
