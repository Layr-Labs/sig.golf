import SigGolfCandidate.T3.Secc.CreationSharedLaw
import SigGolfCandidate.T3.Secc.CaseCCore
import SigGolfCandidate.T3.Secc.SeccSufRoute

section
namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCBankDefs : DecidableEq T3.Cache := Classical.decEq _
def IsDigestInput (x : HashInput) : Prop :=
  ∃ (rho : Digest) (m : Message) (c : BitVec 32), x = pad64 (digestInput rho m c)
structure Ghost where
  targets : List HashOutput
  exposures : List HashOutput
  reused : Bool
  dead : Bool
  log : QueryLog Requests
def Ghost.empty : Ghost := ⟨[], [], false, false, []⟩
abbrev BankState := Ghost × QueryRecorded.State
def countOf (s : QueryRecorded.State) : Nat := s.base.source.1
def lazyOf (s : QueryRecorded.State) : LazyPrivate.State := s.base.source.2
def horizon : Nat := BPORS.Numeric.proposalLength
def Birth (budget : Nat) (x : HashInput) (before : QueryRecorded.State) : Prop :=
  IsDigestInput x ∧ (lazyOf before).2 x = none ∧ countOf before < budget
def FreshSigning (published : T3.Cache) (request : Request) (before : QueryRecorded.State) : Prop :=
  request.cache = published ∧ (lazyOf before).1 (.inr (.inl request.message)) = none
end SigGolfCandidate.T3.Security.CaseC
end
section
namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCBankReuse : DecidableEq T3.Cache := Classical.decEq _
theorem query_new_public (input : T3.Spec.Domain) (before : LazyPrivate.State)
    (result : T3.Spec.Range input × LazyPrivate.State)
    (h : result ∈ support (LazyPrivate.run (liftM (T3.Spec.query input)) before)) (x : HashInput)
    (hx : before.2 x = none) (hr : result.2.2 x ≠ none) : input = .inl (.inr x) := by
  rw [LazyPrivate.run_query] at h
  cases input with
  | inl input =>
      simp only [PrivateTable.lazyImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at h
      obtain ⟨step, hstep, rfl⟩ := h
      cases input with
      | inl n =>
          change step ∈ support ((fun answer => (answer, before.2)) <$>
            ($ᵗ (SphincsSecurity.OracleWorld.Range (.inl n)) : ProbComp _)) at hstep
          rw [support_map] at hstep
          obtain ⟨_, _, rfl⟩ := hstep
          exact absurd hx hr
      | inr y =>
          by_cases hxy : y = x
          · rw [hxy]
          · exfalso
            apply hr
            change step ∈ support ((randomOracle (spec := SphincsSecurity.HashSpec) y).run before.2) at hstep
            rw [OracleSpec.randomOracle] at hstep
            cases hc : before.2 y with
            | some u =>
                rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hstep
                subst step
                exact hx
            | none =>
                rw [QueryImpl.withCaching_run_none _ hc, support_map] at hstep
                obtain ⟨v, _, rfl⟩ := hstep
                change (before.2.cacheQuery y v) x = none
                rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hxy)]
                exact hx
  | inr coordinate =>
      simp only [PrivateTable.lazyImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at h
      obtain ⟨step, _, rfl⟩ := h
      exact absurd hx hr
theorem run_new_public {α : Type} (program : M α) (Q : HashInput → Prop)
    (hQ : AllQueriesSatisfy program (fun q => ∀ x, q = .inl (.inr x) → Q x))
    (before : LazyPrivate.State) (result : α × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run program before)) (x : HashInput)
    (hx : before.2 x = none) (hnew : result.2.2 x ≠ none) : Q x := by
  induction program using OracleComp.inductionOn generalizing before with
  | pure value =>
      rw [LazyPrivate.run_pure, mem_support_pure_iff] at hr
      subst result
      exact absurd hx hnew
  | query_bind input next ih =>
      obtain ⟨hinput, htail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hQ
      rw [LazyPrivate.run_bind, mem_support_bind_iff] at hr
      obtain ⟨step, hstep, htailResult⟩ := hr
      by_cases hs : step.2.2 x = none
      · exact ih step.1 (htail step.1) step.2 htailResult hs
      · exact hinput x (query_new_public input before step hstep x hx hs)
theorem allQueriesSatisfy_mono {α : Type} (program : M α) (P Q : T3.Spec.Domain → Prop)
    (hPQ : ∀ q, P q → Q q) (h : AllQueriesSatisfy program P) : AllQueriesSatisfy program Q := by
  induction program using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hPQ _ hi, fun u => ih u (hn u)⟩
def DigestRowOf (x : HashInput) (m : Message) : Prop :=
  ∃ p : Digest × Fin (2 ^ 32), x = Sampling.digestTrial p.1 m p.2.val
def SignerQ (m : Message) : T3.Spec.Domain → Prop :=
  fun q => ∀ x, q = .inl (.inr x) → IsDigestInput x → DigestRowOf x m
theorem notDigestQ_signerQ (m : Message) (q : T3.Spec.Domain) (h : BPB.NotDigestQ q) : SignerQ m q := by
  intro x hq ⟨rho, m', c, hx⟩
  subst hq
  exfalso
  have := BPB.hdrMarker_digestInput rho m' c
  rw [← hx] at this
  exact h this
theorem digestTrial_rowOf (rho : Digest) (m : Message) (c : Nat) (hc : c < 2 ^ 32) :
    DigestRowOf (Sampling.digestTrial rho m c) m := ⟨(rho, ⟨c, hc⟩), rfl⟩
theorem digestRowOf_unique {x : HashInput} {m m' : Message} (h : DigestRowOf x m) (h' : DigestRowOf x m') :
    m = m' := by
  obtain ⟨p, rfl⟩ := h
  obtain ⟨p', hp'⟩ := h'
  have he := Sampling.pad64_inj_of_length (by simp [digestInput, SphincsSecurity.bytesLE_length]) hp'
  exact (digestInput_injective he).2.1
theorem tsum_indicator_le_of_subsingleton {β : Type} (P : β → Prop) [DecidablePred P]
    (hP : ∀ a b, P a → P b → a = b)
    (c : ENNReal) : (∑' b, if P b then c else 0) ≤ c := by
  by_cases h : ∃ b, P b
  · obtain ⟨b0, hb0⟩ := h
    rw [tsum_eq_single b0 (fun b hb => if_neg (fun hP' => hb (hP b b0 hP' hb0)))]
    simp [hb0]
  · push Not at h
    simp [h]
noncomputable def reusePotential (s : LazyPrivate.State) : ENNReal :=
  ∑' m : Message, if s.1 (.inr (.inl m)) = none then reuseMass s.2 m else 0
end SigGolfCandidate.T3.Security.CaseC
end
