import SigGolfCandidate.T3.Secc.CaseCBankStep

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCBankMain : DecidableEq T3.Cache := Classical.decEq _
theorem pmf_expectedValue_mono {α : Type} (p : PMF α) {f g : α → ENNReal} (h : ∀ x ∈ p.support, f x ≤ g x) :
    expectedValue p f ≤ expectedValue p g := by
  unfold expectedValue
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ p.support
  · exact mul_le_mul' le_rfl (h x hx)
  · have hp : Pr[= x | p] = 0 := by
      rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
      exact hx
    rw [hp, zero_mul, zero_mul]
theorem keygen_notDigest : AllQueriesSatisfy keygen BPB.NotDigestQ := by
  unfold keygen keygenPayload
  apply SourceQueries.bind_allowed
  · apply SourceQueries.bind_allowed _ BPB.buildTopTree_ok
    intro levels
    apply SourceQueries.bind_allowed
    · apply SourceQueries.mapM_allowed
      intro level
      unfold maskedLevel pairedMask
      apply SourceQueries.bind_allowed
      · apply SourceQueries.mapM_allowed
        intro pair
        exact SourceQueries.bind_allowed _ (BPB.privatePair_ok 13 0 0 level pair)
          (fun _ => SourceQueries.pure_allowed _ _)
      · intro _; exact SourceQueries.pure_allowed _ _
    · intro _
      exact SourceQueries.pure_allowed _ _
  · intro generated
    rcases generated with ⟨publicKey, region⟩
    apply SourceQueries.bind_allowed
    · exact SourceQueries.privateMac_allowed BPB.NotDigestQ (fun _ => trivial) region
    · intro _
      exact SourceQueries.pure_allowed _ _
theorem reuseMass_of_noDigest (cache : Sampling.RCache) (h : ∀ x, IsDigestInput x → cache x = none) (m : Message) :
    reuseMass cache m = 0 := by
  unfold reuseMass
  rw [ENNReal.div_eq_zero_iff]
  left
  apply ENNReal.tsum_eq_zero.mpr
  intro p
  simp [admissibleEntry, h _ (digestRowOf_isDigest ⟨p, rfl⟩)]
theorem keygen_noDigest (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    ∀ x, IsDigestInput x → (lazyOf generated.2).2 x = none := by
  intro x hx
  by_contra hne
  have hl := recorded_lazy_support keygen QueryRecorded.initial generated hg
  have := run_new_public keygen (fun x => ¬IsDigestInput x)
    (allQueriesSatisfy_mono _ _ _ (fun q hq x hqx hd => by
      subst hqx
      obtain ⟨rho, m, c, rfl⟩ := hd
      exact hq (BPB.hdrMarker_digestInput rho m c)) keygen_notDigest)
    (lazyOf QueryRecorded.initial) (generated.1, lazyOf generated.2) hl x rfl hne
  exact this hx
theorem potential_initial_le (budget : Nat) (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    potential budget (Ghost.empty, generated.2) ≤ (budget : ENNReal) * (11324 / 100000000) / 2 ^ 128 := by
  have hreuse : reusePotential (lazyOf generated.2) = 0 := by
    unfold reusePotential
    apply ENNReal.tsum_eq_zero.mpr
    intro m
    split_ifs
    · exact reuseMass_of_noDigest _ (keygen_noDigest generated hg) m
    · rfl
  unfold potential livePotential
  split_ifs with h1 h2
  · exact bot_le
  · simp [Ghost.empty] at h2
  · simp only [hreuse, add_zero]
    have hbank : bankValue Ghost.empty = 0 := by simp [bankValue, Ghost.empty]
    rw [hbank, zero_add]
    unfold excessTerm
    apply ENNReal.div_le_div_right
    apply mul_le_mul'
    · exact_mod_cast Nat.sub_le budget _
    · have he := excess_three_quarters
      simpa [excessForecast, Ghost.empty, labels, horizon] using he
end SigGolfCandidate.T3.Security.CaseC
