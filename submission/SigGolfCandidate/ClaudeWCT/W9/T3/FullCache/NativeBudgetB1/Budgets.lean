import SigGolfCandidate.ClaudeWCT.Bank.WCTAccept
import SigGolfCandidate.ClaudeWCT.Numerics.N600CapCount
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.Presampling
import SigGolfCandidate.ClaudeWCT.W9.T3.Gate6.SourceBudget

section



namespace ClaudeWCT.W9.T3.Budgets
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Finset
open SigGolfCandidate.T3 (HashOutput)
open ClaudeWCT.Bank.WCT (WProposal proposal)
open ClaudeWCT.WCT9 (Coord Child Rank)
def capP (p : WProposal) : Prop :=
  ClaudeWCT.Numerics.N600Cap.pairCost p.2 ≤ ClaudeWCT.WCT9.jointCap
instance : DecidablePred capP := fun _ => Nat.decLe _ _
theorem producerAdmissible_iff_capP (x : HashOutput) :
    ClaudeWCT.WCT9.producerAdmissible x = true ↔ ClaudeWCT.WCT9.admissible x = true ∧ capP (proposal x) := by
  rw [ClaudeWCT.WCT9.producerAdmissible_iff, ClaudeWCT.WCT9.jointCost_eq_sum]
  rfl
theorem card_capP : #{p : WProposal | capP p} = 2 ^ 31 * ClaudeWCT.Numerics.N600Cap.J := by
  have h : (univ.filter capP : Finset WProposal) =
      (univ ×ˢ ClaudeWCT.Numerics.N600Cap.capSet : Finset (Fin (2 ^ 31) × (Coord → Child × Rank))) :=
    Finset.ext fun p => by
      rw [mem_filter, mem_product, ClaudeWCT.Numerics.N600Cap.mem_capSet]
      simp only [mem_univ, true_and]
      exact Iff.rfl
  rw [h, card_product, ClaudeWCT.Numerics.N600Cap.card_capSet, card_univ, Fintype.card_fin]
theorem acceptanceV5 :
    Pr[fun x : HashOutput => ClaudeWCT.WCT9.producerAdmissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (1451 * ClaudeWCT.Numerics.N600Cap.J : ENNReal) / 2 ^ 167 := by
  rw [← expectedValue_ite_one, SigGolfCandidate.T3.BPORS.expected_uniform_eq_finiteAverage]
  unfold SigGolfResearch.Gate6.Moments.finiteAverage
  have hsum : (∑ x : HashOutput, if ClaudeWCT.WCT9.producerAdmissible x = true then (1 : ENNReal) else 0) =
      ∑ x : HashOutput, if ClaudeWCT.WCT9.admissible x = true then
        (if capP (proposal x) then (1 : ENNReal) else 0) else 0 := by
    refine sum_congr rfl fun x _ => ?_
    by_cases ha : ClaudeWCT.WCT9.admissible x = true
    · simp only [ha, if_true]
      exact if_congr ((producerAdmissible_iff_capP x).trans (and_iff_right ha)) rfl rfl
    · rw [if_neg ha, if_neg (fun h => ha ((producerAdmissible_iff_capP x).mp h).1)]
  rw [hsum, ClaudeWCT.Bank.WCT.sum_admissible (fun p : WProposal => if capP p then (1 : ENNReal) else 0),
    sum_boole, card_capP, Fintype.card_bitVec]
  unfold ClaudeWCT.WCT9.gateLimit
  generalize hJ : ClaudeWCT.Numerics.N600Cap.J = J
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
theorem acceptanceV5_eq_p0 :
    Pr[fun x : HashOutput => ClaudeWCT.WCT9.producerAdmissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ENNReal.ofReal (BaseAudit.V5.p0 : ℝ) := by
  rw [acceptanceV5]
  have hq : ((BaseAudit.V5.p0 : ℚ) : ℝ) = (1451 : ℝ) * (ClaudeWCT.Numerics.N600Cap.J : ℝ) / 2 ^ 167 := by
    simp only [BaseAudit.V5.p0, BaseAudit.V5.J, ClaudeWCT.Numerics.N600Cap.J]
    push_cast
    ring
  rw [hq, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_pow (by norm_num)]
  simp
end ClaudeWCT.W9.T3.Budgets
end

section







section
namespace ClaudeWCT.W9.T3.Correctness
open OracleComp OracleSpec
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit honestForest eval_signForest)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Correctness (Answers DigestFamily KeygenCorrect)
open ClaudeWCT.W9.T3.QuerySpace (EncodingFamilyBC routedTree routedLeaf routedTree_of routedLeaf_of)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def DigestSearchesSucceed (answers : Answers) : Prop :=
  ∀ family : DigestFamily, ∃ found,
    evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch family.1 family.2 0 digestAttemptLimit) = some found
def EncodingSearchesSucceedBC (answers : Answers) : Prop :=
  ∀ family : EncodingFamilyBC, ∃ found,
    evalWithAnswerFn answers (ClaudeWCT.WCT9.layerCounterSearch family.1 (routedTree family.1 family.2.1)
      (routedLeaf family.1 family.2.1) (.pair family.2.2.1 family.2.2.2) 0 (ClaudeWCT.WCT9.searchLimit family.1)) =
      some found
theorem encodingSearchesSucceedBC_msg (answers : Answers) (hgood : EncodingSearchesSucceedBC answers)
    (lay : Layer) (tree leaf : Nat) (hleaf : leaf < 2 ^ height lay) (hr : tree * 2 ^ height lay + leaf < 2 ^ 32)
    (msg : ClaudeWCT.WCT9.LayerMsg) : ∃ found,
    evalWithAnswerFn answers (ClaudeWCT.WCT9.layerCounterSearch lay tree leaf msg 0 (ClaudeWCT.WCT9.searchLimit lay)) =
      some found := by
  have ht := routedTree_of lay (tree := tree) hleaf
  have hl := routedLeaf_of lay (tree := tree) hleaf
  cases msg with
  | forest root =>
      rw [ClaudeWCT.W9.T3.PairRows.layerCounterSearch_forest_eval]
      have h := hgood (lay, ⟨_, hr⟩, root, 0)
      simp only [ht, hl] at h
      exact h
  | pair left right =>
      have h := hgood (lay, ⟨_, hr⟩, left, right)
      simp only [ht, hl] at h
      exact h
theorem route_routed_lt (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 < 2 ^ 32 := by
  fin_cases lay <;> simp [route, height] <;> omega
theorem encodingSearchesSucceedBC_at_route (answers : Answers) (hgood : EncodingSearchesSucceedBC answers)
    (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) (msg : ClaudeWCT.WCT9.LayerMsg) : ∃ found,
    evalWithAnswerFn answers (ClaudeWCT.WCT9.layerCounterSearch lay (route index lay).2
      (route index lay).1 msg 0 (ClaudeWCT.WCT9.searchLimit lay)) = some found :=
  encodingSearchesSucceedBC_msg answers hgood lay _ _ (route_leaf_bound index lay)
    (route_routed_lt index hindex lay) msg
theorem topSearchesSucceedBC_of (answers : Answers) (hgood : EncodingSearchesSucceedBC answers) :
    ClaudeWCT.WCT9.TopSearchesSucceedBC answers :=
  fun index hindex msg => encodingSearchesSucceedBC_at_route answers hgood index hindex (Fin.ofNat 4 0) msg
theorem signLayersBC_succeeds (answers : Answers) (cache : Cache) (index : Nat)
    (hindex : index < 2 ^ 31) (hgood : EncodingSearchesSucceedBC answers) :
    ∀ n msg, ∃ pieces,
      evalWithAnswerFn answers (ClaudeWCT.WCT9.signLayersBC cache index n msg) = some pieces := by
  intro n
  induction n with
  | zero => intro msg; exact ⟨[], rfl⟩
  | succ n ih =>
      intro msg
      obtain ⟨⟨counter, digits⟩, hs⟩ :=
        encodingSearchesSucceedBC_at_route answers hgood index hindex (Fin.ofNat 4 n) msg
      have hd := (ClaudeWCT.WCT9.layerCounterSearch_some answers (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg
        (ClaudeWCT.WCT9.searchLimit (Fin.ofNat 4 n)) 0 counter digits
        (by have := ClaudeWCT.WCT9.searchLimit_le (Fin.ofNat 4 n); unfold counterLimit at this; omega) hs).2.2
      have hvalid := Cost.validDigits_decode hd
      simp only [ClaudeWCT.WCT9.signLayersBC, evalWithAnswerFn_bind, hs]
      by_cases hn : n = 0
      · simp only [hn, if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
        exact ⟨_, rfl⟩
      · simp only [hn, if_false, evalWithAnswerFn_bind]
        obtain ⟨previous, hp⟩ := ih (.pair
          (ClaudeWCT.WCT9.topPair (Fin.ofNat 4 n) (evalWithAnswerFn answers (ClaudeWCT.WCT9.buildTreeP
            (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 digits)).1).1
          (ClaudeWCT.WCT9.topPair (Fin.ofNat 4 n) (evalWithAnswerFn answers (ClaudeWCT.WCT9.buildTreeP
            (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 digits)).1).2)
        simp only [hp, evalWithAnswerFn_pure]
        exact ⟨_, rfl⟩
def SearchesSucceed (answers : Answers) : Prop :=
  DigestSearchesSucceed answers ∧ EncodingSearchesSucceedBC answers
theorem signPayload_succeeds (answers : Answers) (cache : Cache) (message : Message)
    (hgood : SearchesSucceed answers) :
    ∃ sig, evalWithAnswerFn answers (signPayload cache message) = some sig := by
  obtain ⟨⟨counter, output⟩, hd⟩ := hgood.1 (evalWithAnswerFn answers (privateNonce message), message)
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  simp only [evalWithAnswerFn_bind, hd, eval_signForest]
  obtain ⟨pieces, hp⟩ := signLayersBC_succeeds answers cache (ClaudeWCT.WCT9.digestIndex output)
    (ClaudeWCT.WCT9.digestIndex_lt output) hgood.2 4 (.forest (honestForest answers (ClaudeWCT.WCT9.digestIndex output)))
  simp only [hp, evalWithAnswerFn_pure]
  exact ⟨_, rfl⟩
def SigningComplete (answers : Answers) (keys : Digest × Cache) : Prop :=
  ∀ message : Message, ∃ sig : Signature, ∃ w : Witness,
    evalWithAnswerFn answers (sign keys.2 message) = some sig ∧
    evalWithAnswerFn answers (expand message keys.1 sig) = some w ∧
    evalWithAnswerFn answers (verify message keys.1 w) = true
theorem signing_complete_at (answers : Answers) (keys : Digest × Cache)
    (hkeys : KeygenCorrect answers keys) (htop : ClaudeWCT.WCT9.TopSearchesSucceedBC answers) (message : Message)
    (hpayload : ∃ sig, evalWithAnswerFn answers (signPayload keys.2 message) = some sig) :
    ∃ sig : Signature, ∃ w : Witness,
      evalWithAnswerFn answers (sign keys.2 message) = some sig ∧
      evalWithAnswerFn answers (expand message keys.1 sig) = some w ∧
      evalWithAnswerFn answers (verify message keys.1 w) = true := by
  obtain ⟨sig, hs⟩ := hpayload
  have hs' : evalWithAnswerFn answers (sign keys.2 message) = some sig := by
    rw [show sign keys.2 message = ClaudeWCT.WCT9.signWith digestAttemptLimit keys.2 message from rfl,
      ClaudeWCT.WCT9.signWith_valid_cache digestAttemptLimit answers keys message hkeys.2.2]
    exact hs
  obtain ⟨w, he, hv⟩ := ClaudeWCT.WCT9.signingWith_success_valid digestAttemptLimit
    ClaudeWCT.WCT9.digestAttemptLimit_le answers keys hkeys htop message sig hs'
  exact ⟨sig, w, hs', he, hv⟩
theorem signing_complete_of_searches (answers : Answers) (keys : Digest × Cache)
    (hkeys : KeygenCorrect answers keys) (hgood : SearchesSucceed answers) :
    SigningComplete answers keys :=
  fun message => signing_complete_at answers keys hkeys (topSearchesSucceedBC_of answers hgood.2) message
    (signPayload_succeeds answers keys.2 message hgood)
theorem honest_signing_complete_of_searches (answers : Answers) (hgood : SearchesSucceed answers) :
    SigningComplete answers (evalWithAnswerFn answers keygen) :=
  signing_complete_of_searches answers _ (SigGolfCandidate.T3.Correctness.keygen_correct answers) hgood
def RealizedSigningComplete (answers : QueryImpl SphincsSecurity.OracleWorld Id)
    (secret : BitVec 256) (keys : Digest × Cache) : Prop :=
  ∀ message : Message, ∃ sig : Signature, ∃ w : Witness,
    evalWithAnswerFn answers (realize secret (sign keys.2 message)) = some sig ∧
    evalWithAnswerFn answers (realize secret (expand message keys.1 sig)) = some w ∧
    evalWithAnswerFn answers (realize secret (verify message keys.1 w)) = true
theorem realized_honest_signing_complete_of_searches
    (answers : QueryImpl SphincsSecurity.OracleWorld Id) (secret : BitVec 256)
    (hgood : SearchesSucceed (answers.compose (realHandler secret))) :
    RealizedSigningComplete answers secret (evalWithAnswerFn answers (realize secret keygen)) := by
  unfold RealizedSigningComplete
  simp only [SigGolfCandidate.T3.Correctness.realize_eval]
  exact honest_signing_complete_of_searches (answers.compose (realHandler secret)) hgood
def SearchesSucceedFor (answers : Answers) (message : Message) : Prop :=
  (∀ rho : Digest, ∃ found,
    evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch rho message 0 digestAttemptLimit) = some found) ∧
  EncodingSearchesSucceedBC answers
theorem signPayload_succeedsFor (answers : Answers) (cache : Cache) (message : Message)
    (hgood : SearchesSucceedFor answers message) :
    ∃ sig, evalWithAnswerFn answers (signPayload cache message) = some sig := by
  obtain ⟨⟨counter, output⟩, hd⟩ := hgood.1 (evalWithAnswerFn answers (privateNonce message))
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  simp only [evalWithAnswerFn_bind, hd, eval_signForest]
  obtain ⟨pieces, hp⟩ := signLayersBC_succeeds answers cache (ClaudeWCT.WCT9.digestIndex output)
    (ClaudeWCT.WCT9.digestIndex_lt output) hgood.2 4 (.forest (honestForest answers (ClaudeWCT.WCT9.digestIndex output)))
  simp only [hp, evalWithAnswerFn_pure]
  exact ⟨_, rfl⟩
theorem signing_complete_for_of_searches (answers : Answers) (keys : Digest × Cache)
    (hkeys : KeygenCorrect answers keys) (message : Message)
    (hgood : SearchesSucceedFor answers message) :
    ∃ sig : Signature, ∃ w : Witness,
      evalWithAnswerFn answers (sign keys.2 message) = some sig ∧
      evalWithAnswerFn answers (expand message keys.1 sig) = some w ∧
      evalWithAnswerFn answers (verify message keys.1 w) = true :=
  signing_complete_at answers keys hkeys (topSearchesSucceedBC_of answers hgood.2) message (signPayload_succeedsFor answers keys.2 message hgood)
def SearchesSucceedSelected (answers : Answers) : Prop :=
  (∀ message : Message, ∃ found,
    evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch
      (evalWithAnswerFn answers (privateNonce message)) message 0 digestAttemptLimit) = some found) ∧
  EncodingSearchesSucceedBC answers
theorem signPayload_succeedsSelected (answers : Answers) (cache : Cache) (message : Message)
    (hgood : SearchesSucceedSelected answers) :
    ∃ sig, evalWithAnswerFn answers (signPayload cache message) = some sig := by
  obtain ⟨⟨counter, output⟩, hd⟩ := hgood.1 message
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  simp only [evalWithAnswerFn_bind, hd, eval_signForest]
  obtain ⟨pieces, hp⟩ := signLayersBC_succeeds answers cache (ClaudeWCT.WCT9.digestIndex output)
    (ClaudeWCT.WCT9.digestIndex_lt output) hgood.2 4 (.forest (honestForest answers (ClaudeWCT.WCT9.digestIndex output)))
  simp only [hp, evalWithAnswerFn_pure]
  exact ⟨_, rfl⟩
theorem signing_complete_of_selected_searches (answers : Answers) (keys : Digest × Cache)
    (hkeys : KeygenCorrect answers keys) (hgood : SearchesSucceedSelected answers) :
    SigningComplete answers keys :=
  fun message => signing_complete_at answers keys hkeys (topSearchesSucceedBC_of answers hgood.2) message
    (signPayload_succeedsSelected answers keys.2 message hgood)
end ClaudeWCT.W9.T3.Correctness
end
section
namespace ClaudeWCT.W9.T3.Budgets
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass failMass_eq_probEvent)
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Correctness (Answers DigestFamily digestFamily_card KeygenCorrect)
open SigGolfCandidate.T3.Budgets (zeroAnswers failMass_eq_one_sub_accept
  rejection_power_le ofReal_inv_two_pow finite_family_failure_le)
open ClaudeWCT.W9.T3.Correctness (SearchesSucceed DigestSearchesSucceed EncodingSearchesSucceedBC SigningComplete
  SearchesSucceedFor SearchesSucceedSelected signing_complete_of_searches honest_signing_complete_of_searches
  signing_complete_for_of_searches signing_complete_of_selected_searches)
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery EncodingFamilyBC encodingFamilyBC_card_le routedTree routedLeaf)
open ClaudeWCT.W9.T3.PairRows (pairTrial msgLeft msgRight layerCounterSearch_none_iff eval_shortHash_layer)
open ClaudeWCT.W9.T3.Sampling (digestDecode)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
theorem digest_probability_eq_p0 :
    Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal (BaseAudit.V5.p0 : ℝ) := by
  have h : (fun answer : HashOutput => (digestDecode answer).isSome = true) =
      fun x => ClaudeWCT.WCT9.producerAdmissible x = true := by
    funext x
    simp only [digestDecode]
    split <;> simp_all
  rw [h, acceptanceV5_eq_p0]
theorem digest_failure_power_of_acceptance (p : ℝ) (hp : 1 / 5026 ≤ p) (hp1 : p ≤ 1)
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal p) :
    failMass digestDecode ^ digestAttemptLimit ≤ 1 / (2 : ENNReal) ^ 450 := by
  have hm : failMass digestDecode = ENNReal.ofReal (1 - p) := by
    rw [failMass_eq_one_sub_accept, haccept, ENNReal.ofReal_sub 1 (by linarith)]
    simp
  rw [hm, ← ENNReal.ofReal_pow (by linarith)]
  have hreal := rejection_power_le p hp1 digestAttemptLimit 450
    (by have hl := Real.log_two_lt_d9
        change (450 : ℝ) * Real.log 2 ≤ 2097152 * p
        nlinarith)
  have hcast := ENNReal.ofReal_le_ofReal hreal
  simpa only [ofReal_inv_two_pow] using hcast
theorem digest_failure_power :
    failMass digestDecode ^ digestAttemptLimit ≤ 1 / (2 : ENNReal) ^ 450 :=
  digest_failure_power_of_acceptance (BaseAudit.V5.p0 : ℝ)
    (by norm_num [BaseAudit.V5.p0, BaseAudit.V5.J]) (by norm_num [BaseAudit.V5.p0, BaseAudit.V5.J]) digest_probability_eq_p0
theorem digest_failMass_eq :
    failMass digestDecode = 1 - (1451 * ClaudeWCT.Numerics.N600Cap.J : ENNReal) / 2 ^ 167 := by
  have h : (fun answer : HashOutput => (digestDecode answer).isSome = true) =
      fun x => ClaudeWCT.WCT9.producerAdmissible x = true := by
    funext x
    simp only [digestDecode]
    split <;> simp_all
  rw [failMass_eq_one_sub_accept, h, acceptanceV5]
theorem digest_failure_explicit :
    (1 - (1451 * ClaudeWCT.Numerics.N600Cap.J : ENNReal) / 2 ^ 167) ^ (2 ^ 21) ≤
      1 / (2 : ENNReal) ^ 450 := by
  rw [← digest_failMass_eq]
  exact digest_failure_power
theorem digest_failure_power_900 :
    failMass digestDecode ^ digestAttemptLimit ≤ 1 / (2 : ENNReal) ^ 900 :=
  V5.digest_failure_power_900_of digestDecode digest_probability_eq_p0
theorem digest_failure_power_752 :
    failMass digestDecode ^ digestAttemptLimit ≤ 1 / (2 : ENNReal) ^ 752 := by
  refine digest_failure_power_900.trans ?_
  gcongr
  · norm_num
  · norm_num
theorem digest_failure_power_602 :
    failMass digestDecode ^ digestAttemptLimit ≤ 1 / (2 : ENNReal) ^ 602 := by
  refine digest_failure_power_752.trans ?_
  gcongr
  · norm_num
  · norm_num
def DigestFailed (family : DigestFamily) (answers : Answers) : Prop :=
  evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch family.1 family.2 0 digestAttemptLimit) = none
def EncodingFailedBC (family : EncodingFamilyBC) (answers : Answers) : Prop :=
  evalWithAnswerFn answers (ClaudeWCT.WCT9.layerCounterSearch family.1 (routedTree family.1 family.2.1)
    (routedLeaf family.1 family.2.1) (.pair family.2.2.1 family.2.2.2) 0 (ClaudeWCT.WCT9.searchLimit family.1)) = none
theorem not_searchesSucceed_iff (answers : Answers) :
    ¬ SearchesSucceed answers ↔
      (∃ family, DigestFailed family answers) ∨ (∃ family, EncodingFailedBC family answers) := by
  classical
  simp only [SearchesSucceed, DigestSearchesSucceed, EncodingSearchesSucceedBC,
    ← Option.ne_none_iff_exists', not_and_or, not_forall, not_not, DigestFailed, EncodingFailedBC]
theorem incomplete_implies_failed_search (answers : Answers)
    (h : ¬SigningComplete answers (evalWithAnswerFn answers keygen)) :
    (∃ family, DigestFailed family answers) ∨ (∃ family, EncodingFailedBC family answers) :=
  (not_searchesSucceed_iff answers).mp (fun hgood => h (honest_signing_complete_of_searches answers hgood))
theorem signing_incomplete_probability_le (law : ProbComp Answers) (digestFail encodingFail : ENNReal)
    (hd : ∀ family, Pr[DigestFailed family | law] ≤ digestFail)
    (he : ∀ family, Pr[EncodingFailedBC family | law] ≤ encodingFail) :
    Pr[fun answers => ¬SigningComplete answers (evalWithAnswerFn answers keygen) | law] ≤
      (2 : ENNReal) ^ 384 * digestFail + (2 : ENNReal) ^ 301 * encodingFail := by
  have hm := probEvent_mono (mx := law) (fun answers _ => incomplete_implies_failed_search answers)
  have hd' := finite_family_failure_le law DigestFailed digestFail hd
  have he' := finite_family_failure_le law EncodingFailedBC encodingFail he
  rw [digestFamily_card, Nat.cast_pow, Nat.cast_ofNat] at hd'
  replace he' := he'.trans (mul_le_mul' encodingFamilyBC_card_le le_rfl)
  exact hm.trans ((probEvent_or_le law _ _).trans (add_le_add hd' he'))
theorem union_real_65 : (2 : ℝ) ^ 384 * (1 / 2 ^ 450) + 2 ^ 301 * (1 / 2 ^ 600) ≤ 1 / 2 ^ 65 := by
  set_option exponentiation.threshold 2048 in norm_num
theorem union_real_298 : (2 : ℝ) ^ 128 * (1 / 2 ^ 450) + 2 ^ 301 * (1 / 2 ^ 600) ≤ 1 / 2 ^ 298 := by
  set_option exponentiation.threshold 2048 in norm_num
theorem union_ennreal (a c : ℕ)
    (hreal : (2 : ℝ) ^ a * (1 / 2 ^ 450) + 2 ^ 301 * (1 / 2 ^ 600) ≤ 1 / 2 ^ c) :
    (2 : ENNReal) ^ a * (1 / 2 ^ 450) + (2 : ENNReal) ^ 301 * (1 / 2 ^ 600) ≤ 1 / 2 ^ c := by
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (show 0 ≤ (2 : ℝ) ^ a * (1 / 2 ^ 450) by positivity)
    (show 0 ≤ (2 : ℝ) ^ 301 * (1 / 2 ^ 600) by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ a by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ 301 by positivity)] at hcast
  simpa only [ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num),
    ENNReal.ofReal_ofNat, ofReal_inv_two_pow] using hcast
theorem signing_incomplete_probability_small (law : ProbComp Answers)
    (hd : ∀ family, Pr[DigestFailed family | law] ≤ 1 / (2 : ENNReal) ^ 450)
    (he : ∀ family, Pr[EncodingFailedBC family | law] ≤ 1 / (2 : ENNReal) ^ 600) :
    Pr[fun answers => ¬SigningComplete answers (evalWithAnswerFn answers keygen) | law] ≤
      1 / (2 : ENNReal) ^ 65 :=
  (signing_incomplete_probability_le law _ _ hd he).trans (union_ennreal 384 65 union_real_65)
noncomputable local instance : SampleableType (SearchKey → HashOutput) := Presampling.tableSampler
def SearchAgreement (outputs : SearchKey → HashOutput) (answers : Answers) : Prop :=
  ∀ key, answers (.inl (.inr (searchQuery key))) = outputs key
def tableGood (outputs : SearchKey → HashOutput) : Prop :=
  SearchesSucceed (Presampling.tableAnswers outputs zeroAnswers)
theorem layerCounterSearch_none_agreement (outputs : SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) (lay : Layer) (r : Fin (2 ^ 32))
    (msg : ClaudeWCT.WCT9.LayerMsg) :
    evalWithAnswerFn answers
      (ClaudeWCT.WCT9.layerCounterSearch lay (routedTree lay r) (routedLeaf lay r) msg 0
        (ClaudeWCT.WCT9.searchLimit lay)) = none ↔
    ∀ c : Fin (ClaudeWCT.WCT9.searchLimit lay), ClaudeWCT.W9.T3.ProducerV5.producerEncodingDecode lay
      (outputs (.inl ((lay, r, msgLeft msg, msgRight msg),
        Fin.castLE (Presampling.searchLimit_le_rows lay) c))) = none := by
  rw [layerCounterSearch_none_iff]
  have hv (c : Nat) (hc : c < ClaudeWCT.WCT9.searchLimit lay) :
      evalWithAnswerFn answers
        (shortHash (ClaudeWCT.WCT9.layerEncodingInput lay (routedTree lay r) (routedLeaf lay r) msg
          (BitVec.ofNat 32 (0 + c)))) =
        (outputs (.inl ((lay, r, msgLeft msg, msgRight msg),
          Fin.castLE (Presampling.searchLimit_le_rows lay) ⟨c, hc⟩))).extractLsb' 0 128 := by
    rw [Nat.zero_add, eval_shortHash_layer]
    have hinput : pairTrial lay (routedTree lay r) (routedLeaf lay r) (msgLeft msg) (msgRight msg) c =
        searchQuery (.inl ((lay, r, msgLeft msg, msgRight msg),
          Fin.castLE (Presampling.searchLimit_le_rows lay) ⟨c, hc⟩)) := rfl
    rw [hinput, hagree]
  constructor
  · intro h c
    have h := h c c.isLt
    rw [hv c c.isLt] at h
    exact h
  · intro h c hc
    rw [hv c hc]
    exact h ⟨c, hc⟩
theorem encodingFamily_none_iff (outputs : SearchKey → HashOutput) (answers : Answers)
    (hagree : SearchAgreement outputs answers) (family : EncodingFamilyBC) :
    EncodingFailedBC family answers ↔ EncodingFailedBC family (Presampling.tableAnswers outputs zeroAnswers) :=
  (layerCounterSearch_none_agreement outputs answers hagree family.1 family.2.1
    (.pair family.2.2.1 family.2.2.2)).trans
    (Presampling.layerCounterSearch_none_table outputs zeroAnswers family.1 family.2.1
      (.pair family.2.2.1 family.2.2.2)).symm
theorem digestSearch_none_agreement (outputs : SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) (family : DigestFamily) :
    evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch family.1 family.2 0 digestAttemptLimit) = none ↔
    ∀ c : Fin (2 ^ 21), digestDecode (outputs (.inr (family, c))) = none := by
  rw [ClaudeWCT.WCT9.digestSearch_none_iff]
  have hv (c : Nat) (hc : c < digestAttemptLimit) :
      evalWithAnswerFn answers (digest family.1 family.2 (BitVec.ofNat 32 (0 + c))) =
        outputs (.inr (family, ⟨c, hc⟩)) := by
    rw [SigGolfCandidate.T3.Presampling.eval_digest]
    have hinput : pad64 (digestInput family.1 family.2 (BitVec.ofNat 32 (0 + c))) =
        searchQuery (.inr (family, ⟨c, hc⟩)) := by
      simp only [searchQuery, Sum.elim_inr, ClaudeWCT.W9.T3.QuerySpace.digestQuery,
        SigGolfCandidate.T3.Sampling.digestTrial, Nat.zero_add]
    rw [hinput, hagree]
  constructor
  · intro h c
    rw [ClaudeWCT.W9.T3.Sampling.digestDecode_eq_none_iff]
    have h := h c c.isLt
    rwa [hv c c.isLt] at h
  · intro h c hc
    rw [hv c hc]
    exact (ClaudeWCT.W9.T3.Sampling.digestDecode_eq_none_iff _).mp (h ⟨c, hc⟩)
theorem digestFamily_none_iff (outputs : SearchKey → HashOutput) (answers : Answers)
    (hagree : SearchAgreement outputs answers) (family : DigestFamily) :
    DigestFailed family answers ↔ DigestFailed family (Presampling.tableAnswers outputs zeroAnswers) :=
  (digestSearch_none_agreement outputs answers hagree family).trans
    (Presampling.digestSearch_none_table outputs zeroAnswers family).symm
theorem tableGood_iff_searchesSucceed (outputs : SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) :
    tableGood outputs ↔ SearchesSucceed answers := by
  unfold tableGood
  rw [← not_iff_not, not_searchesSucceed_iff, not_searchesSucceed_iff]
  exact or_congr (exists_congr fun family => (digestFamily_none_iff outputs answers hagree family).symm)
    (exists_congr fun family => (encodingFamily_none_iff outputs answers hagree family).symm)
theorem tableGood_searchesSucceed (outputs : SearchKey → HashOutput)
    (answers : Answers) (hgood : tableGood outputs) (hagree : SearchAgreement outputs answers) :
    SearchesSucceed answers := (tableGood_iff_searchesSucceed outputs answers hagree).mp hgood
theorem tableGood_fallback_iff (outputs : SearchKey → HashOutput) (fallback : Answers) :
    tableGood outputs ↔ SearchesSucceed (Presampling.tableAnswers outputs fallback) :=
  tableGood_iff_searchesSucceed outputs _ (Presampling.tableAnswers_apply outputs fallback)
theorem encodingFamily_table_failure (encodingFail : ENNReal)
    (he : ∀ lay, failMass (ClaudeWCT.W9.T3.ProducerV5.producerEncodingDecode lay) ^ ClaudeWCT.WCT9.searchLimit lay ≤
      encodingFail)
    (family : EncodingFamilyBC) :
    Pr[fun outputs => EncodingFailedBC family (Presampling.tableAnswers outputs zeroAnswers) |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ encodingFail :=
  (Presampling.layerCounterSearch_table_failure zeroAnswers family.1 family.2.1
    family.2.2.1 family.2.2.2).le.trans (he family.1)
theorem tableGood_failure_le (digestFail encodingFail : ENNReal)
    (hd : failMass digestDecode ^ digestAttemptLimit ≤ digestFail)
    (he : ∀ lay, failMass (ClaudeWCT.W9.T3.ProducerV5.producerEncodingDecode lay) ^ ClaudeWCT.WCT9.searchLimit lay ≤
      encodingFail) :
    Pr[fun outputs => ¬tableGood outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤
      (2 : ENNReal) ^ 384 * digestFail + (2 : ENNReal) ^ 301 * encodingFail := by
  let law := ($ᵗ (SearchKey → HashOutput) : ProbComp _)
  have hd' := finite_family_failure_le law
    (fun family outputs => DigestFailed family (Presampling.tableAnswers outputs zeroAnswers)) digestFail
    (fun family => (Presampling.digestSearch_table_failure zeroAnswers family).le.trans hd)
  have he' := finite_family_failure_le law
    (fun family outputs => EncodingFailedBC family (Presampling.tableAnswers outputs zeroAnswers)) encodingFail
    (encodingFamily_table_failure encodingFail he)
  rw [digestFamily_card, Nat.cast_pow, Nat.cast_ofNat] at hd'
  replace he' := he'.trans (mul_le_mul' encodingFamilyBC_card_le le_rfl)
  simp only [tableGood, not_searchesSucceed_iff]
  exact (probEvent_or_le law _ _).trans (add_le_add hd' he')
theorem tableGood_failure_small_of_acceptance (p : ℝ) (hp : 1 / 5026 ≤ p) (hp1 : p ≤ 1)
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal p) :
    Pr[fun outputs => ¬tableGood outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ 1 / (2 : ENNReal) ^ 65 :=
  (tableGood_failure_le _ _ (digest_failure_power_of_acceptance p hp hp1 haccept) ClaudeWCT.W9.T3.ProducerV5.producer_failure_power).trans
    (union_ennreal 384 65 union_real_65)
def tableGoodFor (message : Message) (outputs : SearchKey → HashOutput) : Prop :=
  SearchesSucceedFor (Presampling.tableAnswers outputs zeroAnswers) message
theorem not_searchesSucceedFor_iff (answers : Answers) (message : Message) :
    ¬ SearchesSucceedFor answers message ↔
      (∃ rho : Digest, DigestFailed (rho, message) answers) ∨ (∃ family, EncodingFailedBC family answers) := by
  classical
  simp only [SearchesSucceedFor, EncodingSearchesSucceedBC,
    ← Option.ne_none_iff_exists', not_and_or, not_forall, not_not, DigestFailed, EncodingFailedBC]
theorem tableGoodFor_iff_searchesSucceedFor (message : Message) (outputs : SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) :
    tableGoodFor message outputs ↔ SearchesSucceedFor answers message := by
  unfold tableGoodFor
  rw [← not_iff_not, not_searchesSucceedFor_iff, not_searchesSucceedFor_iff]
  exact or_congr (exists_congr fun rho => (digestFamily_none_iff outputs answers hagree (rho, message)).symm)
    (exists_congr fun family => (encodingFamily_none_iff outputs answers hagree family).symm)
theorem tableGoodFor_searchesSucceedFor (message : Message) (outputs : SearchKey → HashOutput)
    (answers : Answers) (hgood : tableGoodFor message outputs) (hagree : SearchAgreement outputs answers) :
    SearchesSucceedFor answers message :=
  (tableGoodFor_iff_searchesSucceedFor message outputs answers hagree).mp hgood
theorem tableGoodFor_failure_le (message : Message) (digestFail encodingFail : ENNReal)
    (hd : failMass digestDecode ^ digestAttemptLimit ≤ digestFail)
    (he : ∀ lay, failMass (ClaudeWCT.W9.T3.ProducerV5.producerEncodingDecode lay) ^ ClaudeWCT.WCT9.searchLimit lay ≤
      encodingFail) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤
      (2 : ENNReal) ^ 128 * digestFail + (2 : ENNReal) ^ 301 * encodingFail := by
  let law := ($ᵗ (SearchKey → HashOutput) : ProbComp _)
  have hd' := finite_family_failure_le law
    (fun (rho : Digest) outputs => DigestFailed (rho, message) (Presampling.tableAnswers outputs zeroAnswers))
    digestFail
    (fun rho => (Presampling.digestSearch_table_failure zeroAnswers (rho, message)).le.trans hd)
  have he' := finite_family_failure_le law
    (fun family outputs => EncodingFailedBC family (Presampling.tableAnswers outputs zeroAnswers)) encodingFail
    (encodingFamily_table_failure encodingFail he)
  rw [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat] at hd'
  replace he' := he'.trans (mul_le_mul' encodingFamilyBC_card_le le_rfl)
  simp only [tableGoodFor, not_searchesSucceedFor_iff]
  exact (probEvent_or_le law _ _).trans (add_le_add hd' he')
theorem tableGoodFor_failure_small_of_acceptance (message : Message) (p : ℝ) (hp : 1 / 5026 ≤ p) (hp1 : p ≤ 1)
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal p) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ 1 / (2 : ENNReal) ^ 298 :=
  (tableGoodFor_failure_le message _ _ (digest_failure_power_of_acceptance p hp hp1 haccept)
    ClaudeWCT.W9.T3.ProducerV5.producer_failure_power).trans (union_ennreal 128 298 union_real_298)
theorem tableGood_failure_small :
    Pr[fun outputs => ¬tableGood outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ 1 / (2 : ENNReal) ^ 65 :=
  tableGood_failure_small_of_acceptance (BaseAudit.V5.p0 : ℝ) (by norm_num [BaseAudit.V5.p0, BaseAudit.V5.J])
    (by norm_num [BaseAudit.V5.p0, BaseAudit.V5.J]) digest_probability_eq_p0
theorem tableGoodFor_failure_small (message : Message) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ 1 / (2 : ENNReal) ^ 298 :=
  tableGoodFor_failure_small_of_acceptance message (BaseAudit.V5.p0 : ℝ) (by norm_num [BaseAudit.V5.p0, BaseAudit.V5.J])
    (by norm_num [BaseAudit.V5.p0, BaseAudit.V5.J]) digest_probability_eq_p0
theorem tableGoodFor_failure_128 (message : Message) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ 1 / (2 : ENNReal) ^ 128 := by
  refine (tableGoodFor_failure_small message).trans ?_
  simp only [one_div, ENNReal.inv_le_inv]
  exact pow_le_pow_right₀ (by norm_num) (by decide)
def tableGoodForNonces (nonces : Message → HashOutput) (outputs : SearchKey → HashOutput) : Prop :=
  (∀ message : Message, ∃ found,
    evalWithAnswerFn (Presampling.tableAnswers outputs zeroAnswers)
      (ClaudeWCT.WCT9.digestSearch ((nonces message).extractLsb' 0 128) message 0 digestAttemptLimit) =
        some found) ∧
  EncodingSearchesSucceedBC (Presampling.tableAnswers outputs zeroAnswers)
def NonceAgreement (nonces : Message → HashOutput) (answers : Answers) : Prop :=
  ∀ message, evalWithAnswerFn answers (privateNonce message) = (nonces message).extractLsb' 0 128
theorem tableGoodForNonces_searchesSucceedSelected (nonces : Message → HashOutput)
    (outputs : SearchKey → HashOutput) (answers : Answers)
    (hgood : tableGoodForNonces nonces outputs) (hagree : SearchAgreement outputs answers)
    (hnonce : NonceAgreement nonces answers) : SearchesSucceedSelected answers := by
  constructor
  · intro message
    rw [hnonce]
    apply Option.ne_none_iff_exists'.mp
    intro hnone
    have hnone' := (digestFamily_none_iff outputs answers hagree
      ((nonces message).extractLsb' 0 128, message)).mp hnone
    obtain ⟨found, hfound⟩ := hgood.1 message
    simp only [DigestFailed] at hnone'
    rw [hfound] at hnone'
    cases hnone'
  · intro family
    apply Option.ne_none_iff_exists'.mp
    intro hnone
    have hnone' := (encodingFamily_none_iff outputs answers hagree family).mp hnone
    obtain ⟨found, hfound⟩ := hgood.2 family
    simp only [EncodingFailedBC] at hnone'
    rw [hfound] at hnone'
    cases hnone'
theorem tableGoodForNonces_signingComplete (nonces : Message → HashOutput)
    (outputs : SearchKey → HashOutput) (answers : Answers)
    (hgood : tableGoodForNonces nonces outputs) (hagree : SearchAgreement outputs answers)
    (hnonce : NonceAgreement nonces answers) :
    SigningComplete answers (evalWithAnswerFn answers keygen) :=
  signing_complete_of_selected_searches answers _ (SigGolfCandidate.T3.Correctness.keygen_correct answers)
    (tableGoodForNonces_searchesSucceedSelected nonces outputs answers hgood hagree hnonce)
theorem not_tableGoodForNonces_iff (nonces : Message → HashOutput)
    (outputs : SearchKey → HashOutput) :
    ¬tableGoodForNonces nonces outputs ↔
    (∃ message : Message, DigestFailed ((nonces message).extractLsb' 0 128, message)
      (Presampling.tableAnswers outputs zeroAnswers)) ∨
    (∃ family, EncodingFailedBC family (Presampling.tableAnswers outputs zeroAnswers)) := by
  classical
  simp only [tableGoodForNonces, EncodingSearchesSucceedBC,
    ← Option.ne_none_iff_exists', not_and_or, not_forall, not_not, DigestFailed, EncodingFailedBC]
theorem tableGoodForNonces_failure_le (nonces : Message → HashOutput) :
    Pr[fun outputs => ¬tableGoodForNonces nonces outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤
      (2 : ENNReal) ^ 256 * (1 / 2 ^ 450) + (2 : ENNReal) ^ 301 * (1 / 2 ^ 600) := by
  let law := ($ᵗ (SearchKey → HashOutput) : ProbComp _)
  have hd' := finite_family_failure_le law
    (fun (message : Message) outputs => DigestFailed ((nonces message).extractLsb' 0 128, message)
      (Presampling.tableAnswers outputs zeroAnswers)) (1 / (2 : ENNReal) ^ 450)
    (fun message => (Presampling.digestSearch_table_failure zeroAnswers
      ((nonces message).extractLsb' 0 128, message)).le.trans digest_failure_power)
  have he' := finite_family_failure_le law
    (fun family outputs => EncodingFailedBC family (Presampling.tableAnswers outputs zeroAnswers))
      (1 / (2 : ENNReal) ^ 600)
    (encodingFamily_table_failure _ ClaudeWCT.W9.T3.ProducerV5.producer_failure_power)
  rw [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat] at hd'
  replace he' := he'.trans (mul_le_mul' encodingFamilyBC_card_le le_rfl)
  simp only [not_tableGoodForNonces_iff]
  exact (probEvent_or_le law _ _).trans (add_le_add hd' he')
theorem tableGoodForNonces_failure_small (nonces : Message → HashOutput) :
    Pr[fun outputs => ¬tableGoodForNonces nonces outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ 1 / (2 : ENNReal) ^ 193 :=
  (tableGoodForNonces_failure_le nonces).trans (union_ennreal 256 193 BaseAudit.V5.completeness_union)
theorem union_failure_small_bc {α ι κ : Type} [Fintype ι] [Fintype κ] (law : ProbComp α)
    (digestFailed : ι → α → Prop) (encodingFailed : κ → α → Prop)
    (hι : Fintype.card ι ≤ 2 ^ 256) (hκ : Fintype.card κ ≤ 2 ^ 301)
    (hd : ∀ i, Pr[digestFailed i | law] ≤ 1 / (2 : ENNReal) ^ 450)
    (he : ∀ k, Pr[encodingFailed k | law] ≤ 1 / (2 : ENNReal) ^ 600) :
    Pr[fun value => (∃ i, digestFailed i value) ∨ (∃ k, encodingFailed k value) | law] ≤
      1 / (2 : ENNReal) ^ 193 := by
  have hd' := finite_family_failure_le law digestFailed _ hd
  have he' := finite_family_failure_le law encodingFailed _ he
  have hι' : (Fintype.card ι : ENNReal) ≤ 2 ^ 256 := by exact_mod_cast hι
  have hκ' : (Fintype.card κ : ENNReal) ≤ 2 ^ 301 := by exact_mod_cast hκ
  refine ((probEvent_or_le law _ _).trans (add_le_add hd' he')).trans ?_
  refine (add_le_add (mul_le_mul' hι' le_rfl) (mul_le_mul' hκ' le_rfl)).trans ?_
  exact union_ennreal 256 193 BaseAudit.V5.completeness_union
end ClaudeWCT.W9.T3.Budgets
end
end
