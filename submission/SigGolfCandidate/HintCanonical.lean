import SigGolfCandidate.Merge045
set_option autoImplicit false
namespace ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Research.SharedForest OracleComp
def HintCanonical (sig : SharedSignature) : Prop :=
  sig.policyHints.toNat < 7744 ∧ sig.policyHints.toNat / 484 % 2 = 0 ∧ sig.policyHints.toNat / 22 % 22 ≤ 18
theorem hintCanonical_of_valid (sig : SharedSignature) (digits : List (List Nat)) (lows : List Bool)
    (hv : policyHintsValid sig.policyHints digits lows = true) : HintCanonical sig := by
  simp only [policyHintsValid, decide_eq_true_eq] at hv
  have h1lt : hintFloor sig.policyHints 1 < 22 := by
    change sig.policyHints.toNat / 484 % 22 < 22
    exact Nat.mod_lt _ (by decide)
  have h2lt : hintFloor sig.policyHints 2 < 22 := by
    change sig.policyHints.toNat / 22 % 22 < 22
    exact Nat.mod_lt _ (by decide)
  have h1even : hintFloor sig.policyHints 1 % 2 = 0 := by
    rw [hv.2.2.1]
    change HintPolicyResearch.one.getD _ 301 % 2 = 0
    apply HintPolicyResearch.one_even
    change ClaudeWCT.WCT9.CanonicalPolicy.threshold 1 _ < 22
    rw [← hv.2.2.1]
    exact h1lt
  have h2le : hintFloor sig.policyHints 2 ≤ 18 := by
    rw [hv.2.2.2.1]
    change HintPolicyResearch.two.getD _ 301 ≤ 18
    apply HintPolicyResearch.two_le
    change ClaudeWCT.WCT9.CanonicalPolicy.threshold 2 _ < 22
    rw [← hv.2.2.2.1]
    exact h2lt
  change (sig.policyHints.toNat / 484 % 22) % 2 = 0 at h1even
  change sig.policyHints.toNat / 22 % 22 ≤ 18 at h2le
  have hdiv : sig.policyHints.toNat / 484 < 22 := by omega
  rw [Nat.mod_eq_of_lt hdiv] at h1even
  exact ⟨hv.1,h1even,h2le⟩

theorem sign_hintCanonical (answers : SigGolfCandidate.T3.Correctness.Answers)
    (cache : SigGolfCandidate.T3.Cache) (message : SigGolfCandidate.T3.Message) (sig : SharedSignature)
    (he : evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.sign cache message) = some sig) :
    HintCanonical sig := by
  unfold SigGolfCandidate.Research.SharedForest.sign at he
  simp only [evalWithAnswerFn_bind] at he
  split_ifs at he with htag
  · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
  · obtain ⟨counter, output, w, hd, hw, heq⟩ := signPayload_components answers cache message sig he
    obtain ⟨result, hr, hrho, hh, hforest, hlayers, hcounter, hcounters⟩ :=
      signFromOutput_components answers cache _ counter output w hw
    have hv := (searchPreparedLayers_some answers cache _ _ _ result hr).hints_valid
    apply hintCanonical_of_valid sig result.digits result.lows
    rw [← heq, hh]
    exact hv


end ClaudeWCT.W9.T3M.SharedCodec
#print axioms ClaudeWCT.W9.T3M.SharedCodec.sign_hintCanonical
