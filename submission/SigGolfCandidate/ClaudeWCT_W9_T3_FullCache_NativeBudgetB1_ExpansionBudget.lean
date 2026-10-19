import SigGolfCandidate.ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_ExpansionBudget_A

set_option Elab.async false


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
open ClaudeWCT.W9.T3.ExpansionBudget (cost_bind_le cost_topNode)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem cost_recoverHintedLayers_other (answers : Answers) (sig : Signature)
    (index : Nat) (other other' : Digest) :
    ∀ n msg, cost answers (recoverHintedLayers sig index other n msg) =
      cost answers (recoverHintedLayers sig index other' n msg) := by
  intro n
  induction n with
  | zero => intro msg; rfl
  | succ n ih =>
    intro msg
    simp only [recoverHintedLayers, cost_bind]
    congr 1
    cases hs : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt (Fin.ofNat 4 n)
      (hintFloor sig.policyHints (Fin.ofNat 4 n)) (route index (Fin.ofNat 4 n)).2
      (route index (Fin.ofNat 4 n)).1 msg 0 (searchLimit (Fin.ofNat 4 n))) with
    | none => rfl
    | some found =>
      obtain ⟨counter, digits, low⟩ := found
      by_cases hn : n = 0
      · subst hn
        simp only [if_true, cost_bind, cost_topNode, cost_pure]
      · simp only [hn, if_false, cost_bind]
        rw [ih]
        congr 1
        congr 1
        split <;> split <;> simp

theorem expand_cost_le_recovery (answers : Answers) (message : Message) (pk : Digest) (sig : Signature)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 digestAttemptLimit) =
      some (counter, output)) :
    cost answers (expandFill message pk sig) ≤
      cost answers (sharedDigestSearch sig.rho message 0 digestAttemptLimit) +
      cost answers (recoverForest (digestIndex output) (forestSelectionFromOutput output)
        (forestWordsFromOutput output) sig.forest) +
      cost answers (recoverHintedLayers sig (digestIndex output) ((sig.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
          (evalWithAnswerFn answers (recoverForest (digestIndex output)
            (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)) + searchFuel := by
  unfold expandFill
  split
  · simp only [cost_pure]; omega
  · simp only [cost_bind, nonce_retained, hd,
      show (fillTopSignature sig 0).forest = sig.forest from rfl]
    rw [recoverHintedLayers_fill _ _ _ _ _ le_rfl,
      cost_recoverHintedLayers_other answers sig (digestIndex output)
        (((fillTopSignature sig 0).layers 0).path topJ) ((sig.layers 0).path topJ)]
    simp only [Nat.add_assoc]
    apply Nat.add_le_add_left
    apply Nat.add_le_add_left
    apply Nat.add_le_add_left
    split
    · split
      · simp only [cost_pure]; exact Nat.zero_le _
      · split
        · simp only [cost_pure]; exact Nat.zero_le _
        · refine le_trans (cost_bind_le answers _ _ 0 ?_) ?_
          · split <;> simp only [cost_pure, le_refl]
          · rw [Nat.add_zero]
            exact cost_bound answers (ClaudeWCT.WCT9.Cost.bound_searchTop ..)
    · simp only [cost_pure]; exact Nat.zero_le _

#print axioms cost_recoverHintedLayers_other
#print axioms expand_cost_le_recovery
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signFromOutput_cost (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    cost answers (signFromOutput cache rho counter output) =
      cost answers (buildForest (digestIndex output) (forestSelectionFromOutput output) (forestWordsFromOutput output)) +
      cost answers (prepareRoots (digestIndex output)) +
      cost answers (searchPreparedLayers cache (digestIndex output)
        (evalWithAnswerFn answers (prepareRoots (digestIndex output)))
        (evalWithAnswerFn answers (buildForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output))).2) := by
  simp only [signFromOutput, cost_bind]
  split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]

theorem signFromOutput_cost_ge (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    28800 ≤ cost answers (signFromOutput cache rho counter output) := by
  rw [signFromOutput_cost]
  have h := buildForest_cost_ge answers (digestIndex output) (forestSelectionFromOutput output) (forestWordsFromOutput output)
  omega

theorem signFromOutput_recovery_cost_le (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    cost answers (recoverHintedLayers w.signature (digestIndex output) ((w.signature.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1
        (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2)) ≤
      cost answers (signFromOutput cache rho counter output) + (1616 + 425765) := by
  let index := digestIndex output
  let built := evalWithAnswerFn answers (buildForest index (forestSelectionFromOutput output) (forestWordsFromOutput output))
  let prepared := evalWithAnswerFn answers (prepareRoots index)
  unfold signFromOutput at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs : evalWithAnswerFn answers (searchPreparedLayers cache index prepared built.2) with
  | none =>
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some layers =>
    have hf := searchPreparedLayers_some answers cache index prepared built.2 layers hs
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
    subst w
    let sig : Signature := ⟨rho, layers.policyHints, built.1,
      fun lay => piecesSignature lay (layers.pieces.getD lay.val ([], []))⟩
    have hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
        (recoverLayerPair (mainSignature sig) index lay (layers.digits.getD lay.val [])) =
        builtPair answers lay (route index lay).2 := by
      intro lay hl
      apply recoverLayerPair_wotsPieces answers sig index lay hl _ (hf.validDigits lay)
      change piecesSignature lay (layers.pieces.getD lay.val ([], [])) = _
      rw [hf.honest_pieces hcache (digestIndex_lt output)]
    have hm0 : topPair 1 prepared.one.levels = builtPair answers 1 (route index 1).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 1
    have hm1 : topPair 2 prepared.two.levels = builtPair answers 2 (route index 2).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 2
    have hm2 : topPair 3 prepared.three.levels = builtPair answers 3 (route index 3).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 3
    have hc := hf.recovery_cost_le sig ((sig.layers 0).path topJ) rfl hm0 hm1 hm2 hp
    have hforest : evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
      (forestWordsFromOutput output) built.1) = built.2 := recoverForest_honest answers index _ _
    change cost answers (recoverHintedLayers sig index ((sig.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
        (forestWordsFromOutput output) built.1)).1
        (evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
          (forestWordsFromOutput output) built.1)).2)) ≤ _
    rw [hforest, signFromOutput_cost]
    dsimp only [index, prepared, built] at hc ⊢
    omega

/-- The recovery replay bound also holds for the img-v6 normal form of the signer's output (the top path enters
only through `topFoldN`, whose cost is bounded coarsely; the 13-bit hint and the lower layers are unchanged). -/
theorem signFromOutput_recovery_cost_le_norm (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    cost answers (recoverHintedLayers (normTop w.signature) (digestIndex output)
      (((normTop w.signature).layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1
        (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2)) ≤
      cost answers (signFromOutput cache rho counter output) + (1616 + 425765) := by
  let index := digestIndex output
  let built := evalWithAnswerFn answers (buildForest index (forestSelectionFromOutput output) (forestWordsFromOutput output))
  let prepared := evalWithAnswerFn answers (prepareRoots index)
  unfold signFromOutput at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs : evalWithAnswerFn answers (searchPreparedLayers cache index prepared built.2) with
  | none =>
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some layers =>
    have hf := searchPreparedLayers_some answers cache index prepared built.2 layers hs
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
    subst w
    let sig : Signature := ⟨rho, layers.policyHints, built.1,
      fun lay => piecesSignature lay (layers.pieces.getD lay.val ([], []))⟩
    let sig' := normTop sig
    have hh' : sig'.policyHints = layers.policyHints := by
      apply normTop_hints
      have := hf.hints_spec.1
      show layers.policyHints.toNat < 2 ^ 13
      omega
    have hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
        (recoverLayerPair (mainSignature sig') index lay (layers.digits.getD lay.val [])) =
        builtPair answers lay (route index lay).2 := by
      intro lay hl
      apply recoverLayerPair_wotsPieces answers sig' index lay hl _ (hf.validDigits lay)
      rw [normTop_layers_ne sig lay hl]
      change piecesSignature lay (layers.pieces.getD lay.val ([], [])) = _
      rw [hf.honest_pieces hcache (digestIndex_lt output)]
    have hm0 : topPair 1 prepared.one.levels = builtPair answers 1 (route index 1).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 1
    have hm1 : topPair 2 prepared.two.levels = builtPair answers 2 (route index 2).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 2
    have hm2 : topPair 3 prepared.three.levels = builtPair answers 3 (route index 3).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 3
    have hc := hf.recovery_cost_le sig' ((sig'.layers 0).path topJ) hh' hm0 hm1 hm2 hp
    have hforest : evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
      (forestWordsFromOutput output) built.1) = built.2 := recoverForest_honest answers index _ _
    change cost answers (recoverHintedLayers sig' index ((sig'.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
        (forestWordsFromOutput output) built.1)).1
        (evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
          (forestWordsFromOutput output) built.1)).2)) ≤ _
    rw [hforest, signFromOutput_cost]
    dsimp only [index, prepared, built] at hc ⊢
    omega

theorem signPayload_cost_step (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
      message 0 digestAttemptLimit) = some (counter, output)) :
    cost answers (signPayload cache message) = cost answers (privateNonce message) +
      cost answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message)) message 0 digestAttemptLimit) +
      cost answers (signFromOutput cache (evalWithAnswerFn answers (privateNonce message)) counter output) := by
  simp only [signPayload, cost_bind, hd]
  split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]

/-- Expand's pointwise excess over the signer (img-v6): replay 1,616 + 284 = 1,900 plus the worst-case re-derivation of the
11 ancestor top-node nonces `Σ_h (104·2^h − 1) = 425,765`. -/
def expandReplayExtra : Nat := 1900 + 425765

theorem expand_cost_le_payload_add (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (message : Message) (sig : Signature)
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) (pk : Digest) :
    cost answers (expand message pk sig) ≤ cost answers (signPayload cache message) + expandReplayExtra + searchFuel := by
  unfold expandReplayExtra
  unfold signPayload at he
  simp only [evalWithAnswerFn_bind] at he
  let rho := evalWithAnswerFn answers (privateNonce message)
  cases hd : evalWithAnswerFn answers (sharedDigestSearch rho message 0 digestAttemptLimit) with
  | none =>
    dsimp only [rho] at hd
    simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
    obtain ⟨counter, output⟩ := found
    dsimp only [rho] at hd
    simp only [hd, evalWithAnswerFn_bind] at he
    cases hs : evalWithAnswerFn answers (signFromOutput cache rho counter output) with
    | none =>
      dsimp only [rho] at hs
      simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
    | some original =>
      have hr := signFromOutput_recovery_cost_le_norm answers cache hcache rho counter output original hs
      have hh := signFromOutput_recovery answers cache hcache rho counter output original hs
      dsimp only [rho] at hs
      simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
      subst sig
      have hd' : evalWithAnswerFn answers (sharedDigestSearch (normTop original.signature).rho message 0
          digestAttemptLimit) = some (counter, output) := by rw [normTop_rho, hh.1]; exact hd
      have hx := expand_cost_le_recovery answers message pk (normTop original.signature) counter output hd'
      have hf := cost_bound answers (bound_recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) original.signature.forest)
      simp only [normTop_rho, normTop_forest] at hx
      rw [hh.1] at hx
      change cost answers (expandFill message pk (normTop original.signature)) ≤ _
      rw [signPayload_cost_step answers cache message counter output hd]
      dsimp only [rho] at hx hr
      omega

#print axioms signFromOutput_recovery_cost_le
#print axioms expand_cost_le_payload_add
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signPayload_cost_ge (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (signPayload cache message) = some sig) :
    28800 ≤ cost answers (signPayload cache message) := by
  unfold signPayload at hs
  simp only [evalWithAnswerFn_bind] at hs
  cases hd : evalWithAnswerFn answers (sharedDigestSearch
    (evalWithAnswerFn answers (privateNonce message)) message 0 digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at hs
  | some found =>
    obtain ⟨counter, output⟩ := found
    rw [signPayload_cost_step answers cache message counter output hd]
    have h := signFromOutput_cost_ge answers cache
      (evalWithAnswerFn answers (privateNonce message)) counter output
    omega

theorem sign_cost_honest (answers : Answers) (message : Message) :
    cost answers (sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) =
      2 + cost answers (signPayload (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) := by
  have hvalid := keygen_cache_tag answers
  have hmac : cost answers (privateMac (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2.region) = 2 := by
    simp only [SigGolfCandidate.T3.SearchCost.cost, privateMac_count, evalWithAnswerFn_map]
  simp only [CacheTagCorrect] at hvalid
  simp only [sign, cost_bind, hmac, ← hvalid, ne_eq, not_true_eq_false, ite_false]

/-- img-v6: the pointwise route `expand ≤ 8·sign` is FALSE (PORT v6 §E). What holds pointwise is
`expand ≤ sign + expandReplayExtra + searchFuel` (replay 1,900 + worst ancestor nonce re-derivation 425,765, brute force);
the expand moment is closed by Hölder (`ClaudeWCT.Arith.ExpectHolder.expand_moment_of_holder`). -/
theorem expand_cost_le_sign_add (answers : Answers) (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) = some sig) :
    cost answers (expand message (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).1 sig) ≤
      cost answers (sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) +
        expandReplayExtra + searchFuel := by
  have hvalid := keygen_cache_tag answers
  have hs' : evalWithAnswerFn answers (signPayload (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) = some sig := by
    simp only [CacheTagCorrect] at hvalid
    simpa only [sign, evalWithAnswerFn_bind, ← hvalid, ne_eq, not_true_eq_false, ite_false] using hs
  have hk := SigGolfCandidate.T3.Correctness.keygen_correct answers
  have h := expand_cost_le_payload_add answers (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 hk.2.1
    message sig hs' (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).1
  have hmin := signPayload_cost_ge answers (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message sig hs'
  rw [sign_cost_honest]
  omega

#print axioms expand_cost_le_sign_add
end SigGolfCandidate.Research.SharedForest
