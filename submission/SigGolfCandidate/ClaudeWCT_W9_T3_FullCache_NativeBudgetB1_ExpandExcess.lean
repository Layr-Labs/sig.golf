import SigGolfCandidate.ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_ExpansionBudget
import SigGolfCandidate.ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_TopSibling

/-! # img-v6 expand excess, pointwise part (r3-lean-topbytes)

`expand_cost_le_sign_field`: on the honest run, expand ≤ sign + `expandReplayExtra` + the omitted 19-bit field of the
signer's top sibling, and that sibling is one of the two level-11 nodes of the keygen top tree, so the excess is at
most `expandReplayExtra + max (field v₂) (field v₃)` (`v₂, v₃ = treeValue (builtTree answers 0 0) 11 0/1`). -/

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
open ClaudeWCT.W9.T3.ExpansionBudget (cost_bind_le cost_topNode)

/-- img-v6: the brute force stops at the first hit; with a hit at `c` it costs at most `c + 1 - c0` node hashes. -/
theorem cost_searchTop_le_hit (answers : Answers) (index : Nat) (v sib pk : Digest) :
    ∀ fuel c0 c, c0 ≤ c → c < c0 + fuel → evalWithAnswerFn answers (topNode index v (setTop sib c)) = pk →
      cost answers (searchTop index v sib pk fuel c0) ≤ c + 1 - c0 := by
  intro fuel
  induction fuel with
  | zero => intro c0 c h1 h2; omega
  | succ fuel ih =>
    intro c0 c h1 h2 h3
    simp only [searchTop, cost_bind, cost_topNode]
    split
    · simp only [cost_pure]; omega
    · rename_i hne
      have hc : c ≠ c0 := by rintro rfl; exact hne h3
      have := ih (c0 + 1) c (by omega) (by omega) h3
      omega

/-- The brute-forced field of a top sibling: bits 109..127 (19 bits). -/
def topField (d : Digest) : Nat := d.toNat / 2 ^ 109

/-- **img-v6 refined expand cost**: on a signature whose full (unfilled) top path recovers to the key, the brute
force costs at most the omitted field of the true top sibling (`topField`), instead of `searchFuel`. -/
theorem expand_cost_le_recovery_field (answers : Answers) (message : Message) (pk : Digest) (sig : Signature)
    (counter : BitVec 32) (output : HashOutput) (result : RecoveredLayers)
    (hd : evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 digestAttemptLimit) =
      some (counter, output))
    (hr : evalWithAnswerFn answers (recoverHintedLayers sig (digestIndex output) ((sig.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
        (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)) = some result)
    (hpk : result.root = pk) :
    cost answers (expandFill message pk sig) ≤
      cost answers (sharedDigestSearch sig.rho message 0 digestAttemptLimit) +
      cost answers (recoverForest (digestIndex output) (forestSelectionFromOutput output)
        (forestWordsFromOutput output) sig.forest) +
      cost answers (recoverHintedLayers sig (digestIndex output) ((sig.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
          (evalWithAnswerFn answers (recoverForest (digestIndex output)
            (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)) +
      topField ((sig.layers 0).path topJ) := by
  let index := digestIndex output
  let forest := evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output) sig.forest)
  let sig0 := fillTopSignature sig 0
  have hroot : evalWithAnswerFn answers (topNode index result.foldedTop ((sig.layers 0).path topJ)) = pk := by
    have he := eval_recoverHintedLayers_other answers sig index ((sig.layers 0).path topJ)
      ((sig.layers 0).path topJ) 4 (.pair forest.1 forest.2)
    rw [hr] at he
    simp only [Option.map_some, Option.some.injEq] at he
    exact (congrArg RecoveredLayers.root he).symm.trans hpk
  have hr0 : evalWithAnswerFn answers (recoverHintedLayers sig index ((sig0.layers 0).path topJ) 4
      (.pair forest.1 forest.2)) = some {result with
        root := evalWithAnswerFn answers (topNode index result.foldedTop ((sig0.layers 0).path topJ))} := by
    rw [eval_recoverHintedLayers_other answers sig index ((sig.layers 0).path topJ)]
    rw [hr]
    rfl
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
    dsimp only [sig0, index, forest] at hr0
    rw [hr0]
    simp only
    split
    · simp only [cost_pure]; exact Nat.zero_le _
    · split
      · simp only [cost_pure]; exact Nat.zero_le _
      · rename_i hz
        refine le_trans (cost_bind_le answers _ _ 0 ?_) ?_
        · split <;> simp only [cost_pure, le_refl]
        · rw [Nat.add_zero]
          have hcompletion : evalWithAnswerFn answers (topNode (digestIndex output) result.foldedTop
              (setTop (((fillTopSignature sig 0).layers 0).path topJ) (topField ((sig.layers 0).path topJ)))) = pk := by
            rw [topPath_fill_signature, setTop_setTop]
            unfold topField
            rw [setTop_self]
            exact hroot
          have hn : topField ((sig.layers 0).path topJ) ≠ 0 := by
            intro he
            rw [he, topPath_fill_signature, setTop_setTop] at hcompletion
            exact hz hcompletion
          have ht := top_lt ((sig.layers 0).path topJ)
          have := cost_searchTop_le_hit answers (digestIndex output) result.foldedTop
            (((fillTopSignature sig 0).layers 0).path topJ) pk searchFuel 1 (topField ((sig.layers 0).path topJ))
            (by omega) (by unfold searchFuel topField at *; omega) hcompletion
          omega

#print axioms expand_cost_le_recovery_field


theorem route_top_tree (index : Nat) (h : index < 2 ^ 31) : (route index 0).2 = 0 := by
  simp only [route]
  apply Nat.div_eq_of_lt
  simpa [height] using h

theorem route_top_leaf_lt (index : Nat) : (route index 0).1 < 2 ^ 12 := by
  simp only [route]
  exact Nat.mod_lt _ (by simp [height])

/-- The signer's top sibling (path node at height 11) is the keygen's level-11 node next to the signed leaf. -/
theorem signFromOutput_topSib (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    (w.signature.layers 0).path topJ =
      treeValue (builtTree answers 0 0) 11 ((route (digestIndex output) 0).1 / 2 ^ 11 ^^^ 1) := by
  let index := digestIndex output
  let built := evalWithAnswerFn answers (buildForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output))
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
    have hp := hf.honest_pieces hcache (digestIndex_lt output) 0
    change (piecesSignature 0 (layers.pieces.getD (0 : Layer).val ([], []))).path topJ = _
    rw [hp, route_top_tree _ (digestIndex_lt output)]
    simp [piecesSignature, wotsPieces, topJ, wotsTree_top, height, index]

theorem topField_sib_le (answers : Answers) (index : Nat) :
    topField (treeValue (builtTree answers 0 0) 11 ((route index 0).1 / 2 ^ 11 ^^^ 1)) ≤
      max (topField (treeValue (builtTree answers 0 0) 11 0)) (topField (treeValue (builtTree answers 0 0) 11 1)) := by
  have hl := route_top_leaf_lt index
  have h2 : (route index 0).1 / 2 ^ 11 < 2 := by omega
  generalize (route index 0).1 / 2 ^ 11 = b at h2
  interval_cases b
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- Pointwise expand excess over the signer's payload (honest cache, key = top root). -/
theorem expand_cost_le_payload_field (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hreg : cache.region = cacheRegion (maskedTop answers)) (message : Message) (sig : Signature)
    (hs' : evalWithAnswerFn answers (signPayload cache message) = some sig) (pk : Digest)
    (hpk : pk = treeValue (builtTree answers 0 0) 12 0) (htree : TopTreeOK answers) :
    cost answers (expand message pk sig) ≤ cost answers (signPayload cache message) + expandReplayExtra +
        max (topField (treeValue (builtTree answers 0 0) 11 0)) (topField (treeValue (builtTree answers 0 0) 11 1)) := by
  unfold signPayload at hs'
  simp only [evalWithAnswerFn_bind] at hs'
  let rho := evalWithAnswerFn answers (privateNonce message)
  cases hd : evalWithAnswerFn answers (sharedDigestSearch rho message 0 digestAttemptLimit) with
  | none =>
    dsimp only [rho] at hd
    simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at hs'
  | some found =>
    obtain ⟨counter, output⟩ := found
    dsimp only [rho] at hd
    simp only [hd, evalWithAnswerFn_bind] at hs'
    cases hso : evalWithAnswerFn answers (signFromOutput cache rho counter output) with
    | none =>
      dsimp only [rho] at hso
      simp only [hso, evalWithAnswerFn_pure, reduceCtorEq] at hs'
    | some original =>
      have hr := signFromOutput_recovery_cost_le answers cache hreg rho counter output original hso
      have hh := signFromOutput_recovery answers cache hreg rho counter output original hso
      have hsib := signFromOutput_topSib answers cache hreg rho counter output original hso
      have htop := signFromOutput_topPathOK answers cache hreg htree rho counter output original hso
      dsimp only [rho] at hso
      simp only [hso, evalWithAnswerFn_pure, Option.some.injEq] at hs'
      subst sig
      obtain ⟨hrho, result, hres, hroot, hval, _⟩ := hh
      have hhb : original.signature.policyHints.toNat < 2 ^ 13 := by
        have hv := hval
        simp only [policyHintsValid, decide_eq_true_eq] at hv
        have := hv.1
        omega
      rw [expand_eq_expandFill message pk original.signature hhb htop]
      have hd' : evalWithAnswerFn answers (sharedDigestSearch original.signature.rho message 0 digestAttemptLimit) =
          some (counter, output) := by rw [hrho]; exact hd
      have hx := expand_cost_le_recovery_field answers message pk original.signature counter output result hd'
        hres (hroot.trans hpk.symm)
      have hf := cost_bound answers (bound_recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) original.signature.forest)
      have hle := topField_sib_le answers (digestIndex output)
      rw [← hsib] at hle
      rw [hrho] at hx
      dsimp only [rho] at hx hr
      rw [signPayload_cost_step answers cache message counter output hd]
      unfold expandReplayExtra
      omega

/-- The brute-force part of the excess: the larger root-child field if every top node passed its zero test,
the whole search otherwise (cap exhaustion, probability ≤ 2^-143). -/
noncomputable def excessField (answers : Answers) : Nat :=
  open Classical in
  if TopTreeOK answers then
    max (topField (treeValue (builtTree answers 0 0) 11 0)) (topField (treeValue (builtTree answers 0 0) 11 1))
  else searchFuel

/-- **img-v6 pointwise expand excess** (replaces `expand ≤ 8·sign`). -/
theorem expand_cost_le_sign_field (answers : Answers) (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) = some sig) :
    cost answers (expand message (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).1 sig) ≤
      cost answers (sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) + expandReplayExtra +
        excessField answers := by
  unfold excessField
  by_cases htree : TopTreeOK answers
  swap
  · simp only [htree, if_false]
    exact expand_cost_le_sign_add answers message sig hs
  simp only [htree, if_true]
  have hvalid := keygen_cache_tag answers
  have hk := SigGolfCandidate.T3.Correctness.keygen_correct answers
  have hs' : evalWithAnswerFn answers (signPayload (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) =
      some sig := by
    simp only [CacheTagCorrect] at hvalid
    simpa only [sign, evalWithAnswerFn_bind, ← hvalid, ne_eq, not_true_eq_false, ite_false] using hs
  have h := expand_cost_le_payload_field answers _ hk.2.1 message sig hs' _ hk.1 htree
  rw [sign_cost_honest]
  omega

#print axioms expand_cost_le_sign_field
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedExpansionV6
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Correctness (Answers builtTree treeValue)
open SigGolfCandidate.T3.SourceReplay (fixedAnswers)
open SigGolfCandidate.T3.SearchCost (cost counted_fst)
open SigGolfCandidate.T3.ExpansionClosure (jointCounts)
open SigGolfCandidate.T3.SourceReplay (HashOnly hashOnly_pure hashOnly_bind hashOnly_map hashOnly_buildTopTree)
open SigGolfCandidate.T3.CountedReplay (hashOnly_countBlocks support_replay)
open SigGolfCandidate.Research.SharedForest (Signature Witness sign expand expandReplayExtra topField
  expand_cost_le_sign_field)
open ClaudeWCT.W9.T3.TopMoment
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The keygen payload after the top tree (masking). -/
def payloadTail (levels : List (List Digest)) : M (Digest × Region) := do
  let masked ← (List.range' 0 12).mapM fun level => maskedLevel (levels.getD level []) level
  let raw := (masked.flatten.flatMap (SphincsSecurity.bytesLE 16)).toArray
  pure ((levels.getD 12 []).getD 0 0, fun i => raw.getD i.val 0)

/-- The keygen after the top tree (masking, MAC). -/
def keygenRest (levels : List (List Digest)) : M (Digest × SigGolfCandidate.T3.Cache) := do
  let (publicKey, region) ← payloadTail levels
  let tag ← privateMac region
  pure (publicKey, ⟨tag, region⟩)

theorem keygen_split : keygen = (buildTopTree >>= keygenRest) := by
  unfold keygen keygenPayload keygenRest payloadTail
  simp only [bind_assoc]

/-- The joint run after the keys (`jointCounts` from fixed keys). -/
def afterKeys (message : Message) (keys : Digest × SigGolfCandidate.T3.Cache) : M (Nat × Nat) :=
  jointCounts (pure keys) (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)

theorem jointCounts_bind {κ σ ω : Type} (initial : M κ) (signer : κ → M (Option σ)) (expander : κ → σ → M ω) :
    jointCounts initial signer expander = (initial >>= fun k => jointCounts (pure k) signer expander) := by
  unfold jointCounts
  simp only [pure_bind]

/-- The joint run, also returning the keygen's level-11 nodes. -/
def jointI (message : Message) : M ((Nat × Nat) × List Digest) :=
  buildTopTree >>= fun levels => (fun c => (c, levels.getD 11 [])) <$> (keygenRest levels >>= afterKeys message)

theorem jointCounts_eq (message : Message) :
    jointCounts keygen (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig) =
      Prod.fst <$> jointI message := by
  rw [jointCounts_bind, keygen_split]
  unfold jointI afterKeys
  simp only [bind_assoc, map_bind, Functor.map_map, id_map']

/-- Additive version of `eval_joint_cost_le`. -/
theorem eval_joint_cost_le_add {κ σ ω : Type} (answers : Answers)
    (initial : M κ) (signer : κ → M (Option σ)) (expander : κ → σ → M ω) (B : Nat)
    (hbound : ∀ sig, evalWithAnswerFn answers (signer (evalWithAnswerFn answers initial)) = some sig →
      cost answers (expander (evalWithAnswerFn answers initial) sig) ≤
        cost answers (signer (evalWithAnswerFn answers initial)) + B) :
    (evalWithAnswerFn answers (jointCounts initial signer expander)).2 ≤
      (evalWithAnswerFn answers (jointCounts initial signer expander)).1 + B := by
  unfold jointCounts
  have hfst := counted_fst answers (signer (evalWithAnswerFn answers initial))
  generalize hk : evalWithAnswerFn answers initial = keys at hfst hbound ⊢
  simp only [evalWithAnswerFn_bind, hk]
  generalize hc : evalWithAnswerFn answers (countBlocks (signer keys)) = signed at hfst ⊢
  rcases signed with ⟨sig, n⟩
  cases sig with
  | none => simp only [evalWithAnswerFn_pure]; omega
  | some sig =>
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      have hh := hbound sig hfst.symm
      simpa only [SigGolfCandidate.T3.SearchCost.cost, hc] using hh

/-- The leaf part of the top-tree build avoids the root children's trials and yields 4096 leaves (scheme-dependent;
discharged per keygen spec). -/
def TopPrefixOK (secret : BitVec 256) : Prop :=
  ∃ (γ : Type) (pre : M γ) (sel : γ → List Digest) (k : Nat),
    buildTopTree = (pre >>= fun s => buildTopLevels (sel s)) ∧
    ∀ heap target, TopQ heap target → (heap = 2 ∨ heap = 3) →
      Bound (PAv secret target) (fun s => (sel s).length = 2 ^ 12) k pre

/-- The excess weight `2^((8/7)(K + c)/2^20)`. -/
noncomputable def excessWeight (c : Nat) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ ((8 / 7 : ℝ) * ((expandReplayExtra + c : ℕ) : ℝ) / 1048576)

/-- **Numeric obligation (N2b, r3k numerics porter)**: `E_{c₂,c₃ uniform}[2^((8/7)(K + max c₂ c₃)/2^20)] ≤ 2`
(value ≈ 1.806). -/
def ExpandExcessNumeric : Prop := avgF (fun c2 => avgF (fun c3 => excessWeight (max c2 c3))) ≤ 2

theorem excessWeight_mono {a b : Nat} (h : a ≤ b) : excessWeight a ≤ excessWeight b := by
  unfold excessWeight
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  have : ((expandReplayExtra + a : ℕ) : ℝ) ≤ ((expandReplayExtra + b : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have h87 : (0 : ℝ) ≤ 8 / 7 := by norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this h87) (by norm_num)

/- `expand_excess_moment` moved to `ExpandMomentV6.lean` (needs the cap-exhaustion bound `TopCapBad`). -/
end SigGolfCandidate.Research.SharedExpansionV6
