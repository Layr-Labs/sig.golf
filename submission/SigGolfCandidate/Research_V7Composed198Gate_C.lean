import SigGolfCandidate.Research_V7Composed198Gate_B

set_option autoImplicit false
set_option Elab.async false


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem recoverHintedLayers_verified (answers : Answers) (sig : Signature) (index : Nat) :
    ∀ n, n ≤ 4 → ∀ msg result,
      evalWithAnswerFn answers (recoverHintedLayers sig index ((sig.layers 0).path topJ) n msg) = some result →
      result.counters.length = n ∧ result.digits.length = n ∧ result.lows.length = n ∧
        ∀ w : Witness, w.signature = sig →
          (∀ lay : Layer, lay.val < n → w.counters lay = result.counters.getD lay.val 0) →
          w.topHigh = !(result.lows.getD 0 true) → w.topNonces = result.nonces →
          evalWithAnswerFn answers (verifyLayers w index n msg) = some result.root := by
  intro n
  induction n with
  | zero =>
      intro _ msg result he
      simp [recoverHintedLayers] at he
  | succ n ih =>
      intro hn msg result he
      simp only [recoverHintedLayers, evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt (Fin.ofNat 4 n)
        (hintFloor sig.policyHints (Fin.ofNat 4 n))
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg 0
        (searchLimit (Fin.ofNat 4 n))) with
      | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some found =>
          obtain ⟨counter, digits, low⟩ := found
          have hlim := searchLimit_le (Fin.ofNat 4 n)
          obtain ⟨_, hbound, hlow, hproducer⟩ := canonical_search_some' answers (Fin.ofNat 4 n)
            (hintFloor sig.policyHints (Fin.ofNat 4 n))
            (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg
            (searchLimit (Fin.ofNat 4 n)) 0 counter digits low (by unfold counterLimit at hlim; omega) hs
          have hdecode := (CanonicalPolicy.producerDecodeAt_spec hproducer).1
          have hnot : ¬counter.toNat ≥ verifyWindow := ctr_not_ge_verifyWindow counter
          have hlay := ofNat_layer_val n (by omega)
          simp only [hs] at he
          by_cases hn0 : n = 0
          · subst n
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at he
            subst result
            refine ⟨rfl, rfl, rfl, fun w hw hc hh hnon => ?_⟩
            have hcounter : w.counters (Fin.ofNat 4 0) = counter := by
              rw [hc _ (by rw [hlay]; omega), hlay]; rfl
            have hdecode0 : SigGolfCandidate.T3.decode 0
                (evalWithAnswerFn answers (encodingHash 0
                  (layerEncodingInput 0 (route index 0).2 (route index 0).1 msg counter))) = some digits := hdecode
            have hv : evalWithAnswerFn answers (verificationHash 0 w.topHigh
                (layerEncodingInput 0 (route index 0).2 (route index 0).1 msg counter)) =
                evalWithAnswerFn answers (encodingHash 0
                  (layerEncodingInput 0 (route index 0).2 (route index 0).1 msg counter)) := by
              apply eval_verificationHash_honest
              rw [hh, encodingHigh_top]
              simp only [List.getD_cons_zero]
              exact congrArg (fun b => !b) hlow
            simp only [verifyLayers, hcounter, hnot, ite_false, evalWithAnswerFn_bind, if_true, hw]
            simp only [show (Fin.ofNat 4 0 : Layer) = 0 from rfl]
            rw [hv, hnon]
            exact eval_verifyTopN_topFoldN answers _ index hdecode0
          · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
            cases hr : evalWithAnswerFn answers (recoverHintedLayers sig index ((sig.layers 0).path topJ) n
              (.pair (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index (Fin.ofNat 4 n) digits)).1
                (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index (Fin.ofNat 4 n) digits)).2)) with
            | none => simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at he
            | some previous =>
                simp only [hr, evalWithAnswerFn_pure, Option.some.injEq] at he
                subst result
                obtain ⟨hlen, hdlen, hllen, hverify⟩ := ih (by omega) _ _ hr
                refine ⟨by simp [hlen], by simp [hdlen], by simp [hllen], fun w hw hc hh => ?_⟩
                have hcounter : w.counters (Fin.ofNat 4 n) = counter := by
                  rw [hc _ (by rw [hlay]; omega), hlay,
                    List.getD_append_right previous.counters [counter] 0 n (by omega), hlen]
                  simp
                have hnonzero : (Fin.ofNat 4 n : Layer) ≠ 0 := by
                  intro h; have := congrArg Fin.val h; rw [hlay] at this; exact hn0 this
                have hgood : lowerRankGood (evalWithAnswerFn answers (encodingHash (Fin.ofNat 4 n)
                    (layerEncodingInput (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
                      (route index (Fin.ofNat 4 n)).1 msg counter))) :=
                  (CanonicalPolicy.producerDecodeAt_spec hproducer).2.2.2.resolve_left hnonzero
                simp only [verifyLayers, hcounter, hnot, ite_false, evalWithAnswerFn_bind,
                  verificationHash_lower (Fin.ofNat 4 n) hnonzero,
                  hdecode, hn0, hw, recoverLayerPairGuard_of_good _ _ _ _ _ hgood, evalWithAnswerFn_map]
                apply hverify w hw
                · intro lay hsmall
                  rw [hc lay (by omega), List.getD_append previous.counters [counter] 0 lay.val (by omega)]
                · rw [hh, List.getD_append previous.lows [low] true 0 (by omega)]

#print axioms recoverHintedLayers_verified
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 ClaudeWCT.WCT9

/-- The paired table selector is exactly the canonical A leaf position. -/
theorem physicalFromOutput_first (output : HashOutput) (pair : Fin 4) :
    physicalChildFromOutput output ⟨2 * pair.val, by have := pair.isLt; omega⟩ =
      firstChild ((forestSelectionFromOutput output).pairs pair) := by
  apply Fin.ext
  fin_cases pair <;>
    simp [physicalChildFromOutput, firstCoord, physicalChild, rawChildFromOutput, rawChildBase,
      forestSelectionFromOutput, selectionFromOutput, firstChild] <;> omega

/-- The rotated B selector shares A's branch and retains six independent path bits. -/
theorem physicalFromOutput_second (output : HashOutput) (pair : Fin 4) :
    physicalChildFromOutput output ⟨2 * pair.val + 1, by have := pair.isLt; omega⟩ =
      secondChild ((forestSelectionFromOutput output).pairs pair) := by
  apply Fin.ext
  fin_cases pair <;>
    simp [physicalChildFromOutput, firstCoord, physicalChild, rawChildFromOutput, rawChildBase,
      forestSelectionFromOutput, selectionFromOutput, secondChild] <;> omega

theorem physicalFromOutput_singleton (output : HashOutput) :
    physicalChildFromOutput output 8 = (forestSelectionFromOutput output).singleton := by
  rfl

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem mainSignature_fill (sig : Signature) (c : Nat) :
    mainSignature (fillTopSignature sig c) = fillTop (mainSignature sig) c := rfl

theorem topFold_fill_signature (sig : Signature) (index : Nat) (digits : List Nat) (c : Nat) :
    topFold (mainSignature (fillTopSignature sig c)) index digits =
      topFold (mainSignature sig) index digits := by
  rw [mainSignature_fill]
  have h := topFold_fill (mainSignature sig) index digits c
    ((topSib (mainSignature sig)).toNat / 2 ^ 109)
  rw [fillTop_self] at h
  exact h

theorem topFoldN_fill_signature (sig : Signature) (index : Nat) (digits : List Nat) (c : Nat) :
    topFoldN (mainSignature (fillTopSignature sig c)) index digits =
      topFoldN (mainSignature sig) index digits := by
  rw [mainSignature_fill]
  have h := topFoldN_fill (mainSignature sig) index digits c
    ((topSib (mainSignature sig)).toNat / 2 ^ 109)
  rw [fillTop_self] at h
  exact h

theorem recoverHintedLayers_fill (sig : Signature) (index : Nat) (other : Digest) (c : Nat) :
    ∀ n, n ≤ 4 → ∀ msg,
      recoverHintedLayers (fillTopSignature sig c) index other n msg =
        recoverHintedLayers sig index other n msg := by
  intro n
  induction n with
  | zero => intro _ msg; rfl
  | succ n ih =>
      intro hn msg
      simp only [recoverHintedLayers, hints_retained]
      apply bind_congr
      intro found
      cases found with
      | none => rfl
      | some found =>
          obtain ⟨counter, digits, low⟩ := found
          cases n with
          | zero =>
              simp only [if_true, topFoldN_fill_signature]
          | succ k =>
              have hne := fin_ofNat_succ_ne k (by omega)
              simp only [Nat.succ_ne_zero, if_false, mainSignature_fill,
                recoverLayerPair_fill _ _ _ _ _ hne]
              apply bind_congr
              intro pair
              rw [ih (by omega)]

theorem eval_recoverHintedLayers_other (answers : Answers) (sig : Signature)
    (index : Nat) (other other' : Digest) :
    ∀ n msg, evalWithAnswerFn answers (recoverHintedLayers sig index other' n msg) =
      (evalWithAnswerFn answers (recoverHintedLayers sig index other n msg)).map
        (fun result => {result with root := evalWithAnswerFn answers (topNode index result.foldedTop other')}) := by
  intro n
  induction n with
  | zero => intro msg; simp [recoverHintedLayers]
  | succ n ih =>
      intro msg
      simp only [recoverHintedLayers, evalWithAnswerFn_bind]
      cases evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt (Fin.ofNat 4 n)
        (hintFloor sig.policyHints (Fin.ofNat 4 n)) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 msg 0 (searchLimit (Fin.ofNat 4 n))) with
      | none => simp
      | some found =>
          obtain ⟨counter, digits, low⟩ := found
          by_cases hn : n = 0
          · simp [hn]
          · simp only [hn, if_false, evalWithAnswerFn_bind, ih]
            cases evalWithAnswerFn answers (recoverHintedLayers sig index other n _) with
            | none => simp
            | some previous => simp

theorem sharedDigestSearch_some (answers : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter found output, counter + fuel ≤ 2 ^ 32 →
      evalWithAnswerFn answers (sharedDigestSearch rho message counter fuel) = some (found, output) →
      counter ≤ found.toNat ∧ found.toNat < counter + fuel ∧ digestAccepted output = true ∧
        evalWithAnswerFn answers (digest rho message found) = output := by
  intro fuel
  induction fuel with
  | zero => intro counter found output _ he; simp [sharedDigestSearch] at he
  | succ fuel ih =>
      intro counter found output hlimit he
      simp only [sharedDigestSearch, evalWithAnswerFn_bind] at he
      split_ifs at he with hg
      · simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hc : (BitVec.ofNat 32 counter).toNat = counter := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact ⟨by rw [hc], by rw [hc]; omega, hg, rfl⟩
      · obtain ⟨hlo, hhi, hg, ho⟩ := ih (counter + 1) found output (by omega) he
        exact ⟨by omega, by omega, hg, ho⟩

theorem verify_from_recovered (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (counter : BitVec 32) (output : HashOutput) (result : RecoveredLayers)
    (ho : evalWithAnswerFn answers (digest sig.rho message counter) = output)
    (ha : verifyDigestAccepted output = true)
    (hr : evalWithAnswerFn answers (recoverHintedLayers sig (digestIndex output)
      ((sig.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
        (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)) = some result)
    (hpk : result.root = pk) :
    evalWithAnswerFn answers (verify message pk
      ⟨sig, counter, fun lay => result.counters.getD lay.val 0, !(result.lows.getD 0 true), result.nonces⟩) = true := by
  have hc : ¬counter.toNat ≥ digestVerifyWindow := Nat.not_le.mpr counter.isLt
  have hv := (recoverHintedLayers_verified answers sig (digestIndex output) 4 le_rfl _ _ hr).2.2.2
    ⟨sig, counter, fun lay => result.counters.getD lay.val 0, !(result.lows.getD 0 true), result.nonces⟩ rfl (by intros; rfl) rfl
  simp only [verify, hc, if_false, evalWithAnswerFn_bind, ho, ha, Bool.not_true,
    Bool.false_eq_true, hv, evalWithAnswerFn_pure, hpk, beq_self_eq_true]

#print axioms recoverHintedLayers_fill
#print axioms eval_recoverHintedLayers_other
#print axioms sharedDigestSearch_some
#print axioms verify_from_recovered
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- The forest commitment depends only on the signing index and oracle answers;
selector and rank choices determine its opening, but not its value. -/
def forestCommitment (answers : Answers) (index : Nat) : PairRoot :=
  let first := expectedPairRoot answers index 0 ftsStart
  let second := expectedPairRoot answers index 1 first
  let third := expectedPairRoot answers index 2 second
  let fourth := expectedPairRoot answers index 3 third
  let nodes := sharedNodes answers false index 8 (fun _ => fourth)
  (nodes.getD 2 0, nodes.getD 3 0)

attribute [local irreducible] sharedNodes

theorem buildForest_commitment (answers : Answers) (index : Nat)
    (selected : ForestSelection) (words : ForestWords) :
    (evalWithAnswerFn answers (buildForest index selected words)).2 = forestCommitment answers index := by
  have hfour : List.finRange 4 = [0, 1, 2, 3] := by decide
  simp only [buildForest, hfour, List.foldlM_cons, List.foldlM_nil,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, buildPair_result,
    buildSingleton, buildSharedCoordinate_result]
  rfl

theorem recoverForest_commitment (answers : Answers) (index : Nat)
    (selected : ForestSelection) (words : ForestWords) :
    evalWithAnswerFn answers (recoverForest index selected words
      (evalWithAnswerFn answers (buildForest index selected words)).1) = forestCommitment answers index :=
  (recoverForest_honest answers index selected words).trans (buildForest_commitment answers index selected words)

def fixedPrepared (answers : Answers) (index : Nat) (lay : Layer) : PreparedLower :=
  ⟨(wotsTree answers lay (route index lay).2).take (height lay),
    prefixRows answers lay (route index lay).2 (route index lay).1⟩

theorem prepareRoots_result (answers : Answers) (index : Nat) :
    evalWithAnswerFn answers (prepareRoots index) =
      ⟨fixedPrepared answers index 1, fixedPrepared answers index 2, fixedPrepared answers index 3⟩ := by
  simp only [prepareRoots, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [eval_buildTreePrefixes_result answers (by decide) _ _ (route_leaf_bound index 1),
    eval_buildTreePrefixes_result answers (by decide) _ _ (route_leaf_bound index 2),
    eval_buildTreePrefixes_result answers (by decide) _ _ (route_leaf_bound index 3)]
  rfl

theorem fixedPrepared_pair (answers : Answers) (index : Nat) (lay : Layer) :
    topPair lay (fixedPrepared answers index lay).levels = builtPair answers lay (route index lay).2 :=
  topPair_take lay _

#print axioms buildForest_commitment
#print axioms recoverForest_commitment
#print axioms prepareRoots_result
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem topPath_fill_signature (sig : Signature) (c : Nat) :
    ((fillTopSignature sig c).layers 0).path topJ = setTop ((sig.layers 0).path topJ) c :=
  topSib_fillTop (mainSignature sig) c

theorem expandFill_verified (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (w : Witness)
    (he : evalWithAnswerFn answers (expandFill message pk sig) = some w) :
    evalWithAnswerFn answers (verify message pk w) = true := by
  unfold expandFill at he
  by_cases hh : sig.policyHints.toNat ≥ 7744
  · simp only [hh, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he
  simp only [hh, if_false, evalWithAnswerFn_bind] at he
  let sig0 := fillTopSignature sig 0
  cases hd : evalWithAnswerFn answers (sharedDigestSearch sig0.rho message 0 digestAttemptLimit) with
  | none =>
      dsimp only [sig0] at hd
      simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      have hdlim : 0 + digestAttemptLimit ≤ 2 ^ 32 := by simpa using digestAttemptLimit_le
      obtain ⟨_, _, haccept, houtput⟩ := sharedDigestSearch_some answers sig0.rho message
        digestAttemptLimit 0 counter output hdlim hd
      have ha := digestAccepted_implies_verify haccept
      dsimp only [sig0] at hd
      simp only [hd, evalWithAnswerFn_bind] at he
      let index := digestIndex output
      let forest := evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
        (forestWordsFromOutput output) sig0.forest)
      cases hr : evalWithAnswerFn answers (recoverHintedLayers sig0 index ((sig0.layers 0).path topJ)
        4 (.pair forest.1 forest.2)) with
      | none =>
          dsimp only [index, forest, sig0] at hr
          simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some result =>
          dsimp only [index, forest, sig0] at hr
          simp only [hr] at he
          cases hp : policyHintsValid sig0.policyHints result.digits result.lows with
          | false =>
              dsimp only [sig0] at hp
              simp only [hp, Bool.not_false, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he
          | true =>
              dsimp only [sig0] at hp
              simp only [hp, Bool.not_true, Bool.false_eq_true, if_false] at he
              by_cases hpk : result.root = pk
              · simp only [hpk, if_true, evalWithAnswerFn_pure, Option.some.injEq] at he
                subst w
                exact verify_from_recovered answers message pk sig0 counter output result houtput ha hr hpk
              · simp only [hpk, if_false, evalWithAnswerFn_bind] at he
                cases hs : evalWithAnswerFn answers
                  (searchTop index result.foldedTop ((sig0.layers 0).path topJ) pk searchFuel 1) with
                | none =>
                    dsimp only [index, sig0] at hs
                    simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
                | some c =>
                    dsimp only [index, sig0] at hs
                    simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
                    subst w
                    have hc := (eval_searchTop answers index result.foldedTop ((sig0.layers 0).path topJ)
                      pk searchFuel 1 c hs).2.2
                    let completed : RecoveredLayers := {result with
                      root := evalWithAnswerFn answers
                        (topNode index result.foldedTop (((fillTopSignature sig0 c).layers 0).path topJ))}
                    have hcompleted : completed.root = pk := by
                      dsimp only [completed]
                      rw [topPath_fill_signature]
                      exact hc
                    have hr' : evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig0 c) index
                        (((fillTopSignature sig0 c).layers 0).path topJ) 4 (.pair forest.1 forest.2)) =
                        some completed := by
                      rw [recoverHintedLayers_fill _ _ _ _ _ le_rfl]
                      rw [eval_recoverHintedLayers_other answers sig0 index ((sig0.layers 0).path topJ)]
                      rw [hr]
                      rfl
                    exact verify_from_recovered answers message pk (fillTopSignature sig0 c)
                      counter output completed houtput ha hr' hcompleted

theorem expand_verified (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (w : Witness)
    (he : evalWithAnswerFn answers (expand message pk sig) = some w) :
    evalWithAnswerFn answers (verify message pk w) = true :=
  expandFill_verified answers message pk (normTop sig) w he

#print axioms expand_verified
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def preparedResidual1 (result : CanonicalLayers) : Nat :=
  CanonicalPolicy.nextResidual (CanonicalPolicy.totalCredit) 0 (result.lows.getD 0 true) (result.digits.getD 0 [])

def preparedResidual2 (result : CanonicalLayers) : Nat :=
  CanonicalPolicy.nextResidual (preparedResidual1 result) 1 (result.lows.getD 1 true) (result.digits.getD 1 [])

def preparedResidual3 (result : CanonicalLayers) : Nat :=
  CanonicalPolicy.nextResidual (preparedResidual2 result) 2 (result.lows.getD 2 true) (result.digits.getD 2 [])

/-- The successful source program exposes exactly the four canonical searches,
with every lower threshold determined by its already selected ancestors. -/
structure PreparedSearchFacts (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) (result : CanonicalLayers) : Prop where
  pieces_length : result.pieces.length = 4
  counters_length : result.counters.length = 4
  digits_length : result.digits.length = 4
  lows_length : result.lows.length = 4
  search0 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 0
    (CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit) (route index 0).2 (route index 0).1
    (.pair (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2) 0 (searchLimit 0)) =
      some (result.counters.getD 0 0, result.digits.getD 0 [], result.lows.getD 0 true)
  search1 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 1
    (CanonicalPolicy.threshold 1 (preparedResidual1 result)) (route index 1).2 (route index 1).1
    (.pair (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2) 0 (searchLimit 1)) =
      some (result.counters.getD 1 0, result.digits.getD 1 [], result.lows.getD 1 true)
  search2 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 2
    (CanonicalPolicy.threshold 2 (preparedResidual2 result)) (route index 2).2 (route index 2).1
    (.pair (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2) 0 (searchLimit 2)) =
      some (result.counters.getD 2 0, result.digits.getD 2 [], result.lows.getD 2 true)
  search3 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 3
    (CanonicalPolicy.threshold 3 (preparedResidual3 result)) (route index 3).2 (route index 3).1
    (.pair (forest).1 (forest).2) 0 (searchLimit 3)) =
      some (result.counters.getD 3 0, result.digits.getD 3 [], result.lows.getD 3 true)
  floor1_lt : CanonicalPolicy.threshold 1 (preparedResidual1 result) < 16
  floor2_lt : CanonicalPolicy.threshold 2 (preparedResidual2 result) < 22
  floor3_lt : CanonicalPolicy.threshold 3 (preparedResidual3 result) < 22
  residual_eq : result.residual = CanonicalPolicy.nextResidual (preparedResidual3 result) 3
    (result.lows.getD 3 true) (result.digits.getD 3 [])
  hints_eq : result.policyHints = BitVec.ofNat 16
    (484 * CanonicalPolicy.threshold 1 (preparedResidual1 result) +
     22 * CanonicalPolicy.threshold 2 (preparedResidual2 result) +
     CanonicalPolicy.threshold 3 (preparedResidual3 result))
  pieces_eq : result.pieces = [
    evalWithAnswerFn answers (signTop cache (route index 0).1 (result.digits.getD 0 [])),
    preparedPieces 1 (route index 1).1 prepared.one (result.digits.getD 1 []),
    preparedPieces 2 (route index 2).1 prepared.two (result.digits.getD 2 []),
    preparedPieces 3 (route index 3).1 prepared.three (result.digits.getD 3 [])]

theorem searchPreparedLayers_some (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (index : Nat)
    (prepared : PreparedRoots) (forest : PairRoot) (result : CanonicalLayers)
    (he : evalWithAnswerFn answers (searchPreparedLayers cache index prepared forest) = some result) :
    PreparedSearchFacts answers cache index prepared forest result := by
  unfold searchPreparedLayers at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs0 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 0
    (CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit) (route index 0).2 (route index 0).1
    (.pair (topPair 1 prepared.one.levels).1 (topPair 1 prepared.one.levels).2) 0 (searchLimit 0)) with
  | none => simp only [hs0, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found0 =>
      obtain ⟨c0, d0, l0⟩ := found0
      simp only [hs0, evalWithAnswerFn_bind] at he
      let r1 := CanonicalPolicy.nextResidual CanonicalPolicy.totalCredit 0 l0 d0
      let f1 := CanonicalPolicy.threshold 1 r1
      by_cases hf1 : f1 ≥ 16
      · dsimp only [r1, f1] at hf1
        simp only [hf1, if_true,
          evalWithAnswerFn_pure, reduceCtorEq] at he
      dsimp only [r1, f1] at hf1
      simp only [hf1, if_false,
        evalWithAnswerFn_bind] at he
      cases hs1 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 1
        f1 (route index 1).2 (route index 1).1
        (.pair (topPair 2 prepared.two.levels).1 (topPair 2 prepared.two.levels).2) 0 (searchLimit 1)) with
      | none =>
          dsimp only [r1, f1] at hs1
          simp only [hs1, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some found1 =>
          obtain ⟨c1, d1, l1⟩ := found1
          dsimp only [r1, f1] at hs1
          simp only [hs1, evalWithAnswerFn_bind] at he
          let r2 := CanonicalPolicy.nextResidual r1 1 l1 d1
          let f2 := CanonicalPolicy.threshold 2 r2
          by_cases hf2 : f2 ≥ 22
          · dsimp only [r1, f1, r2, f2] at hf2
            simp only [hf2, if_true,
              evalWithAnswerFn_pure, reduceCtorEq] at he
          dsimp only [r1, f1, r2, f2] at hf2
          simp only [hf2, if_false,
            evalWithAnswerFn_bind] at he
          cases hs2 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 2
            f2 (route index 2).2 (route index 2).1
            (.pair (topPair 3 prepared.three.levels).1 (topPair 3 prepared.three.levels).2) 0 (searchLimit 2)) with
          | none =>
              dsimp only [r1, f1, r2, f2] at hs2
              simp only [hs2, evalWithAnswerFn_pure, reduceCtorEq] at he
          | some found2 =>
              obtain ⟨c2, d2, l2⟩ := found2
              dsimp only [r1, f1, r2, f2] at hs2
              simp only [hs2, evalWithAnswerFn_bind] at he
              let r3 := CanonicalPolicy.nextResidual r2 2 l2 d2
              let f3 := CanonicalPolicy.threshold 3 r3
              by_cases hf3 : f3 ≥ 22
              · dsimp only [r1, f1, r2, f2, r3, f3] at hf3
                simp only [hf3, if_true,
                  evalWithAnswerFn_pure, reduceCtorEq] at he
              dsimp only [r1, f1, r2, f2, r3, f3] at hf3
              simp only [hf3, if_false,
                evalWithAnswerFn_bind] at he
              cases hs3 : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt 3
                f3 (route index 3).2 (route index 3).1
                (.pair (forest).1 (forest).2) 0 (searchLimit 3)) with
              | none =>
                  dsimp only [r1, f1, r2, f2, r3, f3] at hs3
                  simp only [hs3, evalWithAnswerFn_pure, reduceCtorEq] at he
              | some found3 =>
                  obtain ⟨c3, d3, l3⟩ := found3
                  dsimp only [r1, f1, r2, f2, r3, f3] at hs3
                  simp only [hs3, evalWithAnswerFn_bind] at he
                  simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
                  subst result
                  constructor
                  · rfl
                  · rfl
                  · rfl
                  · rfl
                  · exact hs0
                  · exact hs1
                  · exact hs2
                  · exact hs3
                  · exact Nat.lt_of_not_ge hf1
                  · exact Nat.lt_of_not_ge hf2
                  · exact Nat.lt_of_not_ge hf3
                  · rfl
                  · rfl
                  · rfl

#print axioms searchPreparedLayers_some
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem recoverLayerPair_wotsPieces (answers : Answers) (sig : Signature) (index : Nat)
    (lay : Layer) (hl : lay ≠ 0) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (hpieces : sig.layers lay = piecesSignature lay
      (wotsPieces answers lay (route index lay).2 (route index lay).1 digits)) :
    evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index lay digits) =
      builtPair answers lay (route index lay).2 := by
  apply eval_recoverLayerPair_honest answers (mainSignature sig) index lay hl digits hvalid
  · intro i
    change (sig.layers lay).values i = _
    rw [hpieces]
    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, i.isLt]
  · intro j
    change (sig.layers lay).path j = _
    rw [hpieces]
    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, j.isLt]

theorem topNode_wotsPieces (answers : Answers) (sig : Signature) (index : Nat)
    (hindex : index < 2 ^ 31) (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (hpieces : sig.layers 0 = piecesSignature 0
      (wotsPieces answers 0 (route index 0).2 (route index 0).1 digits)) :
    evalWithAnswerFn answers (topNode index
      (evalWithAnswerFn answers (topFoldN (mainSignature sig) index digits)).1
      ((sig.layers 0).path topJ)) = treeValue (builtTree answers 0 0) 12 0 := by
  have ht : (route index 0).2 = 0 := route_top_tree index hindex
  have hp : sig.layers 0 = piecesSignature 0 (honestPieces answers 0 0 (route index 0).1 digits) := by
    rw [hpieces, ht, wotsPieces_top]
  exact eval_topNode_topFoldN_honest answers (mainSignature sig) index hindex digits hvalid
    (fun i => by
      change (sig.layers 0).values i = _
      rw [hp]
      simp [piecesSignature, honestPieces, List.getD_eq_getElem, i.isLt])
    (fun j => by
      change (sig.layers 0).path j = _
      rw [hp]
      simp [piecesSignature, honestPieces, List.getD_eq_getElem, j.isLt])

theorem recoverHintedLayers_replay (answers : Answers) (sig : Signature) (index : Nat)
    (other : Digest) (forest : PairRoot)
    (counter : Layer → BitVec 32) (digits : Layer → List Nat) (lows : Layer → Bool)
    (hs : ∀ lay, evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay
      (hintFloor sig.policyHints lay) (route index lay).2 (route index lay).1
      (if lay = 3 then .pair forest.1 forest.2 else
        let lower : Layer := Fin.ofNat 4 (lay.val + 1)
        .pair (builtPair answers lower (route index lower).2).1
          (builtPair answers lower (route index lower).2).2)
      0 (searchLimit lay)) = some (counter lay, digits lay, lows lay))
    (hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
      (recoverLayerPair (mainSignature sig) index lay (digits lay)) =
      builtPair answers lay (route index lay).2) :
    evalWithAnswerFn answers (recoverHintedLayers sig index other 4 (.pair forest.1 forest.2)) =
      some ⟨(evalWithAnswerFn answers (topFoldN (mainSignature sig) index (digits 0))).1,
        evalWithAnswerFn answers (topNode index
          (evalWithAnswerFn answers (topFoldN (mainSignature sig) index (digits 0))).1 other),
        [counter 0, counter 1, counter 2, counter 3],
        [digits 0, digits 1, digits 2, digits 3],
        [lows 0, lows 1, lows 2, lows 3],
        (evalWithAnswerFn answers (topFoldN (mainSignature sig) index (digits 0))).2⟩ := by
  have hs0 := hs 0
  have hs1 := hs 1
  have hs2 := hs 2
  have hs3 := hs 3
  have hp1 := hp 1 (by decide)
  have hp2 := hp 2 (by decide)
  have hp3 := hp 3 (by decide)
  simp only [show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
    show (2 : Layer) ≠ 3 by decide, if_false, if_true,
    show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
    show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
    show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl] at hs0 hs1 hs2 hs3
  simp only [recoverHintedLayers, evalWithAnswerFn_bind,
    show (Fin.ofNat 4 0 : Layer) = 0 from rfl,
    show (Fin.ofNat 4 1 : Layer) = 1 from rfl,
    show (Fin.ofNat 4 2 : Layer) = 2 from rfl,
    show (Fin.ofNat 4 3 : Layer) = 3 from rfl,
    hs0, hs1, hs2, hs3, hp1, hp2, hp3,
    Nat.reduceEqDiff, if_false, if_true, evalWithAnswerFn_pure]
  rfl

#print axioms recoverLayerPair_wotsPieces
#print axioms topNode_wotsPieces
#print axioms recoverHintedLayers_replay
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem layer_four_cases (lay : Layer) : lay = 0 ∨ lay = 1 ∨ lay = 2 ∨ lay = 3 := by
  fin_cases lay <;> decide

@[simp] theorem layer_val_0 : (0 : Layer).val = 0 := rfl
@[simp] theorem layer_val_1 : (1 : Layer).val = 1 := rfl
@[simp] theorem layer_val_2 : (2 : Layer).val = 2 := rfl
@[simp] theorem layer_val_3 : (3 : Layer).val = 3 := rfl

theorem PreparedSearchFacts.validDigits {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result) (lay : Layer) :
    Cost.ValidDigits lay (result.digits.getD lay.val []) := by
  rcases layer_four_cases lay with rfl | rfl | rfl | rfl
  · exact (canonical_search_valid_credit answers 0 _ _ _ _ _ _ _ _ _
      (by have hb := searchLimit_le (0 : Layer); unfold counterLimit at hb; omega) h.search0).1
  · exact (canonical_search_valid_credit answers 1 _ _ _ _ _ _ _ _ _
      (by have hb := searchLimit_le (1 : Layer); unfold counterLimit at hb; omega) h.search1).1
  · exact (canonical_search_valid_credit answers 2 _ _ _ _ _ _ _ _ _
      (by have hb := searchLimit_le (2 : Layer); unfold counterLimit at hb; omega) h.search2).1
  · exact (canonical_search_valid_credit answers 3 _ _ _ _ _ _ _ _ _
      (by have hb := searchLimit_le (3 : Layer); unfold counterLimit at hb; omega) h.search3).1

theorem PreparedSearchFacts.hints_spec {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result) :
    result.policyHints.toNat < 7744 ∧
      hintFloor result.policyHints 1 = CanonicalPolicy.threshold 1 (preparedResidual1 result) ∧
      hintFloor result.policyHints 2 = CanonicalPolicy.threshold 2 (preparedResidual2 result) ∧
      hintFloor result.policyHints 3 = CanonicalPolicy.threshold 3 (preparedResidual3 result) := by
  rw [h.hints_eq]
  exact encodedHints_spec _ _ _ h.floor1_lt h.floor2_lt h.floor3_lt

theorem PreparedSearchFacts.hints_valid {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result) :
    policyHintsValid result.policyHints result.digits result.lows = true := by
  simp only [policyHintsValid, decide_eq_true_eq]
  exact ⟨h.hints_spec.1, h.digits_length, h.hints_spec.2⟩

theorem preparedPieces_fixed (answers : Answers) (index : Nat) {lay : Layer}
    (hlay : lay ≠ 0) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits) :
    preparedPieces lay (route index lay).1 (fixedPrepared answers index lay) digits =
      wotsPieces answers lay (route index lay).2 (route index lay).1 digits := by
  have h := preparedPieces_result answers hlay (route index lay).2 (route index lay).1
    digits hvalid (route_leaf_bound index lay)
  rw [eval_buildTreePrefixes_result answers hlay _ _ (route_leaf_bound index lay)] at h
  exact h

theorem PreparedSearchFacts.honest_pieces {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index (evalWithAnswerFn answers (prepareRoots index)) forest result)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (hindex : index < 2 ^ 31)
    (lay : Layer) :
    result.pieces.getD lay.val ([], []) =
      wotsPieces answers lay (route index lay).2 (route index lay).1 (result.digits.getD lay.val []) := by
  have hv := h.validDigits lay
  rw [h.pieces_eq, prepareRoots_result]
  rcases layer_four_cases lay with rfl | rfl | rfl | rfl <;>
    simp only [layer_val_0, layer_val_1, layer_val_2, layer_val_3] at hv ⊢
  · simp only [Fin.val_zero, List.getD_cons_zero]
    rw [eval_signTop_honest answers cache _ _ hcache (route_leaf_bound index 0) hv,
      route_top_tree index hindex, wotsPieces_top]
  · simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      preparedPieces_fixed answers index (lay := 1) (by decide) _ hv
  · simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      preparedPieces_fixed answers index (lay := 2) (by decide) _ hv
  · simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      preparedPieces_fixed answers index (lay := 3) (by decide) _ hv

theorem list_four_getD {α : Type} (xs : List α) (zero : α) (hlen : xs.length = 4) :
    [xs.getD 0 zero, xs.getD 1 zero, xs.getD 2 zero, xs.getD 3 zero] = xs := by
  apply List.ext_getElem (by simpa using hlen.symm)
  intro i hi hj
  have hi4 : i < 4 := by simpa using hi
  interval_cases i <;> simp_all [List.getD_eq_getElem]

#print axioms PreparedSearchFacts.validDigits
#print axioms PreparedSearchFacts.hints_valid
#print axioms PreparedSearchFacts.honest_pieces
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem PreparedSearchFacts.recover_honest {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index (evalWithAnswerFn answers (prepareRoots index)) forest result)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (hindex : index < 2 ^ 31)
    (sig : Signature) (hhints : sig.policyHints = result.policyHints)
    (hpieces : ∀ lay, sig.layers lay = piecesSignature lay (result.pieces.getD lay.val ([], []))) :
    ∃ folded nonces, evalWithAnswerFn answers (recoverHintedLayers sig index ((sig.layers 0).path topJ)
      4 (.pair forest.1 forest.2)) = some ⟨folded,
        treeValue (builtTree answers 0 0) 12 0, result.counters, result.digits, result.lows, nonces⟩ := by
  have hpiece : ∀ lay, sig.layers lay = piecesSignature lay
      (wotsPieces answers lay (route index lay).2 (route index lay).1 (result.digits.getD lay.val [])) := by
    intro lay
    rw [hpieces lay, h.honest_pieces hcache hindex lay]
  have hs0 := h.search0
  have hs1 := h.search1
  have hs2 := h.search2
  have hs3 := h.search3
  simp only [prepareRoots_result, fixedPrepared_pair] at hs0 hs1 hs2
  have hs : ∀ lay, evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay
      (hintFloor sig.policyHints lay) (route index lay).2 (route index lay).1
      (if lay = 3 then .pair forest.1 forest.2 else
        let lower : Layer := Fin.ofNat 4 (lay.val + 1)
        .pair (builtPair answers lower (route index lower).2).1
          (builtPair answers lower (route index lower).2).2)
      0 (searchLimit lay)) = some (result.counters.getD lay.val 0, result.digits.getD lay.val [],
        result.lows.getD lay.val true) := by
    intro lay
    rw [hhints]
    rcases layer_four_cases lay with rfl | rfl | rfl | rfl <;>
      simp only [layer_val_0, layer_val_1, layer_val_2, layer_val_3,
        show (Fin.ofNat 4 1 : Layer) = 1 from rfl,
        show (Fin.ofNat 4 2 : Layer) = 2 from rfl,
        show (Fin.ofNat 4 3 : Layer) = 3 from rfl, Nat.reduceAdd, show (0 : Layer) ≠ 3 by decide,
        show (1 : Layer) ≠ 3 by decide, show (2 : Layer) ≠ 3 by decide, if_false, if_true]
    · exact hs0
    · simpa only [h.hints_spec.2.1] using hs1
    · simpa only [h.hints_spec.2.2.1] using hs2
    · simpa only [h.hints_spec.2.2.2] using hs3
  have hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
      (recoverLayerPair (mainSignature sig) index lay (result.digits.getD lay.val [])) =
      builtPair answers lay (route index lay).2 := by
    intro lay hl
    exact recoverLayerPair_wotsPieces answers sig index lay hl _ (h.validDigits lay) (hpiece lay)
  have hr := recoverHintedLayers_replay answers sig index ((sig.layers 0).path topJ) forest
    (fun lay => result.counters.getD lay.val 0) (fun lay => result.digits.getD lay.val [])
    (fun lay => result.lows.getD lay.val true) hs hp
  simp only [layer_val_0, layer_val_1, layer_val_2, layer_val_3] at hr
  have ht := topNode_wotsPieces answers sig index hindex _ (h.validDigits 0) (hpiece 0)
  simp only [layer_val_0] at ht
  rw [ht,
    list_four_getD result.counters 0 h.counters_length,
    list_four_getD result.digits [] h.digits_length,
    list_four_getD result.lows true h.lows_length] at hr
  exact ⟨_, _, hr⟩

#print axioms PreparedSearchFacts.recover_honest
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem expand_complete_of_recovered (answers : Answers) (message : Message) (pk : Digest)
    (sig : Signature) (counter : BitVec 32) (output : HashOutput) (result : RecoveredLayers)
    (hd : evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 digestAttemptLimit) =
      some (counter, output))
    (hr : evalWithAnswerFn answers (recoverHintedLayers sig (digestIndex output)
      ((sig.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
        (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)) = some result)
    (hh : policyHintsValid sig.policyHints result.digits result.lows = true) (hpk : result.root = pk)
    (htop : TopPathOK sig) :
    ∃ w, evalWithAnswerFn answers (expand message pk sig) = some w := by
  have hhbound' : sig.policyHints.toNat < 2 ^ 13 := by
    simp only [policyHintsValid, decide_eq_true_eq] at hh
    have := hh.1
    omega
  rw [expand_eq_expandFill message pk sig hhbound' htop]
  have hhbound : sig.policyHints.toNat < 7744 := by
    simp only [policyHintsValid, decide_eq_true_eq] at hh
    exact hh.1
  let index := digestIndex output
  let forest := evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output) sig.forest)
  let sig0 := fillTopSignature sig 0
  let result0 : RecoveredLayers := {result with
    root := evalWithAnswerFn answers (topNode index result.foldedTop ((sig0.layers 0).path topJ))}
  have hr0 : evalWithAnswerFn answers (recoverHintedLayers sig0 index
      ((sig0.layers 0).path topJ) 4 (.pair forest.1 forest.2)) = some result0 := by
    dsimp only [sig0]
    rw [recoverHintedLayers_fill _ _ _ _ _ le_rfl,
      eval_recoverHintedLayers_other answers sig index ((sig.layers 0).path topJ)]
    rw [hr]
    rfl
  have hroot : evalWithAnswerFn answers (topNode index result.foldedTop ((sig.layers 0).path topJ)) = pk := by
    have he := eval_recoverHintedLayers_other answers sig index ((sig.layers 0).path topJ)
      ((sig.layers 0).path topJ) 4 (.pair forest.1 forest.2)
    rw [hr] at he
    simp only [Option.map_some, Option.some.injEq] at he
    have he' := congrArg RecoveredLayers.root he
    exact he'.symm.trans hpk
  unfold expandFill
  simp only [show ¬sig.policyHints.toNat ≥ 7744 by omega, if_false, evalWithAnswerFn_bind]
  simp only [nonce_retained, hd, evalWithAnswerFn_bind]
  dsimp only [sig0, index, forest] at hr0
  simp only [show (fillTopSignature sig 0).forest = sig.forest from rfl]
  rw [hr0]
  simp only [result0, sig0, hints_retained, hh, Bool.not_true, Bool.false_eq_true, if_false]
  by_cases hzero : result0.root = pk
  · dsimp only [result0, sig0] at hzero
    rw [if_pos hzero, evalWithAnswerFn_pure]
    exact ⟨_, rfl⟩
  · have hz : evalWithAnswerFn answers (topNode index result.foldedTop ((sig0.layers 0).path topJ)) ≠ pk := hzero
    have hcompletion : evalWithAnswerFn answers (topNode index result.foldedTop
        (setTop ((sig0.layers 0).path topJ) (((sig.layers 0).path topJ).toNat / 2 ^ 109))) = pk := by
      rw [topPath_fill_signature, setTop_setTop, setTop_self]
      exact hroot
    have hn : ((sig.layers 0).path topJ).toNat / 2 ^ 109 ≠ 0 := by
      intro he
      rw [he, topPath_fill_signature, setTop_setTop] at hcompletion
      exact hz hcompletion
    obtain ⟨c, hc⟩ := searchTop_complete answers index result.foldedTop ((sig0.layers 0).path topJ)
      pk searchFuel 1 (((sig.layers 0).path topJ).toNat / 2 ^ 109) (by omega)
      (by have ht := top_lt ((sig.layers 0).path topJ); unfold searchFuel; omega) hcompletion
    dsimp only [sig0] at hz
    dsimp only [sig0, index] at hc
    rw [if_neg hz, evalWithAnswerFn_bind, hc, evalWithAnswerFn_pure]
    exact ⟨_, rfl⟩

#print axioms expand_complete_of_recovered
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signFromOutput_recovery (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    w.signature.rho = rho ∧ ∃ result : RecoveredLayers,
      evalWithAnswerFn answers (recoverHintedLayers w.signature (digestIndex output)
        ((w.signature.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1
          (evalWithAnswerFn answers (recoverForest (digestIndex output)
            (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2)) = some result ∧
      result.root = treeValue (builtTree answers 0 0) 12 0 ∧
      policyHintsValid w.signature.policyHints result.digits result.lows = true ∧
      w.topHigh = !(result.lows.getD 0 true) := by
  let index := digestIndex output
  let built := evalWithAnswerFn answers (buildForest index
    (forestSelectionFromOutput output) (forestWordsFromOutput output))
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
      obtain ⟨folded, nonces, hr⟩ := hf.recover_honest hcache (digestIndex_lt output) sig rfl (by intro lay; rfl)
      refine ⟨rfl, ⟨folded, _, layers.counters, layers.digits, layers.lows, nonces⟩, ?_, rfl, hf.hints_valid, rfl⟩
      change evalWithAnswerFn answers (recoverHintedLayers sig index ((sig.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
          (forestWordsFromOutput output) built.1)).1
          (evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
            (forestWordsFromOutput output) built.1)).2)) = _
      have hforest : evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
          (forestWordsFromOutput output) built.1) = built.2 :=
        recoverForest_honest answers index _ _
      rw [hforest]
      exact hr

/-- img-v6 completeness event: every node of the keygen top tree (heights 1..11) passes its zero test, i.e. no
top nonce search hit its cap (probability ≥ 1 − 2^−143). -/
def TopTreeOK (answers : Answers) : Prop :=
  ∀ j : Nat, 1 ≤ j → j ≤ 11 → ∀ i, i < 2 ^ (12 - j) →
    topZeroOk j (treeValue (builtTree answers 0 0) j i) = true

theorem route0_tree (index : Nat) (h : index < 2 ^ 31) : (route index 0).2 = 0 := by
  simp only [route]
  apply Nat.div_eq_of_lt
  simpa [height] using h

theorem route0_leaf_lt (index : Nat) : (route index 0).1 < 2 ^ 12 := by
  simp only [route]
  exact Nat.mod_lt _ (by simp [height])

theorem sibling_lt (leaf j : Nat) (hleaf : leaf < 2 ^ 12) (hj : j ≤ 11) : leaf / 2 ^ j ^^^ 1 < 2 ^ (12 - j) := by
  apply Nat.xor_lt_two_pow
  · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show 12 - j + j = 12 by omega]
    exact hleaf
  · exact Nat.one_lt_two_pow (by omega)

/-- The signer's top path node at height `j` is the keygen's node next to the signed leaf's ancestor. -/
theorem signFromOutput_path (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) (j : Fin (height 0)) :
    (w.signature.layers 0).path j =
      treeValue (builtTree answers 0 0) j.val ((route (digestIndex output) 0).1 / 2 ^ j.val ^^^ 1) := by
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
    change (piecesSignature 0 (layers.pieces.getD (0 : Layer).val ([], []))).path j = _
    have hj : j.val < 12 := j.isLt
    rw [hp, route0_tree _ (digestIndex_lt output)]
    simp [piecesSignature, wotsPieces, wotsTree_top, height, index, hj]

theorem signFromOutput_topPathOK (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (htree : TopTreeOK answers) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    TopPathOK w.signature := by
  intro j hj
  have hj11 : j.val ≤ 11 := Nat.le_of_lt_succ j.isLt
  rw [signFromOutput_path answers cache hcache rho counter output w he j]
  exact htree j.val hj hj11 _ (sibling_lt _ _ (route0_leaf_lt _) hj11)

theorem signPayload_expands (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (htree : TopTreeOK answers)
    (message : Message) (sig : Signature)
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) :
    ∃ w, evalWithAnswerFn answers (expand message (treeValue (builtTree answers 0 0) 12 0) sig) = some w ∧
      evalWithAnswerFn answers (verify message (treeValue (builtTree answers 0 0) 12 0) w) = true := by
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
          have hh := signFromOutput_recovery answers cache hcache rho counter output original hs
          have htop := signFromOutput_topPathOK answers cache hcache htree rho counter output original hs
          dsimp only [rho] at hs
          simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
          subst sig
          obtain ⟨hrho, result, hr, hpk, hp, _⟩ := hh
          have hd' : evalWithAnswerFn answers
              (sharedDigestSearch original.signature.rho message 0 digestAttemptLimit) = some (counter, output) := by
            rw [hrho]
            exact hd
          obtain ⟨w, hw⟩ := expand_complete_of_recovered answers message _ original.signature
            counter output result hd' hr hp hpk htop
          exact ⟨w, hw, expand_verified answers message _ original.signature w hw⟩

theorem sign_expands (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (htree : TopTreeOK answers)
    (message : Message) (sig : Signature)
    (he : evalWithAnswerFn answers (sign cache message) = some sig) :
    ∃ w, evalWithAnswerFn answers (expand message (treeValue (builtTree answers 0 0) 12 0) sig) = some w ∧
      evalWithAnswerFn answers (verify message (treeValue (builtTree answers 0 0) 12 0) w) = true := by
  unfold sign at he
  simp only [evalWithAnswerFn_bind] at he
  split_ifs at he with htag
  · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
  · exact signPayload_expands answers cache hcache htree message sig he

#print axioms signFromOutput_recovery
#print axioms signPayload_expands
#print axioms sign_expands
end SigGolfCandidate.Research.SharedForest
