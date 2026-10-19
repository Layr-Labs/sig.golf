import SigGolfCandidate.Research_V7Composed198Gate_D

set_option autoImplicit false
set_option Elab.async false


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def recoverySearch (answers : Answers) (sig : Signature) (index : Nat) (forest : PairRoot) (lay : Layer) :
    M (Option (BitVec 32 × List Nat × Bool)) :=
  CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
    (route index lay).2 (route index lay).1
    (if lay = 3 then .pair forest.1 forest.2 else
      let lower : Layer := Fin.ofNat 4 (lay.val + 1)
      .pair (builtPair answers lower (route index lower).2).1
        (builtPair answers lower (route index lower).2).2) 0 (searchLimit lay)

def recoverySearchCost (answers : Answers) (sig : Signature) (index : Nat) (forest : PairRoot) : Nat :=
  cost answers (recoverySearch answers sig index forest 0) +
  cost answers (recoverySearch answers sig index forest 1) +
  cost answers (recoverySearch answers sig index forest 2) +
  cost answers (recoverySearch answers sig index forest 3)

theorem recoverHintedLayers_cost_replay (answers : Answers) (sig : Signature) (index : Nat)
    (other : Digest) (forest : PairRoot) (counter : Layer → BitVec 32) (digits : Layer → List Nat)
    (lows : Layer → Bool)
    (hs : ∀ lay, evalWithAnswerFn answers (recoverySearch answers sig index forest lay) =
      some (counter lay, digits lay, lows lay))
    (hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
      (recoverLayerPair (mainSignature sig) index lay (digits lay)) =
      builtPair answers lay (route index lay).2) :
    cost answers (recoverHintedLayers sig index other 4 (.pair forest.1 forest.2)) ≤
      recoverySearchCost answers sig index forest + (1616 + 425765) := by
  have hs0 := hs 0
  have hs1 := hs 1
  have hs2 := hs 2
  have hs3 := hs 3
  have hp1 := hp 1 (by decide)
  have hp2 := hp 2 (by decide)
  have hp3 := hp 3 (by decide)
  have hc1 := cost_bound answers (bound_recoverLayerPair_coarse (mainSignature sig) index 1 (digits 1))
  have hc2 := cost_bound answers (bound_recoverLayerPair_coarse (mainSignature sig) index 2 (digits 2))
  have hc3 := cost_bound answers (bound_recoverLayerPair_coarse (mainSignature sig) index 3 (digits 3))
  have hct := cost_bound answers (bound_topFoldN_coarse (mainSignature sig) index (digits 0))
  have hcn := cost_bound answers (ClaudeWCT.WCT9.Cost.bound_topNode index
    (evalWithAnswerFn answers (topFoldN (mainSignature sig) index (digits 0))).1 other)
  simp only [recoverySearch, show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
    show (2 : Layer) ≠ 3 by decide, if_false, if_true,
    show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
    show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
    show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl] at hs0 hs1 hs2 hs3 ⊢
  simp only [recoverySearchCost, recoverySearch,
    show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
    show (2 : Layer) ≠ 3 by decide, if_false, if_true,
    show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
    show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
    show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl]
  simp only [recoverHintedLayers, cost_bind, evalWithAnswerFn_bind,
    show (Fin.ofNat 4 0 : Layer) = 0 from rfl,
    show (Fin.ofNat 4 1 : Layer) = 1 from rfl,
    show (Fin.ofNat 4 2 : Layer) = 2 from rfl,
    show (Fin.ofNat 4 3 : Layer) = 3 from rfl,
    hs0, hs1, hs2, hs3, hp1, hp2, hp3,
    Nat.reduceEqDiff, if_false, if_true, evalWithAnswerFn_pure, cost_pure]
  simp only [topFoldNCost] at hct
  omega

#print axioms recoverHintedLayers_cost_replay
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem PreparedSearchFacts.cost_eq {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result)
    (sig : Signature) (hh : sig.policyHints = result.policyHints)
    (hm0 : topPair 1 prepared.one.levels = builtPair answers 1 (route index 1).2)
    (hm1 : topPair 2 prepared.two.levels = builtPair answers 2 (route index 2).2)
    (hm2 : topPair 3 prepared.three.levels = builtPair answers 3 (route index 3).2) :
    cost answers (searchPreparedLayers cache index prepared forest) =
      recoverySearchCost answers sig index forest +
        cost answers (signTop cache (route index 0).1 (result.digits.getD 0 [])) := by
  have hs0 := h.search0
  have hs1 := h.search1
  have hs2 := h.search2
  have hs3 := h.search3
  have hf1 := Nat.not_le.mpr h.floor1_lt
  have hf2 := Nat.not_le.mpr h.floor2_lt
  have hf3 := Nat.not_le.mpr h.floor3_lt
  dsimp only [preparedResidual1, preparedResidual2, preparedResidual3] at hs1 hs2 hs3 hf1 hf2 hf3
  simp only [searchPreparedLayers, cost_bind, hs0, hs1, hs2, hs3,
    hf1, hf2, hf3, if_false, cost_pure, Nat.add_zero]
  simp only [recoverySearchCost, recoverySearch, hh, h.hints_spec.2.1,
    h.hints_spec.2.2.1, h.hints_spec.2.2.2, hm0, hm1, hm2,
    show hintFloor result.policyHints 0 = CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit from rfl,
    show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
    show (2 : Layer) ≠ 3 by decide, if_false, if_true,
    show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
    show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
    show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl,
    preparedResidual1, preparedResidual2, preparedResidual3]
  omega

#print axioms PreparedSearchFacts.cost_eq
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp SigGolfCandidate.T3 ClaudeWCT.WCT9

theorem expand_fillTopSignature (message : Message) (pk : Digest) (sig : Signature) (c : Nat) :
    expand message pk (fillTopSignature sig c) = expand message pk sig := by
  rw [← expand_normTop message pk (fillTopSignature sig c), normTop_fill, expand_normTop]

#print axioms expand_fillTopSignature
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem PreparedSearchFacts.recovery_cost_le {answers : Answers} {cache : SigGolfCandidate.T3.Cache} {index : Nat}
    {prepared : PreparedRoots} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index prepared forest result)
    (sig : Signature) (other : Digest) (hh : sig.policyHints = result.policyHints)
    (hm0 : topPair 1 prepared.one.levels = builtPair answers 1 (route index 1).2)
    (hm1 : topPair 2 prepared.two.levels = builtPair answers 2 (route index 2).2)
    (hm2 : topPair 3 prepared.three.levels = builtPair answers 3 (route index 3).2)
    (hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
      (recoverLayerPair (mainSignature sig) index lay (result.digits.getD lay.val [])) =
      builtPair answers lay (route index lay).2) :
    cost answers (recoverHintedLayers sig index other 4 (.pair forest.1 forest.2)) ≤
      cost answers (searchPreparedLayers cache index prepared forest) + (1616 + 425765) := by
  have hs0 := h.search0
  have hs1 := h.search1
  have hs2 := h.search2
  have hs3 := h.search3
  rw [hm0] at hs0
  rw [hm1] at hs1
  rw [hm2] at hs2
  have hs : ∀ lay, evalWithAnswerFn answers (recoverySearch answers sig index forest lay) =
      some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true) := by
    intro lay
    rcases layer_four_cases lay with rfl | rfl | rfl | rfl <;>
      simp only [recoverySearch, hh, h.hints_spec.2.1, h.hints_spec.2.2.1, h.hints_spec.2.2.2,
        show hintFloor result.policyHints 0 = CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit from rfl,
        show (0 : Layer) ≠ 3 by decide, show (1 : Layer) ≠ 3 by decide,
        show (2 : Layer) ≠ 3 by decide, if_false, if_true,
        show (Fin.ofNat 4 ((0 : Layer).val + 1) : Layer) = 1 from rfl,
        show (Fin.ofNat 4 ((1 : Layer).val + 1) : Layer) = 2 from rfl,
        show (Fin.ofNat 4 ((2 : Layer).val + 1) : Layer) = 3 from rfl]
    · exact hs0
    · exact hs1
    · exact hs2
    · exact hs3
  have hc := recoverHintedLayers_cost_replay answers sig index other forest
    (fun lay => result.counters.getD lay.val 0) (fun lay => result.digits.getD lay.val [])
    (fun lay => result.lows.getD lay.val true) hs hp
  have he := h.cost_eq sig hh hm0 hm1 hm2
  omega

#print axioms PreparedSearchFacts.recovery_cost_le
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem policyHintsValid_congr_lows (hints : BitVec 16) (digits : List (List Nat)) {lowsA lowsB : List Bool}
    (h0 : lowsA.getD 0 true = lowsB.getD 0 true) (h1 : lowsA.getD 1 true = lowsB.getD 1 true)
    (h2 : lowsA.getD 2 true = lowsB.getD 2 true) :
    policyHintsValid hints digits lowsA = policyHintsValid hints digits lowsB := by
  simp only [policyHintsValid, h0, h1, h2]

theorem hintedSelections_unique (answers : Answers) (index : Nat) (messages : Layer → LayerMsg)
    (hintsA hintsB : BitVec 16) (countersA countersB : Layer → BitVec 32)
    (digitsA digitsB : List (List Nat)) (lowsA lowsB : List Bool)
    (hvalidA : policyHintsValid hintsA digitsA lowsA = true)
    (hvalidB : policyHintsValid hintsB digitsB lowsB = true)
    (hsearchA : ∀ lay, evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay (hintFloor hintsA lay) (route index lay).2
        (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (countersA lay, digitsA.getD lay.val [], lowsA.getD lay.val true))
    (hsearchB : ∀ lay, evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay (hintFloor hintsB lay) (route index lay).2
        (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (countersB lay, digitsB.getD lay.val [], lowsB.getD lay.val true)) :
    hintsA = hintsB ∧ countersA = countersB ∧ digitsA = digitsB ∧
      ∀ lay : Layer, lowsA.getD lay.val true = lowsB.getD lay.val true := by
  have hA := hvalidA
  have hB := hvalidB
  simp only [policyHintsValid, decide_eq_true_eq] at hA hB
  have same (lay : Layer) (hf : hintFloor hintsA lay = hintFloor hintsB lay) :
      (countersA lay, digitsA.getD lay.val [], lowsA.getD lay.val true) =
        (countersB lay, digitsB.getD lay.val [], lowsB.getD lay.val true) := by
    have ha := hsearchA lay
    rw [hf] at ha
    exact Option.some.inj (ha.symm.trans (hsearchB lay))
  have h0 := same 0 (by rfl)
  have hd0 : digitsA.getD 0 [] = digitsB.getD 0 [] := congrArg (fun x => x.2.1) h0
  have hl0 : lowsA.getD 0 true = lowsB.getD 0 true := congrArg (fun x => x.2.2) h0
  have h1 := same 1 (by rw [hA.2.2.1, hB.2.2.1, hd0, hl0])
  have hd1 : digitsA.getD 1 [] = digitsB.getD 1 [] := congrArg (fun x => x.2.1) h1
  have hl1 : lowsA.getD 1 true = lowsB.getD 1 true := congrArg (fun x => x.2.2) h1
  have h2 := same 2 (by rw [hA.2.2.2.1, hB.2.2.2.1, hd0, hd1, hl0, hl1])
  have hd2 : digitsA.getD 2 [] = digitsB.getD 2 [] := congrArg (fun x => x.2.1) h2
  have hl2 : lowsA.getD 2 true = lowsB.getD 2 true := congrArg (fun x => x.2.2) h2
  have h3 := same 3 (by rw [hA.2.2.2.2, hB.2.2.2.2, hd0, hd1, hd2, hl0, hl1, hl2])
  have hd3 : digitsA.getD 3 [] = digitsB.getD 3 [] := congrArg (fun x => x.2.1) h3
  have hl3 : lowsA.getD 3 true = lowsB.getD 3 true := congrArg (fun x => x.2.2) h3
  have hd : digitsA = digitsB := by
    apply List.ext_getElem (hA.2.1.trans hB.2.1.symm)
    intro i hi hj
    have hi4 : i < 4 := by omega
    have he : digitsA.getD i [] = digitsB.getD i [] := by
      interval_cases i <;> assumption
    simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using he
  have hvB : policyHintsValid hintsB digitsA lowsA = true := by
    rw [policyHintsValid_congr_lows hintsB digitsA hl0 hl1 hl2, hd]; exact hvalidB
  refine ⟨policyHintsValid_unique hvalidA hvB, ?_, hd, ?_⟩
  · funext lay
    fin_cases lay
    · exact congrArg Prod.fst h0
    · exact congrArg Prod.fst h1
    · exact congrArg Prod.fst h2
    · exact congrArg Prod.fst h3
  · intro lay
    fin_cases lay
    · exact hl0
    · exact hl1
    · exact hl2
    · exact hl3
#print axioms hintedSelections_unique
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def recoveredMessage (answers : Answers) (sig : Signature) (index n : Nat)
    (message : LayerMsg) (digits : List (List Nat)) (lay : Layer) : LayerMsg :=
  if lay.val + 1 = n then message else
    let next : Layer := Fin.ofNat 4 (lay.val + 1)
    let pair := evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index next
      (digits.getD (lay.val + 1) []))
    .pair pair.1 pair.2

theorem recoverHintedLayers_selections (answers : Answers) (sig : Signature) (index : Nat)
    (other : Digest) : ∀ n, n ≤ 4 → ∀ message result,
    evalWithAnswerFn answers (recoverHintedLayers sig index other n message) = some result →
    result.counters.length = n ∧ result.digits.length = n ∧ result.lows.length = n ∧
      ∀ lay : Layer, lay.val < n → evalWithAnswerFn answers
        (CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
          (route index lay).2 (route index lay).1
          (recoveredMessage answers sig index n message result.digits lay) 0 (searchLimit lay)) =
            some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true) := by
  intro n
  induction n with
  | zero => intro _ message result he; simp [recoverHintedLayers] at he
  | succ n ih =>
      intro hn message result he
      have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
      simp only [recoverHintedLayers, evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt (Fin.ofNat 4 n)
        (hintFloor sig.policyHints (Fin.ofNat 4 n)) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 message 0 (searchLimit (Fin.ofNat 4 n))) with
      | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some found =>
          obtain ⟨counter, digits, low⟩ := found
          simp only [hs] at he
          by_cases hn0 : n = 0
          · subst n
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at he
            subst result
            refine ⟨rfl, rfl, rfl, ?_⟩
            intro lay hlay
            have hl : lay = 0 := Fin.ext (by omega)
            subst lay
            simp only [show (Fin.ofNat 4 0 : Layer) = 0 from rfl] at hs
            simpa only [recoveredMessage, Fin.val_zero, Nat.zero_add, if_true, List.getD_cons_zero] using hs
          · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
            let pair := evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index
              (Fin.ofNat 4 n) digits)
            cases hr : evalWithAnswerFn answers (recoverHintedLayers sig index other n
              (.pair pair.1 pair.2)) with
            | none =>
                dsimp only [pair] at hr
                simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at he
            | some previous =>
                dsimp only [pair] at hr
                simp only [hr, evalWithAnswerFn_pure, Option.some.injEq] at he
                subst result
                obtain ⟨hcl, hdl, hll, hsel⟩ := ih (by omega) _ _ hr
                refine ⟨by simp [hcl], by simp [hdl], by simp [hll], ?_⟩
                intro lay hlay
                by_cases hlt : lay.val < n
                · have hcounter : (previous.counters ++ [counter]).getD lay.val 0 =
                      previous.counters.getD lay.val 0 := List.getD_append _ _ _ _ (by omega)
                  have hdigit : (previous.digits ++ [digits]).getD lay.val [] =
                      previous.digits.getD lay.val [] := List.getD_append _ _ _ _ (by omega)
                  have hlow : (previous.lows ++ [low]).getD lay.val true =
                      previous.lows.getD lay.val true := List.getD_append _ _ _ _ (by omega)
                  rw [hcounter, hdigit, hlow]
                  have hm : recoveredMessage answers sig index (n + 1) message
                        (previous.digits ++ [digits]) lay =
                      recoveredMessage answers sig index n (.pair pair.1 pair.2) previous.digits lay := by
                    unfold recoveredMessage
                    rw [if_neg (by omega)]
                    by_cases hnxt : lay.val + 1 = n
                    · rw [if_pos hnxt, hnxt, List.getD_append_right _ _ _ _ (by omega), hdl]
                      simp only [Nat.sub_self, List.getD_cons_zero]
                      rfl
                    · rw [if_neg hnxt, List.getD_append _ _ _ _ (by omega)]
                  rw [hm]
                  exact hsel lay hlt
                · have hl : lay = Fin.ofNat 4 n := Fin.ext (by rw [hv]; omega)
                  subst lay
                  simp only [recoveredMessage, hv, if_true]
                  rw [List.getD_append_right _ _ _ _ (by omega), hcl,
                    List.getD_append_right _ _ _ _ (by omega), hdl,
                    List.getD_append_right _ _ _ _ (by omega), hll]
                  simpa only [Nat.sub_self, List.getD_cons_zero] using hs
#print axioms recoverHintedLayers_selections
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
theorem fillTopSignature_fillTopSignature (sig : Signature) (a b : Nat) :
    fillTopSignature (fillTopSignature sig a) b = fillTopSignature sig b := by
  unfold fillTopSignature
  simp only [Signature.mk.injEq, true_and]
  funext lay
  exact fillLayer_fillLayer lay (sig.layers lay) a b
end SigGolfCandidate.Research.SharedForest


namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem recoveredMessage_fill (answers : Answers) (sig : Signature) (index n : Nat)
    (hn : n ≤ 4) (message : LayerMsg) (digits : List (List Nat)) (lay : Layer)
    (hlay : lay.val < n) (c : Nat) :
    recoveredMessage answers (fillTopSignature sig c) index n message digits lay =
      recoveredMessage answers sig index n message digits lay := by
  unfold recoveredMessage
  split_ifs with htop
  · rfl
  · have hnext : (Fin.ofNat 4 (lay.val + 1) : Layer).val ≠ 0 := by
      rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hmain : mainSignature (fillTopSignature sig c) = fillTop (mainSignature sig) c := rfl
    dsimp only
    rw [hmain, recoverLayerPair_fill _ _ _ _ c hnext]

theorem recoveredPair_of_pieces (answers : Answers) (sig : Signature) (index : Nat)
    (lay : Layer) (hl : lay ≠ 0) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (hlayer : sig.layers lay = piecesSignature lay
      (wotsPieces answers lay (route index lay).2 (route index lay).1 digits)) :
    evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index lay digits) =
      builtPair answers lay (route index lay).2 := by
  apply eval_recoverLayerPair_honest answers (mainSignature sig) index lay hl digits hvalid
  · intro i
    change (sig.layers lay).values i = _
    rw [hlayer]
    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, i.isLt]
  · intro j
    change (sig.layers lay).path j = _
    rw [hlayer]
    simp [piecesSignature, wotsPieces, List.getD_eq_getElem, j.isLt]

theorem recoveredSelections_canonical (answers : Answers) (sig : Signature) (index : Nat)
    (input : LayerMsg) (result : RecoveredLayers) (messages : Layer → LayerMsg)
    (hinput : input = messages 3)
    (hlower : ∀ n, n < 3 → messages (Fin.ofNat 4 n) =
      .pair (builtPair answers (Fin.ofNat 4 (n+1)) (route index (Fin.ofNat 4 (n+1))).2).1
        (builtPair answers (Fin.ofNat 4 (n+1)) (route index (Fin.ofNat 4 (n+1))).2).2)
    (hselections : ∀ lay : Layer, evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
        (route index lay).2 (route index lay).1
        (recoveredMessage answers sig index 4 input result.digits lay) 0 (searchLimit lay)) =
          some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true))
    (hshape : ∀ lay : Layer, ∃ digits,
      CanonicalPolicy.decode lay (evalWithAnswerFn answers (encodingHash lay
        (layerEncodingInput lay (route index lay).2 (route index lay).1 (messages lay)
          (result.counters.getD lay.val 0)))) = some digits ∧
      sig.layers lay = piecesSignature lay
        (wotsPieces answers lay (route index lay).2 (route index lay).1 digits)) :
    ∀ lay : Layer,
      evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
        (route index lay).2 (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true) ∧
      sig.layers lay = piecesSignature lay
        (wotsPieces answers lay (route index lay).2 (route index lay).1 (result.digits.getD lay.val [])) := by
  have step (lay : Layer)
      (hm : recoveredMessage answers sig index 4 input result.digits lay = messages lay) :
      evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
        (route index lay).2 (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (result.counters.getD lay.val 0, result.digits.getD lay.val [], result.lows.getD lay.val true) ∧
      sig.layers lay = piecesSignature lay
        (wotsPieces answers lay (route index lay).2 (route index lay).1 (result.digits.getD lay.val [])) ∧
      Cost.ValidDigits lay (result.digits.getD lay.val []) := by
    have hs := hselections lay
    rw [hm] at hs
    have hlim := searchLimit_le lay
    have hp := (canonical_search_some' answers lay (hintFloor sig.policyHints lay)
      (route index lay).2 (route index lay).1 (messages lay) (searchLimit lay) 0
      (result.counters.getD lay.val 0) (result.digits.getD lay.val []) (result.lows.getD lay.val true)
      (by unfold counterLimit at hlim; omega) hs).2.2.2
    have hd := (CanonicalPolicy.producerDecodeAt_spec hp).1
    obtain ⟨ds, hds, hfields⟩ := hshape lay
    have heq := Option.some.inj (hds.symm.trans hd)
    subst ds
    exact ⟨hs, hfields, canonical_decode_valid hd⟩
  have h3 := step 3 (by change input = messages 3; exact hinput)
  have h2 := step 2 (by
    change LayerMsg.pair
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 3 (result.digits.getD 3 []))).1
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 3 (result.digits.getD 3 []))).2 = messages 2
    have hp := recoveredPair_of_pieces answers sig index 3 (by decide) _ h3.2.2 h3.2.1
    change evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 3
      (result.digits.getD 3 [])) = builtPair answers 3 (route index 3).2 at hp
    rw [hp]
    exact (hlower 2 (by decide)).symm)
  have h1 := step 1 (by
    change LayerMsg.pair
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 2 (result.digits.getD 2 []))).1
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 2 (result.digits.getD 2 []))).2 = messages 1
    have hp := recoveredPair_of_pieces answers sig index 2 (by decide) _ h2.2.2 h2.2.1
    change evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 2
      (result.digits.getD 2 [])) = builtPair answers 2 (route index 2).2 at hp
    rw [hp]
    exact (hlower 1 (by decide)).symm)
  have h0 := step 0 (by
    change LayerMsg.pair
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 1 (result.digits.getD 1 []))).1
      (evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 1 (result.digits.getD 1 []))).2 = messages 0
    have hp := recoveredPair_of_pieces answers sig index 1 (by decide) _ h1.2.2 h1.2.1
    change evalWithAnswerFn answers (recoverLayerPair (mainSignature sig) index 1
      (result.digits.getD 1 [])) = builtPair answers 1 (route index 1).2 at hp
    rw [hp]
    exact (hlower 0 (by decide)).symm)
  intro lay
  fin_cases lay
  · exact ⟨h0.1,h0.2.1⟩
  · exact ⟨h1.1,h1.2.1⟩
  · exact ⟨h2.1,h2.2.1⟩
  · exact ⟨h3.1,h3.2.1⟩
#print axioms recoveredMessage_fill
#print axioms recoveredSelections_canonical
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signature_unique_of_selections (answers : Answers) (index : Nat)
    (messages : Layer → LayerMsg) (a b : Signature)
    (ca cb : Layer → BitVec 32) (da db : List (List Nat)) (la lb : List Bool)
    (hrho : a.rho = b.rho) (hforest : a.forest = b.forest)
    (ha : policyHintsValid a.policyHints da la = true)
    (hb : policyHintsValid b.policyHints db lb = true)
    (hsa : ∀ lay, evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay (hintFloor a.policyHints lay)
        (route index lay).2 (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (ca lay, da.getD lay.val [], la.getD lay.val true))
    (hsb : ∀ lay, evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay (hintFloor b.policyHints lay)
        (route index lay).2 (route index lay).1 (messages lay) 0 (searchLimit lay)) =
          some (cb lay, db.getD lay.val [], lb.getD lay.val true))
    (hla : ∀ lay, a.layers lay = piecesSignature lay
      (wotsPieces answers lay (route index lay).2 (route index lay).1 (da.getD lay.val [])))
    (hlb : ∀ lay, b.layers lay = piecesSignature lay
      (wotsPieces answers lay (route index lay).2 (route index lay).1 (db.getD lay.val []))) : a = b := by
  obtain ⟨hh, -, hd, -⟩ := hintedSelections_unique answers index messages a.policyHints b.policyHints
    ca cb da db la lb ha hb hsa hsb
  have hl : a.layers = b.layers := by
    funext lay
    rw [hla, hlb, hd]
  cases a
  cases b
  simp only [Signature.mk.injEq]
  exact ⟨hrho, hh, hforest, hl⟩
#print axioms signature_unique_of_selections
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signFromOutput_components (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    ∃ result : CanonicalLayers,
      evalWithAnswerFn answers (searchPreparedLayers cache (digestIndex output)
        (evalWithAnswerFn answers (prepareRoots (digestIndex output)))
        (evalWithAnswerFn answers (buildForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output))).2) = some result ∧
      w.signature.rho = rho ∧ w.signature.policyHints = result.policyHints ∧
      w.signature.forest = (evalWithAnswerFn answers (buildForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output))).1 ∧
      (∀ lay, w.signature.layers lay = piecesSignature lay (result.pieces.getD lay.val ([],[]))) ∧
      w.digestCounter = counter ∧ ∀ lay, w.counters lay = result.counters.getD lay.val 0 := by
  unfold signFromOutput at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs : evalWithAnswerFn answers (searchPreparedLayers cache (digestIndex output)
    (evalWithAnswerFn answers (prepareRoots (digestIndex output)))
    (evalWithAnswerFn answers (buildForest (digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output))).2) with
  | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some result =>
      simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
      subst w
      exact ⟨result, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, fun _ => rfl⟩

theorem signPayload_components (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (sig : Signature)
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) :
    ∃ counter output w,
      evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
        message 0 digestAttemptLimit) = some (counter, output) ∧
      evalWithAnswerFn answers (signFromOutput cache (evalWithAnswerFn answers (privateNonce message))
        counter output) = some w ∧ w.signature = sig := by
  unfold signPayload at he
  simp only [evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
    message 0 digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (signFromOutput cache (evalWithAnswerFn answers (privateNonce message))
        counter output) with
      | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some w =>
          simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
          exact ⟨counter,output,w,rfl,hs,he⟩
#print axioms signFromOutput_components
#print axioms signPayload_components
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem PreparedSearchFacts.hinted_searches {answers : Answers} {cache : SigGolfCandidate.T3.Cache}
    {index : Nat} {forest : PairRoot} {result : CanonicalLayers}
    (h : PreparedSearchFacts answers cache index (evalWithAnswerFn answers (prepareRoots index)) forest result) :
    ∀ lay, evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt lay
      (hintFloor result.policyHints lay) (route index lay).2 (route index lay).1
      (if lay=3 then .pair forest.1 forest.2 else
        let lower : Layer := Fin.ofNat 4 (lay.val+1)
        .pair (builtPair answers lower (route index lower).2).1
          (builtPair answers lower (route index lower).2).2)
      0 (searchLimit lay)) = some (result.counters.getD lay.val 0,result.digits.getD lay.val [],result.lows.getD lay.val true) := by
  have hs0 := h.search0
  have hs1 := h.search1
  have hs2 := h.search2
  have hs3 := h.search3
  simp only [prepareRoots_result,fixedPrepared_pair] at hs0 hs1 hs2
  intro lay
  rcases layer_four_cases lay with rfl | rfl | rfl | rfl <;>
    simp only [layer_val_0,layer_val_1,layer_val_2,layer_val_3,
      show (Fin.ofNat 4 1 : Layer)=1 from rfl,
      show (Fin.ofNat 4 2 : Layer)=2 from rfl,
      show (Fin.ofNat 4 3 : Layer)=3 from rfl, Nat.reduceAdd,
      show (0 : Layer)≠3 by decide,show (1 : Layer)≠3 by decide,
      show (2 : Layer)≠3 by decide,if_false,if_true]
  · exact hs0
  · simpa only [h.hints_spec.2.1] using hs1
  · simpa only [h.hints_spec.2.2.1] using hs2
  · simpa only [h.hints_spec.2.2.2] using hs3
#print axioms PreparedSearchFacts.hinted_searches
end SigGolfCandidate.Research.SharedForest
