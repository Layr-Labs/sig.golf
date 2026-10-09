import SigGolfCandidate.ClaudeWCT.WCT9.Core

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
theorem producerDecode_decode {lay : Layer} {answer : Digest} {digits : List Nat}
    (h : producerDecode lay answer = some digits) : decode lay answer = some digits := by
  unfold producerDecode at h
  cases hd : decode lay answer with
  | none => simp [hd] at h
  | some ds =>
      simp only [hd] at h
      split_ifs at h
      cases h
      rfl
theorem producerDecode_credit {lay : Layer} {answer : Digest} {digits : List Nat}
    (h : producerDecode lay answer = some digits) : producerFloor lay ≤ wordCredit lay digits := by
  unfold producerDecode at h
  cases hd : decode lay answer with
  | none => simp [hd] at h
  | some ds =>
      simp only [hd] at h
      split_ifs at h with hc
      cases h
      exact hc
theorem producerDecode_of {lay : Layer} {answer : Digest} {digits : List Nat}
    (hd : decode lay answer = some digits) (hc : producerFloor lay ≤ wordCredit lay digits) :
    producerDecode lay answer = some digits := by
  unfold producerDecode
  simp only [hd, hc, ↓reduceIte]
theorem producerDecode_eq_some_iff (lay : Layer) (answer : Digest) (digits : List Nat) :
    producerDecode lay answer = some digits ↔
      decode lay answer = some digits ∧ producerFloor lay ≤ wordCredit lay digits :=
  ⟨fun h => ⟨producerDecode_decode h, producerDecode_credit h⟩, fun h => producerDecode_of h.1 h.2⟩
theorem producerDecode_eq_none_or (lay : Layer) (answer : Digest) :
    producerDecode lay answer = none ∨ producerDecode lay answer = decode lay answer := by
  unfold producerDecode
  cases decode lay answer with
  | none => exact Or.inl rfl
  | some ds =>
      simp only
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
theorem producerFloor_values :
    producerFloor 0 = 9 ∧ producerFloor 1 = 5 ∧ producerFloor 2 = 5 ∧ producerFloor 3 = 5 :=
  ⟨rfl, rfl, rfl, rfl⟩
theorem searchLimit_top : searchLimit 0 = counterLimit := rfl
theorem searchLimit_lower {lay : Layer} (h : lay ≠ 0) : searchLimit lay = lowerSearchLimit := by
  unfold searchLimit
  rw [if_neg h]
theorem searchLimit_le (lay : Layer) : searchLimit lay ≤ counterLimit := by
  unfold searchLimit lowerSearchLimit counterLimit
  split <;> norm_num
theorem lowerSearchLimit_eq : lowerSearchLimit = 2 ^ 21 := rfl
theorem chainCount_top : chainCount 0 = 54 := rfl
theorem decode_top_some {answer : Digest} {digits : List Nat} (h : decode 0 answer = some digits) :
    answer.toNat < 2 ^ encodedBits 0 ∧ topRanksValid answer = true ∧ (dataDigits 0 answer).sum = target 0 ∧
      digits = dataDigits 0 answer := by
  unfold decode at h
  split at h
  · cases h
  · rename_i hg
    simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨by omega, hc.1, hc.2, rfl⟩
    · cases h
theorem decode_top_of {answer : Digest} (hg : answer.toNat < 2 ^ encodedBits 0)
    (hr : topRanksValid answer = true) (hs : (dataDigits 0 answer).sum = target 0) :
    decode 0 answer = some (dataDigits 0 answer) := by
  unfold decode
  rw [if_neg (by omega)]
  simp only [↓reduceIte, hr, hs, decide_true, Bool.and_self]
theorem topGroupBad_eq_false_iff (answer : Digest) (i : Nat) :
    topGroupBad answer i = false ↔ ¬(i % 3 = 0 ∧ i < 51 ∧ 125 ≤ topCode answer / 2 ^ (7 * (i / 3)) % 128) := by
  unfold topGroupBad
  exact decide_eq_false_iff_not
theorem topRanksValid_iff_good (answer : Digest) :
    topRanksValid answer = true ↔ ∀ i : Fin (chainCount 0), topGroupBad answer i.val = false := by
  unfold topRanksValid
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq, topGroupBad_eq_false_iff]
  constructor
  · intro h i hb
    have hi : i.val < 54 := i.isLt
    exact absurd hb.2.2 (Nat.not_le.mpr (h (i.val / 3) (by omega)))
  · intro h j hj
    by_contra hc
    apply h ⟨3 * j, by rw [chainCount_top]; omega⟩
    refine ⟨by simp, by simp only; omega, ?_⟩
    simp only
    rw [show 3 * j / 3 = j by omega]
    exact Nat.not_lt.mp hc
section Loop
variable (run : Fin (chainCount 0) → Nat → M Digest) (answer : Digest)
theorem topDecodeStep_none (i : Fin (chainCount 0)) : topDecodeStep run answer none i = pure none := rfl
theorem topDecodeStep_bad (ends : List Digest) (i : Fin (chainCount 0)) (h : topGroupBad answer i.val = true) :
    topDecodeStep run answer (some ends) i = pure none := by
  simp only [topDecodeStep, h, ↓reduceIte]
theorem topDecodeStep_good (ends : List Digest) (i : Fin (chainCount 0)) (h : topGroupBad answer i.val = false) :
    topDecodeStep run answer (some ends) i =
      (fun value => some (ends ++ [value])) <$> run i ((dataDigits 0 answer).getD i.val 0) := by
  simp only [topDecodeStep, h, Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp]
  rfl
theorem foldlM_topDecodeStep_none :
    ∀ L : List (Fin (chainCount 0)), L.foldlM (topDecodeStep run answer) none = pure none
  | [] => rfl
  | i :: L => by
      rw [List.foldlM_cons, topDecodeStep_none, pure_bind, foldlM_topDecodeStep_none L]
theorem foldlM_topDecodeStep_good :
    ∀ (L : List (Fin (chainCount 0))) (acc : List Digest), (∀ i ∈ L, topGroupBad answer i.val = false) →
      L.foldlM (topDecodeStep run answer) (some acc) =
        (fun ends => some (acc ++ ends)) <$> L.mapM (fun i => run i ((dataDigits 0 answer).getD i.val 0))
  | [], acc, _ => by simp
  | i :: L, acc, h => by
      rw [List.foldlM_cons, List.mapM_cons, topDecodeStep_good run answer acc i (h i List.mem_cons_self),
        bind_map_left, map_bind]
      congr 1
      funext value
      rw [foldlM_topDecodeStep_good L (acc ++ [value]) (fun j hj => h j (List.mem_cons_of_mem _ hj)),
        map_eq_bind_pure_comp, map_eq_bind_pure_comp, bind_assoc]
      congr 1
      funext ends
      simp
theorem eval_foldlM_topDecodeStep_none (answers : QueryImpl Spec Id) (L : List (Fin (chainCount 0))) :
    evalWithAnswerFn answers (L.foldlM (topDecodeStep run answer) none) = none := by
  rw [foldlM_topDecodeStep_none, evalWithAnswerFn_pure]
theorem eval_foldlM_topDecodeStep_some (answers : QueryImpl Spec Id) :
    ∀ (L : List (Fin (chainCount 0))) (state : Option (List Digest)) (ends : List Digest),
      evalWithAnswerFn answers (L.foldlM (topDecodeStep run answer) state) = some ends →
        ∀ i ∈ L, topGroupBad answer i.val = false
  | [], _, _, _ => by simp
  | i :: L, state, ends, h => by
      rw [List.foldlM_cons, evalWithAnswerFn_bind] at h
      cases state with
      | none =>
          rw [topDecodeStep_none, evalWithAnswerFn_pure, eval_foldlM_topDecodeStep_none] at h
          cases h
      | some acc =>
          cases hb : topGroupBad answer i.val with
          | true =>
              rw [topDecodeStep_bad run answer acc i hb, evalWithAnswerFn_pure,
                eval_foldlM_topDecodeStep_none] at h
              cases h
          | false =>
              intro j hj
              rcases List.mem_cons.mp hj with rfl | hj
              · exact hb
              · exact eval_foldlM_topDecodeStep_some answers L _ ends h j hj
end Loop
theorem topDecodeRun_of_decode {run : Fin (chainCount 0) → Nat → M Digest} {finish : List Digest → M Digest}
    {answer : Digest} {digits : List Nat} (h : decode 0 answer = some digits) :
    topDecodeRun run finish answer =
      some <$> ((List.finRange (chainCount 0)).mapM (fun i => run i (digits.getD i.val 0)) >>= finish) := by
  obtain ⟨hg, hr, hs, rfl⟩ := decode_top_some h
  unfold topDecodeRun
  rw [if_neg (by omega), foldlM_topDecodeStep_good run answer _ []
    (fun i _ => (topRanksValid_iff_good answer).1 hr i), bind_map_left, map_bind]
  simp only [List.nil_append, hs, ne_eq, not_true_eq_false, ↓reduceIte]
def topRejectLength (answer : Digest) : Nat :=
  if answer.toNat ≥ 2 ^ encodedBits 0 then 0
  else (List.finRange (chainCount 0)).findIdx fun i => topGroupBad answer i.val
def topRejectChains (run : Fin (chainCount 0) → Nat → M Digest) (answer : Digest) : M (List Digest) :=
  ((List.finRange (chainCount 0)).take (topRejectLength answer)).mapM
    fun i => run i ((dataDigits 0 answer).getD i.val 0)
theorem topDecodeRun_of_decode_none {run : Fin (chainCount 0) → Nat → M Digest}
    {finish : List Digest → M Digest} {answer : Digest} (h : decode 0 answer = none) :
    topDecodeRun run finish answer = (fun _ => none) <$> topRejectChains run answer := by
  unfold topDecodeRun topRejectChains topRejectLength
  by_cases hg : answer.toNat ≥ 2 ^ encodedBits 0
  · rw [if_pos hg, if_pos hg]
    simp
  rw [if_neg hg, if_neg hg]
  generalize hL : List.finRange (chainCount 0) = L
  generalize hk : L.findIdx (fun i => topGroupBad answer i.val) = k
  have hgood : ∀ i ∈ L.take k, topGroupBad answer i.val = false := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
    rw [List.length_take] at hj
    have hj' : j < L.findIdx (fun i => topGroupBad answer i.val) := by rw [hk]; omega
    rw [List.getElem_take]
    exact List.not_of_lt_findIdx hj'
  conv_lhs => rw [← List.take_append_drop k L, List.foldlM_append]
  rw [foldlM_topDecodeStep_good run answer _ [] hgood, bind_map_left, bind_assoc, map_eq_bind_pure_comp]
  refine bind_congr fun ends => ?_
  by_cases hlt : k < L.length
  · have hbad : topGroupBad answer (L[k]'hlt).val = true := by
      subst hk
      exact List.findIdx_getElem (w := hlt)
    rw [List.drop_eq_getElem_cons hlt, List.foldlM_cons, topDecodeStep_bad run answer _ _ hbad, pure_bind,
      foldlM_topDecodeStep_none, pure_bind]
    rfl
  · have hkL : k = L.length := le_antisymm (hk ▸ List.findIdx_le_length) (by omega)
    have hall : ∀ i : Fin (chainCount 0), topGroupBad answer i.val = false := by
      intro i
      have := List.findIdx_eq_length.mp (hk.trans hkL)
      exact this i (hL ▸ List.mem_finRange i)
    have hr := (topRanksValid_iff_good answer).2 hall
    have hs : (dataDigits 0 answer).sum ≠ target 0 := fun hs => by
      rw [decode_top_of (by omega) hr hs] at h
      cases h
    rw [show L.drop k = [] by rw [hkL]; exact List.drop_length]
    simp [hs]
theorem eval_topDecodeRun_none (answers : QueryImpl Spec Id) {run : Fin (chainCount 0) → Nat → M Digest}
    {finish : List Digest → M Digest} {answer : Digest} (h : decode 0 answer = none) :
    evalWithAnswerFn answers (topDecodeRun run finish answer) = none := by
  rw [topDecodeRun_of_decode_none h, map_eq_bind_pure_comp, evalWithAnswerFn_bind]
  rfl
theorem decode_of_eval_topDecodeRun (answers : QueryImpl Spec Id) {run : Fin (chainCount 0) → Nat → M Digest}
    {finish : List Digest → M Digest} {answer : Digest} {out : Digest}
    (h : evalWithAnswerFn answers (topDecodeRun run finish answer) = some out) :
    ∃ digits, decode 0 answer = some digits := by
  cases hd : decode 0 answer with
  | none => rw [eval_topDecodeRun_none answers hd] at h; cases h
  | some digits => exact ⟨digits, rfl⟩
theorem topRejectLength_le (answer : Digest) : topRejectLength answer ≤ chainCount 0 := by
  unfold topRejectLength
  split
  · exact Nat.zero_le _
  · exact List.findIdx_le_length.trans (le_of_eq List.length_finRange)
theorem dataDigits_top_getD (answer : Digest) {i : Nat} (hi : i < 54) :
    (dataDigits 0 answer).getD i 0 = coreDigit 0 answer i := by
  simp [dataDigits, dataCount, List.getD_eq_getElem?_getD, hi]
theorem wordCredit_top {answer : Digest} {digits : List Nat} (h : decode 0 answer = some digits) :
    wordCredit 0 digits = topCredit answer := by
  obtain ⟨-, -, -, rfl⟩ := decode_top_some h
  unfold wordCredit topCredit
  have key : ∀ L : List Nat, (∀ i ∈ L, i < 54) →
      (L.filter fun i => (dataDigits 0 answer).getD i 0 + 1 = maxDigit 0 i).length =
        (L.map fun i => if coreDigit 0 answer i = (if i < 51 then 3 else 2) then 1 else 0).sum := by
    intro L hL
    induction L with
    | nil => rfl
    | cons i L ih =>
        have hi := hL i List.mem_cons_self
        rw [List.filter_cons, List.map_cons, List.sum_cons, dataDigits_top_getD answer hi,
          ← ih (fun j hj => hL j (List.mem_cons_of_mem _ hj))]
        have hm : maxDigit 0 i = if i < 51 then 4 else 3 := rfl
        by_cases hc : coreDigit 0 answer i = (if i < 51 then 3 else 2)
        · have hp : (decide (coreDigit 0 answer i + 1 = maxDigit 0 i)) = true := by
            rw [decide_eq_true_eq, hm, hc]; split <;> rfl
          rw [if_pos hp, if_pos hc, List.length_cons]
          omega
        · have hp : (decide (coreDigit 0 answer i + 1 = maxDigit 0 i)) = false := by
            rw [decide_eq_false_iff_not, hm]
            intro he
            apply hc
            split at he <;> split <;> omega
          rw [if_neg (by simp [hp]), if_neg hc]
          omega
  rw [chainCount_top]
  exact key _ (fun i hi => List.mem_range.mp hi)
theorem verifyTop_of_decode (sig : WCT9.Signature) (index : Nat) {answer : Digest} {digits : List Nat}
    (h : decode 0 answer = some digits) :
    verifyTop sig index answer = some <$> recoverLayer (toT3Signature sig) index 0 digits := by
  unfold verifyTop recoverLayer
  generalize route index 0 = p
  obtain ⟨leaf, tree⟩ := p
  dsimp only
  rw [topDecodeRun_of_decode h]
  rfl
theorem eval_verifyTop_none (answers : QueryImpl Spec Id) (sig : WCT9.Signature) (index : Nat) {answer : Digest}
    (h : decode 0 answer = none) : evalWithAnswerFn answers (verifyTop sig index answer) = none := by
  unfold verifyTop
  generalize route index 0 = p
  obtain ⟨leaf, tree⟩ := p
  dsimp only
  exact eval_topDecodeRun_none answers h
def dummyLowData : List Nat := List.replicate 5 6 ++ List.replicate 16 5 ++ List.replicate 21 4
def dummyLowDigits (lay : Layer) : List Nat := dummyLowData ++ [target lay - 194]
def dummyLowDigest : Digest := 267364716866451649869350547003163471286
theorem producerDecode_dummyLow (lay : Layer) (h : lay ≠ 0) :
    producerDecode lay dummyLowDigest = some (dummyLowDigits lay) := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide +kernel
end ClaudeWCT.WCT9
