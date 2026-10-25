import SigGolfCandidate.ClaudeWCT_WCT9_Core

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
    (h : producerDecode lay answer = some digits) : producerFloor lay + dispatchPenalty lay digits ≤ wordCredit lay digits + 4 * savedCopies lay digits := by
  unfold producerDecode at h
  cases hd : decode lay answer with
  | none => simp [hd] at h
  | some ds =>
      simp only [hd] at h
      split_ifs at h with hc
      cases h
      exact hc.1
theorem producerDecode_zeroBound {lay : Layer} {answer : Digest} {digits : List Nat}
    (h : producerDecode lay answer = some digits) : producerZeroBound lay digits := by
  unfold producerDecode at h
  cases hd : decode lay answer with
  | none => simp [hd] at h
  | some ds =>
      simp only [hd] at h
      split_ifs at h with hc
      cases h
      exact hc.2.1
theorem producerDecode_rankBound {lay : Layer} {answer : Digest} {digits : List Nat}
    (h : producerDecode lay answer = some digits) : producerRankBound lay answer := by
  unfold producerDecode at h
  cases hd : decode lay answer with
  | none => simp [hd] at h
  | some ds =>
      simp only [hd] at h
      split_ifs at h with hc
      cases h
      exact hc.2.2
theorem producerDecode_lowerRankGood {lay : Layer} (hlay : lay ≠ 0)
    {answer : Digest} {digits : List Nat} (h : producerDecode lay answer = some digits) :
    lowerRankGood answer := (producerDecode_rankBound h).resolve_left hlay
theorem lowerFirstBad_le (answer : Digest) : lowerFirstBad answer ≤ 14 := by
  unfold lowerFirstBad
  cases h : (List.range 14).find? (fun i => decide
      (lowerWord answer / 2 ^ (9 * i) % 512 < producerRankFloor i)) with
  | none => simp
  | some i =>
      have hi := List.mem_of_find?_eq_some h
      simp only [List.mem_range] at hi
      simp only [Option.getD_some]
      omega
theorem lowerFirstBad_find (answer : Digest) (h : ¬lowerRankGood answer) :
    (List.range 14).find? (fun i => decide
      (lowerWord answer / 2 ^ (9 * i) % 512 < producerRankFloor i)) = some (lowerFirstBad answer) := by
  unfold lowerFirstBad
  cases he : (List.range 14).find? (fun i => decide
      (lowerWord answer / 2 ^ (9 * i) % 512 < producerRankFloor i)) with
  | some i => rfl
  | none =>
      exfalso
      apply h
      intro i
      have hi := List.find?_eq_none.mp he i.val (List.mem_range.mpr i.isLt)
      simp only [decide_eq_true_eq, not_lt] at hi
      exact hi
theorem lowerFirstBad_lt (answer : Digest) (h : ¬lowerRankGood answer) : lowerFirstBad answer < 14 := by
  exact List.mem_range.mp (List.mem_of_find?_eq_some (lowerFirstBad_find answer h))
theorem lowerFirstBad_bad (answer : Digest) (h : ¬lowerRankGood answer) :
    lowerWord answer / 2 ^ (9 * lowerFirstBad answer) % 512 < producerRankFloor (lowerFirstBad answer) := by
  have hb := List.find?_some (lowerFirstBad_find answer h)
  exact of_decide_eq_true hb
theorem lowerFirstBad_before (answer : Digest) (h : ¬lowerRankGood answer) (i : Nat)
    (hi : i < lowerFirstBad answer) : producerRankFloor i ≤ lowerWord answer / 2 ^ (9 * i) % 512 := by
  obtain ⟨_, j, hj, hjeq, hbefore⟩ := List.find?_eq_some_iff_getElem.mp (lowerFirstBad_find answer h)
  simp only [List.getElem_range] at hjeq
  subst j
  have hb := hbefore i hi
  simpa only [List.getElem_range, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] using hb
theorem lowerGuardedRun_of_good {α : Type} (run : Nat → M Digest) (finish : M α) (answer : Digest)
    (h : lowerRankGood answer) : lowerGuardedRun run finish answer = some <$> finish := by
  simp only [lowerGuardedRun, if_pos h]
theorem recoverLayerPairGuard_of_good (sig : Signature) (index : Nat) (lay : Layer) (answer : Digest)
    (digits : List Nat) (h : lowerRankGood answer) :
    recoverLayerPairGuard sig index lay answer digits = some <$> recoverLayerPair sig index lay digits :=
  lowerGuardedRun_of_good _ _ _ h
/-- Only producer-selected lower words, not all broad-decoder words, satisfy the B4 cap. -/
theorem lower_zero_count_le_producer {lay : Layer} (hlay : lay ≠ 0)
    {value : Digest} {digits : List Nat} (h : producerDecode lay value = some digits) :
    (digits.filter (· = 0)).length ≤ 5 :=
  (producerDecode_zeroBound h).resolve_left hlay
theorem producerDecode_of {lay : Layer} {answer : Digest} {digits : List Nat}
    (hd : decode lay answer = some digits) (hc : producerFloor lay + dispatchPenalty lay digits ≤ wordCredit lay digits + 4 * savedCopies lay digits)
    (hz : producerZeroBound lay digits) (hr : producerRankBound lay answer) : producerDecode lay answer = some digits := by
  unfold producerDecode
  simp only [hd, hc, hz, hr, and_self, ↓reduceIte]
theorem producerDecode_eq_some_iff (lay : Layer) (answer : Digest) (digits : List Nat) :
    producerDecode lay answer = some digits ↔
      decode lay answer = some digits ∧ producerFloor lay + dispatchPenalty lay digits ≤ wordCredit lay digits + 4 * savedCopies lay digits ∧ producerZeroBound lay digits ∧ producerRankBound lay answer :=
  ⟨fun h => ⟨producerDecode_decode h, producerDecode_credit h, producerDecode_zeroBound h, producerDecode_rankBound h⟩,
    fun h => producerDecode_of h.1 h.2.1 h.2.2.1 h.2.2.2⟩
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
    producerFloor 0 = 21 ∧ producerFloor 1 = 10 ∧ producerFloor 2 = 9 ∧ producerFloor 3 = 9 :=
  ⟨rfl, rfl, rfl, rfl⟩
theorem searchLimit_top : searchLimit 0 = topSearchLimit := rfl
/-- Every lower window is at least `lowerSearchLimit` (L3 is 3·2^20). -/
theorem searchLimit_lower {lay : Layer} (h : lay ≠ 0) : lowerSearchLimit ≤ searchLimit lay := by
  unfold searchLimit lowerSearchLimit
  fin_cases lay <;> simp_all
theorem searchLimit_le (lay : Layer) : searchLimit lay ≤ counterLimit := by
  unfold searchLimit counterLimit
  fin_cases lay <;> simp
theorem searchLimit_values : searchLimit 0 = 2 ^ 20 ∧ searchLimit 1 = 2 ^ 21 ∧ searchLimit 2 = 2 ^ 21 ∧
    searchLimit 3 = 3 * 2 ^ 20 := by decide
theorem lowerSearchLimit_eq : lowerSearchLimit = 2 ^ 21 := rfl
theorem chainCount_top : chainCount 0 = 51 := rfl
theorem dataDigits_top_length (answer : Digest) : (dataDigits 0 answer).length = 50 := by
  simp [dataDigits, dataCount]
/-- Campaign T51: a decoded top word has valid fields (9 r6 ranks < 216, 7 r5 ranks < 125, the r7 rank < 49), its
checksum digit `target 0 - sum` lies in `[0, 5]`, and the digits are the 50 data digits followed by the checksum. -/
theorem decode_top_some {answer : Digest} {digits : List Nat} (h : decode 0 answer = some digits) :
    answer.toNat < 2 ^ encodedBits 0 ∧ topRanksValid answer = true ∧
      ((dataDigits 0 answer).sum ≤ target 0 ∧ target 0 - (dataDigits 0 answer).sum < 6) ∧
      digits = dataDigits 0 answer ++ [target 0 - (dataDigits 0 answer).sum] := by
  unfold decode at h
  split at h
  · cases h
  · rename_i hg
    simp only [↓reduceIte] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨by omega, hc.1, hc.2, rfl⟩
    · cases h
theorem decode_top_of {answer : Digest} (hg : answer.toNat < 2 ^ encodedBits 0)
    (hr : topRanksValid answer = true) (hs : (dataDigits 0 answer).sum ≤ target 0)
    (hc : target 0 - (dataDigits 0 answer).sum < 6) :
    decode 0 answer = some (dataDigits 0 answer ++ [target 0 - (dataDigits 0 answer).sum]) := by
  unfold decode
  rw [if_neg (by omega)]
  simp only [↓reduceIte, hr, hs, hc, and_self]
theorem topGroupBad_eq_false_iff (answer : Digest) (i : Nat) :
    topGroupBad answer i = false ↔
      ¬(i % 3 = 0 ∧ i < 50 ∧ topGroupValid answer (i / 3) = false) ∧ ¬(i = 50 ∧ topChecksumOk answer = false) := by
  unfold topGroupBad
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
/-- Campaign T51: `topRanksValid` is exactly the per-group checks of the 50 data chains (r6 groups 0..8, r5 groups
9..15, the r7 pair at chain 48). -/
theorem topRanksValid_iff_good (answer : Digest) :
    topRanksValid answer = true ↔ ∀ i : Fin (chainCount 0), i.val < 50 → topGroupBad answer i.val = false := by
  unfold topRanksValid
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, List.mem_range'_1]
  constructor
  · rintro ⟨⟨h6, h5⟩, h7⟩
    refine fun i hi => (topGroupBad_eq_false_iff answer i.val).2 ⟨fun ⟨_, _, hv⟩ => ?_, fun ⟨he, _⟩ => by omega⟩
    unfold topGroupValid at hv
    split_ifs at hv with hg hg'
    · rw [h6 _ hg] at hv; cases hv
    · have h5' := h5 (i.val / 3) ⟨by omega, by omega⟩
      simp only [decide_eq_false_iff_not] at hv
      exact hv h5'
    · simp only [decide_eq_false_iff_not] at hv
      exact hv h7
  · intro h
    have hv : ∀ g, g < 17 → topGroupValid answer g = true := by
      intro g hg
      have hb := ((topGroupBad_eq_false_iff answer (3 * g)).1
        (h ⟨3 * g, by rw [chainCount_top]; omega⟩ (by simp only; omega))).1
      by_contra hc
      exact hb ⟨by omega, by omega, by rw [show 3 * g / 3 = g by omega]; simpa using hc⟩
    refine ⟨⟨fun g hg => ?_, fun q hq => ?_⟩, ?_⟩
    · simpa [topGroupValid, hg] using hv g (by omega)
    · have := hv q (by omega)
      simpa [topGroupValid, show ¬ q < 9 by omega, show q < 16 by omega] using this
    · simpa [topGroupValid] using hv 16 (by omega)
/-- Campaign T51: the top decoder accepts iff no check of the verifier's chain loop fires. -/
theorem decode_top_isSome_iff (answer : Digest) :
    (decode 0 answer).isSome = true ↔ ∀ i : Fin (chainCount 0), topGroupBad answer i.val = false := by
  have hlt : answer.toNat < 2 ^ encodedBits 0 := answer.isLt
  constructor
  · intro h
    obtain ⟨digits, hd⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨-, hr, ⟨hs, hc⟩, -⟩ := decode_top_some hd
    have hg := (topRanksValid_iff_good answer).1 hr
    intro i
    by_cases hi : i.val < 50
    · exact hg i hi
    · have hi50 : i.val = 50 := by have : i.val < 51 := i.isLt; omega
      rw [topGroupBad_eq_false_iff]
      refine ⟨fun ⟨_, h2, _⟩ => by omega, fun ⟨_, hk⟩ => ?_⟩
      unfold topChecksumOk at hk
      simp only [decide_eq_false_iff_not, not_and, not_lt] at hk
      have := hk hs
      omega
  · intro hg
    have hr : topRanksValid answer = true := (topRanksValid_iff_good answer).2 (fun i _ => hg i)
    have hk := ((topGroupBad_eq_false_iff answer 50).1 (hg ⟨50, by rw [chainCount_top]; omega⟩)).2
    have hk' : topChecksumOk answer = true := by
      by_contra hc
      exact hk ⟨rfl, by simpa using hc⟩
    unfold topChecksumOk at hk'
    simp only [decide_eq_true_eq] at hk'
    rw [decode_top_of hlt hr hk'.1 hk'.2]
    rfl
/-- Campaign T51: the digit the verifier runs on top chain `i` is the decoded digit `i` (checksum included). -/
theorem topRunDigit_of_decode {answer : Digest} {digits : List Nat} (h : decode 0 answer = some digits) (i : Nat)
    (hi : i < 51) : topRunDigit answer i = digits.getD i 0 := by
  obtain ⟨-, -, -, rfl⟩ := decode_top_some h
  have hl := dataDigits_top_length answer
  unfold topRunDigit
  split_ifs with h50
  · rw [List.getD_append _ _ _ _ (by omega)]
  · have : i = 50 := by omega
    subst this
    rw [List.getD_append_right _ _ _ _ (by omega), hl]
    rfl
section Loop
variable (run : Fin (chainCount 0) → Nat → M Digest) (answer : Digest)
theorem topDecodeStep_none (i : Fin (chainCount 0)) : topDecodeStep run answer none i = pure none := rfl
theorem topDecodeStep_bad (ends : List Digest) (i : Fin (chainCount 0)) (h : topGroupBad answer i.val = true) :
    topDecodeStep run answer (some ends) i = pure none := by
  simp only [topDecodeStep, h, ↓reduceIte]
theorem topDecodeStep_good (ends : List Digest) (i : Fin (chainCount 0)) (h : topGroupBad answer i.val = false) :
    topDecodeStep run answer (some ends) i =
      (fun value => some (ends ++ [value])) <$> run i (topRunDigit answer i.val) := by
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
        (fun ends => some (acc ++ ends)) <$> L.mapM (fun i => run i (topRunDigit answer i.val))
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
  have hsome : (decode 0 answer).isSome = true := by rw [h]; rfl
  have hgood := (decode_top_isSome_iff answer).1 hsome
  have hfun : (fun i : Fin (chainCount 0) => run i (topRunDigit answer i.val)) =
      fun i => run i (digits.getD i.val 0) := by
    funext i
    rw [topRunDigit_of_decode h i.val i.isLt]
  unfold topDecodeRun
  rw [if_neg (by have := answer.isLt; simp only [encodedBits]; omega),
    foldlM_topDecodeStep_good run answer _ [] (fun i _ => hgood i), bind_map_left, map_bind, hfun]
  simp only [List.nil_append]
/-- Chains run before a top rejection: those before the first failing check (T51: no spare bit). -/
def topRejectLength (answer : Digest) : Nat :=
  if answer.toNat ≥ 2 ^ encodedBits 0 then 0
  else (List.finRange (chainCount 0)).findIdx fun i => topGroupBad answer i.val
/-- The chains the verifier runs before it rejects a bad top word (T51: digits as `topDecodeStep` runs them). -/
def topRejectChains (run : Fin (chainCount 0) → Nat → M Digest) (answer : Digest) : M (List Digest) :=
  ((List.finRange (chainCount 0)).take (topRejectLength answer)).mapM
    fun i => run i (topRunDigit answer i.val)
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
  · exfalso
    have hkL : k = L.length := le_antisymm (hk ▸ List.findIdx_le_length) (by omega)
    have hall : ∀ i : Fin (chainCount 0), topGroupBad answer i.val = false := by
      intro i
      have := List.findIdx_eq_length.mp (hk.trans hkL)
      exact this i (hL ▸ List.mem_finRange i)
    have hs := (decode_top_isSome_iff answer).2 hall
    rw [h] at hs
    cases hs
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
  split_ifs
  · exact Nat.zero_le _
  · exact List.findIdx_le_length.trans (le_of_eq List.length_finRange)
theorem dataDigits_top_getD (answer : Digest) {i : Nat} (hi : i < 50) :
    (dataDigits 0 answer).getD i 0 = coreDigit 0 answer i := by
  simp [dataDigits, dataCount, List.getD_eq_getElem?_getD, hi]
/-- Campaigns R6/T51: the canonical top credit of a decoded word is the legacy `topCredit` (every chain one below its
maximum, the checksum included). -/
theorem wordCredit_top {answer : Digest} {digits : List Nat} (h : decode 0 answer = some digits) :
    wordCredit 0 digits = topCredit answer := by
  obtain ⟨-, -, -, rfl⟩ := decode_top_some h
  unfold wordCredit topCredit
  rw [chainCount_top]
  generalize dataDigits 0 answer ++ [target 0 - (dataDigits 0 answer).sum] = ds
  have key : ∀ L : List Nat, (L.filter fun i => ds.getD i 0 + 1 = maxDigit 0 i).length =
      (L.map fun i => if ds.getD i 0 + 1 = maxDigit 0 i then 1 else 0).sum := by
    intro L
    induction L with
    | nil => rfl
    | cons i L ih =>
        by_cases hc : ds.getD i 0 + 1 = maxDigit 0 i
        · rw [List.filter_cons_of_pos (by simpa using hc), List.length_cons, List.map_cons, List.sum_cons, if_pos hc,
            ih]
          omega
        · rw [List.filter_cons_of_neg (by simpa using hc), List.map_cons, List.sum_cons, if_neg hc, ih]
          omega
  exact key _
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
def dummyLowData : List Nat := List.replicate 10 6 ++ List.replicate 3 7 ++ List.replicate 29 4
def dummyLowDigits (lay : Layer) : List Nat := dummyLowData ++ [target lay - 197]
def dummyLowDigest : Digest := 267364716866451649868032922661926170038
theorem producerDecode_dummyLow (lay : Layer) (h : lay ≠ 0) :
    producerDecode lay dummyLowDigest = some (dummyLowDigits lay) := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide +kernel
end ClaudeWCT.WCT9
