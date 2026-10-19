import SigGolfCandidate.W9Machine_WctChainSplit
import SigGolfCandidate.W9Machine_WctSourceWords
set_option Elab.async false

namespace W9Machine.V3SourceEquiv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M publicHash shortHash header)
open W9Machine W9Machine.Chain
theorem traceProgram_append (b : ChainWord → Word) (qs₁ qs₂ : List (List ChainWord))
    (as : List (BitVec 256)) :
    traceProgram b (qs₁ ++ qs₂) as = traceProgram b qs₁ as >>= fun as' => traceProgram b qs₂ as' := by
  induction qs₁ generalizing as with
  | nil => simp only [List.nil_append, traceProgram, pure_bind]
  | cons q qs ih => simp only [List.cons_append, traceProgram, ih, bind_assoc]
theorem sum_take_succ (l : List Nat) (t : Nat) :
    (l.take (t + 1)).sum = (l.take t).sum + l.getD t 0 := by
  induction l generalizing t with
  | nil => simp
  | cons x xs ih =>
    cases t with
    | zero => simp
    | succ t => simp only [List.take_succ_cons, List.sum_cons, ih, List.getD_cons_succ]; omega
theorem extract_lo (x : BitVec 256) :
    (x.extractLsb' 0 128).extractLsb' 0 64 = x.extractLsb' 0 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  rw [Nat.mod_mod_of_dvd _ (by norm_num)]
theorem extract_hi (x : BitVec 256) :
    (x.extractLsb' 0 128).extractLsb' 64 64 = x.extractLsb' 64 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod]
theorem extract_hh_lo (x : BitVec 256) :
    (x.extractLsb' 128 128).extractLsb' 0 64 = x.extractLsb' 128 64 := by
  ext i hi
  have h : i < 128 := by omega
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb', Nat.zero_add, h, decide_true, Bool.true_and]
theorem extract_hh_hi (x : BitVec 256) :
    (x.extractLsb' 128 128).extractLsb' 64 64 = x.extractLsb' 192 64 := by
  ext i hi
  have h : 64 + i < 128 := by omega
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb', h, decide_true, Bool.true_and]
  rw [show 128 + (64 + i) = 192 + i by omega]
theorem projHash_def (high : Bool) (x : List UInt8) :
    SigGolfCandidate.T3.projHash high x =
      publicHash x >>= fun a => pure (SigGolfCandidate.T3.projHalf high a) := rfl
theorem orig_word {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u : MachineState} (hu : Pre L w index k j rank u) (as : List (BitVec 256)) (off : Nat)
    (ho : off < 848) (ha : off % 8 = 0) :
    chainValue (originalValue L u index k j) as (.original off) =
      w.extractLsb' (8 * (V3.regionOffset k.val + off)) 64 := by
  exact hu.witness off ho ha
theorem ftsOff_bound (t : Nat) (ht : t < 6) : ftsOff t ≤ 592 ∧ ftsOff t % 8 = 0 := by
  unfold ftsOff ClaudeWCT.W9.T3M.wctChainOff
  split_ifs <;> omega
/-- A word of chain `t`'s 64-byte block, as the (possibly digested) witness word. -/
theorem orig_block {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u : MachineState} (hu : Pre L w index k j rank u) (as : List (BitVec 256)) (t c : Nat)
    (ht : t < 6) (hc : c < 64) (ha : c % 8 = 0) :
    chainValue (originalValue L u index k j) as (.original (ftsOff t + c)) =
      w.extractLsb' (8 * (V3.chainOffset k.val t + c)) 64 := by
  have hb := ftsOff_bound t ht
  rw [orig_word hu as _ (by omega) (by omega)]
  simp only [V3.chainOffset, ftsOff, Nat.add_assoc]
theorem orig_lo {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u : MachineState} (hu : Pre L w index k j rank u) (as : List (BitVec 256)) (t c : Nat)
    (ht : t < 6) (hc : c + 16 ≤ 64) (ha : c % 8 = 0) :
    chainValue (originalValue L u index k j) as (.original (ftsOff t + c)) =
      (wdig w (V3.chainOffset k.val t + c)).extractLsb' 0 64 := by
  rw [W9Machine.wdig_lo]; exact orig_block hu as t c ht (by omega) ha
theorem orig_hi {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u : MachineState} (hu : Pre L w index k j rank u) (as : List (BitVec 256)) (t c : Nat)
    (ht : t < 6) (hc : c + 16 ≤ 64) (ha : c % 8 = 0) :
    chainValue (originalValue L u index k j) as (.original (ftsOff t + (c + 8))) =
      (wdig w (V3.chainOffset k.val t + c)).extractLsb' 64 64 := by
  rw [W9Machine.wdig_hi, Nat.add_assoc]; exact orig_block hu as t (c + 8) ht (by omega) (by omega)
/-- The value carried into step `s` of chain `t`: the revealed witness value at `s = 0`, otherwise the kept half of
the previous answer (high for interior G steps). -/
def stepValue (w : WBytes) (k : Fin 9) (digits : List Nat) (t s : Nat) (as : List (BitVec 256)) : Digest :=
  if s = 0 then V3.reveal w k.val t (digits.getD t 0)
  else SigGolfCandidate.T3.projHalf (ClaudeWCT.WCT9.ftsChainHigh t (4 - digits.getD t 0 + s - 1))
    (as.getD ((digits.take t).sum + s - 1) 0)
theorem query_bytes {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u : MachineState} (hu : Pre L w index k j rank u) (digits : List Nat) (t s : Nat)
    (ht : t < 6) (hd4 : digits.getD t 0 ≤ 4) (hs : s < digits.getD t 0) (as : List (BitVec 256)) (v : Digest)
    (hv : v = stepValue w k digits t s as) :
    wordBytes ((chainQueryWords digits t s).map (chainValue (originalValue L u index k j) as)) =
      V3.chainInput index k.val j.val t (4 - digits.getD t 0 + s)
        (V3.chainPadA w k.val t) (V3.chainPadB w k.val t) (V3.chainPadC w k.val t) v := by
  rw [← wordBytes_wordsOf (V3.chainInput _ _ _ _ _ _ _ _ _) 8
    (chainInput_length _ _ _ _ _ _ _ _ _), wordsOf_chainInput]
  congr 1
  have hd : digits.getD t 0 ≠ 0 := by omega
  have hB : V3.chainPadB w k.val t = chainValue (originalValue L u index k j) as (.original (ftsOff t + 24)) :=
    (orig_block hu as t 24 ht (by decide) (by decide)).symm
  by_cases hG : ClaudeWCT.WCT9.ftsIsG t = true
  · -- G: `value | header | a | c`, interior values are high halves
    have hA : V3.chainPadA w k.val t = wdig w (V3.chainOffset k.val t + 32) := by
      simp only [V3.chainPadA, ClaudeWCT.W9.T3M.wctPad0Off, hG, eq_self_iff_true, if_true, ↓reduceIte]
    have hC : V3.chainPadC w k.val t = wdig w (V3.chainOffset k.val t + 48) := by
      simp only [V3.chainPadC, ClaudeWCT.W9.T3M.wctPad1Off, hG, eq_self_iff_true, if_true, ↓reduceIte]
    have hlo : chainValue (originalValue L u index k j) as
        (if s = 0 then .original (ftsOff t) else .answer ((digits.take t).sum + s - 1) 2) = v.extractLsb' 0 64 := by
      rw [hv, stepValue]
      by_cases h0 : s = 0
      · rw [if_pos h0, if_pos h0, V3.reveal, if_neg hd, ClaudeWCT.W9.T3M.wctValueOff, if_pos hG]
        exact orig_lo hu as t 0 ht (by decide) (by decide)
      · rw [if_neg h0, if_neg h0, (ClaudeWCT.WCT9.ftsChainHigh_eq_true (i := t)
          (step := 4 - digits.getD t 0 + s - 1)).mpr ⟨ClaudeWCT.WCT9.ftsIsG_eq_true.mp hG, by omega⟩, SigGolfCandidate.T3.projHalf_true, extract_hh_lo]
        rfl
    have hhi : chainValue (originalValue L u index k j) as
        (if s = 0 then .original (ftsOff t + 8) else .answer ((digits.take t).sum + s - 1) 3) =
          v.extractLsb' 64 64 := by
      rw [hv, stepValue]
      by_cases h0 : s = 0
      · rw [if_pos h0, if_pos h0, V3.reveal, if_neg hd, ClaudeWCT.W9.T3M.wctValueOff, if_pos hG]
        exact orig_hi hu as t 0 ht (by decide) (by decide)
      · rw [if_neg h0, if_neg h0, (ClaudeWCT.WCT9.ftsChainHigh_eq_true (i := t)
          (step := 4 - digits.getD t 0 + s - 1)).mpr ⟨ClaudeWCT.WCT9.ftsIsG_eq_true.mp hG, by omega⟩, SigGolfCandidate.T3.projHalf_true, extract_hh_hi]
        rfl
    rw [if_pos hG, hA, hC, hB]
    simp only [chainQueryWords, hG, eq_self_iff_true, if_true, ↓reduceIte, List.map_cons, List.map_nil]
    rw [hlo, hhi, orig_lo hu as t 32 ht (by decide) (by decide),
      orig_lo hu as t 48 ht (by decide) (by decide),
      ← orig_hi hu as t 32 ht (by decide) (by decide), ← orig_hi hu as t 48 ht (by decide) (by decide)]
    rfl
  · -- F: `a | header | c | value`, every value is a low half
    have hF : ClaudeWCT.WCT9.ftsIsG t = false := by simpa using hG
    have hA : V3.chainPadA w k.val t = wdig w (V3.chainOffset k.val t + 0) := by
      simp only [V3.chainPadA, ClaudeWCT.W9.T3M.wctPad0Off, hF, Bool.false_eq_true, if_false, ↓reduceIte]
    have hC : V3.chainPadC w k.val t = wdig w (V3.chainOffset k.val t + 32) := by
      simp only [V3.chainPadC, ClaudeWCT.W9.T3M.wctPad1Off, hF, Bool.false_eq_true, if_false, ↓reduceIte]
    have hlo : chainValue (originalValue L u index k j) as
        (if s = 0 then .original (ftsOff t + 48) else .answer ((digits.take t).sum + s - 1) 0) =
          v.extractLsb' 0 64 := by
      rw [hv, stepValue]
      by_cases h0 : s = 0
      · rw [if_pos h0, if_pos h0, V3.reveal, if_neg hd, ClaudeWCT.W9.T3M.wctValueOff, if_neg hG]
        exact orig_lo hu as t 48 ht (by decide) (by decide)
      · rw [if_neg h0, if_neg h0, ClaudeWCT.WCT9.ftsChainHigh_of_F hF, SigGolfCandidate.T3.projHalf_false,
          extract_lo]
        rfl
    have hhi : chainValue (originalValue L u index k j) as
        (if s = 0 then .original (ftsOff t + 56) else .answer ((digits.take t).sum + s - 1) 1) =
          v.extractLsb' 64 64 := by
      rw [hv, stepValue]
      by_cases h0 : s = 0
      · rw [if_pos h0, if_pos h0, V3.reveal, if_neg hd, ClaudeWCT.W9.T3M.wctValueOff, if_neg hG]
        exact orig_hi hu as t 48 ht (by decide) (by decide)
      · rw [if_neg h0, if_neg h0, ClaudeWCT.WCT9.ftsChainHigh_of_F hF, SigGolfCandidate.T3.projHalf_false,
          extract_hi]
        rfl
    rw [if_neg hG, hA, hC, hB]
    simp only [chainQueryWords, hF, Bool.false_eq_true, if_false, ↓reduceIte, List.map_cons, List.map_nil]
    rw [hlo, hhi, ← orig_lo hu as t 0 ht (by decide) (by decide),
      ← orig_hi hu as t 0 ht (by decide) (by decide),
      ← orig_lo hu as t 32 ht (by decide) (by decide), ← orig_hi hu as t 32 ht (by decide) (by decide)]
    rfl
theorem sum_take_mono (l : List Nat) (a c : Nat) : (l.take a).sum ≤ (l.take (a + c)).sum := by
  induction c with
  | zero => exact le_refl _
  | succ c ih => rw [← Nat.add_assoc, sum_take_succ]; omega
theorem chain_cps {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u : MachineState} (hu : Pre L w index k j rank u) (digits : List Nat) (t : Nat) (ht : t < 6)
    (hd4 : digits.getD t 0 ≤ 4)
    {β : Type} (r : Nat) : ∀ (s : Nat) (as : List (BitVec 256)) (v : Digest)
      (K : List (BitVec 256) → M β) (Kv : Digest → M β),
    s + r = digits.getD t 0 → as.length = (digits.take t).sum + s →
    v = stepValue w k digits t s as →
    (∀ new : List (BitVec 256), new.length = r →
      K (as ++ new) = Kv (if r = 0 then v else SigGolfCandidate.T3.projHalf
        (ClaudeWCT.WCT9.ftsChainHigh t (4 - digits.getD t 0 + s + r - 1)) (new.getD (r - 1) 0))) →
    (traceProgram (originalValue L u index k j) ((List.range' s r).map (chainQueryWords digits t)) as
        >>= K) =
      ((List.range' (4 - digits.getD t 0 + s) r).foldlM
        (fun value step => SigGolfCandidate.T3.projHash (ClaudeWCT.WCT9.ftsChainHigh t step)
          (V3.chainInput index k.val j.val t step
            (V3.chainPadA w k.val t) (V3.chainPadB w k.val t) (V3.chainPadC w k.val t) value)) v
        >>= Kv) := by
  induction r with
  | zero =>
    intro s as v K Kv _ _ _ hK
    simp only [List.range'_zero, List.map_nil, traceProgram, List.foldlM_nil, pure_bind]
    simpa using hK [] rfl
  | succ r ih =>
    intro s as v K Kv hsr hlen hv hK
    rw [List.range'_succ, List.map_cons, List.range'_succ, List.foldlM_cons]
    simp only [traceProgram, bind_assoc]
    rw [query_bytes hu digits t s ht hd4 (by omega) as v hv, projHash_def, bind_assoc]
    simp only [pure_bind]
    refine congrArg (publicHash _ >>= ·) (funext fun ans => ?_)
    rw [show 4 - digits.getD t 0 + s + 1 = 4 - digits.getD t 0 + (s + 1) by omega]
    refine ih (s + 1) (as ++ [ans]) _ K Kv (by omega) (by simp [hlen]; omega) ?_ ?_
    · rw [stepValue, if_neg (by omega), show (digits.take t).sum + (s + 1) - 1 = as.length by omega,
        List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self,
        show 4 - digits.getD t 0 + (s + 1) - 1 = 4 - digits.getD t 0 + s by omega]
      rfl
    · intro new hnew
      rw [List.append_assoc, List.singleton_append, hK (ans :: new) (by simp [hnew])]
      congr 1
      cases r with
      | zero =>
        rw [if_pos rfl, if_neg (by omega), show 4 - digits.getD t 0 + s + (0 + 1) - 1 =
          4 - digits.getD t 0 + s by omega]
        rfl
      | succ r =>
        rw [if_neg (by omega), if_neg (by omega), show 4 - digits.getD t 0 + s + (r + 1 + 1) - 1 =
          4 - digits.getD t 0 + (s + 1) + (r + 1) - 1 by omega]
        rfl
def endOf (w : WBytes) (k : Fin 9) (digits : List Nat) (as : List (BitVec 256)) (t : Nat) :
    Digest :=
  if digits.getD t 0 = 0 then wdig w (V3.regionOffset k.val + V3.leafSlot t)
  else (as.getD ((digits.take (t + 1)).sum - 1) 0).extractLsb' 0 128
def chainProg (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (digits : List Nat) (t : Nat) :
    M Digest :=
  V3.chainP index k.val j.val t (4 - digits.getD t 0) (digits.getD t 0)
    (V3.chainPadA w k.val t) (V3.chainPadB w k.val t) (V3.chainPadC w k.val t)
    (V3.reveal w k.val t (digits.getD t 0))
def chainQs (digits : List Nat) (t : Nat) : List (List ChainWord) :=
  (List.range (digits.getD t 0)).map (chainQueryWords digits t)
theorem outer_cps {L : Layout} {w : WBytes} {index : Nat} {k : Fin 9} {j : Fin 128} {rank : Fin 666}
    {u : MachineState} (hu : Pre L w index k j rank u) (digits : List Nat)
    (hdig : ∀ t, t < 6 → digits.getD t 0 ≤ 4) (m : Nat) :
    ∀ (t : Nat) (as : List (BitVec 256)) (acc : List Digest),
    t + m = 6 → as.length = (digits.take t).sum → acc.length = t →
    (∀ i, i < t → acc.getD i 0 = endOf w k digits as i) →
    (traceProgram (originalValue L u index k j) ((List.range' t m).flatMap (chainQs digits)) as
        >>= fun as' => pure ((List.finRange 6).map fun i => endOf w k digits as' i.val)) =
      ((List.range' t m).mapM (chainProg w index k j digits) >>= fun vs => pure (acc ++ vs)) := by
  induction m with
  | zero =>
    intro t as acc htm hlen hacc hE
    simp only [List.range'_zero, List.flatMap_nil, traceProgram, pure_bind, List.mapM_nil,
      List.append_nil]
    congr 1
    apply List.ext_getElem
    · simp [hacc]; omega
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk]
      rw [← hE i (by omega), List.getD_eq_getElem _ _ h2]
  | succ m ih =>
    intro t as acc htm hlen hacc hE
    rw [List.range'_succ, List.flatMap_cons, List.mapM_cons, traceProgram_append, bind_assoc]
    simp only [bind_assoc, pure_bind]
    unfold chainQs chainProg
    rw [List.range_eq_range', V3.chainP]
    refine chain_cps hu digits t (by omega) (hdig t (by omega)) (digits.getD t 0) 0 as _ _ _ (by omega)
      (by simpa using hlen) (by simp [stepValue]) ?_
    intro new hnew
    rw [show 4 - digits.getD t 0 + 0 + digits.getD t 0 - 1 = 3 by have := hdig t (by omega); omega,
      ClaudeWCT.WCT9.ftsChainHigh_three, SigGolfCandidate.T3.projHalf_false]
    refine (ih (t + 1) (as ++ new) (acc ++ [if digits.getD t 0 = 0 then
        V3.reveal w k.val t (digits.getD t 0)
        else (new.getD (digits.getD t 0 - 1) 0).extractLsb' 0 128]) (by omega)
        (by rw [sum_take_succ]; simp [hlen, hnew]) (by simp [hacc]) ?_).trans ?_
    · intro i hi
      by_cases hit : i < t
      · rw [List.getD_append _ _ _ _ (by omega), hE i hit]
        unfold endOf
        split_ifs with hd
        · rfl
        · have h1 := sum_take_succ digits i
          have h2 := sum_take_mono digits (i + 1) (t - (i + 1))
          rw [show i + 1 + (t - (i + 1)) = t by omega] at h2
          rw [List.getD_append _ _ _ _ (by omega)]
      · have hit : i = t := by omega
        subst hit
        rw [List.getD_append_right _ _ _ _ (by omega), hacc, Nat.sub_self]
        unfold endOf
        split_ifs with hd
        · simp only [List.getD_cons_zero, V3.reveal, if_pos hd]
        · have h1 := sum_take_succ digits i
          rw [List.getD_append_right _ _ _ _ (by omega)]
          simp only [List.getD_cons_zero]
          congr 2
          omega
    · simp only [List.append_assoc, List.singleton_append]
      rfl
theorem sourceEquivalent : W9Machine.Chain.SourceEquivalent := by
  intro L w index k j rank u hu
  have h := outer_cps hu (ClaudeWCT.WCT9.codeword rank)
    (fun t ht => ClaudeWCT.WCT9.digit_le_four rank ⟨t, ht⟩) 6 0 [] [] rfl rfl rfl
    (fun i hi => absurd hi (Nat.not_lt_zero i))
  have hq : expectedQueries (ClaudeWCT.WCT9.codeword rank) =
      (List.range' 0 6).flatMap (chainQs (ClaudeWCT.WCT9.codeword rank)) := by
    rw [expectedQueries, List.range_eq_range']
    rfl
  have hp : program w index k j rank =
      (List.range' 0 6).mapM (chainProg w index k j (ClaudeWCT.WCT9.codeword rank)) := rfl
  rw [hq, hp]
  refine h.trans ?_
  simp only [List.nil_append, bind_pure]
end W9Machine.V3SourceEquiv
