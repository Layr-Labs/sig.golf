import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatchArith
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodOne

section
namespace SigGolfCandidate.T3M.Nonbinary
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def sourceWord (v : Digest) (q : Nat) : Word := if q<9 then v.extractLsb' 0 64 else v.extractLsb' 64 64
def sourceBit (q : Nat) : Nat := if q<9 then 7*q else 7*q-64
theorem extract_field (v : Digest) (a b : Nat) (h : b+7≤64) :
    (v.extractLsb' a 64).toNat/2^b%128=v.toNat/2^(a+b)%128 := by
  have hr := Search.ext_shr_mask v a b 7 h
  have hl : (v.extractLsb' a 64 >>> b) &&& 127#64=
      BitVec.ofNat 64 ((v.extractLsb' a 64).toNat/2^b%128) := by
    have he : v.extractLsb' a 64=BitVec.ofNat 64 (v.extractLsb' a 64).toNat := by
      apply BitVec.eq_of_toNat_eq; simp
    conv_lhs => rw [he]
    rw [ofNat_shr _ _ (v.extractLsb' a 64).isLt,Search.ofNat_and127]
  have hh := hl.symm.trans hr
  exact (ofNat_inj (by omega) (by omega)).mp hh
theorem source_field (v : Digest) (q : Nat) (hq : q<17) (h9 : q≠9) :
    (sourceWord v q).toNat/2^(sourceBit q)%128=Search.topRank v q := by
  unfold sourceWord sourceBit Search.topRank
  split_ifs with h
  · simpa using extract_field v 0 (7*q) (by omega)
  · rw [extract_field v 64 (7*q-64) (by omega),show 64+(7*q-64)=7*q by omega]
theorem sourceBit_lt (q : Nat) (hq : q<17) (h9 : q≠9) : sourceBit q+7 ≤ 64 := by
  unfold sourceBit; split_ifs <;> omega
def hiMask : Word := BitVec.ofNat 64 (2 ^ 64 - 2 ^ 55)
theorem field_xor_hiMask (X : Word) (b : Nat) (hb : b + 7 ≤ 55) :
    (X ^^^ hiMask).toNat / 2 ^ b % 128 = X.toNat / 2 ^ b % 128 := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [show (128 : Nat) = 2 ^ 7 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, BitVec.toNat_xor, Nat.testBit_xor]
  by_cases hj : j < 7
  · have hm : hiMask.toNat.testBit (j + b) = false := by
      unfold hiMask
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num),
        show (2 : Nat) ^ 64 - 2 ^ 55 = 2 ^ 55 * (2 ^ 9 - 1) by norm_num, Nat.testBit_two_pow_mul]
      simp; omega
    simp [hj, hm]
  · simp [hj]
theorem mod64_xor_hiMask (X : Word) : (X ^^^ hiMask).toNat % 64 = X.toNat % 64 := by
  have h := field_xor_hiMask X 0 (by decide +kernel)
  simp only [pow_zero, Nat.div_one] at h
  rw [← Nat.mod_mod_of_dvd (X ^^^ hiMask).toNat (show 64 ∣ 128 by decide +kernel), h,
    Nat.mod_mod_of_dvd _ (show 64 ∣ 128 by decide +kernel)]
theorem dispatch_step {p q : Nat} (hq : q<17) (h9 : q≠9) (hp : p<257181)
    (hrun : vrun p 5=some (dispatchR q)) (s : MachineState) (v : Digest)
    (hpc : s.pc=pcOf p) (h16 : s.getReg .x16= ~~~(v.extractLsb' 0 64))
    (h17 : s.getReg .x17= ~~~(v.extractLsb' 64 64) ^^^ hiMask) (h6 : s.getReg .x6=520192#64) :
    ∃t, Steps Images.verifyImage s 3 3 t ∧
      t.pc=BitVec.ofNat 64 (4096*(127-Search.topRank v q)+2^64+4*entOff q-4096) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hW : s.getReg (if q<9 then .x16 else .x17)= ~~~(sourceWord v q) ^^^ (if q<9 then 0 else hiMask) := by
    unfold sourceWord
    split_ifs
    · rw [h16]; exact BitVec.xor_zero.symm
    · exact h17
  have hb := sourceBit_lt q hq h9
  have hf : (~~~(sourceWord v q) ^^^ (if q<9 then 0 else hiMask)).toNat/2^(sourceBit q)%128 =
      (~~~(sourceWord v q)).toNat/2^(sourceBit q)%128 := by
    split_ifs with h
    · rw [show (~~~(sourceWord v q) ^^^ (0 : Word)) = ~~~(sourceWord v q) from BitVec.xor_zero]
    · apply field_xor_hiMask
      unfold sourceBit; rw [if_neg h]; omega
  refine ⟨(dispatchR q).toState s,piece_steps45 hrun hp s hpc (by simp [dispatchR]),?_,?_,?_⟩
  · change (((shift12 (if q<9 then .x16 else .x17) (sourceBit q)).eval s &&& s.getReg .x6)+
      BitVec.ofNat 64 (2^64+4*entOff q-4096)) &&& ~~~1#64=_
    rw [h6,shift12_eval s _ _ hW _ (by omega),dispatch_value _ _ q (by omega) hq,hf,not_field _ _ hb,
      source_field v q hq h9]
  · intro r hr
    rw [Result.toState_getReg]
    simp only [dispatchR]
    rw [RegFile.get_set_ne _ _ (show r≠.x14 by simpa using hr),RegFile.init_get_eval]
  · intro A _ _
    simp [dispatchR,rv_simp]
theorem dispatch9_step {p : Nat} (hp : p<257181)
    (hrun : vrun p 5=some dispatch9R) (s : MachineState) (v : Digest)
    (hpc : s.pc=pcOf p) (h17 : s.getReg .x17= ~~~(v.extractLsb' 64 64) ^^^ hiMask) (h6 : s.getReg .x6=520192#64) :
    ∃t, Steps Images.verifyImage s 3 3 t ∧
      t.pc=BitVec.ofNat 64 (8192*(63-v.toNat/2^64%64)+256) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨dispatch9R.toState s,piece_steps45 hrun hp s hpc (by simp [dispatch9R]),?_,?_,?_⟩
  · change (((s.getReg .x17 <<< (BitVec.ofNat 64 13).toNat) &&& s.getReg .x6)+256#64) &&& ~~~1#64=_
    rw [h6,h17,g9_value,mod64_xor_hiMask]
    congr 2
    have := not_field (v.extractLsb' 64 64) 0 (by decide +kernel)
    have e1 : (~~~(v.extractLsb' 64 64)).toNat%64=((~~~(v.extractLsb' 64 64)).toNat/2^0%128)%64 := by
      simp [Nat.mod_mod_of_dvd _ (show 64 ∣ 128 by decide +kernel)]
    have e2 : v.toNat/2^64%64=((v.extractLsb' 64 64).toNat/2^0%128)%64 := by
      rw [extract_field v 64 0 (by decide +kernel)]
      simp [Nat.mod_mod_of_dvd _ (show 64 ∣ 128 by decide +kernel)]
    rw [e1,e2,this]
    have hlt : (v.extractLsb' 64 64).toNat/2^0%128 < 128 := Nat.mod_lt _ (by decide +kernel)
    omega
  · intro r hr
    rw [Result.toState_getReg]
    simp only [dispatch9R]
    rw [RegFile.get_set_ne _ _ (show r≠.x14 by simpa using hr),RegFile.init_get_eval]
  · intro A _ _
    simp [dispatch9R,rv_simp]
theorem bge9_step (k : Nat) (hk : k<125) (he : k%2=0) (s : MachineState) (v : Digest)
    (hpc : s.pc=pcOf (cellW 9 k)) (h16 : s.getReg .x16= ~~~(v.extractLsb' 0 64)) :
    ∃t, Steps Images.verifyImage s 1 1 t ∧
      t.pc=(if v.toNat/2^63%2=1 then BitVec.ofNat 64 (0x1000+4*cellW 9 k-4096) else pcOf (cellW 9 k+1)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := bge9_at k hk he
  have hp : cellW 9 k<257181 := by unfold cellW entOff; simp; omega
  refine ⟨(bge9R (cellW 9 k)).toState s,piece_steps45 hrun hp s hpc (by simp [bge9R,SymState.init]),?_,?_,?_⟩
  · rw [Result.toState_pc]
    simp only [bge9R,E.eval,h16]
    have hb : v.getLsbD 63=decide (v.toNat/2^63%2=1) := by
      rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
    have hsign : CmpOp.eval .ge (~~~(v.extractLsb' 0 64)) 0=decide (v.toNat/2^63%2=1) := by
      have hz : (0 : BitVec 64)=0#64 := rfl
      simp only [CmpOp.eval]
      rw [hz, BitVec.slt_zero_eq_msb, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_not, BitVec.getLsbD_extractLsb', hb]
      simp
    rw [hsign]
    by_cases hb' : v.toNat/2^63%2=1 <;> simp [hb']
  · intro r _; rw [Result.toState_getReg]; simp [bge9R,SymState.init,RegFile.init_get_eval]
  · intro A _ _
    simp [bge9R,rv_simp,SymState.init]
theorem fault_top_fetch (q : Nat) (hq : q<17) (h8 : 8≤q) (s : MachineState)
    (hpc : s.pc=pcOf (entOff q)) : fetch vimage s=none := by
  have hw := fault_top_word q hq h8
  have hc := lcodeAt (entOff q) (by have := entOff_le q hq; omega)
  cases he : lcode (entOff q) with
  | nil => simp [he] at hw
  | cons w ws =>
    simp only [he, List.head?_cons, Option.some.injEq] at hw
    subst w
    rw [he] at hc
    exact hc.fetch s hpc
theorem fault_top126_fetch (q : Nat) (hq : q<17) (h8 : 8≤q) (he : 1024≤entOff q) (s : MachineState)
    (hpc : s.pc=pcOf (entOff q-1024)) : fetch vimage s=none := by
  have hw := fault_top126_word q hq h8 he
  have hc := lcodeAt (entOff q-1024) (by have := entOff_le q hq; omega)
  cases hx : lcode (entOff q-1024) with
  | nil => simp [hx] at hw
  | cons w ws =>
    simp only [hx, List.head?_cons, Option.some.injEq] at hw
    subst w
    rw [hx] at hc
    exact hc.fetch s hpc
#print axioms dispatch_step
#print axioms dispatch9_step
#print axioms bge9_step
/-! ### R6 dispatch landings (VER-A)
Machine-level facts for the R6 top region: zero-word guards fault; the dispatch into r6 group h (1..7) lands on
`cell6 h raw` (a cell for raw < 216, a guard otherwise); the prologue's g0 dispatch lands on the g0 column (a cell
for raw >= 40, otherwise a guard or outside the code); the checksum dispatch lands on an arm or a guard. -/
theorem fetch_zero_word {p : Nat} (hp : p < 257214) (hz : zeroAt p = true) (s : MachineState)
    (hpc : s.pc = pcOf p) : fetch vimage s = none := by
  have hw : (lcode p).head? = some 0#32 := by simpa [zeroAt] using hz
  have hc := lcodeAt p hp
  cases he : lcode p with
  | nil => simp [he] at hw
  | cons w ws =>
    simp only [he, List.head?_cons, Option.some.injEq] at hw
    subst w
    rw [he] at hc
    exact hc.fetch s hpc
theorem fetch_below (s : MachineState) (h : s.pc.toNat < 0x1000) : fetch vimage s = none := by
  unfold fetch; simp [h]
theorem fetch_above (s : MachineState) (h : 0x1000+4*257280 ≤ s.pc.toNat) : fetch vimage s = none := by
  have hl : vimage.code.length ≤ 257280 := verifyCode_length_le
  have hn : vimage.code[(s.pc.toNat-0x1000)/4]? = none :=
    List.getElem?_eq_none_iff.mpr (by omega)
  unfold fetch
  split
  · rfl
  · rw [hn]; rfl
theorem cell6_lt (g raw : Nat) (hg : g < 8) (hr : raw < 256) : cell6 g raw < 257214 := by
  unfold cell6 r6Off; split_ifs <;> omega
/-- r6 group `g`, field value `raw`: a valid raw lands on the cell of rank `raw - 40` (g = 0) or `raw`; an invalid
raw (g = 0: 3 <= raw < 40; g >= 1: raw >= 216) lands on a zero word. -/
theorem cell6_valid (g raw : Nat) (hg : g < 8) (hv : raw6Valid g raw = true) :
    cell6 g raw = cellW g (if g = 0 then raw - 40 else raw) := by
  unfold cellW rawOf6
  rw [if_pos hg]
  by_cases h0 : g = 0
  · subst h0
    simp only [raw6Valid, if_true, decide_eq_true_eq] at hv
    simp only [if_true]; congr 1; omega
  · simp [h0]
theorem mod64_field (X b : Nat) (hb : b + 8 ≤ 64) : X % 2^64 / 2^b % 256 = X / 2^b % 256 := by
  rw [show (2:Nat)^64 = 2^b * 2^(64-b) by rw [← pow_add]; congr 1; omega, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (show 256 ∣ 2^(64-b) from ⟨2^(64-b-8), by rw [show (256:Nat) = 2^8 by norm_num, ← pow_add]; congr 1; omega⟩)]
theorem lo_field (V : Digest) (b : Nat) (hb : b + 8 ≤ 64) :
    (V.extractLsb' 0 64).toNat / 2^b % 256 = V.toNat / 2^b % 256 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, mod64_field _ _ hb]
theorem hi_field (V : Digest) (b : Nat) (hb : b + 8 ≤ 64) :
    (V.extractLsb' 64 64).toNat / 2^b % 256 = V.toNat / 2^(64+b) % 256 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, mod64_field _ _ hb, Nat.div_div_eq_div_mul, ← pow_add]
theorem r6Src_mid (h : Nat) (h2 : 2 ≤ h) (h6 : h ≤ 6) (s : MachineState) :
    (r6Src h).eval s = s.getReg .x16 >>> (8*h-8) := by
  unfold r6Src; rw [if_neg (by omega), if_pos (by omega)]
  show s.getReg .x16 >>> ((BitVec.ofNat 64 (8*h-8)).toNat % 64) = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 8*h-8 < 2^64 by omega), Nat.mod_eq_of_lt (show 8*h-8 < 64 by omega)]
/-- The masked field of the dispatch into r6 group `h`: `256 raw`. -/
theorem r6Src_eval (h : Nat) (h1 : 1 ≤ h) (h7 : h ≤ 7) (V : Digest) (s : MachineState)
    (h16 : s.getReg .x16 = V.extractLsb' 0 64) (h17 : s.getReg .x17 = V.extractLsb' 64 64) :
    (r6Src h).eval s &&& 65280#64 = BitVec.ofNat 64 (256 * (V.toNat / 2^(r6Pos h) % 256)) := by
  by_cases e1 : h = 1
  · subst e1
    simp only [r6Src, if_true, E.eval, h16]; rw [word_ff00, lo_field V 8 (by omega)]; rfl
  by_cases e7 : h = 7
  · subst e7
    have hs : (r6Src 7).eval s = s.getReg .x17 >>> 47 := by
      unfold r6Src; rw [if_neg (by omega), if_neg (by omega)]; rfl
    rw [hs, h17, field_ff00, hi_field V 55 (by omega)]; rfl
  · rw [r6Src_mid h (by omega) (by omega) s, h16, field_ff00, lo_field V _ (by omega)]
    unfold r6Pos; rw [if_neg e7, show 8*h-8+8 = 8*h by omega]
theorem guard6_fault (g raw : Nat) (hg : g < 8) (hr : raw < 256) (hv : raw6Valid g raw = false)
    (h3 : g = 0 → 3 ≤ raw) (s : MachineState) (hpc : s.pc = pcOf (cell6 g raw)) : fetch vimage s = none := by
  have hc := guard6Check_at g raw hg hr
  unfold guard6Check at hc
  rw [hv, Bool.false_or] at hc
  have hz : zeroAt (cell6 g raw) = true := by
    by_cases h0 : g = 0
    · have := h3 h0; subst h0; simpa [show ¬ raw < 3 by omega] using hc
    · simpa [h0] using hc
  exact fetch_zero_word (cell6_lt g raw hg hr) hz s hpc
/-- `a4` of the dispatch into r6 group `h`. -/
theorem r6A_eval (h : Nat) (h1 : 1 ≤ h) (h7 : h ≤ 7) (V : Digest) (s : MachineState)
    (h16 : s.getReg .x16 = V.extractLsb' 0 64) (h17 : s.getReg .x17 = V.extractLsb' 64 64)
    (h29 : s.getReg .x29 = 65280#64) (h18 : s.getReg .x18 = 856064#64) :
    (r6A h).eval s = if h<4 then 856064#64 - BitVec.ofNat 64 (256 * (V.toNat / 2^(r6Pos h) % 256))
      else BitVec.ofNat 64 (256 * (V.toNat / 2^(r6Pos h) % 256)) + 856064#64 := by
  have hf := r6Src_eval h h1 h7 V s h16 h17
  unfold r6A
  split_ifs
  · show s.getReg .x18 - ((r6Src h).eval s &&& s.getReg .x29) = _
    rw [h18, h29, hf]
  · show ((r6Src h).eval s &&& s.getReg .x29) + s.getReg .x18 = _
    rw [h18, h29, hf]
/-- Dispatch into r6 group `h` (1..7): three or four instructions, then pc at the cell of the field value. -/
theorem r6_dispatch_pc (h : Nat) (h1 : 1 ≤ h) (h7 : h ≤ 7) (V : Digest) (s : MachineState)
    (h16 : s.getReg .x16 = V.extractLsb' 0 64) (h17 : s.getReg .x17 = V.extractLsb' 64 64)
    (h29 : s.getReg .x29 = 65280#64) (h18 : s.getReg .x18 = 856064#64) :
    (r6DispR h).pc.eval s = pcOf (cell6 h (V.toNat / 2^(r6Pos h) % 256)) := by
  have ha := r6A_eval h h1 h7 V s h16 h17 h29 h18
  have hr : V.toNat / 2^(r6Pos h) % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have ho := r6Off_lt h
  show ((r6A h).eval s + r6Imm h) &&& ~~~1#64 = _
  rw [ha, cell6_tab h _ h1 h7]
  unfold r6Imm
  split_ifs with hh
  · exact tabB_target _ _ hr ho
  · exact tabA_target _ _ hr ho
theorem r6_dispatch_step {p h : Nat} (h1 : 1 ≤ h) (h7 : h ≤ 7) (hp : p < 257181)
    (hrun : vrun p 5 = some (r6DispR h)) (s : MachineState) (V : Digest) (hpc : s.pc = pcOf p)
    (h16 : s.getReg .x16 = V.extractLsb' 0 64) (h17 : s.getReg .x17 = V.extractLsb' 64 64)
    (h29 : s.getReg .x29 = 65280#64) (h18 : s.getReg .x18 = 856064#64) :
    ∃ t, Steps Images.verifyImage s (r6DispR h).steps (r6DispR h).cycles t ∧
      t.pc = pcOf (cell6 h (V.toNat / 2^(r6Pos h) % 256)) ∧ RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨(r6DispR h).toState s, piece_steps45 hrun hp s hpc (by simp [r6DispR]), ?_, ?_, ?_⟩
  · rw [Result.toState_pc]; exact r6_dispatch_pc h h1 h7 V s h16 h17 h29 h18
  · intro r hr
    rw [Result.toState_getReg]
    simp only [r6DispR]
    rw [RegFile.get_set_ne _ _ (show r ≠ .x14 by simpa using hr), RegFile.init_get_eval]
  · intro A _ _
    simp [r6DispR, rv_simp]
/-- The checksum dispatch (end of group 16): pc at `ckWord ds` for `s8 = T - ds`, `ds <= 228`. -/
theorem ck_dispatch_step {p : Nat} (hp : p < 257181) (hrun : vrun p 5 = some ckDispR) (s : MachineState)
    (ds : Nat) (hd : ds ≤ 228) (hpc : s.pc = pcOf p)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 topT - BitVec.ofNat 64 ds) :
    ∃ t, Steps Images.verifyImage s 3 3 t ∧ t.pc = pcOf (ckWord ds) ∧ RegsExcept s t [.x14] ∧
      Frame s t (fun _ => False) := by
  refine ⟨ckDispR.toState s, piece_steps45 hrun hp s hpc (by simp [ckDispR]), ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    show ((((s.getReg .x24 + 89#64) <<< ((11#64).toNat % 64))) + 1168#64) &&& ~~~1#64 = _
    rw [h24]; exact ck_target ds hd
  · intro r hr
    rw [Result.toState_getReg]
    simp only [ckDispR]
    rw [RegFile.get_set_ne _ _ (show r ≠ .x14 by simpa using hr), RegFile.init_get_eval]
  · intro A _ _
    simp [ckDispR, rv_simp]
theorem ckWord_lt (ds : Nat) : ckWord ds < 257214 := by unfold ckWord topT; omega
/-- Checksum landing: an arm when `T - 7 <= ds <= T`, otherwise a zero word (fetch faults). -/
theorem ck_landing (ds : Nat) (hd : ds < 229) :
    (topT - 7 ≤ ds ∧ ds ≤ topT ∧ ckWord ds = ckArm (topT - ds)) ∨
      (∀ s : MachineState, s.pc = pcOf (ckWord ds) → fetch vimage s = none) := by
  by_cases h : topT - 7 ≤ ds ∧ ds ≤ topT
  · left; refine ⟨h.1, h.2, ?_⟩; unfold ckWord ckArm topT at *; omega
  · right; intro s hpc
    have hc := ckGuardCheck_at ds hd
    unfold ckGuardCheck at hc
    have hz : zeroAt (ckWord ds) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
      rcases hc with hc | hc
      · exact absurd hc h
      · exact hc
    exact fetch_zero_word (ckWord_lt ds) hz s hpc
/-- r6 group `h >= 1` landing: rank `raw < 216` at its cell, otherwise a zero-word guard. -/
theorem r6_landing (h raw : Nat) (h1 : 1 ≤ h) (h7 : h ≤ 7) (hr : raw < 256) :
    (raw < 216 ∧ cell6 h raw = cellW h raw) ∨
      (∀ s : MachineState, s.pc = pcOf (cell6 h raw) → fetch vimage s = none) := by
  by_cases hv : raw < 216
  · left; refine ⟨hv, ?_⟩
    have := cell6_valid h raw (by omega) (by simp [raw6Valid, show h ≠ 0 by omega, hv])
    simpa [show h ≠ 0 by omega] using this
  · right; intro s hpc
    exact guard6_fault h raw (by omega) hr (by simp [raw6Valid, show h ≠ 0 by omega, hv]) (by omega) s hpc
/-- g0 landing (prologue dispatch on `a6`): field value `raw >= 40` at the cell of rank `raw - 40`; every other
value faults (zero-word guards for 3 <= raw < 40, below the code for raw = 1, 2, above it for raw = 0). -/
theorem g0_landing (W : Word) (s : MachineState)
    (hpc : s.pc = (((W <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64) :
    (40 ≤ W.toNat % 256 ∧ s.pc = pcOf (cellW 0 (W.toNat % 256 - 40))) ∨ fetch vimage s = none := by
  have hr : W.toNat % 256 < 256 := Nat.mod_lt _ (by norm_num)
  by_cases h0 : W.toNat % 256 = 0
  · right; apply fetch_above; rw [hpc]; exact g0_target0 W h0
  rw [g0_target W _ rfl (by omega)] at hpc
  by_cases h3 : W.toNat % 256 < 3
  · right; apply fetch_below; rw [hpc]; exact g0_low _ h3
  rw [g0_cell _ (by omega)] at hpc
  by_cases h40 : 40 ≤ W.toNat % 256
  · left; refine ⟨h40, ?_⟩
    rw [hpc, cell6_valid 0 _ (by omega) (by simp [raw6Valid, h40])]; rfl
  · right
    exact guard6_fault 0 _ (by omega) hr (by simp [raw6Valid]; omega) (fun _ => by omega) s hpc
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
theorem next_inline (c : NCtx) (s0 : MachineState) (i : Nat) (hi : i<51) (h2 : i%3≠2)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) :
    c.ChainIn s0 (i+1) acc s := by
  obtain ⟨hB,hlen,hpc⟩ := hs
  refine ⟨hB,hlen,?_⟩
  rw [hpc]
  unfold endPc startPc
  rw [if_pos hi, if_pos (show i+1<51 by omega)]
  have e : (i+1)/3=i/3 := by omega
  by_cases h0 : i%3=0
  · rw [if_pos h0,if_neg (show (i+1)%3≠0 by omega),if_pos (show (i+1)%3=1 by omega)]
    unfold qB;rw [e]
  · rw [if_neg h0,if_pos (show i%3=1 by omega),if_neg (show (i+1)%3≠0 by omega),
      if_neg (show (i+1)%3≠1 by omega)]
    unfold qC;rw [e]
def chainF (c : NCtx) (ends : List Digest) (i : Nat) : M (List Digest) := do
  let v ← chainP 0 c.tree c.leaf i (c.dig i) (topMax i-c.dig i) (c.pad0 i) (c.pad1 i) (c.padHeader i) (c.bufferVal i)
  pure (ends++[v])
theorem group_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (q : Nat) (hq : q<17) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t,c.EndInv s0 (3*q+2) ends t → Verify.GoodQP P t N C Q A (K ends)) :
    ∀ k i, 3*q ≤ i → i+k = 3*q+3 → 0 < k → ∀ acc s, c.ChainIn s0 i acc s →
      Verify.GoodQP P s (N+40*k) (C+c.chainsCost i k) Q (A+c.chainsCost i k)
        (Verify.ccM ((List.range' i k).foldlM c.chainF acc) K) := by
  intro k
  induction k with
  | zero => intro i _ _ h;omega
  | succ k ih =>
    intro i hi hik _ acc s hs
    rw [List.range'_succ,List.foldlM_cons]
    simp only [chainF,bind_assoc,pure_bind,Verify.ccM_bind]
    have H := c.chain_good hc hds hk h0 i (by omega) acc
      (fun ends => Verify.ccM ((List.range' (i+1) k).foldlM c.chainF ends) K)
      (N+40*k) (C+c.chainsCost (i+1) k) (A+c.chainsCost (i+1) k) Q
      (fun v t ht => by
        by_cases hk0 : k=0
        · subst hk0
          have he : i=3*q+2 := by omega
          rw [he] at ht
          simpa [chainsCost] using hK _ t ht
        · have ht' : c.ChainIn s0 (i+1) (acc++[v]) t := c.next_inline s0 i (by omega) (by omega) (acc++[v]) t ht
          exact ih (i+1) (by omega) (by omega) (by omega) (acc++[v]) t ht') s hs
    refine H.mono (by omega) ?_ (fun hq => ⟨hq,?_⟩)
    · simp only [chainsCost,List.range'_succ,List.map_cons,List.sum_cons];omega
    · simp only [chainsCost,List.range'_succ,List.map_cons,List.sum_cons];omega
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def GroupIn (c : NCtx) (s0 : MachineState) (q : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (3*q)) acc s ∧ acc.length=3*q ∧ s.pc=pcOf (c.entPc q)
theorem fetch_fault (s : MachineState) (h : s.pc.toNat<0x1000) : fetch vimage s=none := by
  unfold fetch; simp [h]
theorem fetch_high (s : MachineState) (h : 0x1000+4*257280 ≤ s.pc.toNat) : fetch vimage s=none := by
  have hl : vimage.code.length ≤ 257280 := verifyCode_length_le
  have hn : vimage.code[(s.pc.toNat-0x1000)/4]?=none :=
    List.getElem?_eq_none_iff.mpr (by omega)
  unfold fetch
  split
  · rfl
  · rw [hn]; rfl
theorem fetch_outside (s : MachineState)
    (h : s.pc.toNat<0x1000 ∨ 0x1000+4*257280 ≤ s.pc.toNat) : fetch vimage s=none := by
  rcases h with h|h
  · exact fetch_fault s h
  · exact fetch_high s h
theorem topRank_lt (v : Digest) (q : Nat) : Search.topRank v q<128 := by
  unfold Search.topRank; omega
theorem topRank9 (v : Digest) : Search.topRank v 9=v.toNat/2^63%2+2*(v.toNat/2^64%64) := by
  unfold Search.topRank
  rw [show 7*9=63 from rfl]
  have h : v.toNat/2^64=v.toNat/2^63/2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
  rw [h]; omega
/-- Theoretical reverse checksum after all digits of groups `0..q`, including digit 53 at `q = 17`. -/
def s8v (c : NCtx) (q : Nat) : Word := BitVec.ofNat 64 topT-BitVec.ofNat 64 (((List.range (3*q+3)).map c.dig).sum)
def set24 (b : MachineState) (x : Word) : MachineState := b.setReg .x24 x
theorem set24_regs (b : MachineState) (x : Word) (r : Reg) (hr : r≠.x24) : (set24 b x).getReg r=b.getReg r := by
  unfold set24
  rw [setReg_of_ne b _ (by decide +kernel)]
  cases r <;> simp_all [MachineState.getReg]
theorem set24_24 (b : MachineState) (x : Word) : (set24 b x).getReg .x24=x := by
  unfold set24
  rw [setReg_of_ne b _ (by decide +kernel)]
  rfl
theorem set24_mem (b : MachineState) (x : Word) (a : Word) : (set24 b x).getMem a=b.getMem a := rfl
theorem set24_known (c : NCtx) {b : MachineState} (x : Word) (hk : ∀p∈c.known,b.getReg p.1=p.2) :
    ∀p∈c.known,(set24 b x).getReg p.1=p.2 := by
  intro p hp
  have hn : ∀ p ∈ c.known, p.1 ≠ .x24 := by simp [known]
  rw [set24_regs _ _ _ (hn p hp)]
  exact hk p hp
theorem set24_orig (c : NCtx) {b : MachineState} (x : Word) (h0 : c.Orig0 b) : c.Orig0 (set24 b x) :=
  ⟨⟨fun i hi k hk => h0.1.1 i hi k hk,fun i hi k hk => h0.1.2 i hi k hk⟩, h0.2.congr (fun A _ _ => set24_mem b x _)⟩
theorem sum_range_three (f : Nat → Nat) (n : Nat) :
    ((List.range (n+3)).map f).sum=((List.range n).map f).sum+(f n+f (n+1)+f (n+2)) := by
  simp only [List.range_succ,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega
theorem kss_kOf (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) :
    kss q (c.kOf q)=c.dig (3*q)+c.dig (3*q+1)+c.dig (3*q+2) := by
  obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds q (by omega)
  simp only [kss,k1,k2,k3]
theorem s8v_succ (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<16) :
    c.s8v q+(-BitVec.ofNat 64 (kss (q+1) (c.kOf (q+1))))=c.s8v (q+1) := by
  have hS : ((List.range (3*(q+1)+3)).map c.dig).sum =
      ((List.range (3*q+3)).map c.dig).sum+kss (q+1) (c.kOf (q+1)) := by
    rw [c.kss_kOf hds (q+1) (by omega),show 3*(q+1)+3=(3*q+3)+3 by ring,sum_range_three]
    simp only [show 3*(q+1)=3*q+3 by ring]
  unfold s8v
  rw [hS,BitVec.ofNat_add]
  simp only [BitVec.sub_eq_add_neg,BitVec.neg_add]
  ac_rfl
/-- Entry words (and the lead after them) of every top group lie in the code. -/
theorem entW_lt (q k : Nat) (hq : q < 17) (hk : k < (mx q+1)^3) : entW q k + 1 < 257181 := by
  have he := entOff_le q hq
  by_cases h8 : q < 8
  · simp only [mx, h8, if_true] at hk
    unfold entW cellW cell6 rawOf6 r6Off; simp only [h8, if_true]
    split_ifs <;> omega
  · simp only [mx, h8, if_false, show q < 17 from hq, if_true] at hk
    unfold entW cellW; simp only [h8, if_false, hq, if_true]
    split_ifs <;> omega
theorem entry_step (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {b : MachineState} (q : Nat) (hq : q<16)
    (h24 : b.getReg .x24=c.s8v q) (acc : List Digest) (s : MachineState) (hs : c.GroupIn b (q+1) acc s) :
    ∃t,Steps vimage s 1 1 t ∧ c.ChainIn (set24 b (c.s8v (q+1))) (3*(q+1)) acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hfacts := c.groupFacts hds (q+1) (by omega)
  have hchk := s8Run_at (q+1) (c.kOf (q+1)) (by omega) (c.kOf_lt hds (q+1) (by omega))
  rw [if_neg (show q+1≠0 by omega)] at hchk
  have hrun := rOK_eq hchk
  have hp : entW (q+1) (c.kOf (q+1))<257181 := by
    have := entW_lt (q+1) (c.kOf (q+1)) (by omega) (c.kOf_lt hds (q+1) (by omega)); omega
  have hst := piece_steps45 hrun hp s hpc (by simp [s8R])
  set r := s8R (kss (q+1) (c.kOf (q+1))) (entW (q+1) (c.kOf (q+1))) with hr
  have h24s : s.getReg .x24=c.s8v q := (hR .x24 (by decide +kernel)).trans h24
  refine ⟨r.toState s,hst,⟨⟨fun x hx => ?_,fun A hA hn => ?_,fun j hj => ?_⟩,hlen,?_⟩⟩
  · rw [Result.toState_getReg]
    by_cases hx : x=.x24
    · subst x
      simp only [hr,s8R]
      rw [RegFile.get_set_self _ _ (by decide +kernel),addC_eval,set24_24]
      simp only [E.eval,h24s]
      exact c.s8v_succ hds q hq
    · simp only [hr,s8R]
      rw [RegFile.get_set_ne _ _ hx,RegFile.init_get_eval,set24_regs _ _ _ hx]
      exact hR x (by assumption)
  · rw [Result.toState_getMem,set24_mem]
    simp only [hr,s8R]
    rw [memEval_nil]
    exact hF A hA hn
  · have hfr : Frame s (r.toState s) (fun _ => False) := fun A _ _ => by
      rw [Result.toState_getMem]; simp [hr,s8R,memEval_nil]
    exact (hS j hj).frame hfr (by unfold slot; omega) (by simp) (by simp)
  · rw [Result.toState_pc]
    simp only [hr,s8R,E.eval]
    unfold startPc leadPc leadOff
    simp only [show 3*(q+1)<51 by omega,show 3*(q+1)%3=0 by omega,if_true,show 3*(q+1)/3=q+1 by omega,show q+1≠0 by omega,if_false]
/-- Reverse checksum `topT - (d_0 + ... + d_(n-1))` (the checksum dispatch reads it at `n = 51`). -/
def s8w (c : NCtx) (n : Nat) : Word := BitVec.ofNat 64 topT-BitVec.ofNat 64 (((List.range n).map c.dig).sum)
theorem s8v_eq (c : NCtx) (q : Nat) : c.s8v q=c.s8w (3*q+3) := rfl
theorem sum_range_add (f : Nat → Nat) (n k : Nat) :
    ((List.range (n+k)).map f).sum = ((List.range n).map f).sum + ((List.range' n k).map f).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, List.range_succ, List.map_append, List.sum_append, ih, List.range'_concat]
    simp; omega
theorem s8w_add (c : NCtx) (n k : Nat) :
    c.s8w n+(-BitVec.ofNat 64 (((List.range' n k).map c.dig).sum))=c.s8w (n+k) := by
  unfold s8w
  rw [sum_range_add, BitVec.ofNat_add]
  simp only [BitVec.sub_eq_add_neg,BitVec.neg_add]
  ac_rfl
/-! ### R6 group transitions (VER-A) -/
/-- R6 register invariants of the top region: the selected half `V` in a6/a7, the r6 mask t4 = 0xFF00, the table
base s2 = 856064, the r5 mask t1 = 0x7F000. -/
structure Encoded6 (V : Digest) (s : MachineState) : Prop where
  lo : s.getReg .x16 = V.extractLsb' 0 64
  hi : s.getReg .x17 = V.extractLsb' 64 64
  mask6 : s.getReg .x29 = 65280#64
  base6 : s.getReg .x18 = 856064#64
  mask5 : s.getReg .x6 = 520192#64
/-- The 8-bit field of r6 group `h` (1..7) in the selected half. -/
def raw6Of (V : Digest) (h : Nat) : Nat := V.toNat / 2^(r6Pos h) % 256
theorem gX_r6_lt (q k : Nat) (hq : q < 8) : gX q k < 257181 := by
  have hn : rowInl q k = false := by simp [rowInl, inl]; omega
  have hm : mx q = 5 := by simp [mx, hq]
  have hb := base_lt q (kdig q k 1) (kdig q k 2)
  have p1 := partLen_le q (kdig q k 1)
  have p2 := partLen_le q (kdig q k 2)
  simp only [gX, gC, gB, gbase, hn, if_pos hq, Bool.false_eq_true, if_false, hm]
  split_ifs <;> omega
/-- End of r6 group `q < 7` (chain 3q+2 done): the dispatch into group `q+1` reaches its cell (valid field) or
faults (invalid field). -/
def DispOut6 (c : NCtx) (s0 : MachineState) (V : Digest) (q : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  (raw6Of V (q+1) < 216 → ∃ t, Steps vimage s (r6DispR (q+1)).steps (r6DispR (q+1)).cycles t ∧
      c.Base s0 (c.Wr (3*(q+1))) acc t ∧ acc.length = 3*(q+1) ∧ t.pc = pcOf (entW (q+1) (raw6Of V (q+1)))) ∧
  (216 ≤ raw6Of V (q+1) → ∃ t, Steps vimage s (r6DispR (q+1)).steps (r6DispR (q+1)).cycles t ∧
      fetch vimage t = none)
theorem end_dispatch6 (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded6 V s0) (q : Nat) (hq : q < 7) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 (3*q+2) acc s) : c.DispOut6 s0 V q acc s := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hr : vrun (gX q (c.kOf q)) 5 = some (r6DispR (q+1)) := by
    have := (c.groupFacts hds q (by omega)).disp (by omega)
    simpa [nextDispR, hq] using this
  have hpc' : s.pc = pcOf (gX q (c.kOf q)) := by
    rw [hpc]; simp [endPc, qX, show 3*q+2 < 51 by omega, show (3*q+2)%3 = 2 by omega, show (3*q+2)/3 = q by omega]
  have hbound := gX_r6_lt q (c.kOf q) (by omega)
  have h16 : s.getReg .x16 = V.extractLsb' 0 64 := (hR _ (by decide +kernel)).trans he.lo
  have h17 : s.getReg .x17 = V.extractLsb' 64 64 := (hR _ (by decide +kernel)).trans he.hi
  have h29 : s.getReg .x29 = 65280#64 := (hR _ (by decide +kernel)).trans he.mask6
  have h18 : s.getReg .x18 = 856064#64 := (hR _ (by decide +kernel)).trans he.base6
  obtain ⟨t, st, pt, rt, ft⟩ := r6_dispatch_step (h := q+1) (by omega) (by omega) hbound hr s V hpc' h16 h17 h29 h18
  have base_of : c.Base s0 (c.Wr (3*(q+1))) acc t := by
    refine ⟨fun x hx => ?_, (hF.trans ft).mono (by intro A hA h; rcases h with h|h; simpa only [show 3*q+2+1=3*(q+1) by omega] using h; contradiction), fun j hj => ?_⟩
    · rw [rt.get (by intro h; simp only [List.mem_singleton] at h; subst x; exact hx (by decide +kernel))]
      exact hR x hx
    · exact (hS j hj).frame ft (by unfold slot; omega) (by simp) (by simp)
  have hraw : V.toNat / 2^(r6Pos (q+1)) % 256 < 256 := Nat.mod_lt _ (by norm_num)
  refine ⟨fun hv => ⟨t, st, base_of, by omega, ?_⟩, fun hv => ⟨t, st, ?_⟩⟩
  · have hcell := cell6_valid (q+1) (V.toNat / 2^(r6Pos (q+1)) % 256) (by omega)
      (by simp only [raw6Valid, show q+1 ≠ 0 by omega, if_false, decide_eq_true_eq]; unfold raw6Of at hv; exact hv)
    rw [pt, hcell]; unfold entW raw6Of; simp [show q ≠ 8 by omega, show q+1 ≠ 0 by omega]
  · exact guard6_fault (q+1) _ (by omega) hraw
      (by simp only [raw6Valid, show q+1 ≠ 0 by omega, if_false, decide_eq_false_iff_not]; unfold raw6Of at hv; omega)
      (by omega) t pt
theorem gX5_all : (List.range' 8 9).all (fun q => (List.range 125).all (fun k => decide (gX q k < 257181))) = true := by
  decide +kernel
theorem gX5_lt (q k : Nat) (h8 : 8 ≤ q) (hq : q < 17) (hk : k < 125) : gX q k < 257181 := by
  have h1 := List.all_eq_true.mp gX5_all q (List.mem_range'_1.mpr ⟨h8, by omega⟩)
  have := List.all_eq_true.mp h1 k (List.mem_range.mpr hk)
  simpa using this
theorem gX16_lt (k : Nat) (hk : k < 125) : gX 16 k < 257181 := gX5_lt 16 k (by omega) (by omega) hk
theorem data_sum_le (c : NCtx) (hds : c.DigitsOk) : ((List.range 51).map c.dig).sum ≤ 228 := by
  have h : ∀ n, n ≤ 51 → ((List.range n).map c.dig).sum ≤ ((List.range n).map topMax).sum := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
      have h1 := hds n (by omega)
      have h2 := ih (by omega)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
  have h2 : ((List.range 51).map topMax).sum = 228 := by decide +kernel
  exact (h 51 le_rfl).trans h2.le
/-- A dispatch (only x14 written, no memory written) keeps the chain-loop base invariant. -/
theorem base_disp (c : NCtx) {s0 s t : MachineState} {acc : List Digest} {W : Nat → Prop}
    (hl : acc.length ≤ 54) (hB : c.Base s0 W acc s) (rt : RegsExcept s t [.x14])
    (ft : Frame s t (fun _ => False)) : c.Base s0 W acc t := by
  obtain ⟨hR, hF, hS⟩ := hB
  refine ⟨fun x hx => ?_, (hF.trans ft).mono (by intro A hA h; rcases h with h|h; exact h; contradiction), fun j hj => ?_⟩
  · rw [rt.get (by intro h; simp only [List.mem_singleton] at h; subst x; exact hx (by decide +kernel))]
    exact hR x hx
  · exact (hS j hj).frame ft (by unfold slot; omega) (by simp) (by simp)
/-- End of group 16 (chain 50 done, s8 = T - data sum): the checksum dispatch reaches chain 51's arm for digit
`T - ds` when that lies in 0..7, otherwise it faults. -/
theorem end_ck (c : NCtx) (hds : c.DigitsOk) {s0 : MachineState} (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 50 acc s) (ds : Nat) (hdsum : ((List.range 51).map c.dig).sum = ds)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 topT - BitVec.ofNat 64 ds) :
    (topT - 7 ≤ ds ∧ ds ≤ topT → ∃ t, Steps vimage s 3 3 t ∧ c.Base s0 (c.Wr (50+1)) acc t ∧ acc.length = 50+1 ∧
        t.pc = pcOf (ckArm (topT - ds))) ∧
      (¬ (topT - 7 ≤ ds ∧ ds ≤ topT) → ∃ t, Steps vimage s 3 3 t ∧ fetch vimage t = none) := by
  obtain ⟨hB, hlen, hpc⟩ := hs
  have hk := c.kOf_lt hds 16 (by omega)
  have hk' : c.kOf 16 < 125 := by simpa [mx] using hk
  have hr : vrun (gX 16 (c.kOf 16)) 5 = some ckDispR := by
    have := (c.groupFacts hds 16 (by omega)).disp (by omega)
    simpa [nextDispR] using this
  have hpc' : s.pc = pcOf (gX 16 (c.kOf 16)) := by
    rw [hpc]; unfold endPc; rw [if_pos (by decide), if_neg (by decide), if_neg (by decide)]; rfl
  have hd : ds ≤ 228 := hdsum ▸ c.data_sum_le hds
  obtain ⟨t, st, pt, rt, ft⟩ := ck_dispatch_step (gX16_lt _ hk') hr s ds hd hpc' h24
  have base_of : c.Base s0 (c.Wr (50+1)) acc t := c.base_disp (by omega) hB rt ft
  refine ⟨fun hv => ⟨t, st, base_of, hlen, ?_⟩, fun hv => ⟨t, st, ?_⟩⟩
  · have hw : ckWord ds = ckArm (topT - ds) := by unfold ckWord ckArm topT at *; omega
    rw [pt, hw]
  · rcases ck_landing ds (by omega) with ⟨h1, h2, -⟩ | hf
    · exact absurd ⟨h1, h2⟩ hv
    · exact hf t pt
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
/-! ### R6 top word at the machine (VER-A, round 2)
The selected half `V` sits in a6/a7 unflipped (`Encoded6`). The r6 groups read `T3.r6Raw V g` directly (the
`topMask` flip only touches bits 56..118); the r5 groups 8..16 run main's dispatch code, which sees the word
`r5V V = V ^^^ (2^119 - 1)` in main's `Encoded` convention, whose `Search.topRank` is `T3.r5Rank V`. -/
section
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
/-- The r5 groups' view of the selected half (main's `Encoded` word). -/
def r5V (V : Digest) : Digest := V ^^^ BitVec.ofNat 128 (2^119-1)
theorem r5V_lo (V : Digest) : ~~~((r5V V).extractLsb' 0 64) = V.extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [r5V, BitVec.getLsbD_not, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one, hj, Nat.zero_add]
  have h1 : j < 128 := by omega
  have h2 : j < 119 := by omega
  simp [h1, h2]
theorem hiMask_bit (j : Nat) (hj : j < 64) : hiMask.getLsbD j = decide (55 ≤ j) := by
  unfold hiMask
  rw [BitVec.getLsbD_ofNat, show (2:Nat)^64-2^55=2^55*(2^9-1) by norm_num, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one]
  by_cases h : 55 ≤ j
  · simp [h, hj]; omega
  · simp [h]
theorem r5V_hi (V : Digest) : ~~~((r5V V).extractLsb' 64 64) ^^^ hiMask = V.extractLsb' 64 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_xor, hiMask_bit j hj, r5V, BitVec.getLsbD_not, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, hj]
  have h1 : 64 + j < 128 := by omega
  by_cases h : 55 ≤ j
  · have h2 : ¬ 64 + j < 119 := by omega
    simp [h, h1, h2]
  · have h2 : 64 + j < 119 := by omega
    simp [h, h1, h2]
theorem nat_field_eq (X Y b : Nat) (n : Nat) (h : ∀ j, j < n → X.testBit (j+b) = Y.testBit (j+b)) :
    X / 2^b % 2^n = Y / 2^b % 2^n := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < n
  · simp [hj, h j hj]
  · simp [hj]
/-- The 7-bit field of r5 group `q` (bits 7q..7q+6, inside 56..118) under main's word is the spec rank. -/
theorem topRank_r5V (V : Digest) (q : Nat) (h8 : 8 ≤ q) (hq : q < 17) :
    Search.topRank (r5V V) q = T3.r5Rank V q := by
  unfold Search.topRank T3.r5Rank T3.topCode T3.topFlip r5V
  have e := nat_field_eq (V ^^^ BitVec.ofNat 128 (2^119-1)).toNat (V ^^^ BitVec.ofNat 128 T3.topMask).toNat (7*q) 7
    (by
      intro j hj
      rw [BitVec.toNat_xor, BitVec.toNat_xor, Nat.testBit_xor, Nat.testBit_xor]
      have e1 : (BitVec.ofNat 128 (2^119-1)).toNat.testBit (j + 7*q) = true := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), Nat.testBit_two_pow_sub_one]; simp; omega
      have e2 : (BitVec.ofNat 128 T3.topMask).toNat.testBit (j + 7*q) = true := by
        unfold T3.topMask
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), show (2:Nat)^119-2^56 = 2^56*(2^63-1) by norm_num,
          Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
        simp; omega
      rw [e1, e2])
  simpa using e
/-- Bits outside 56..118 of the spec word `topCode V` are the bits of `V`. -/
theorem topCode_field (V : Digest) (b n : Nat) (h : b + n ≤ 56 ∨ 119 ≤ b) :
    T3.topCode V / 2^b % 2^n = V.toNat / 2^b % 2^n := by
  unfold T3.topCode T3.topFlip
  apply nat_field_eq
  intro j hj
  rw [BitVec.toNat_xor, Nat.testBit_xor]
  have e : (BitVec.ofNat 128 T3.topMask).toNat.testBit (j + b) = false := by
    unfold T3.topMask
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), show (2:Nat)^119-2^56 = 2^56*(2^63-1) by norm_num,
      Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
    simp; omega
  rw [e]; simp
theorem r6Shift_eq (g : Nat) : T3.r6Shift g = r6Pos g := rfl
/-- The 8-bit field of r6 group `g` is read from `V` itself (no flip). -/
theorem r6Raw_eq (V : Digest) (g : Nat) (hg : g < 8) : T3.r6Raw V g = V.toNat / 2^(r6Pos g) % 256 := by
  unfold T3.r6Raw
  rw [r6Shift_eq, show (256:Nat) = 2^8 by norm_num]
  apply topCode_field
  unfold r6Pos; split_ifs <;> omega
/-- The spare bit is bit 127 of `V`. -/
theorem topSpare_eq (V : Digest) : T3.topSpare V = V.toNat / 2^127 % 2 := by
  unfold T3.topSpare
  rw [show (2:Nat) = 2^1 by norm_num]
  exact topCode_field V 127 1 (Or.inr (by omega))
theorem raw6Of_eq (V : Digest) (h : Nat) (hh : h < 8) : NCtx.raw6Of V h = T3.r6Raw V h := (r6Raw_eq V h hh).symm
/-- g0's field (the low byte of a6). -/
theorem g0_raw (V : Digest) : (V.extractLsb' 0 64).toNat % 256 = T3.r6Raw V 0 := by
  rw [r6Raw_eq V 0 (by omega)]
  have := lo_field V 0 (by omega)
  simpa [r6Pos] using this
/-! #### Spare-bit reject: the 128 `blt a7,zero,+32` sites (word `h+13` of the top copy at `h = 1064 + 1024 c`)
jump to the zero word `h+21` (fetch faults). -/
theorem spare_zero_all : (List.range 128).all (fun c => zeroAt (1085 + 1024*c)) = true := by decide +kernel
theorem spare_fault (c : Nat) (hc : c < 128) (s : MachineState) (hpc : s.pc = pcOf (1085 + 1024*c)) :
    fetch vimage s = none := by
  have hz := List.all_eq_true.mp spare_zero_all c (List.mem_range.mpr hc)
  exact fetch_zero_word (by omega) hz s hpc
theorem spare_target (h : Nat) (hh : h < 2^60) : pcOf (h+13) + 32#64 = pcOf (h+21) := by
  unfold pcOf; rw [BitVec.ofNat_add_ofNat]; congr 1
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
/-- R6 validity of top group `q < 17` (the range check its dispatch performs). -/
def gValid (V : Digest) (q : Nat) : Prop := if q < 8 then T3.r6Valid V q = true else T3.r5Rank V q < 125
instance (V : Digest) (q : Nat) : Decidable (gValid V q) := by unfold gValid; infer_instance
/-- R6 rank of top group `q < 17`. -/
def gRank (V : Digest) (q : Nat) : Nat := if q < 8 then T3.r6Rank V q else T3.r5Rank V q
/-- Steps from the end of group `j - 1` (its dispatch word) to the entry word of group `j`. -/
def dspR6 (j : Nat) : Nat := if j = 1 then 3 else if j < 8 then 4 else if j = 9 then 4 else 3
theorem dspR6_le (j : Nat) : dspR6 j ≤ 4 := by unfold dspR6; split_ifs <;> omega
theorem r6DispR_steps (h : Nat) (h7 : h < 8) : (r6DispR h).steps = dspR6 h ∧ (r6DispR h).cycles = dspR6 h := by
  unfold r6DispR dspR6
  by_cases h1 : h = 1 <;> simp [h1, h7]
theorem gValid_r6 (V : Digest) (h : Nat) (h1 : 1 ≤ h) (h7 : h < 8) : gValid V h ↔ raw6Of V h < 216 := by
  unfold gValid T3.r6Valid; rw [raw6Of_eq V h h7]; simp [h7, show h ≠ 0 by omega]
theorem gRank_r6 (V : Digest) (h : Nat) (h1 : 1 ≤ h) (h7 : h < 8) : gRank V h = raw6Of V h := by
  unfold gRank T3.r6Rank; rw [raw6Of_eq V h h7]; simp [h7, show h ≠ 0 by omega]
theorem gValid_r5 (V : Digest) (q : Nat) (h8 : 8 ≤ q) : gValid V q ↔ T3.r5Rank V q < 125 := by
  unfold gValid; simp [show ¬ q < 8 by omega]
theorem gRank_r5 (V : Digest) (q : Nat) (h8 : 8 ≤ q) : gRank V q = T3.r5Rank V q := by
  unfold gRank; simp [show ¬ q < 8 by omega]
theorem gValid_g0 (V : Digest) : gValid V 0 ↔ 40 ≤ T3.r6Raw V 0 := by
  unfold gValid T3.r6Valid; simp
theorem gRank_g0 (V : Digest) : gRank V 0 = T3.r6Raw V 0 - 40 := by
  unfold gRank T3.r6Rank; simp
/-- Valid top words (spare bit 0, every group in range) in the dispatch's terms. -/
theorem topRanksValid_iff (V : Digest) :
    T3.topRanksValid V = true ↔ V.toNat / 2^127 % 2 = 0 ∧ ∀ q, q < 17 → gValid V q := by
  simp only [T3.topRanksValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.mem_range'_1, topSpare_eq]
  constructor
  · rintro ⟨⟨hs, h6⟩, h5⟩
    refine ⟨hs, fun q hq => ?_⟩
    unfold gValid; split_ifs with h8
    · exact h6 q h8
    · exact h5 q ⟨by omega, by omega⟩
  · rintro ⟨hs, hg⟩
    refine ⟨⟨hs, fun q hq => ?_⟩, fun q hq => ?_⟩
    · have := hg q (by omega); unfold gValid at this; simpa [hq] using this
    · have := hg q (by omega); unfold gValid at this; simpa [show ¬ q < 8 by omega] using this
/-- End of top group `q < 16`: the dispatch into group `q+1` reaches its entry word (valid field) or faults. -/
def DispOutR6 (c : NCtx) (s0 : MachineState) (V : Digest) (q : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  (gValid V (q+1) → ∃ t, Steps vimage s (dspR6 (q+1)) (dspR6 (q+1)) t ∧
      c.Base s0 (c.Wr (3*(q+1))) acc t ∧ acc.length = 3*(q+1) ∧ t.pc = pcOf (entW (q+1) (gRank V (q+1)))) ∧
  (¬ gValid V (q+1) → ∃ k t, Steps vimage s k k t ∧ k ≤ 5 ∧ fetch vimage t = none)
/-- R6 r5 transitions: end of group `q` (7 <= q < 16) into r5 group `q+1` (main's dispatch code on `r5V V`). -/
theorem end_dispatch5 (c : NCtx) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded6 V s0) (q : Nat) (h7 : 7 ≤ q) (hq : q < 16) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 (3*q+2) acc s) : c.DispOutR6 s0 V q acc s := by
  obtain ⟨hB, hlen, hpc⟩ := hs
  have hR := hB.1
  have hr : vrun (gX q (c.kOf q)) 5 = some (nextDispR q) := (c.groupFacts hds q (by omega)).disp (by omega)
  have hpc' : s.pc = pcOf (gX q (c.kOf q)) := by
    rw [hpc]; simp [endPc, qX, show 3*q+2 < 51 by omega, show (3*q+2)%3 = 2 by omega, show (3*q+2)/3 = q by omega]
  have hbound : gX q (c.kOf q) < 257181 := by
    by_cases h8 : q < 8
    · exact gX_r6_lt q _ h8
    · have hk := c.kOf_lt hds q (by omega)
      have hm : mx q = 4 := by simp [mx, h8, show q < 17 by omega]
      rw [hm] at hk
      exact gX5_lt q _ (by omega) (by omega) (by norm_num at hk; omega)
  have h16 : s.getReg .x16 = ~~~((r5V V).extractLsb' 0 64) := by
    rw [r5V_lo]; exact (hR _ (by decide +kernel)).trans he.lo
  have h17 : s.getReg .x17 = ~~~((r5V V).extractLsb' 64 64) ^^^ hiMask := by
    rw [r5V_hi]; exact (hR _ (by decide +kernel)).trans he.hi
  have h6 : s.getReg .x6 = 520192#64 := (hR _ (by decide +kernel)).trans he.mask5
  have base_of : ∀ t, RegsExcept s t [.x14] → Frame s t (fun _ => False) →
      c.Base s0 (c.Wr (3*(q+1))) acc t := by
    intro t rt ft
    rw [show 3*(q+1) = 3*q+2+1 by omega]
    exact c.base_disp (by omega) hB rt ft
  unfold DispOutR6
  rw [gValid_r5 V (q+1) (by omega), gRank_r5 V (q+1) (by omega), ← topRank_r5V V (q+1) (by omega) (by omega)]
  set v := r5V V with hvdef
  by_cases h8 : q = 8
  · subst q
    have hr9 : nextDispR 8 = dispatch9R := by simp [nextDispR]
    rw [hr9] at hr
    obtain ⟨t,st,pt,rt,ft⟩ := dispatch9_step hbound hr s v hpc' h17 h6
    have hr9 : Search.topRank v (8+1)=v.toNat/2^63%2+2*(v.toNat/2^64%64) := topRank9 v
    have hd9 : dspR6 (8+1)=4 := rfl
    rw [hr9,hd9]
    have hb2 : v.toNat/2^63%2<2 := Nat.mod_lt _ (by decide +kernel)
    have hu : v.toNat/2^64%64<64 := Nat.mod_lt _ (by decide +kernel)
    by_cases hu63 : v.toNat/2^64%64=63
    · refine ⟨fun hv => by omega,fun _ => ⟨3,t,st,by omega,fetch_fault t ?_⟩⟩
      rw [pt,hu63]; exact g9_fault
    · set u := v.toNat/2^64%64 with hudef
      have hpc9 : t.pc=pcOf (cellW 9 (2*u)) := by rw [pt]; exact g9_cell u (by omega)
      have h16t : t.getReg .x16= ~~~(v.extractLsb' 0 64) := (rt.get (by decide +kernel)).trans h16
      obtain ⟨z,sz,pz,rz,fz⟩ := bge9_step (2*u) (by omega) (by omega) t v hpc9 h16t
      have rtz : RegsExcept s z [.x14] := fun x hx => (rz.get (by simp)).trans (rt x hx)
      have ftz : Frame s z (fun _ => False) := (ft.trans fz).mono (by intro A _ h; simpa using h)
      have st5 : Steps vimage s 4 4 z := st.trans sz
      by_cases hb : v.toNat/2^63%2=1
      · rw [if_pos hb] at pz
        rw [hb]
        by_cases hu62 : u=62
        · refine ⟨fun hv => by omega,fun _ => ⟨4,z,st5,by omega,fault_top_fetch 9 (by omega) (by omega) z ?_⟩⟩
          rw [pz,hu62]; decide +kernel
        · refine ⟨fun _ => ⟨z,st5,base_of z rtz ftz,by omega,?_⟩,fun hv => by omega⟩
          rw [pz]
          have he9 : entW (8+1) (1+2*u)=cellW 9 (1+2*u) := by
            unfold entW; rw [if_neg (by omega)]; rfl
          rw [he9]
          unfold pcOf cellW entOff
          norm_num
          congr 1; omega
      · have hb0 : v.toNat/2^63%2=0 := by omega
        rw [if_neg hb] at pz
        rw [hb0]
        refine ⟨fun _ => ⟨z,st5,base_of z rtz ftz,by omega,?_⟩,fun hv => by omega⟩
        rw [pz]
        have he9 : entW (8+1) (0+2*u)=cellW 9 (2*u)+1 := by
          unfold entW; rw [if_pos (by omega)]; simp
        rw [he9]
  · have hr' : nextDispR q = dispatchR (q+1) := by
      simp [nextDispR, show ¬ q < 7 by omega, h8, hq]
    rw [hr'] at hr
    obtain ⟨t,st,pt,rt,ft⟩ := dispatch_step (q := q+1) (by omega) (by omega) hbound hr s v hpc' h16 h17 h6
    have hd : dspR6 (q+1)=3 := by
      unfold dspR6; simp only [show q+1 ≠ 1 by omega, show ¬ q+1 < 8 by omega, show q+1 ≠ 9 by omega, if_false]
    rw [hd]
    have hk := topRank_lt v (q+1)
    refine ⟨fun hv => ⟨t,st,base_of t rt ft,by omega,?_⟩,fun hv => ⟨3,t,st,by omega,?_⟩⟩
    · rw [pt,cell_value _ _ (by omega) (by omega) (by omega)]
      have e : entW (q+1) (Search.topRank v (q+1)) = cellW (q+1) (Search.topRank v (q+1)) := by
        unfold entW; rw [if_neg (fun h => h8 (by omega))]; rfl
      rw [e]
    · by_cases h125 : Search.topRank v (q+1)=125
      · apply fault_top_fetch (q+1) (by omega) (by omega) t
        rw [pt,h125]
        exact fault125_value _ (by omega)
      · by_cases h126 : Search.topRank v (q+1)=126
        · by_cases hE : 1024≤entOff (q+1)
          · apply fault_top126_fetch (q+1) (by omega) (by omega) hE t
            rw [pt,h126]
            exact fault126_value _ (by omega) hE
          · apply fetch_fault t
            rw [pt,h126]
            exact fault126_low _ (by omega)
        · apply fetch_outside t
          rw [pt]
          exact fault_value _ _ (by omega) (by omega) hk
/-- Every R6 group transition `q -> q+1` (q < 16): r6 dispatch (q < 7), main's r5 dispatch (7 <= q < 16). -/
theorem end_dispatchR6 (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded6 V s0) (q : Nat) (hq : q < 16) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 (3*q+2) acc s) : c.DispOutR6 s0 V q acc s := by
  by_cases h7 : q < 7
  · have hd6 := c.end_dispatch6 hc hds he q h7 acc s hs
    obtain ⟨hst, hcy⟩ := r6DispR_steps (q+1) (by omega)
    unfold DispOut6 at hd6
    rw [hst, hcy] at hd6
    unfold DispOutR6
    rw [gValid_r6 V (q+1) (by omega) (by omega), gRank_r6 V (q+1) (by omega) (by omega)]
    refine ⟨hd6.1, fun hv => ?_⟩
    obtain ⟨t, st, ft⟩ := hd6.2 (by omega)
    exact ⟨dspR6 (q+1), t, st, by have := dspR6_le (q+1); omega, ft⟩
  · exact c.end_dispatch5 hds he q (by omega) hq acc s hs
/-- The NCtx digits of chains 0..50 are the spec's decoded digits of the selected half `V`. -/
def Fit6 (c : NCtx) (V : Digest) : Prop := ∀ i, i < 51 → c.dig i = T3.coreDigit 0 V i
theorem coreDigit_top (V : Digest) (q k : Nat) (hq : q < 17) (hk : k < 3) :
    T3.coreDigit 0 V (3*q+k) = if q < 8 then T3.r6Rank V q / 6^k % 6 else T3.r5Rank V q / 5^k % 5 := by
  unfold T3.coreDigit
  simp only [if_true, show (3*q+k)/3 = q by omega, show (3*q+k)%3 = k by omega]
  by_cases h8 : q < 8
  · simp [h8, show 3*q+k < 24 by omega]
  · simp [h8, show ¬ 3*q+k < 24 by omega, show 3*q+k < 51 by omega]
theorem fit6_le (c : NCtx) {V : Digest} (hf : c.Fit6 V) (i : Nat) (hi : i < 51) : c.dig i ≤ topMax i := by
  obtain ⟨q, k, hk, rfl⟩ : ∃ q k, k < 3 ∧ i = 3*q+k := ⟨i/3, i%3, by omega, by omega⟩
  rw [hf _ hi, coreDigit_top V q k (by omega) hk]
  unfold topMax mx
  rw [show (3*q+k)/3 = q by omega]
  by_cases h8 : q < 8
  · simp only [h8, if_true]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  · simp only [h8, if_false, show q < 17 by omega, if_true]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
theorem gRank_lt (V : Digest) (q : Nat) (hq : q < 17) (hv : gValid V q) : gRank V q < (mx q+1)^3 := by
  unfold gValid at hv; unfold gRank
  by_cases h8 : q < 8
  · simp only [h8, if_true] at hv ⊢
    simp only [mx, h8, if_true]
    unfold T3.r6Valid at hv; unfold T3.r6Rank
    have := Nat.mod_lt (T3.topCode V / 2 ^ T3.r6Shift q) (show 0 < 256 by norm_num)
    unfold T3.r6Raw at hv ⊢
    split_ifs at hv ⊢ <;> simp at hv <;> omega
  · simp only [h8, if_false] at hv ⊢
    simp only [mx, h8, if_false, hq, if_true]; omega
/-- With fitting digits, the NCtx group index of a valid group is the field's rank. -/
theorem fit_rank6 (c : NCtx) {V : Digest} (hf : c.Fit6 V) (q : Nat) (hq : q < 17) (hv : gValid V q) :
    c.kOf q = gRank V q := by
  have hl := gRank_lt V q hq hv
  unfold kOf
  rw [hf (3*q) (by omega), hf (3*q+1) (by omega), hf (3*q+2) (by omega)]
  have e0 := coreDigit_top V q 0 hq (by omega)
  have e1 := coreDigit_top V q 1 hq (by omega)
  have e2 := coreDigit_top V q 2 hq (by omega)
  simp only [Nat.add_zero] at e0
  rw [e0, e1, e2]
  unfold gRank at hl ⊢
  by_cases h8 : q < 8
  · simp only [h8, if_true, mx] at hl ⊢; norm_num at hl ⊢; omega
  · simp only [h8, if_false, mx, hq] at hl ⊢; norm_num at hl ⊢; omega
/-- Group transition into the next group's `GroupIn` (valid field). -/
theorem end_dispatchR6_in (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded6 V s0) (hf : c.Fit6 V) (q : Nat) (hq : q < 16) (hv : gValid V (q+1))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 (3*q+2) acc s) :
    ∃ t, Steps vimage s (dspR6 (q+1)) (dspR6 (q+1)) t ∧ c.GroupIn s0 (q+1) acc t := by
  obtain ⟨t, st, hB, hl, pt⟩ := (c.end_dispatchR6 hc hds he q hq acc s hs).1 hv
  refine ⟨t, st, hB, hl, ?_⟩
  rw [pt]; unfold entPc; rw [c.fit_rank6 hf (q+1) (by omega) hv]
/-- Group transition into an invalid next group: the run faults within 5 steps. -/
theorem end_dispatchR6_bad (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded6 V s0) (q : Nat) (hq : q < 16) (hv : ¬ gValid V (q+1))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 (3*q+2) acc s) :
    ∃ k t, Steps vimage s k k t ∧ k ≤ 5 ∧ fetch vimage t = none :=
  (c.end_dispatchR6 hc hds he q hq acc s hs).2 hv
theorem g0_valid (W : Word) (s : MachineState) (h40 : 40 ≤ W.toNat % 256)
    (hpc : s.pc = (((W <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64) :
    s.pc = pcOf (cellW 0 (W.toNat % 256 - 40)) := by
  rw [g0_target W _ rfl (by omega), g0_cell _ (by omega)] at hpc
  rw [hpc, cell6_valid 0 _ (by omega) (by simp [raw6Valid, h40])]; rfl
theorem g0_bad (W : Word) (s : MachineState) (h40 : W.toNat % 256 < 40)
    (hpc : s.pc = (((W <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64) : fetch vimage s = none := by
  rcases g0_landing W s hpc with ⟨h, -⟩ | h
  · omega
  · exact h
/-- The prologue's g0 dispatch (on a6 = the low half of `V`) at NCtx level. -/
theorem g0_group (c : NCtx) {V : Digest} (hf : c.Fit6 V) (s : MachineState)
    (hpc : s.pc = ((((V.extractLsb' 0 64) <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64) :
    (gValid V 0 → s.pc = pcOf (c.entPc 0)) ∧ (¬ gValid V 0 → fetch vimage s = none) := by
  have hr := g0_raw V
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · have h40 := (gValid_g0 V).mp hv
    rw [g0_valid _ s (by omega) hpc, hr]
    unfold entPc; rw [c.fit_rank6 hf 0 (by omega) hv, gRank_g0]
    unfold entW; simp
  · have h40 : ¬ 40 ≤ T3.r6Raw V 0 := fun h => hv ((gValid_g0 V).mpr h)
    exact g0_bad _ s (by omega) hpc
/-- Group 0's cell word `addi s8,zero,T-kss`: the R6 top-region entry into chain 0. -/
theorem g0_entry (c : NCtx) (hds : c.DigitsOk) {b : MachineState} (acc : List Digest) (s : MachineState)
    (hs : c.GroupIn b 0 acc s) :
    ∃t,Steps vimage s 1 1 t ∧ c.ChainIn (set24 b (c.s8v 0)) 0 acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hk := c.kOf_lt hds 0 (by omega)
  have hchk := s8Run_at 0 (c.kOf 0) (by omega) hk
  rw [if_pos rfl] at hchk
  have hrun := rOK_eq hchk
  have hp : entW 0 (c.kOf 0)<257181 := by have := entW_lt 0 _ (by omega) hk; omega
  have hst := piece_steps45 hrun hp s hpc (by simp [guardR])
  set r := guardR (c.kOf 0) with hr
  have hsum : ((List.range (3*0+3)).map c.dig).sum = kss 0 (c.kOf 0) := by
    rw [c.kss_kOf hds 0 (by omega)]; simp [List.range_succ]; omega
  refine ⟨r.toState s,hst,⟨⟨fun x hx => ?_,fun A hA hn => ?_,fun j hj => ?_⟩,hlen,?_⟩⟩
  · rw [Result.toState_getReg]
    by_cases hx : x=.x24
    · subst x
      simp only [hr,guardR]
      rw [RegFile.get_set_self _ _ (by decide +kernel),set24_24]
      simp only [E.eval]
      unfold s8v; rw [hsum]
    · simp only [hr,guardR]
      rw [RegFile.get_set_ne _ _ hx,RegFile.init_get_eval,set24_regs _ _ _ hx]
      exact hR x (by assumption)
  · rw [Result.toState_getMem,set24_mem]
    simp only [hr,guardR]
    rw [memEval_nil]
    exact hF A hA hn
  · have hfr : Frame s (r.toState s) (fun _ => False) := fun A _ _ => by
      rw [Result.toState_getMem]; simp [hr,guardR,memEval_nil]
    exact (hS j hj).frame hfr (by unfold slot; omega) (by simp) (by simp)
  · rw [Result.toState_pc]
    simp only [hr,guardR,E.eval]
    unfold startPc leadPc leadOff entW
    simp
theorem set24_encoded6 {V : Digest} {b : MachineState} (x : Word) (he : Encoded6 V b) : Encoded6 V (set24 b x) :=
  ⟨(set24_regs _ _ _ (by decide +kernel)).trans he.lo,(set24_regs _ _ _ (by decide +kernel)).trans he.hi,
    (set24_regs _ _ _ (by decide +kernel)).trans he.mask6,(set24_regs _ _ _ (by decide +kernel)).trans he.base6,
    (set24_regs _ _ _ (by decide +kernel)).trans he.mask5⟩
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
