import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsDispatchArith
import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsGoodOne

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
/-- T51: r5 groups 9..15 (#938's column) fault on rank 125 (word `entOff q` is zero). -/
theorem fault_top_fetch (q : Nat) (hq : q<16) (h9 : 9≤q) (s : MachineState)
    (hpc : s.pc=pcOf (entOff q)) : fetch vimage s=none := by
  have hw := fault_top_word q hq h9
  have hc := lcodeAt (entOff q) (by have := entOff_le q (by omega); omega)
  cases he : lcode (entOff q) with
  | nil => simp [he] at hw
  | cons w ws =>
    simp only [he, List.head?_cons, Option.some.injEq] at hw
    subst w
    rw [he] at hc
    exact hc.fetch s hpc
theorem fault_top126_fetch (q : Nat) (hq : q<16) (h9 : 9≤q) (he : 1024≤entOff q) (s : MachineState)
    (hpc : s.pc=pcOf (entOff q-1024)) : fetch vimage s=none := by
  have hw := fault_top126_word q hq h9 he
  have hc := lcodeAt (entOff q-1024) (by have := entOff_le q (by omega); omega)
  cases hx : lcode (entOff q-1024) with
  | nil => simp [hx] at hw
  | cons w ws =>
    simp only [hx, List.head?_cons, Option.some.injEq] at hw
    subst w
    rw [hx] at hc
    exact hc.fetch s hpc
/-! ### T51 dispatch landings (VERA2; R6 VER-A's template)
Machine-level facts for the T51 top region: zero-word guards fault; the dispatch into r6 group `h` (1..8) lands on
`cell6 h raw` (a cell for raw < 216, a guard otherwise); the prologue's g0 dispatch lands on the g0 column; group 0's
5-word dispatch also loads the r6 mask (t4 = 0xFF00) and the table base (s2 = 856064); q15's dispatch (#938's into
group 8) lands on the r7 pair's cells (rank < 49) or guards; the checksum dispatch lands on an arm or a guard. -/
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
theorem fetch_outside' (s : MachineState)
    (h : s.pc.toNat<0x1000 ∨ 0x1000+4*257280 ≤ s.pc.toNat) : fetch vimage s=none := by
  rcases h with h|h
  · exact fetch_below s h
  · exact fetch_above s h
theorem cell6_lt (g raw : Nat) (hg : g < 9) (hr : raw < 256) : cell6 g raw < 257214 := by
  unfold cell6 r6Off; split_ifs <;> omega
/-- r6 group `g`, field value `raw`: a valid raw lands on the cell of rank `raw - 40` (g = 0) or `raw`. -/
theorem cell6_valid (g raw : Nat) (hg : g < 9) (hv : raw6Valid g raw = true) :
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
/-- The masked field of the dispatch into r6 group `h` (1..8): `256 raw`. -/
theorem r6Src_eval (h : Nat) (h1 : 1 ≤ h) (h8 : h ≤ 8) (V : Digest) (s : MachineState)
    (h16 : s.getReg .x16 = V.extractLsb' 0 64) (h17 : s.getReg .x17 = V.extractLsb' 64 64) :
    (r6Src h).eval s &&& 65280#64 = BitVec.ofNat 64 (256 * (V.toNat / 2^(r6Pos h) % 256)) := by
  by_cases e1 : h = 1
  · subst e1
    simp only [r6Src, if_true, E.eval, h16]; rw [word_ff00, lo_field V 8 (by omega)]; rfl
  by_cases e7 : h = 7
  · subst e7
    have hs : (r6Src 7).eval s = s.getReg .x17 >>> 40 := by
      unfold r6Src; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]; rfl
    rw [hs, h17, field_ff00, hi_field V 48 (by omega)]; rfl
  by_cases e8 : h = 8
  · subst e8
    have hs : (r6Src 8).eval s = s.getReg .x17 >>> 48 := by
      unfold r6Src; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; rfl
    rw [hs, h17, field_ff00, hi_field V 56 (by omega)]; rfl
  · rw [r6Src_mid h (by omega) (by omega) s, h16, field_ff00, lo_field V _ (by omega)]
    unfold r6Pos; rw [if_neg e7, if_neg e8, show 8*h-8+8 = 8*h by omega]
theorem guard6_fault (g raw : Nat) (hg : g < 9) (hr : raw < 256) (hv : raw6Valid g raw = false)
    (h3 : g = 0 → 3 ≤ raw) (s : MachineState) (hpc : s.pc = pcOf (cell6 g raw)) : fetch vimage s = none := by
  have hc := guard6Check_at g raw hg hr
  unfold guard6Check at hc
  rw [hv, Bool.false_or] at hc
  have hz : zeroAt (cell6 g raw) = true := by
    by_cases h0 : g = 0
    · have := h3 h0; subst h0; simpa [show ¬ raw < 3 by omega] using hc
    · simpa [h0] using hc
  exact fetch_zero_word (cell6_lt g raw hg hr) hz s hpc
/-- `a4` of the dispatch into r6 group `h` (2..8; group 1 is entered by group 0's `g0DispR`). -/
theorem r6A_eval (h : Nat) (h1 : 1 ≤ h) (h8 : h ≤ 8) (V : Digest) (s : MachineState)
    (h16 : s.getReg .x16 = V.extractLsb' 0 64) (h17 : s.getReg .x17 = V.extractLsb' 64 64)
    (h29 : s.getReg .x29 = 65280#64) (h18 : s.getReg .x18 = 856064#64) :
    (r6A h).eval s = if r6B h then 856064#64 - BitVec.ofNat 64 (256 * (V.toNat / 2^(r6Pos h) % 256))
      else BitVec.ofNat 64 (256 * (V.toNat / 2^(r6Pos h) % 256)) + 856064#64 := by
  have hf := r6Src_eval h h1 h8 V s h16 h17
  unfold r6A
  split_ifs
  · show s.getReg .x18 - ((r6Src h).eval s &&& s.getReg .x29) = _
    rw [h18, h29, hf]
  · show ((r6Src h).eval s &&& s.getReg .x29) + s.getReg .x18 = _
    rw [h18, h29, hf]
/-- Dispatch into r6 group `h` (1..8): pc at the cell of the field value. -/
theorem r6_dispatch_pc (h : Nat) (h1 : 1 ≤ h) (h8 : h ≤ 8) (V : Digest) (s : MachineState)
    (h16 : s.getReg .x16 = V.extractLsb' 0 64) (h17 : s.getReg .x17 = V.extractLsb' 64 64)
    (h29 : s.getReg .x29 = 65280#64) (h18 : s.getReg .x18 = 856064#64) :
    (r6DispR h).pc.eval s = pcOf (cell6 h (V.toNat / 2^(r6Pos h) % 256)) := by
  have ha := r6A_eval h h1 h8 V s h16 h17 h29 h18
  have hr : V.toNat / 2^(r6Pos h) % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have ho := r6Off_lt h
  show ((r6A h).eval s + r6Imm h) &&& ~~~1#64 = _
  rw [ha, cell6_tab h _ h1 h8]
  unfold r6Imm
  split_ifs with hh
  · exact tabB_target _ _ hr ho
  · exact tabA_target _ _ hr ho
theorem r6_dispatch_step {p h : Nat} (h1 : 1 ≤ h) (h8 : h ≤ 8) (hp : p < 257181)
    (hrun : vrun p 5 = some (r6DispR h)) (s : MachineState) (V : Digest) (hpc : s.pc = pcOf p)
    (h16 : s.getReg .x16 = V.extractLsb' 0 64) (h17 : s.getReg .x17 = V.extractLsb' 64 64)
    (h29 : s.getReg .x29 = 65280#64) (h18 : s.getReg .x18 = 856064#64) :
    ∃ t, Steps Images.verifyImage s (r6DispR h).steps (r6DispR h).cycles t ∧
      t.pc = pcOf (cell6 h (V.toNat / 2^(r6Pos h) % 256)) ∧ RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨(r6DispR h).toState s, piece_steps45 hrun hp s hpc (by simp [r6DispR]), ?_, ?_, ?_⟩
  · rw [Result.toState_pc]; exact r6_dispatch_pc h h1 h8 V s h16 h17 h29 h18
  · intro r hr
    rw [Result.toState_getReg]
    simp only [r6DispR]
    rw [RegFile.get_set_ne _ _ (show r ≠ .x14 by simpa using hr), RegFile.init_get_eval]
  · intro A _ _
    simp [r6DispR, rv_simp]
/-- Group 0's 5-word dispatch into group 1: loads t4 = 0xFF00 (verify data word 16 at `s1 - 288`) and s2 = 856064,
then jumps to group 1's cell of the field `a6 bits 8..15`. -/
theorem g0_dispatch_step {p : Nat} (hp : p < 257181) (hrun : vrun p 5 = some g0DispR) (s : MachineState)
    (V : Digest) (hpc : s.pc = pcOf p) (h16 : s.getReg .x16 = V.extractLsb' 0 64)
    (h9 : s.getReg .x9 = 0xffbf10#64) (hmask : s.getMem 0xffbdf0#64 = 65280#64) :
    ∃ t, Steps Images.verifyImage s 5 5 t ∧ t.pc = pcOf (cell6 1 (V.toNat / 2^8 % 256)) ∧
      t.getReg .x29 = 65280#64 ∧ t.getReg .x18 = 856064#64 ∧ RegsExcept s t [.x29, .x18, .x14] ∧
      Frame s t (fun _ => False) := by
  have hobl : ∀ o ∈ g0DispR.st.obl, o.holds s := by
    intro o ho
    simp [g0DispR] at ho
    subst ho
    simp [Oblig.holds, rv_simp, accessValid_iff, MEMORY_BYTES, h9]
  have hm : maskE.eval s = 65280#64 := by
    change s.getMem (s.getReg .x9 + BitVec.ofNat 64 (2^64-288)) = _
    rw [h9, show (0xffbf10#64 : Word) + BitVec.ofNat 64 (2^64-288) = 0xffbdf0#64 from rfl]; exact hmask
  refine ⟨g0DispR.toState s, piece_steps45 hrun hp s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    show ((g0A.eval s) + BitVec.ofNat 64 (2^64-72)) &&& ~~~1#64 = _
    have hg : g0A.eval s = 856064#64 - BitVec.ofNat 64 (256 * (V.toNat / 2^8 % 256)) := by
      show 856064#64 - (s.getReg .x16 &&& maskE.eval s) = _
      rw [hm, h16, word_ff00, lo_field V 8 (by omega)]
    have hr : V.toNat / 2^8 % 256 < 256 := Nat.mod_lt _ (by norm_num)
    rw [hg, cell6_tab 1 _ (by omega) (by omega)]
    simp only [r6B, show (1:Nat) < 4 by decide, true_or, decide_true, if_true]
    have := tabB_target _ (r6Off 1) hr (r6Off_lt 1)
    rwa [show BitVec.ofNat 64 (2^64+4*r6Off 1-256) = BitVec.ofNat 64 (2^64-72) by unfold r6Off; rfl] at this
  · rw [Result.toState_getReg]; simp only [g0DispR]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    exact hm
  · rw [Result.toState_getReg]; simp only [g0DispR]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]; rfl
  · intro r hr
    rw [Result.toState_getReg]
    simp only [g0DispR]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegFile.get_set_ne _ _ hr.2.2, RegFile.get_set_ne _ _ hr.2.1, RegFile.get_set_ne _ _ hr.1,
      RegFile.init_get_eval]
  · intro A _ _
    simp [g0DispR, rv_simp]
/-- The checksum dispatch (end of the r7 pair): pc at `ckWord ds` for `s8 = T - ds`, `ds <= 231`. -/
theorem ck_dispatch_step {p : Nat} (hp : p < 257181) (hrun : vrun p 5 = some ckDispR) (s : MachineState)
    (ds : Nat) (hd : ds ≤ 231) (hpc : s.pc = pcOf p)
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
/-- Checksum landing: an arm when `T - 5 <= ds <= T` (checksum digit 0..5), otherwise a zero word. -/
theorem ck_landing (ds : Nat) (hd : ds < 232) :
    (topT - 5 ≤ ds ∧ ds ≤ topT ∧ ckWord ds = ckArm (topT - ds)) ∨
      (∀ s : MachineState, s.pc = pcOf (ckWord ds) → fetch vimage s = none) := by
  by_cases h : topT - 5 ≤ ds ∧ ds ≤ topT
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
theorem r6_landing (h raw : Nat) (h1 : 1 ≤ h) (h8 : h ≤ 8) (hr : raw < 256) :
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
theorem cellW16_lt (k : Nat) : cellW 16 k < 257214 := by
  have he : entOff 8 = 676 := rfl
  unfold cellW; simp only [show ¬ (16:Nat)<9 by omega, show ¬ (16:Nat)<16 by omega, if_false, if_true]; omega
/-- r7-pair landing (q15's dispatch, #938's into group 8, on the rank `k = topRank v 8`): rank `k < 49` lands on
its cell; ranks 49..125 on zero-word guards; ranks 126, 127 outside the code. -/
theorem pair_landing (k : Nat) (hk : k < 128) (t : MachineState)
    (hpc : t.pc = BitVec.ofNat 64 (4096*(127-k)+2^64+4*entOff 8-4096)) :
    (k < 49 ∧ t.pc = pcOf (cellW 16 k)) ∨ fetch vimage t = none := by
  by_cases h49 : k < 49
  · left; exact ⟨h49, by rw [hpc, cell_value_pair k (by omega)]⟩
  right
  by_cases h125 : k ≤ 125
  · have hg := r7GuardCheck_at k (by omega)
    unfold r7GuardCheck at hg
    simp only [Bool.or_eq_true, decide_eq_true_eq, h49, false_or] at hg
    have hp : t.pc = pcOf (cellW 16 k) := by
      by_cases h4 : k ≤ 124
      · rw [hpc, cell_value_pair k h4]
      · have : k = 125 := by omega
        subst this
        rw [hpc, fault125_value 8 (by omega)]
        unfold cellW; simp only [show ¬ (16:Nat)<9 by omega, show ¬ (16:Nat)<16 by omega, if_false, if_true]; rfl
    exact fetch_zero_word (cellW16_lt k) hg t hp
  · by_cases h126 : k = 126
    · apply fetch_below; rw [hpc, h126]; exact fault126_low 8 (by decide)
    · apply fetch_outside'; rw [hpc]; exact fault_value 8 k (by omega) (by omega) hk
end SigGolfCandidate.T3M.Nonbinary
end
/-! ### T51 top word at the machine
The selected half `V` sits in a6/a7 unflipped (`Encoded0` / `Encoded6`). The r6 groups read `T3.r6Raw V g` directly
(the T51 `topMask` flip only touches bits 56..111); the r5 groups 9..15 and the r7 pair run #938's dispatch code,
which sees the word `r5V V = V ^^^ (2^119 - 1)` in #938's convention (x16 = ~lo, x17 = ~hi ^ hiMask), whose
`Search.topRank` is `T3.r5Rank V` (q = 9..15) and `T3.r7Rank V` (q = 8, bits 56..62). -/
section
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
/-- The r5 groups' view of the selected half (#938's `Encoded` word). -/
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
theorem topMask_eq : T3.topMask = 2^56*(2^56-1) := by unfold T3.topMask; norm_num
/-- The 7-bit field `q` (8 <= q < 16: bits 7q..7q+6 inside 56..111) under #938's word is the spec's flipped field. -/
theorem topRank_r5V (V : Digest) (q : Nat) (h8 : 8 ≤ q) (hq : q < 16) :
    Search.topRank (r5V V) q = T3.r5Rank V q := by
  unfold Search.topRank T3.r5Rank T3.topCode T3.topFlip r5V
  have e := nat_field_eq (V ^^^ BitVec.ofNat 128 (2^119-1)).toNat (V ^^^ BitVec.ofNat 128 T3.topMask).toNat (7*q) 7
    (by
      intro j hj
      rw [BitVec.toNat_xor, BitVec.toNat_xor, Nat.testBit_xor, Nat.testBit_xor]
      have e1 : (BitVec.ofNat 128 (2^119-1)).toNat.testBit (j + 7*q) = true := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), Nat.testBit_two_pow_sub_one]; simp; omega
      have e2 : (BitVec.ofNat 128 T3.topMask).toNat.testBit (j + 7*q) = true := by
        rw [topMask_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), Nat.testBit_two_pow_mul,
          Nat.testBit_two_pow_sub_one]
        simp; omega
      rw [e1, e2])
  simpa using e
theorem cellW9 (k : Nat) : cellW 9 k = 1024*(125-k)+64 := by
  unfold cellW; simp only [show ¬ (9:Nat)<9 by omega, show (9:Nat)<16 by omega, if_false, if_true]; rfl
theorem r7Rank_eq (V : Digest) : T3.r7Rank V = T3.r5Rank V 8 := rfl
theorem topRank_r5V_pair (V : Digest) : Search.topRank (r5V V) 8 = T3.r7Rank V := by
  rw [topRank_r5V V 8 (by omega) (by omega)]; rfl
/-- Bits outside 56..111 of the spec word `topCode V` are the bits of `V`. -/
theorem topCode_field (V : Digest) (b n : Nat) (h : b + n ≤ 56 ∨ 112 ≤ b) :
    T3.topCode V / 2^b % 2^n = V.toNat / 2^b % 2^n := by
  unfold T3.topCode T3.topFlip
  apply nat_field_eq
  intro j hj
  rw [BitVec.toNat_xor, Nat.testBit_xor]
  have e : (BitVec.ofNat 128 T3.topMask).toNat.testBit (j + b) = false := by
    rw [topMask_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), Nat.testBit_two_pow_mul,
      Nat.testBit_two_pow_sub_one]
    simp; omega
  rw [e]; simp
theorem r6Shift_eq (g : Nat) (hg : g < 9) : T3.r6Shift g = r6Pos g := by
  unfold T3.r6Shift r6Pos; split_ifs <;> omega
/-- The 8-bit field of r6 group `g` is read from `V` itself (no flip). -/
theorem r6Raw_eq (V : Digest) (g : Nat) (hg : g < 9) : T3.r6Raw V g = V.toNat / 2^(r6Pos g) % 256 := by
  unfold T3.r6Raw
  rw [r6Shift_eq g hg, show (256:Nat) = 2^8 by norm_num]
  apply topCode_field
  unfold r6Pos; split_ifs <;> omega
/-- g0's field (the low byte of a6). -/
theorem g0_raw (V : Digest) : (V.extractLsb' 0 64).toNat % 256 = T3.r6Raw V 0 := by
  rw [r6Raw_eq V 0 (by omega)]
  have := lo_field V 0 (by omega)
  simpa [r6Pos] using this
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
/-- Inside a group: chain A -> B, B -> C (T51: chains < 50; the r7 pair's chain 49 ends at the checksum dispatch). -/
theorem next_inline (c : NCtx) (s0 : MachineState) (i : Nat) (hi : i<50) (h2 : i%3≠2) (h49 : i≠49)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) :
    c.ChainIn s0 (i+1) acc s := by
  obtain ⟨hB,hlen,hpc⟩ := hs
  refine ⟨hB,hlen,?_⟩
  rw [hpc]
  unfold endPc startPc
  rw [if_pos hi, if_pos (show i+1<50 by omega)]
  have e : (i+1)/3=i/3 := by omega
  by_cases h0 : i%3=0
  · rw [if_pos h0,if_neg (show (i+1)%3≠0 by omega),if_pos (show (i+1)%3=1 by omega)]
    unfold qB;rw [e]
  · rw [if_neg h0,if_pos (show i%3=1 by omega),if_neg (show (i+1)%3≠0 by omega),
      if_neg (show (i+1)%3≠1 by omega)]
    unfold qC;rw [e]
def chainF (c : NCtx) (ends : List Digest) (i : Nat) : M (List Digest) := do
  let v ← ClaudeWCT.W9.T3M.chainPW 0 c.tree c.leaf i (c.dig i) (topMax i-c.dig i) (c.pad0 i) (c.pad1 i)
    (c.padHeader i) (c.bufferVal i)
  pure (ends++[v])
/-- Chains of top group `q`: 3 (q < 16), the r7 pair (q = 16) 2. -/
def nCh (q : Nat) : Nat := if q = 16 then 2 else 3
theorem nCh_cases (q : Nat) : (q = 16 ∧ nCh q = 2) ∨ (q ≠ 16 ∧ nCh q = 3) := by
  unfold nCh; by_cases h : q = 16 <;> simp [h]
/-- Top group `q < 17` (chains `3q .. 3q + nCh q - 1`) from any of its chains to its last chain's end. -/
theorem group_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (q : Nat) (hq : q<17) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t,c.EndInv s0 (3*q+nCh q-1) ends t → Verify.GoodQP P t N C Q A (K ends)) :
    ∀ k i, 3*q ≤ i → i+k = 3*q+nCh q → 0 < k → ∀ acc s, c.ChainIn s0 i acc s →
      Verify.GoodQP P s (N+40*k) (C+c.chainsCost i k) Q (A+c.chainsCost i k)
        (Verify.ccM ((List.range' i k).foldlM c.chainF acc) K) := by
  have hn := nCh_cases q
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
          have he : i=3*q+nCh q-1 := by omega
          rw [he] at ht
          simpa [chainsCost] using hK _ t ht
        · have ht' : c.ChainIn s0 (i+1) (acc++[v]) t :=
            c.next_inline s0 i (by omega) (by omega) (by omega) (acc++[v]) t ht
          exact ih (i+1) (by omega) (by omega) (by omega) (acc++[v]) t ht') s hs
    refine H.mono (by omega) ?_ (fun hq => ⟨hq,?_⟩)
    · simp only [chainsCost,List.range'_succ,List.map_cons,List.sum_cons];omega
    · simp only [chainsCost,List.range'_succ,List.map_cons,List.sum_cons];omega
def GroupIn (c : NCtx) (s0 : MachineState) (q : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (3*q)) acc s ∧ acc.length=3*q ∧ s.pc=pcOf (c.entPc q)
theorem fetch_fault (s : MachineState) (h : s.pc.toNat<0x1000) : fetch vimage s=none := fetch_below s h
theorem fetch_high (s : MachineState) (h : 0x1000+4*257280 ≤ s.pc.toNat) : fetch vimage s=none := fetch_above s h
theorem fetch_outside (s : MachineState)
    (h : s.pc.toNat<0x1000 ∨ 0x1000+4*257280 ≤ s.pc.toNat) : fetch vimage s=none := fetch_outside' s h
theorem topRank_lt (v : Digest) (q : Nat) : Search.topRank v q<128 := by
  unfold Search.topRank; omega
theorem topRank9 (v : Digest) : Search.topRank v 9=v.toNat/2^63%2+2*(v.toNat/2^64%64) := by
  unfold Search.topRank
  rw [show 7*9=63 from rfl]
  have h : v.toNat/2^64=v.toNat/2^63/2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
  rw [h]; omega
/-- Reverse checksum `topT - (digits of the chains of groups 0..q)` (q = 16: chains 0..49). -/
def s8v (c : NCtx) (q : Nat) : Word :=
  BitVec.ofNat 64 topT-BitVec.ofNat 64 (((List.range (3*q+nCh q)).map c.dig).sum)
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
/-- T51: group 0's dispatch loads t4 = 0xFF00 and s2 = 856064; the later groups run on this base. -/
def setTab (b : MachineState) : MachineState := (b.setReg .x29 65280#64).setReg .x18 856064#64
theorem setTab_regs (b : MachineState) (r : Reg) (h29 : r≠.x29) (h18 : r≠.x18) :
    (setTab b).getReg r=b.getReg r := by
  unfold setTab
  rw [setReg_of_ne _ _ (by decide +kernel), setReg_of_ne b _ (by decide +kernel)]
  cases r <;> simp_all [MachineState.getReg]
theorem setTab_29 (b : MachineState) : (setTab b).getReg .x29=65280#64 := by
  unfold setTab
  rw [setReg_of_ne _ _ (by decide +kernel), setReg_of_ne b _ (by decide +kernel)]
  rfl
theorem setTab_18 (b : MachineState) : (setTab b).getReg .x18=856064#64 := by
  unfold setTab
  rw [setReg_of_ne _ _ (by decide +kernel)]
  rfl
theorem setTab_mem (b : MachineState) (a : Word) : (setTab b).getMem a=b.getMem a := rfl
theorem setTab_known (c : NCtx) {b : MachineState} (hk : ∀p∈c.known,b.getReg p.1=p.2) :
    ∀p∈c.known,(setTab b).getReg p.1=p.2 := by
  intro p hp
  have h29 : ∀ p ∈ c.known, p.1 ≠ .x29 := by simp [known]
  have h18 : ∀ p ∈ c.known, p.1 ≠ .x18 := by simp [known]
  rw [setTab_regs _ _ (h29 p hp) (h18 p hp)]
  exact hk p hp
theorem setTab_orig (c : NCtx) {b : MachineState} (h0 : c.Orig0 b) : c.Orig0 (setTab b) :=
  ⟨⟨fun i hi k hk => h0.1.1 i hi k hk,fun i hi k hk => h0.1.2 i hi k hk⟩, h0.2.congr (fun A _ _ => setTab_mem b _)⟩
theorem setTab_24 (b : MachineState) : (setTab b).getReg .x24=b.getReg .x24 :=
  setTab_regs b .x24 (by decide) (by decide)
theorem sum_range_three (f : Nat → Nat) (n : Nat) :
    ((List.range (n+3)).map f).sum=((List.range n).map f).sum+(f n+f (n+1)+f (n+2)) := by
  simp only [List.range_succ,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega
theorem kss_kOf (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<16) :
    kss q (c.kOf q)=c.dig (3*q)+c.dig (3*q+1)+c.dig (3*q+2) := by
  obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds q hq
  simp only [kss,k1,k2,k3]
theorem kss_kOf16 (c : NCtx) (hds : c.DigitsOk) : kss 16 (c.kOf 16)=c.dig 48+c.dig 49 := by
  obtain ⟨k1,k2,k3⟩ := c.kdig_kOf16 hds
  simp only [kss,k1,k2,k3,Nat.add_zero]
/-- The digit sum of group `q` (its cell's s8 word subtracts `kss q (kOf q)`). -/
theorem kss_group (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) :
    ((List.range (3*q+nCh q)).map c.dig).sum = ((List.range (3*q)).map c.dig).sum + kss q (c.kOf q) := by
  rcases nCh_cases q with ⟨rfl, h2⟩ | ⟨h16, h3⟩
  · rw [h2, c.kss_kOf16 hds, show 3*16+2 = (48+1)+1 from rfl, List.range_succ, List.range_succ,
      show 3*16 = 48 from rfl]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.reduceAdd]
    omega
  · rw [h3, c.kss_kOf hds q (by omega), sum_range_three]
theorem s8v_succ (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<16) :
    c.s8v q+(-BitVec.ofNat 64 (kss (q+1) (c.kOf (q+1))))=c.s8v (q+1) := by
  have hS : ((List.range (3*(q+1)+nCh (q+1))).map c.dig).sum =
      ((List.range (3*q+nCh q)).map c.dig).sum+kss (q+1) (c.kOf (q+1)) := by
    rw [c.kss_group hds (q+1) (by omega)]
    have hn : nCh q = 3 := by unfold nCh; rw [if_neg (by omega)]
    rw [hn, show 3*(q+1) = 3*q+3 by ring]
  unfold s8v
  rw [hS,BitVec.ofNat_add]
  simp only [BitVec.sub_eq_add_neg,BitVec.neg_add]
  ac_rfl
theorem s8v0 (c : NCtx) (hds : c.DigitsOk) :
    c.s8v 0 = BitVec.ofNat 64 topT-BitVec.ofNat 64 (kss 0 (c.kOf 0)) := by
  have h : ((List.range (3*0+nCh 0)).map c.dig).sum = kss 0 (c.kOf 0) := by
    rw [c.kss_kOf hds 0 (by omega)]
    show ((List.range 3).map c.dig).sum = c.dig 0 + c.dig 1 + c.dig 2
    simp [List.range_succ]; try omega
  unfold s8v; rw [h]
/-- Entry words (and the lead after them) of every top group lie in the code. -/
theorem entW_all : (List.range 17).all (fun q => (List.range (nRank q)).all (fun k => decide (entW q k + 1 < 257181)))
    = true := by decide +kernel
theorem entW_lt (q k : Nat) (hq : q < 17) (hk : k < nRank q) : entW q k + 1 < 257181 := by
  have h1 := List.all_eq_true.mp entW_all q (List.mem_range.mpr hq)
  have := List.all_eq_true.mp h1 k (List.mem_range.mpr hk)
  simpa using this
theorem kOf_nRank (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q < 17) : c.kOf q < nRank q := by
  by_cases h16 : q = 16
  · subst h16; exact c.kOf16_lt hds
  · have := c.kOf_lt hds q (by omega); unfold nRank; rw [if_neg h16]; exact this
theorem entry_step (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {b : MachineState} (q : Nat) (hq : q<16)
    (h24 : b.getReg .x24=c.s8v q) (acc : List Digest) (s : MachineState) (hs : c.GroupIn b (q+1) acc s) :
    ∃t,Steps vimage s 1 1 t ∧ c.ChainIn (set24 b (c.s8v (q+1))) (3*(q+1)) acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hkq := c.kOf_nRank hds (q+1) (by omega)
  have hchk := s8Run_at (q+1) (c.kOf (q+1)) (by omega) hkq
  rw [if_neg (show q+1≠0 by omega)] at hchk
  have hrun := rOK_eq hchk
  have hp : entW (q+1) (c.kOf (q+1))<257181 := by
    have := entW_lt (q+1) (c.kOf (q+1)) (by omega) hkq; omega
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
    exact (hS j hj).frame hfr (by unfold slot; split <;> omega) (by simp) (by simp)
  · rw [Result.toState_pc]
    simp only [hr,s8R,E.eval]
    unfold startPc leadPc leadOff
    simp only [show 3*(q+1)<50 by omega,show 3*(q+1)%3=0 by omega,if_true,show 3*(q+1)/3=q+1 by omega]
def s8w (c : NCtx) (n : Nat) : Word := BitVec.ofNat 64 topT-BitVec.ofNat 64 (((List.range n).map c.dig).sum)
theorem s8v_eq (c : NCtx) (q : Nat) : c.s8v q=c.s8w (3*q+nCh q) := rfl
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
/-! ### T51 group transitions -/
/-- T51 register invariants at the top start (prologue done): the selected half `V` in a6/a7 (unflipped) and the r5
mask t1 = 0x7F000. -/
structure Encoded0 (V : Digest) (s : MachineState) : Prop where
  lo : s.getReg .x16 = V.extractLsb' 0 64
  hi : s.getReg .x17 = V.extractLsb' 64 64
  mask5 : s.getReg .x6 = 520192#64
/-- ... and after group 0's dispatch: the r6 mask t4 = 0xFF00 and the table base s2 = 856064 (`setTab`). -/
structure Encoded6 (V : Digest) (s : MachineState) : Prop where
  lo : s.getReg .x16 = V.extractLsb' 0 64
  hi : s.getReg .x17 = V.extractLsb' 64 64
  mask6 : s.getReg .x29 = 65280#64
  base6 : s.getReg .x18 = 856064#64
  mask5 : s.getReg .x6 = 520192#64
theorem setTab_encoded {V : Digest} {b : MachineState} (he : Encoded0 V b) : Encoded6 V (setTab b) :=
  ⟨(setTab_regs _ _ (by decide) (by decide)).trans he.lo, (setTab_regs _ _ (by decide) (by decide)).trans he.hi,
    setTab_29 b, setTab_18 b, (setTab_regs _ _ (by decide) (by decide)).trans he.mask5⟩
theorem set24_encoded0 {V : Digest} {b : MachineState} (x : Word) (he : Encoded0 V b) : Encoded0 V (set24 b x) :=
  ⟨(set24_regs _ _ _ (by decide +kernel)).trans he.lo,(set24_regs _ _ _ (by decide +kernel)).trans he.hi,
    (set24_regs _ _ _ (by decide +kernel)).trans he.mask5⟩
theorem set24_encoded6 {V : Digest} {b : MachineState} (x : Word) (he : Encoded6 V b) : Encoded6 V (set24 b x) :=
  ⟨(set24_regs _ _ _ (by decide +kernel)).trans he.lo,(set24_regs _ _ _ (by decide +kernel)).trans he.hi,
    (set24_regs _ _ _ (by decide +kernel)).trans he.mask6,(set24_regs _ _ _ (by decide +kernel)).trans he.base6,
    (set24_regs _ _ _ (by decide +kernel)).trans he.mask5⟩
/-- The 8-bit field of r6 group `h` (1..8) in the selected half. -/
def raw6Of (V : Digest) (h : Nat) : Nat := V.toNat / 2^(r6Pos h) % 256
theorem gX_all : (List.range 17).all (fun q => (List.range (nRank q)).all (fun k => decide (gX q k < 257181)))
    = true := by decide +kernel
theorem gX_lt (q k : Nat) (hq : q < 17) (hk : k < nRank q) : gX q k < 257181 := by
  have h1 := List.all_eq_true.mp gX_all q (List.mem_range.mpr hq)
  have := List.all_eq_true.mp h1 k (List.mem_range.mpr hk)
  simpa using this
/-- A dispatch (only x14 written, no memory written) keeps the chain-loop base invariant. -/
theorem base_disp (c : NCtx) {s0 s t : MachineState} {acc : List Digest} {W : Nat → Prop}
    (hl : acc.length ≤ 51) (hB : c.Base s0 W acc s) (rt : RegsExcept s t [.x14])
    (ft : Frame s t (fun _ => False)) : c.Base s0 W acc t := by
  obtain ⟨hR, hF, hS⟩ := hB
  refine ⟨fun x hx => ?_, (hF.trans ft).mono (by intro A hA h; rcases h with h|h; exact h; contradiction), fun j hj => ?_⟩
  · rw [rt.get (by intro h; simp only [List.mem_singleton] at h; subst x; exact hx (by decide +kernel))]
    exact hR x hx
  · exact (hS j hj).frame ft (by unfold slot; split <;> omega) (by simp) (by simp)
/-- The end pc of group `q`'s last chain is its dispatch word `gX q (kOf q)`. -/
theorem endPc_group (c : NCtx) (q : Nat) (hq : q < 17) : c.endPc (3*q+nCh q-1) = gX q (c.kOf q) := by
  rcases nCh_cases q with ⟨rfl, h2⟩ | ⟨h16, h3⟩
  · rw [h2]
    simp only [endPc, show 3*16+2-1 = 49 from rfl, show (49:Nat) < 50 by decide, if_true, show (49:Nat)%3 ≠ 0 by decide,
      show (49:Nat)%3 = 1 by decide, if_false, qC, show (49:Nat)/3 = 16 by decide, gX]
  · rw [h3]
    simp only [endPc, show 3*q+3-1 = 3*q+2 by omega, show 3*q+2 < 50 by omega, if_true,
      show (3*q+2)%3 ≠ 0 by omega, show (3*q+2)%3 ≠ 1 by omega, if_false, qX, show (3*q+2)/3 = q by omega]
theorem raw6Of_eq (V : Digest) (h : Nat) (hh : h < 9) : raw6Of V h = T3.r6Raw V h := (r6Raw_eq V h hh).symm
/-- Validity of top group `q < 17` (the range check its dispatch performs): r6 groups `T3.r6Valid`, r5 groups
rank < 125, the r7 pair rank < 49. -/
def gValid (V : Digest) (q : Nat) : Prop :=
  if q < 9 then T3.r6Valid V q = true else if q < 16 then T3.r5Rank V q < 125 else T3.r7Rank V < 49
instance (V : Digest) (q : Nat) : Decidable (gValid V q) := by unfold gValid; infer_instance
/-- Rank of top group `q < 17`. -/
def gRank (V : Digest) (q : Nat) : Nat :=
  if q < 9 then T3.r6Rank V q else if q < 16 then T3.r5Rank V q else T3.r7Rank V
/-- Steps from the end of group `j - 1` (its dispatch word) to the entry word of group `j`: group 0's 5-word
dispatch, the r6 dispatches (4), dispatch9 + bge9 (4), #938's r5 dispatches and the pair's (3). -/
def dspR6 (j : Nat) : Nat := if j = 1 then 5 else if j < 9 then 4 else if j = 9 then 4 else 3
theorem dspR6_le (j : Nat) : dspR6 j ≤ 5 := by unfold dspR6; split_ifs <;> omega
theorem r6DispR_steps (h : Nat) (h2 : 2 ≤ h) (h8 : h < 9) : (r6DispR h).steps = dspR6 h ∧ (r6DispR h).cycles = dspR6 h := by
  unfold r6DispR dspR6
  simp [show h ≠ 1 by omega, h8]
theorem gValid_r6 (V : Digest) (h : Nat) (h1 : 1 ≤ h) (h8 : h < 9) : gValid V h ↔ raw6Of V h < 216 := by
  unfold gValid T3.r6Valid; rw [raw6Of_eq V h h8]; simp [h8, show h ≠ 0 by omega]
theorem gRank_r6 (V : Digest) (h : Nat) (h1 : 1 ≤ h) (h8 : h < 9) : gRank V h = raw6Of V h := by
  unfold gRank T3.r6Rank; rw [raw6Of_eq V h h8]; simp [h8, show h ≠ 0 by omega]
theorem gValid_r5 (V : Digest) (q : Nat) (h9 : 9 ≤ q) (hq : q < 16) : gValid V q ↔ T3.r5Rank V q < 125 := by
  unfold gValid; simp [show ¬ q < 9 by omega, hq]
theorem gRank_r5 (V : Digest) (q : Nat) (h9 : 9 ≤ q) (hq : q < 16) : gRank V q = T3.r5Rank V q := by
  unfold gRank; simp [show ¬ q < 9 by omega, hq]
theorem gValid_pair (V : Digest) : gValid V 16 ↔ T3.r7Rank V < 49 := by unfold gValid; simp
theorem gRank_pair (V : Digest) : gRank V 16 = T3.r7Rank V := by unfold gRank; simp
theorem gValid_g0 (V : Digest) : gValid V 0 ↔ 40 ≤ T3.r6Raw V 0 := by
  unfold gValid T3.r6Valid; simp
theorem gRank_g0 (V : Digest) : gRank V 0 = T3.r6Raw V 0 - 40 := by
  unfold gRank T3.r6Rank; simp
/-- Valid T51 top words (every group in range; no spare bit) in the dispatch's terms. -/
theorem topRanksValid_iff (V : Digest) :
    T3.topRanksValid V = true ↔ ∀ q, q < 17 → gValid V q := by
  simp only [T3.topRanksValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.mem_range'_1]
  constructor
  · rintro ⟨⟨h6, h5⟩, h7⟩ q hq
    unfold gValid; split_ifs with h9 h16
    · exact h6 q h9
    · exact h5 q ⟨by omega, by omega⟩
    · exact h7
  · intro hg
    refine ⟨⟨fun q hq => ?_, fun q hq => ?_⟩, ?_⟩
    · have := hg q (by omega); unfold gValid at this; simpa [hq] using this
    · have := hg q (by omega); unfold gValid at this; simpa [show ¬ q < 9 by omega, show q < 16 by omega] using this
    · have := hg 16 (by omega); unfold gValid at this; simpa using this
/-- End of top group `q` (1 <= q < 16): the dispatch into group `q+1` reaches its entry word (valid field) or faults. -/
def DispOutR6 (c : NCtx) (s0 : MachineState) (V : Digest) (q : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  (gValid V (q+1) → ∃ t, Steps vimage s (dspR6 (q+1)) (dspR6 (q+1)) t ∧
      c.Base s0 (c.Wr (3*(q+1))) acc t ∧ acc.length = 3*(q+1) ∧ t.pc = pcOf (entW (q+1) (gRank V (q+1)))) ∧
  (¬ gValid V (q+1) → ∃ k t, Steps vimage s k k t ∧ k ≤ 5 ∧ fetch vimage t = none)
theorem endInv_group (c : NCtx) {s0 s : MachineState} {acc : List Digest} (q : Nat) (hq : q < 16)
    (hs : c.EndInv s0 (3*q+2) acc s) : s.pc = pcOf (gX q (c.kOf q)) := by
  have he := c.endPc_group q (by omega)
  rw [show 3*q+nCh q-1 = 3*q+2 by unfold nCh; rw [if_neg (by omega)]; omega] at he
  rw [hs.2.2, he]
/-- T51: end of group 0 (chain 2 done). Group 0's 5-word dispatch loads t4 = 0xFF00 / s2 = 856064 (the base becomes
`setTab s0`) and lands on group 1's cell (field `raw6Of V 1 < 216`) or a zero-word guard. -/
theorem end_dispatch0 (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded0 V s0) (hk : ∀p∈c.known,s0.getReg p.1=p.2) (hmask : s0.getMem 0xffbdf0#64 = 65280#64)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 2 acc s) :
    (gValid V 1 → ∃ t, Steps vimage s (dspR6 1) (dspR6 1) t ∧ c.Base (setTab s0) (c.Wr 3) acc t ∧
        acc.length = 3 ∧ t.pc = pcOf (entW 1 (gRank V 1))) ∧
    (¬ gValid V 1 → ∃ k t, Steps vimage s k k t ∧ k ≤ 5 ∧ fetch vimage t = none) := by
  have hpc' := c.endInv_group 0 (by omega) hs
  obtain ⟨⟨hR,hF,hS⟩,hlen,-⟩ := hs
  have hr : vrun (gX 0 (c.kOf 0)) 5 = some g0DispR := by
    have := (c.groupFacts hds 0 (by omega)).disp
    simpa [nextDispR] using this
  have hbound := gX_lt 0 (c.kOf 0) (by omega) (c.kOf_nRank hds 0 (by omega))
  have h16 : s.getReg .x16 = V.extractLsb' 0 64 := (hR _ (by decide +kernel)).trans he.lo
  have h9 : s.getReg .x9 = 0xffbf10#64 :=
    (hR _ (by decide +kernel)).trans (hk (.x9, BitVec.ofNat 64 0xffbf10) (by simp [known]))
  have hnw : ¬ c.Wr 3 0xffbdf0 := by
    have hb := c.bufferEnd_bounds 3
    rw [slot_pos 3 (by omega)] at hb
    have hhi := hc.2.2.2.2.1
    unfold Wr; rw [slot0, slot1]; omega
  have hm : s.getMem 0xffbdf0#64 = 65280#64 := by
    rw [show (0xffbdf0#64 : Word) = BitVec.ofNat 64 0xffbdf0 from rfl, hF.get (by norm_num) hnw]; exact hmask
  obtain ⟨t, st, pt, t29, t18, rt, ft⟩ := g0_dispatch_step hbound hr s V hpc' h16 h9 hm
  have base_of : c.Base (setTab s0) (c.Wr 3) acc t := by
    refine ⟨fun x hx => ?_, fun A hA hn => ?_, fun j hj => ?_⟩
    · by_cases h29 : x = .x29
      · subst h29; rw [t29, setTab_29]
      · by_cases h18 : x = .x18
        · subst h18; rw [t18, setTab_18]
        · have h14 : x ≠ .x14 := fun h => hx (by subst h; decide)
          rw [rt.get (by simp [h29, h18, h14]), setTab_regs _ _ h29 h18]; exact hR x hx
    · rw [ft A hA (by simp), setTab_mem]; exact hF A hA hn
    · exact (hS j hj).frame ft (by unfold slot; split <;> omega) (by simp) (by simp)
  have hraw : V.toNat / 2^8 % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have e1 : raw6Of V 1 = V.toNat / 2^8 % 256 := by unfold raw6Of r6Pos; norm_num
  rw [gValid_r6 V 1 (by omega) (by omega), gRank_r6 V 1 (by omega) (by omega), e1]
  have hd : dspR6 1 = 5 := rfl
  rw [hd]
  refine ⟨fun hv => ⟨t, st, base_of, hlen, ?_⟩, fun hv => ⟨5, t, st, le_rfl, ?_⟩⟩
  · have hcell := cell6_valid 1 _ (by omega) (by simp [raw6Valid]; omega)
    rw [pt, hcell]; simp [entW]
  · exact guard6_fault 1 _ (by omega) hraw (by simp [raw6Valid]; omega) (by omega) t pt
/-- End of r6 group `q` (1 <= q < 8): the dispatch into r6 group `q+1`. -/
theorem end_dispatch6 (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded6 V s0) (q : Nat) (h1 : 1 ≤ q) (hq : q < 8) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 (3*q+2) acc s) : c.DispOutR6 s0 V q acc s := by
  have hpc' := c.endInv_group q (by omega) hs
  obtain ⟨hB,hlen,-⟩ := hs
  have hR := hB.1
  have hr : vrun (gX q (c.kOf q)) 5 = some (r6DispR (q+1)) := by
    have := (c.groupFacts hds q (by omega)).disp
    simpa [nextDispR, show q ≠ 0 by omega, hq] using this
  have hbound := gX_lt q (c.kOf q) (by omega) (c.kOf_nRank hds q (by omega))
  have h16 : s.getReg .x16 = V.extractLsb' 0 64 := (hR _ (by decide +kernel)).trans he.lo
  have h17 : s.getReg .x17 = V.extractLsb' 64 64 := (hR _ (by decide +kernel)).trans he.hi
  have h29 : s.getReg .x29 = 65280#64 := (hR _ (by decide +kernel)).trans he.mask6
  have h18 : s.getReg .x18 = 856064#64 := (hR _ (by decide +kernel)).trans he.base6
  obtain ⟨t, st, pt, rt, ft⟩ := r6_dispatch_step (h := q+1) (by omega) (by omega) hbound hr s V hpc' h16 h17 h29 h18
  obtain ⟨hst, hcy⟩ := r6DispR_steps (q+1) (by omega) (by omega)
  rw [hst, hcy] at st
  have base_of : c.Base s0 (c.Wr (3*(q+1))) acc t := by
    rw [show 3*(q+1) = 3*q+2+1 by omega]; exact c.base_disp (by omega) hB rt ft
  have hraw : V.toNat / 2^(r6Pos (q+1)) % 256 < 256 := Nat.mod_lt _ (by norm_num)
  unfold DispOutR6
  rw [gValid_r6 V (q+1) (by omega) (by omega), gRank_r6 V (q+1) (by omega) (by omega)]
  refine ⟨fun hv => ⟨t, st, base_of, by omega, ?_⟩, fun hv => ⟨dspR6 (q+1), t, st, dspR6_le _, ?_⟩⟩
  · have hcell := cell6_valid (q+1) (V.toNat / 2^(r6Pos (q+1)) % 256) (by omega)
      (by simp only [raw6Valid, show q+1 ≠ 0 by omega, if_false, decide_eq_true_eq]; unfold raw6Of at hv; exact hv)
    rw [pt, hcell]; unfold entW raw6Of; simp [show q+1 ≠ 9 by omega, show q+1 ≠ 0 by omega]
  · exact guard6_fault (q+1) _ (by omega) hraw
      (by simp only [raw6Valid, show q+1 ≠ 0 by omega, if_false, decide_eq_false_iff_not]; unfold raw6Of at hv; omega)
      (by omega) t pt
/-- End of group `q` (8 <= q < 16) into group `q+1`: g8 -> q9 (#938's dispatch9 + bge9), q9..q14 -> q+1 (#938's
dispatch), q15 -> the r7 pair (#938's dispatch into group 8). -/
theorem end_dispatch5 (c : NCtx) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded6 V s0) (q : Nat) (h8 : 8 ≤ q) (hq : q < 16) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 (3*q+2) acc s) : c.DispOutR6 s0 V q acc s := by
  have hpc' := c.endInv_group q (by omega) hs
  obtain ⟨hB, hlen, -⟩ := hs
  have hR := hB.1
  have hr : vrun (gX q (c.kOf q)) 5 = some (nextDispR q) := (c.groupFacts hds q (by omega)).disp
  have hbound := gX_lt q (c.kOf q) (by omega) (c.kOf_nRank hds q (by omega))
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
  set v := r5V V with hvdef
  by_cases hq8 : q = 8
  · subst q
    rw [gValid_r5 V 9 (by omega) (by omega), gRank_r5 V 9 (by omega) (by omega), ← topRank_r5V V 9 (by omega) (by omega),
      ← hvdef]
    have hr9 : nextDispR 8 = dispatch9R := by simp [nextDispR]
    rw [hr9] at hr
    obtain ⟨t,st,pt,rt,ft⟩ := dispatch9_step hbound hr s v hpc' h17 h6
    have hr9 : Search.topRank (r5V V) (8+1)=v.toNat/2^63%2+2*(v.toNat/2^64%64) := topRank9 v
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
          rw [he9, cellW9, cellW9]
          unfold pcOf
          exact congrArg (BitVec.ofNat 64) (by omega)
      · have hb0 : v.toNat/2^63%2=0 := by omega
        rw [if_neg hb] at pz
        rw [hb0]
        refine ⟨fun _ => ⟨z,st5,base_of z rtz ftz,by omega,?_⟩,fun hv => by omega⟩
        rw [pz]
        have he9 : entW (8+1) (0+2*u)=cellW 9 (2*u)+1 := by
          unfold entW; rw [if_pos (by omega)]; simp
        rw [he9]
  · by_cases hq15 : q = 15
    · -- q15 -> the r7 pair (#938's dispatch into group 8, bits 56..62)
      subst q
      rw [gValid_pair, gRank_pair, ← topRank_r5V_pair V, ← hvdef]
      have hr' : nextDispR 15 = dispatchR 8 := by simp [nextDispR]
      rw [hr'] at hr
      obtain ⟨t,st,pt,rt,ft⟩ := dispatch_step (q := 8) (by omega) (by omega) hbound hr s v hpc' h16 h17 h6
      have hd : dspR6 (15+1)=3 := rfl
      rw [hd]
      have hk := topRank_lt v 8
      by_cases h49 : Search.topRank v 8 < 49
      · refine ⟨fun _ => ⟨t,st,base_of t rt ft,by omega,?_⟩,fun hv => absurd h49 hv⟩
        rw [pt, cell_value_pair _ (by omega)]; unfold entW; simp
      · refine ⟨fun hv => absurd hv h49, fun _ => ⟨3,t,st,by omega,?_⟩⟩
        rcases pair_landing _ hk t pt with ⟨h, -⟩ | hf
        · exact absurd h h49
        · exact hf
    · have hr' : nextDispR q = dispatchR (q+1) := by
        simp [nextDispR, show q ≠ 0 by omega, show ¬ q < 8 by omega, hq8, show q < 15 by omega]
      rw [hr'] at hr
      rw [gValid_r5 V (q+1) (by omega) (by omega), gRank_r5 V (q+1) (by omega) (by omega),
        ← topRank_r5V V (q+1) (by omega) (by omega), ← hvdef]
      obtain ⟨t,st,pt,rt,ft⟩ := dispatch_step (q := q+1) (by omega) (by omega) hbound hr s v hpc' h16 h17 h6
      have hd : dspR6 (q+1)=3 := by
        unfold dspR6; simp only [show q+1 ≠ 1 by omega, show ¬ q+1 < 9 by omega, show q+1 ≠ 9 by omega, if_false]
      rw [hd]
      have hk := topRank_lt v (q+1)
      refine ⟨fun hv => ⟨t,st,base_of t rt ft,by omega,?_⟩,fun hv => ⟨3,t,st,by omega,?_⟩⟩
      · rw [pt,cell_value _ _ (by omega) (by omega) (by omega)]
        have e : entW (q+1) (Search.topRank v (q+1)) = cellW (q+1) (Search.topRank v (q+1)) := by
          unfold entW; rw [if_neg (fun h => hq8 (by omega))]; rfl
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
/-- Every T51 group transition `q -> q+1` (1 <= q < 16; group 0's is `end_dispatch0`). -/
theorem end_dispatchR6 (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded6 V s0) (q : Nat) (h1 : 1 ≤ q) (hq : q < 16) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 (3*q+2) acc s) : c.DispOutR6 s0 V q acc s := by
  by_cases h8 : q < 8
  · exact c.end_dispatch6 hc hds he q h1 h8 acc s hs
  · exact c.end_dispatch5 hds he q (by omega) hq acc s hs
theorem data_sum_le (c : NCtx) (hds : c.DigitsOk) : ((List.range 50).map c.dig).sum ≤ 231 := by
  have h : ∀ n, n ≤ 50 → ((List.range n).map c.dig).sum ≤ ((List.range n).map topMax).sum := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
      have h1 := hds n (by omega)
      have h2 := ih (by omega)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
  have h2 : ((List.range 50).map topMax).sum = 231 := by decide +kernel
  exact (h 50 le_rfl).trans h2.le
/-- End of the r7 pair (chain 49 done, s8 = T - data sum): the checksum dispatch reaches chain 50's arm for digit
`T - ds` when that lies in 0..5, otherwise it faults. -/
theorem end_ck (c : NCtx) (hds : c.DigitsOk) {s0 : MachineState} (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 49 acc s) (ds : Nat) (hdsum : ((List.range 50).map c.dig).sum = ds)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 topT - BitVec.ofNat 64 ds) :
    (topT - 5 ≤ ds ∧ ds ≤ topT → ∃ t, Steps vimage s 3 3 t ∧ c.Base s0 (c.Wr (49+1)) acc t ∧ acc.length = 49+1 ∧
        t.pc = pcOf (ckArm (topT - ds))) ∧
      (¬ (topT - 5 ≤ ds ∧ ds ≤ topT) → ∃ t, Steps vimage s 3 3 t ∧ fetch vimage t = none) := by
  have he49 : c.endPc 49 = gX 16 (c.kOf 16) := by
    have := c.endPc_group 16 (by omega); simpa [nCh] using this
  have hpc' : s.pc = pcOf (gX 16 (c.kOf 16)) := by rw [hs.2.2, he49]
  obtain ⟨hB, hlen, -⟩ := hs
  have hr : vrun (gX 16 (c.kOf 16)) 5 = some ckDispR := by
    have := (c.groupFacts hds 16 (by omega)).disp
    simpa [nextDispR] using this
  have hd : ds ≤ 231 := hdsum ▸ c.data_sum_le hds
  have hbound := gX_lt 16 (c.kOf 16) (by omega) (c.kOf_nRank hds 16 (by omega))
  obtain ⟨t, st, pt, rt, ft⟩ := ck_dispatch_step hbound hr s ds hd hpc' h24
  have base_of : c.Base s0 (c.Wr (49+1)) acc t := c.base_disp (by omega) hB rt ft
  refine ⟨fun hv => ⟨t, st, base_of, hlen, ?_⟩, fun hv => ⟨t, st, ?_⟩⟩
  · have hw : ckWord ds = ckArm (topT - ds) := by unfold ckWord ckArm topT at *; omega
    rw [pt, hw]
  · rcases ck_landing ds (by omega) with ⟨h1, h2, -⟩ | hf
    · exact absurd ⟨h1, h2⟩ hv
    · exact hf t pt
/-- The NCtx digits of chains 0..49 are the spec's decoded digits of the selected half `V`. -/
def Fit6 (c : NCtx) (V : Digest) : Prop := ∀ i, i < 50 → c.dig i = T3.coreDigit 0 V i
theorem coreDigit_top (V : Digest) (q k : Nat) (hq : q < 16) (hk : k < 3) :
    T3.coreDigit 0 V (3*q+k) = if q < 9 then T3.r6Rank V q / 6^k % 6 else T3.r5Rank V q / 5^k % 5 := by
  unfold T3.coreDigit
  simp only [if_true, show (3*q+k)/3 = q by omega, show (3*q+k)%3 = k by omega]
  by_cases h9 : q < 9
  · simp [h9, show 3*q+k < 27 by omega]
  · simp [h9, show ¬ 3*q+k < 27 by omega, show 3*q+k < 48 by omega]
theorem coreDigit_pair (V : Digest) (k : Nat) (hk : k < 2) :
    T3.coreDigit 0 V (48+k) = T3.r7Rank V / 7^k % 7 := by
  unfold T3.coreDigit
  simp [show ¬ 48+k < 27 by omega, show ¬ 48+k < 48 by omega, show 48+k < 50 by omega]
theorem fit6_le (c : NCtx) {V : Digest} (hf : c.Fit6 V) (i : Nat) (hi : i < 50) : c.dig i ≤ topMax i := by
  rw [topMax_mx i hi]
  by_cases h48 : i < 48
  · obtain ⟨q, k, hk, rfl⟩ : ∃ q k, k < 3 ∧ i = 3*q+k := ⟨i/3, i%3, by omega, by omega⟩
    rw [hf _ hi, coreDigit_top V q k (by omega) hk]
    unfold mx
    rw [show (3*q+k)/3 = q by omega]
    by_cases h9 : q < 9
    · simp only [h9, if_true]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    · simp only [h9, if_false, show q < 16 by omega, if_true]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 2 ∧ i = 48+k := ⟨i-48, by omega, by omega⟩
    rw [hf _ hi, coreDigit_pair V k hk, show (48+k)/3 = 16 by omega]
    exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
theorem gRank_lt (V : Digest) (q : Nat) (hq : q < 17) (hv : gValid V q) : gRank V q < nRank q := by
  unfold gValid at hv; unfold gRank nRank
  by_cases h9 : q < 9
  · simp only [h9, if_true] at hv ⊢
    simp only [show q ≠ 16 by omega, if_false, mx, h9, if_true]
    unfold T3.r6Valid at hv; unfold T3.r6Rank
    have := Nat.mod_lt (T3.topCode V / 2 ^ T3.r6Shift q) (show 0 < 256 by norm_num)
    unfold T3.r6Raw at hv ⊢
    split_ifs at hv ⊢ <;> simp at hv <;> omega
  · by_cases h16 : q < 16
    · simp only [h9, h16, if_false, if_true] at hv ⊢
      simp only [show q ≠ 16 by omega, if_false, mx, h9, h16, if_true]; omega
    · have : q = 16 := by omega
      subst this
      simp only [h9, h16, if_false] at hv ⊢
      simpa using hv
/-- With fitting digits, the NCtx group index of a valid group is the field's rank. -/
theorem fit_rank6 (c : NCtx) {V : Digest} (hf : c.Fit6 V) (q : Nat) (hq : q < 17) (hv : gValid V q) :
    c.kOf q = gRank V q := by
  have hl := gRank_lt V q hq hv
  by_cases h16 : q = 16
  · subst h16
    unfold kOf; rw [if_pos rfl, hf 48 (by omega), hf 49 (by omega)]
    have e0 := coreDigit_pair V 0 (by omega)
    have e1 := coreDigit_pair V 1 (by omega)
    simp only [Nat.add_zero] at e0
    rw [e0, show (49:Nat) = 48+1 from rfl, e1]
    rw [gRank_pair] at hl ⊢
    unfold nRank at hl; simp at hl
    norm_num; omega
  rw [c.kOf_triple q (by omega), hf (3*q) (by omega), hf (3*q+1) (by omega), hf (3*q+2) (by omega)]
  have e0 := coreDigit_top V q 0 (by omega) (by omega)
  have e1 := coreDigit_top V q 1 (by omega) (by omega)
  have e2 := coreDigit_top V q 2 (by omega) (by omega)
  simp only [Nat.add_zero] at e0
  rw [e0, e1, e2]
  unfold nRank at hl
  unfold gRank at hl ⊢
  by_cases h9 : q < 9
  · simp only [h9, if_true, mx, h16, if_false] at hl ⊢; norm_num at hl ⊢; omega
  · simp only [h9, if_false, mx, show q < 16 by omega, if_true, h16] at hl ⊢; norm_num at hl ⊢; omega
/-- Group transition into the next group's `GroupIn` (valid field), 1 <= q < 16. -/
theorem end_dispatchR6_in (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded6 V s0) (hf : c.Fit6 V) (q : Nat) (h1 : 1 ≤ q) (hq : q < 16) (hv : gValid V (q+1))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 (3*q+2) acc s) :
    ∃ t, Steps vimage s (dspR6 (q+1)) (dspR6 (q+1)) t ∧ c.GroupIn s0 (q+1) acc t := by
  obtain ⟨t, st, hB, hl, pt⟩ := (c.end_dispatchR6 hc hds he q h1 hq acc s hs).1 hv
  refine ⟨t, st, hB, hl, ?_⟩
  rw [pt]; unfold entPc; rw [c.fit_rank6 hf (q+1) (by omega) hv]
/-- Group transition into an invalid next group: the run faults within 5 steps. -/
theorem end_dispatchR6_bad (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded6 V s0) (q : Nat) (h1 : 1 ≤ q) (hq : q < 16) (hv : ¬ gValid V (q+1))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 (3*q+2) acc s) :
    ∃ k t, Steps vimage s k k t ∧ k ≤ 5 ∧ fetch vimage t = none :=
  (c.end_dispatchR6 hc hds he q h1 hq acc s hs).2 hv
/-- Group 0's transition into group 1's `GroupIn` on the base `setTab s0` (valid field). -/
theorem end_dispatch0_in (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState} {V : Digest}
    (he : Encoded0 V s0) (hk : ∀p∈c.known,s0.getReg p.1=p.2) (hmask : s0.getMem 0xffbdf0#64 = 65280#64)
    (hf : c.Fit6 V) (hv : gValid V 1) (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 2 acc s) :
    ∃ t, Steps vimage s (dspR6 1) (dspR6 1) t ∧ c.GroupIn (setTab s0) 1 acc t := by
  obtain ⟨t, st, hB, hl, pt⟩ := (c.end_dispatch0 hc hds he hk hmask acc s hs).1 hv
  refine ⟨t, st, hB, hl, ?_⟩
  rw [pt]; unfold entPc; rw [c.fit_rank6 hf 1 (by omega) hv]
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
/-- Group 0's cell word `addi s8,zero,T-kss`: the T51 top-region entry into chain 0. -/
theorem g0_entry (c : NCtx) (hds : c.DigitsOk) {b : MachineState} (acc : List Digest) (s : MachineState)
    (hs : c.GroupIn b 0 acc s) :
    ∃t,Steps vimage s 1 1 t ∧ c.ChainIn (set24 b (c.s8v 0)) 0 acc t := by
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩ := hs
  have hk := c.kOf_nRank hds 0 (by omega)
  have hchk := s8Run_at 0 (c.kOf 0) (by omega) hk
  rw [if_pos rfl] at hchk
  have hrun := rOK_eq hchk
  have hp : entW 0 (c.kOf 0)<257181 := by have := entW_lt 0 _ (by omega) hk; omega
  have hst := piece_steps45 hrun hp s hpc (by simp [guardR])
  set r := guardR (c.kOf 0) with hr
  refine ⟨r.toState s,hst,⟨⟨fun x hx => ?_,fun A hA hn => ?_,fun j hj => ?_⟩,hlen,?_⟩⟩
  · rw [Result.toState_getReg]
    by_cases hx : x=.x24
    · subst x
      simp only [hr,guardR]
      rw [RegFile.get_set_self _ _ (by decide +kernel),set24_24]
      simp only [E.eval]
      rw [c.s8v0 hds]
    · simp only [hr,guardR]
      rw [RegFile.get_set_ne _ _ hx,RegFile.init_get_eval,set24_regs _ _ _ hx]
      exact hR x (by assumption)
  · rw [Result.toState_getMem,set24_mem]
    simp only [hr,guardR]
    rw [memEval_nil]
    exact hF A hA hn
  · have hfr : Frame s (r.toState s) (fun _ => False) := fun A _ _ => by
      rw [Result.toState_getMem]; simp [hr,guardR,memEval_nil]
    exact (hS j hj).frame hfr (by unfold slot; split <;> omega) (by simp) (by simp)
  · rw [Result.toState_pc]
    simp only [hr,guardR,E.eval]
    unfold startPc leadPc leadOff entW
    simp
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
