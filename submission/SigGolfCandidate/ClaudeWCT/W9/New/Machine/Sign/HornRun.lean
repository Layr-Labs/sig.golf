import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsChain
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.GfMul

/-!
# The shared GF(2^128) Horner routine HORN of the stage-A sign image

HORN (entry `hornI`, return through `x1`) evaluates `familyEval coefs d` for the 102 coefficients stored at
`COEF + 16 k` and the point `d = x6 < 1024`, and stores the result at `CHAINW + 48`. Horner loop `HK`: `x7` walks
down the coefficients, `(x10, x11)` hold the accumulator; bit loop `HB`: `(x10, x11, x12)` hold `acc * 2^k`,
`(x13, x14, x15)` hold `clmulSmall acc d k`, `x16 = d >> k`; `HF` folds once with 0x87 and adds the coefficient.
-/

section
set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
open Gf ClaudeWCT.Arith

/-- Registers HORN may change. -/
def hornRegs : List Reg := [.x7, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x28, .x29]
/-- The coefficient buffer. -/
def CoefAt (t : MachineState) (coefs : List Digest) : Prop :=
  ∀ k < 102, DigAt t (COEF + 16 * k) (coefs.getD k 0)

theorem CoefAt.frame {s t : MachineState} {coefs : List Digest} {W : Nat → Prop} (h : CoefAt s coefs)
    (hf : Frame s t W) (hW : ∀ A, COEF ≤ A → A < COEF + 1632 → ¬ W A) : CoefAt t coefs :=
  fun k hk => (h k hk).frame hf (by unfold COEF; omega) (hW _ (by omega) (by omega)) (hW _ (by omega) (by omega))

section steps
variable {im : Image}

theorem horn_look (hcode : NewCodeAt im) : LookOK im (coordLook 0) := coordLook_ok hcode (by norm_num)

theorem step_H0 (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf hornI) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf hkI ∧ t.getReg .x7 = BitVec.ofNat 64 (COEF + 16 * 102) ∧
      t.getReg .x10 = BitVec.ofNat 64 0 ∧ t.getReg .x11 = BitVec.ofNat 64 0 ∧
      t.getReg .x28 = BitVec.ofNat 64 COEF ∧ RegsExcept s t [.x7, .x10, .x11, .x28] ∧
      Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (horn_look hcode) runH0_eq s hpc (no_obl s) (no_br s)
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩

theorem step_HK (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf hkI) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf hbI ∧
      t.getReg .x7 = s.getReg .x7 + BitVec.ofNat 64 (2 ^ 64 - 16) ∧ t.getReg .x12 = BitVec.ofNat 64 0 ∧
      t.getReg .x13 = BitVec.ofNat 64 0 ∧ t.getReg .x14 = BitVec.ofNat 64 0 ∧ t.getReg .x15 = BitVec.ofNat 64 0 ∧
      t.getReg .x16 = s.getReg .x6 ∧ RegsExcept s t [.x7, .x12, .x13, .x14, .x15, .x16] ∧
      Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (horn_look hcode) runHK_eq s hpc (no_obl s) (no_br s)
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩

/-- Cycles of one bit iteration (`b1`: the bit is zero, `b2`: more bits follow). -/
def hbRegs : List Reg := [.x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]
def hbK (b1 b2 : Bool) : Nat := (if b1 then 11 else 14) + (if b2 then 0 else 1)

theorem step_HB (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf hbI) (b1 b2 : Bool)
    (h1 : (s.getReg .x16 &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0) = b1)
    (h2 : (s.getReg .x16 >>> 1 != BitVec.ofNat 64 0) = b2) :
    ∃ t, Steps im s (hbK b1 b2) (hbK b1 b2) t ∧ t.pc = pcOf (if b2 then hbI else hfI) ∧
      t.getReg .x10 = s.getReg .x10 <<< 1 ∧
      t.getReg .x11 = (s.getReg .x11 <<< 1) ||| (s.getReg .x10 >>> 63) ∧
      t.getReg .x12 = (s.getReg .x12 <<< 1) ||| (s.getReg .x11 >>> 63) ∧
      t.getReg .x13 = (if b1 then s.getReg .x13 else s.getReg .x13 ^^^ s.getReg .x10) ∧
      t.getReg .x14 = (if b1 then s.getReg .x14 else s.getReg .x14 ^^^ s.getReg .x11) ∧
      t.getReg .x15 = (if b1 then s.getReg .x15 else s.getReg .x15 ^^^ s.getReg .x12) ∧
      t.getReg .x16 = s.getReg .x16 >>> 1 ∧ RegsExcept s t hbRegs ∧ Frame s t (fun _ => False) := by
  have hbr : ∀ b ∈ (expHB b1 b2).brs, b.holds s := by
    intro b hb
    simp only [expHB, pres, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · show (BinOp.eval .srl (s.getReg .x16) (BitVec.ofNat 64 1) != BitVec.ofNat 64 0) = b2
      rw [binop_srl _ _ (by norm_num)]; exact h2
    · exact h1
  obtain ⟨hst, -⟩ := run_pres (horn_look hcode) (runHB_eq b1 b2) s hpc (no_obl s) hbr
  have e10 : ((expHB b1 b2).toState s).getReg .x10 = s.getReg .x10 <<< 1 := by
    rw [PRes.toState_getReg']; cases b1 <;> exact binop_sll _ 1 (by norm_num)
  have e11 : ((expHB b1 b2).toState s).getReg .x11 = (s.getReg .x11 <<< 1) ||| (s.getReg .x10 >>> 63) := by
    rw [PRes.toState_getReg']
    cases b1 <;>
    · show BinOp.eval .or (BinOp.eval .sll (s.getReg .x11) (BitVec.ofNat 64 1))
        (BinOp.eval .srl (s.getReg .x10) (BitVec.ofNat 64 63)) = _
      rw [binop_sll _ _ (by norm_num), binop_srl _ _ (by norm_num)]; rfl
  have e12 : ((expHB b1 b2).toState s).getReg .x12 = (s.getReg .x12 <<< 1) ||| (s.getReg .x11 >>> 63) := by
    rw [PRes.toState_getReg']
    cases b1 <;>
    · show BinOp.eval .or (BinOp.eval .sll (s.getReg .x12) (BitVec.ofNat 64 1))
        (BinOp.eval .srl (s.getReg .x11) (BitVec.ofNat 64 63)) = _
      rw [binop_sll _ _ (by norm_num), binop_srl _ _ (by norm_num)]; rfl
  have e16 : ((expHB b1 b2).toState s).getReg .x16 = s.getReg .x16 >>> 1 := by
    rw [PRes.toState_getReg']; cases b1 <;> exact binop_srl _ 1 (by norm_num)
  refine ⟨_, hst, ?_, e10, e11, e12, ?_, ?_, ?_, e16, (pres_regsExcept _ _ _ _ _ _ _ s).mono ?_, fun A _ _ => rfl⟩
  · cases b2 <;> rfl
  · rw [PRes.toState_getReg']; cases b1 <;> rfl
  · rw [PRes.toState_getReg']; cases b1 <;> rfl
  · rw [PRes.toState_getReg']; cases b1 <;> rfl
  · cases b1 <;> simp [hbShift, hbRegs]

theorem eval_foldE (s : MachineState) : foldE.eval s = foldLo (s.getReg .x13) (s.getReg .x15) := by
  show BinOp.eval .xor (BinOp.eval .xor (BinOp.eval .xor (BinOp.eval .xor (s.getReg .x13)
    (BinOp.eval .sll (s.getReg .x15) (BitVec.ofNat 64 1))) (BinOp.eval .sll (s.getReg .x15) (BitVec.ofNat 64 2)))
    (BinOp.eval .sll (s.getReg .x15) (BitVec.ofNat 64 7))) (s.getReg .x15) = _
  rw [binop_sll _ _ (by norm_num), binop_sll _ _ (by norm_num), binop_sll _ _ (by norm_num)]
  rfl

theorem eval_c0E (s : MachineState) {A : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 A) :
    c0E.eval s = s.getMem (BitVec.ofNat 64 A) := by
  show s.getMem (s.getReg .x7) = _; rw [h7]

theorem eval_c1E (s : MachineState) {A : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 A) :
    c1E.eval s = s.getMem (BitVec.ofNat 64 (A + 8)) := by
  show s.getMem (s.getReg .x7 + BitVec.ofNat 64 8) = _; rw [h7, ofNat_add_ofNat]

theorem hfObl_holds (s : MachineState) {A : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA' : A + 16 ≤ MEMORY_BYTES) : ∀ o ∈ hfObl, o.holds s := by
  intro o ho
  simp only [hfObl, List.mem_cons, List.not_mem_nil, or_false] at ho
  have hb : (E.reg .x7).eval s = BitVec.ofNat 64 A := h7
  rcases ho with rfl | rfl
  · exact valid_ofNat hb (by omega) (by omega)
  · exact valid_ofNat (off := 0) hb (by omega) (by omega)

theorem step_HF_cont (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf hfI) {A : Nat}
    (h7 : s.getReg .x7 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 16 ≤ MEMORY_BYTES)
    (hne : s.getReg .x7 ≠ s.getReg .x28) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf hkI ∧
      t.getReg .x10 = foldLo (s.getReg .x13) (s.getReg .x15) ^^^ s.getMem (BitVec.ofNat 64 A) ∧
      t.getReg .x11 = s.getReg .x14 ^^^ s.getMem (BitVec.ofNat 64 (A + 8)) ∧
      RegsExcept s t hfRegs.unzip.1 ∧ Frame s t (fun _ => False) := by
  have hbr : ∀ b ∈ (expHF true).brs, b.holds s := by
    intro b hb
    simp only [expHF, if_true, pres, List.mem_singleton] at hb
    subst hb
    show (s.getReg .x7 != s.getReg .x28) = true
    simpa using hne
  have hobl : ∀ o ∈ (expHF true).st.obl, o.holds s := hfObl_holds s h7 hA hA'
  obtain ⟨hst, -⟩ := run_pres (horn_look hcode) (runHF_eq true) s hpc hobl hbr
  refine ⟨_, hst, rfl, ?_, ?_, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [hfRegs]), fun A _ _ => rfl⟩
  · rw [pres_getReg]
    show BinOp.eval .xor (foldE.eval s) (c0E.eval s) = _
    rw [eval_foldE, eval_c0E s h7]; rfl
  · rw [pres_getReg]
    show BinOp.eval .xor (s.getReg .x14) (c1E.eval s) = _
    rw [eval_c1E s h7]; rfl

theorem step_HF_exit (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf hfI) {A : Nat}
    (h7 : s.getReg .x7 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 16 ≤ MEMORY_BYTES)
    (heq : s.getReg .x7 = s.getReg .x28) :
    ∃ t, Steps im s 17 17 t ∧ t.pc = s.getReg .x1 &&& BitVec.ofNat 64 (2 ^ 64 - 2) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 48)) =
        foldLo (s.getReg .x13) (s.getReg .x15) ^^^ s.getMem (BitVec.ofNat 64 A) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 56)) = s.getReg .x14 ^^^ s.getMem (BitVec.ofNat 64 (A + 8)) ∧
      RegsExcept s t (.x29 :: hfRegs.unzip.1) ∧ Frame s t (fun B => B = CHAINW + 48 ∨ B = CHAINW + 56) := by
  have hbr : ∀ b ∈ (expHF false).brs, b.holds s := by
    intro b hb
    simp only [expHF, Bool.false_eq_true, if_false, List.mem_singleton] at hb
    subst hb
    show (s.getReg .x7 != s.getReg .x28) = false
    simp [heq]
  have hobl : ∀ o ∈ (expHF false).st.obl, o.holds s := hfObl_holds s h7 hA hA'
  obtain ⟨hst, -⟩ := run_sound (horn_look hcode) (runHF_eq false) s hpc hobl hbr
  have hm : ∀ a, ((expHF false).toState s).getMem a =
      memEval s [mwc (CHAINW + 56) (.bin .xor (.reg .x14) c1E), mwc (CHAINW + 48) (.bin .xor foldE c0E)] a :=
    fun a => rfl
  refine ⟨_, hst, rfl, ?_, ?_, fun x hx => ?_, frame_of_memEval hm _ (fun p hp => ?_)⟩
  · rw [hm, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
    show BinOp.eval .xor (foldE.eval s) (c0E.eval s) = _
    rw [eval_foldE, eval_c0E s h7]; rfl
  · rw [hm, memEval_mwc_self _ _ _ _ (by ao)]
    show BinOp.eval .xor (s.getReg .x14) (c1E.eval s) = _
    rw [eval_c1E s h7]; rfl
  · rw [PRes.toState_getReg']
    show ((regsOf (hfRegs ++ [(.x29, cE CHAINW)])).get x).eval s = _
    rw [regsOf_get_ne _ _ (fun p hp he => hx (by
      simp only [hfRegs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> (subst he; simp [hfRegs]))), RegFile.init_get_eval]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> simp
end steps

section loops
variable {im : Image}

structure HbSt (t0 : MachineState) (d a k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf hbI
  sh : lim3 (t.getReg .x10) (t.getReg .x11) (t.getReg .x12) = a * 2 ^ k
  pr : lim3 (t.getReg .x13) (t.getReg .x14) (t.getReg .x15) = clmulSmall a d k
  dd : t.getReg .x16 = BitVec.ofNat 64 (d / 2 ^ k)
  regs : RegsExcept t0 t hbRegs
  frame : Frame t0 t (fun _ => False)

structure HfSt (t0 : MachineState) (d a : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf hfI
  pr : lim3 (t.getReg .x13) (t.getReg .x14) (t.getReg .x15) = clmulSmall a d 10
  regs : RegsExcept t0 t hbRegs
  frame : Frame t0 t (fun _ => False)

theorem lim3_ite (b : Bool) (a0 a1 a2 x0 x1 x2 : BitVec 64) :
    lim3 (if b then a0 else a0 ^^^ x0) (if b then a1 else a1 ^^^ x1) (if b then a2 else a2 ^^^ x2) =
      if b then lim3 a0 a1 a2 else lim3 a0 a1 a2 ^^^ lim3 x0 x1 x2 := by
  cases b
  · simp only [Bool.false_eq_true, if_false]; exact lim3_xor ..
  · rfl

theorem hbK_le (b1 b2 : Bool) : hbK b1 b2 ≤ 15 := by unfold hbK; cases b1 <;> cases b2 <;> simp

theorem hb_loop (hcode : NewCodeAt im) {t0 : MachineState} {d a : Nat} (ha : a < 2 ^ 128) (hd : d < 2 ^ 10) :
    ∀ n k, k + n = 10 → (k = 0 ∨ 2 ^ k ≤ d) → ∀ t, HbSt t0 d a k t →
      ∃ u m, Steps im t m m u ∧ m ≤ 14 * n + 1 ∧ HfSt t0 d a u := by
  intro n
  induction n with
  | zero =>
    intro k hk hk0 t _
    exfalso
    rcases hk0 with h | h
    · omega
    · have : k = 10 := by omega
      subst this; omega
  | succ n ih =>
    intro k hk hk0 t ht
    have hk9 : k ≤ 9 := by omega
    have hp9 : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hk9
    have hdk : d / 2 ^ k < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    obtain ⟨u, su, upc, u10, u11, u12, u13, u14, u15, u16, uregs, uframe⟩ :=
      step_HB hcode t ht.pc _ _ rfl rfl
    have hand : t.getReg .x16 &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (d / 2 ^ k % 2) := by
      rw [ht.dd]; exact ofNat_and_one _ hdk
    have hshr : t.getReg .x16 >>> 1 = BitVec.ofNat 64 (d / 2 ^ (k + 1)) := by
      rw [ht.dd, ofNat_shr _ _ hdk, Nat.div_div_eq_div_mul, pow_one, ← Nat.pow_succ]
    have hb1 : (t.getReg .x16 &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0) = !(d.testBit k) := by
      rw [hand, Nat.testBit_eq_decide_div_mod_eq]
      have h2 : d / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by norm_num)
      rcases Nat.mod_two_eq_zero_or_one (d / 2 ^ k) with h | h <;> simp [h]
    have hlt12 : (t.getReg .x12).toNat < 2 ^ 63 := by
      have := lim3_lt (t.getReg .x10) (t.getReg .x11) (t.getReg .x12) (n := 9) (by
        rw [ht.sh, Nat.pow_add]
        exact Nat.mul_lt_mul_of_lt_of_le ha hp9 (Nat.two_pow_pos _))
      omega
    have hsh : lim3 (u.getReg .x10) (u.getReg .x11) (u.getReg .x12) = a * 2 ^ (k + 1) := by
      rw [u10, u11, u12, lim3_shl1 _ _ _ hlt12, ht.sh, Nat.pow_succ]; ring
    have hpr : lim3 (u.getReg .x13) (u.getReg .x14) (u.getReg .x15) = clmulSmall a d (k + 1) := by
      rw [u13, u14, u15, lim3_ite, hb1, ht.pr, ht.sh]
      rw [← clmul_step a d k _ rfl (d.testBit k) rfl]
      cases d.testBit k <;> rfl
    have hdd : u.getReg .x16 = BitVec.ofNat 64 (d / 2 ^ (k + 1)) := by rw [u16, hshr]
    have hregs : RegsExcept t0 u hbRegs := (ht.regs.trans uregs).mono (by simp [hbRegs])
    have hframe : Frame t0 u (fun _ => False) := (ht.frame.trans uframe).mono (fun _ _ h => by simpa using h)
    by_cases hz : d / 2 ^ (k + 1) = 0
    · have hb2 : (t.getReg .x16 >>> 1 != BitVec.ofNat 64 0) = false := by rw [hshr, hz]; rfl
      have hdlt : d < 2 ^ (k + 1) := by
        by_contra hc
        have := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.two_pow_pos (k + 1))
        omega
      refine ⟨u, _, su, le_trans (hbK_le _ _) (by omega), ⟨?_, ?_, hregs, hframe⟩⟩
      · rw [upc, hb2]; rfl
      · rw [hpr, clmulSmall_stable a hdlt 10 (by omega)]
    · have hb2 : (t.getReg .x16 >>> 1 != BitVec.ofNat 64 0) = true := by
        rw [hshr, ofNat_bne (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)) (by norm_num)]; simpa using hz
      have hge : 2 ^ (k + 1) ≤ d := by
        by_contra hc
        exact hz (Nat.div_eq_of_lt (Nat.lt_of_not_le hc))
      obtain ⟨v, m, sv, hm, hv⟩ := ih (k + 1) (by omega) (Or.inr hge) u
        ⟨by rw [upc, hb2]; rfl, hsh, hpr, hdd, hregs, hframe⟩
      refine ⟨v, _, su.trans sv, ?_, hv⟩
      have hk14 : hbK (t.getReg .x16 &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0)
          (t.getReg .x16 >>> 1 != BitVec.ofNat 64 0) ≤ 14 := by
        rw [hb2]; unfold hbK; split <;> simp
      omega

structure HkSt (s0 : MachineState) (d : Nat) (coefs : List Digest) (m : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf hkI
  x6 : t.getReg .x6 = BitVec.ofNat 64 d
  x7 : t.getReg .x7 = BitVec.ofNat 64 (COEF + 16 * m)
  x28 : t.getReg .x28 = BitVec.ofNat 64 COEF
  acc : lim2 (t.getReg .x10) (t.getReg .x11) = (familyEval (coefs.drop m) d).toNat
  regs : RegsExcept s0 t hornRegs
  frame : Frame s0 t (fun _ => False)

/-- Cycle bound of one Horner step (HK, at most ten bit iterations, HF). -/
def hornStepC : Nat := 6 + (14 * 10 + 1) + 12

theorem lim3_zero_hi (a b : BitVec 64) : lim3 a b (BitVec.ofNat 64 0) = lim2 a b := by
  unfold lim3 lim2; simp

theorem familyEval_drop (coefs : List Digest) (m : Nat) (hm : m < coefs.length) (d : Nat) :
    familyEval (coefs.drop m) d = gfMulPt (familyEval (coefs.drop (m + 1)) d) d ^^^ coefs.getD m 0 := by
  rw [List.drop_eq_getElem_cons hm, familyEval_cons, List.getD_eq_getElem _ _ hm]

theorem coefAddr (m : Nat) : BitVec.ofNat 64 (COEF + 16 * (m + 1)) + BitVec.ofNat 64 (2 ^ 64 - 16) =
    BitVec.ofNat 64 (COEF + 16 * m) := by
  rw [ofNat_add_ofNat, ofNat_eq_iff]; unfold COEF; omega

theorem horner_mul (hcode : NewCodeAt im) {s0 : MachineState} {d : Nat} {coefs : List Digest} (hd : d < 2 ^ 10)
    {m : Nat} {t : MachineState} (ht : HkSt s0 d coefs (m + 1) t) :
    ∃ u n, Steps im t n n u ∧ n ≤ 6 + (14 * 10 + 1) ∧ u.pc = pcOf hfI ∧
      u.getReg .x7 = BitVec.ofNat 64 (COEF + 16 * m) ∧ u.getReg .x28 = BitVec.ofNat 64 COEF ∧
      u.getReg .x6 = BitVec.ofNat 64 d ∧
      lim3 (u.getReg .x13) (u.getReg .x14) (u.getReg .x15) =
        clmulSmall (familyEval (coefs.drop (m + 1)) d).toNat d 10 ∧
      RegsExcept s0 u hornRegs ∧ Frame s0 u (fun _ => False) := by
  obtain ⟨t1, s1, p1, x7, x12, x13, x14, x15, x16, r1, f1⟩ := step_HK hcode t ht.pc
  have h0 : HbSt t1 d (familyEval (coefs.drop (m + 1)) d).toNat 0 t1 := by
    refine ⟨p1, ?_, ?_, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [x12, lim3_zero_hi, r1.get (by simp), r1.get (by simp), ht.acc]; simp
    · rw [x13, x14, x15]; unfold lim3; simp [clmulSmall]
    · rw [x16, ht.x6]; simp
  obtain ⟨u, n, su, hn, hu⟩ := hb_loop hcode (BitVec.isLt _) hd 10 0 (by norm_num) (Or.inl rfl) t1 h0
  refine ⟨u, 6 + n, s1.trans su, by omega, hu.pc, ?_, ?_, ?_, hu.pr, ?_, ?_⟩
  · rw [hu.regs.get (by simp [hbRegs]), x7, ht.x7, coefAddr]
  · rw [hu.regs.get (by simp [hbRegs]), r1.get (by simp), ht.x28]
  · rw [hu.regs.get (by simp [hbRegs]), r1.get (by simp), ht.x6]
  · exact ((ht.regs.trans r1).trans hu.regs).mono (by simp [hornRegs, hbRegs])
  · exact ((ht.frame.trans f1).trans hu.frame).mono (fun _ _ h => by simpa using h)

/-- The first `n` coefficients of the buffer (stage B: the 17 lower-family coefficients). -/
def CoefAtN (n : Nat) (t : MachineState) (coefs : List Digest) : Prop :=
  ∀ k < n, DigAt t (COEF + 16 * k) (coefs.getD k 0)

theorem coef_limbs {N : Nat} (hN : N ≤ 102) {s0 u : MachineState} {coefs : List Digest}
    (hcoef : CoefAtN N s0 coefs) (hf : Frame s0 u (fun _ => False)) {m : Nat} (hm : m < N) :
    lim2 (u.getMem (BitVec.ofNat 64 (COEF + 16 * m))) (u.getMem (BitVec.ofNat 64 (COEF + 16 * m + 8))) =
      (coefs.getD m 0).toNat := by
  have h := hcoef m hm
  rw [hf.get (by unfold COEF; omega) id, hf.get (by unfold COEF; omega) id, h.1, h.2, lim2_toNat]

/-- The Horner loop over the first `n ≤ 102` coefficients of the buffer (102: HORN of stage A; 17: the lower
seeds of stage B, entered at `HK` with `x7 = COEF + 16 * 17`). -/
theorem horner_loop (hcode : NewCodeAt im) {s0 : MachineState} {d : Nat} {coefs : List Digest} {N : Nat}
    (hN : N ≤ 102) (hd : d < 2 ^ 10) (hlen : coefs.length = N) (hcoef : CoefAtN N s0 coefs) :
    ∀ m, m < N → ∀ t, HkSt s0 d coefs (m + 1) t →
      ∃ u n c, Steps im t n c u ∧ c ≤ hornStepC * (m + 1) + 5 ∧
        u.pc = s0.getReg .x1 &&& BitVec.ofNat 64 (2 ^ 64 - 2) ∧ DigAt u (CHAINW + 48) (familyEval coefs d) ∧
        RegsExcept s0 u hornRegs ∧ Frame s0 u (fun A => A = CHAINW + 48 ∨ A = CHAINW + 56) := by
  intro m
  induction m with
  | zero =>
    intro _ t ht
    obtain ⟨u, n, su, hn, upc, u7, u28, -, upr, uregs, uframe⟩ := horner_mul hcode hd ht
    obtain ⟨v, sv, vpc, v48, v56, vregs, vframe⟩ := step_HF_exit hcode u upc (A := COEF + 16 * 0) u7
      (by unfold COEF; omega) (by unfold COEF MEMORY_BYTES; omega) (by rw [u7, u28])
    have hl := horner_limbs upr (coef_limbs hN hcoef uframe (m := 0) (by omega))
    rw [← familyEval_drop coefs 0 (by omega), List.drop_zero] at hl
    obtain ⟨l0, l1⟩ := limbs_of_lim2 hl
    refine ⟨v, _, _, su.trans sv, by unfold hornStepC; omega, ?_, ⟨by rw [v48, l0], by rw [v56, ← l1]⟩, ?_, ?_⟩
    · rw [vpc, uregs.get (by simp [hornRegs])]
    · exact (uregs.trans vregs).mono (by simp [hornRegs, hfRegs])
    · exact (uframe.trans vframe).mono (fun _ _ h => by simpa using h)
  | succ m ih =>
    intro hm t ht
    obtain ⟨u, n, su, hn, upc, u7, u28, u6, upr, uregs, uframe⟩ := horner_mul hcode hd ht
    have hne : u.getReg .x7 ≠ u.getReg .x28 := by
      rw [u7, u28]; intro h; rw [ofNat_inj (by unfold COEF; omega) (by unfold COEF; omega)] at h; omega
    obtain ⟨v, sv, vpc, v10, v11, vregs, vframe⟩ := step_HF_cont hcode u upc u7
      (by unfold COEF; omega) (by unfold COEF MEMORY_BYTES; omega) hne
    have hl := horner_limbs upr (coef_limbs hN hcoef uframe (m := m + 1) (by omega))
    rw [← familyEval_drop coefs (m + 1) (by omega)] at hl
    have hv : HkSt s0 d coefs (m + 1) v := by
      refine ⟨vpc, ?_, ?_, ?_, ?_, (uregs.trans vregs).mono (by simp [hornRegs, hfRegs]),
        (uframe.trans vframe).mono (fun _ _ h => by simpa using h)⟩
      · rw [vregs.get (by simp [hfRegs]), u6]
      · rw [vregs.get (by simp [hfRegs]), u7]
      · rw [vregs.get (by simp [hfRegs]), u28]
      · rw [v10, v11]; exact hl
    obtain ⟨w, n', c', sw, hc', wpc, wd, wregs, wframe⟩ := ih (by omega) v hv
    refine ⟨w, _, _, (su.trans sv).trans sw, ?_, wpc, wd, wregs, wframe⟩
    unfold hornStepC at *
    omega

/-- Cycle bound of HORN. -/
def hornC : Nat := 6 + (hornStepC * 102 + 5)

theorem horn_run (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf hornI) {d : Nat} (hd : d < 2 ^ 10)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 d) {coefs : List Digest} (hlen : coefs.length = 102)
    (hcoef : CoefAt s coefs) :
    ∃ u n c, Steps im s n c u ∧ c ≤ hornC ∧ u.pc = s.getReg .x1 &&& BitVec.ofNat 64 (2 ^ 64 - 2) ∧
      DigAt u (CHAINW + 48) (familyEval coefs d) ∧ RegsExcept s u hornRegs ∧
      Frame s u (fun A => A = CHAINW + 48 ∨ A = CHAINW + 56) := by
  obtain ⟨t, st, tpc, t7, t10, t11, t28, tregs, tframe⟩ := step_H0 hcode s hpc
  have ht : HkSt s d coefs (101 + 1) t := by
    refine ⟨tpc, by rw [tregs.get (by simp)]; exact h6, t7, t28, ?_, tregs.mono (by simp [hornRegs]), tframe⟩
    rw [t10, t11, List.drop_eq_nil_of_le (by omega)]
    rfl
  obtain ⟨u, n, c, su, hc, upc, ud, uregs, uframe⟩ := horner_loop hcode (le_refl 102) hd hlen hcoef 101 (by norm_num) t ht
  exact ⟨u, _, _, st.trans su, by unfold hornC; omega, upc, ud, uregs, uframe⟩

end loops
end ClaudeWCT.W9.Machine.Sign
end
