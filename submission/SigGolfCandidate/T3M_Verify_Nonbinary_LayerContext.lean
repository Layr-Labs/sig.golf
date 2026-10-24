import SigGolfCandidate.T3M_Verify_Nonbinary_LayerPrefix
import SigGolfCandidate.T3M_Verify_Nonbinary_TopAlias
import SigGolfCandidate.T3M_Verify_LayerSem
import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsSem
import SigGolfCandidate.T3M_Mem
import SigGolfCandidate.T3_Nonbinary_LowerLayout
import SigGolfCandidate.T3M_Verify_LeafSem
import SigGolfCandidate.T3M_Verify_TopSource

set_option Elab.async false

-- Top-half selection (formerly Nonbinary/TopSelect.lean, folded here for the 1000-entry limit).
section
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
theorem byte7_ult (lo : BitVec 128) :
    BitVec.ult ((extractByte (lo.extractLsb' 64 64) 7).zeroExtend 64) 64#64 = decide (T3.TopChoice.blocked lo) := by
  have hl := lo.isLt
  unfold T3.TopChoice.blocked extractByte
  simp only [BitVec.ult, BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth, BitVec.toNat_ushiftRight,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have h1 : lo.toNat / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact hl
  rw [Nat.mod_eq_of_lt h1, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have h2 : lo.toNat / 2 ^ (64 + 7 * 8) < 2 ^ 8 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact hl
  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (lt_trans h2 (by norm_num))]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  norm_num
theorem lb_ge_zero (b : BitVec 8) :
    (!BitVec.slt (b.signExtend 64) (0 : BitVec 64)) = !b.getLsbD 7 := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_signExtend]
  simp [BitVec.msb_eq_getLsbD_last]

end SigGolfCandidate.T3M.Verify.Nonbinary
end


section
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
/-- Campaign T51: the dispatch jump of the head lands on `g0Target V`. -/
theorem g0_jump (V : Digest) :
    ((((V.extractLsb' 0 64) <<< ((56#64 : Word).toNat % 64)) >>> ((45#64 : Word).toNat % 64)) +
      18446744073709550872#64) &&& 18446744073709551614#64 = g0Target V := by
  have e1 : (56#64 : Word).toNat % 64 = 56 := rfl
  have e2 : (45#64 : Word).toNat % 64 = 45 := rfl
  have e3 : (18446744073709550872#64 : Word) = BitVec.ofNat 64 (2^64-744) := rfl
  have e4 : (18446744073709551614#64 : Word) = ~~~1#64 := by decide
  rw [e1, e2, e3, e4]; rfl
/-- One 6-word dispatch block of the d6b head (`hi`: the HIGH block at `a2+16`; T51: 5 instructions run, the
trailing `nop` is never reached). -/
theorem prefix_end_spec (s : MachineState) (hi : Bool) (half : Digest) (d q : Nat)
    (hpc : s.pc = pcOf q) (hcode : CodeAt Verify.image (pcOf q) (if hi then dHigh else dLow))
    (h12 : s.getReg .x12 = BitVec.ofNat 64 d) (hd : d % 8 = 0 ∧ 0x1000 ≤ d ∧ d + 32 ≤ 0x7000)
    (hh : DigAt s (d + (if hi then 16 else 0)) half) :
    ∃ t, Steps Verify.image s 5 5 t ∧ t.pc = g0Target half ∧
      t.getReg .x16 = half.extractLsb' 0 64 ∧ t.getReg .x17 = half.extractLsb' 64 64 ∧
      RegsExcept s t [.x16,.x17,.x14] ∧ Frame s t (fun _ => False) := by
  cases hi with
  | false =>
    simp only [Bool.false_eq_true, if_false, Nat.add_zero] at hcode hh
    have m0 : s.getMem (s.getReg .x12) = half.extractLsb' 0 64 := by rw [h12]; exact hh.1
    have m8 : s.getMem (s.getReg .x12 + 8#64) = half.extractLsb' 64 64 := by
      rw [h12, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat]; exact hh.2
    have es := symRun_sound (dLow_run (pcOf q)) hcode s hpc (by
      simp [dLowBase.res, rv_simp, h12, accessValid_iff, MEMORY_BYTES]; omega)
    refine ⟨_, es, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, dLowBase.res, E.eval, BinOp.eval, m0]
      exact g0_jump half
    · simp only [Result.toState_getReg, dLowBase.res, RegFile.get, E.eval, m0]
    · simpa only [Result.toState_getReg, dLowBase.res, RegFile.get, E.eval, BinOp.eval] using m8
    · intro r hr; cases r <;> simp at hr <;> simp [dLowBase.res, rv_simp] <;> rfl
    · intro A _ _; simp [dLowBase.res, rv_simp]
  | true =>
    simp only [if_true] at hcode hh
    have m0 : s.getMem (s.getReg .x12 + 16#64) = half.extractLsb' 0 64 := by
      rw [h12, show (16#64 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]; exact hh.1
    have m8 : s.getMem (s.getReg .x12 + 24#64) = half.extractLsb' 64 64 := by
      rw [h12, show (24#64 : Word) = BitVec.ofNat 64 24 from rfl, ofNat_add_ofNat]
      simpa [Nat.add_assoc] using hh.2
    have es := symRun_sound (dHigh_run (pcOf q)) hcode s hpc (by
      simp [dHighBase.res, rv_simp, h12, accessValid_iff, MEMORY_BYTES]; omega)
    refine ⟨_, es, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, dHighBase.res, E.eval, BinOp.eval, m0]
      exact g0_jump half
    · simpa only [Result.toState_getReg, dHighBase.res, RegFile.get, E.eval, BinOp.eval] using m0
    · simpa only [Result.toState_getReg, dHighBase.res, RegFile.get, E.eval, BinOp.eval] using m8
    · intro r hr; cases r <;> simp at hr <;> simp [dHighBase.res, rv_simp] <;> rfl
    · intro A _ _; simp [dHighBase.res, rv_simp]
/-- Exact cycle cost of the d6b selector before its 6-word dispatch block: hint clear 4, hint set 6 (HIGH, or LOW
forced). -/
def selCost (high : Bool) (_a : BitVec 256) : Nat := if high then 6 else 4
def selMax : Nat := 6
theorem selCost_le (high : Bool) (a : BitVec 256) : selCost high a ≤ selMax := by
  unfold selCost selMax; split_ifs <;> omega
/-- The whole d6b top head (18 words at `h+6`): loads the verifier-read half `TopChoice.read high a` into a6/a7
and dispatches to its first digit group (T51: the g0 cell), in exactly `selCost high a + 5` cycles. -/
theorem prefix_head_spec (s : MachineState) (a : BitVec 256) (high : Bool) (ra d p : Nat) (hra : ra ∈ aVals)
    (hpc : s.pc = pcOf p) (hc : CodeAt Verify.image (pcOf p) (prefixWordsOf ra))
    (h12 : s.getReg .x12 = BitVec.ofNat 64 d) (hd : d % 8 = 0 ∧ 0x1000 ≤ d ∧ d + 32 ≤ 0x7000)
    (h11 : s.getReg .x11 = 64#64) (h4 : s.getReg .x4 = 24704#64)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 TOPB9) (hmask : s.getMem 0xffbff8#64 = 520192#64)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 ra)
    (hhint : (extractByte (s.getMem 25232#64) 0).getLsbD selHintBit = high)
    (hlo : DigAt s d (a.extractLsb' 0 128))
    (hhi : DigAt s (d+16) (a.extractLsb' 128 128)) :
    ∃ t, Steps Verify.image s (selCost high a + 5) (selCost high a + 5) t ∧
      t.pc = g0Target (T3.TopChoice.read high a) ∧
      t.getReg .x16 = (T3.TopChoice.read high a).extractLsb' 0 64 ∧
      t.getReg .x17 = (T3.TopChoice.read high a).extractLsb' 64 64 ∧
      t.getReg .x8 = 14128#64 ∧ t.getReg .x6 = 520192#64 ∧
      RegsExcept s t [.x16,.x17,.x6,.x8,.x14,.x3] ∧ Frame s t (fun _ => False) := by
  have hsub : ∀ (pre seg post : List (BitVec 32)), prefixWordsOf ra = pre ++ seg ++ post →
      CodeAt Verify.image (pcOf (p + pre.length)) seg := by
    intro pre seg post he
    have h := hc
    rw [he] at h
    have h' := CodeAt.drop_prefix (pre := pre) (seg := seg) (post := post) h
    rwa [pcOf, ofNat_add_ofNat, show 0x1000 + 4 * p + 4 * pre.length = 0x1000 + 4 * (p + pre.length) by ring] at h'
  have hc0 : CodeAt Verify.image (pcOf p) (dProWordsOf ra) := by
    simpa using hsub [] (dProWordsOf ra) (dHint ++ dHead ++ dLow ++ dHigh) (by simp [prefixWordsOf])
  have hc2 : CodeAt Verify.image (pcOf (p+2)) dHint := by
    simpa [dProWordsOf] using hsub (dProWordsOf ra) dHint (dHead ++ dLow ++ dHigh) (by simp [prefixWordsOf])
  have hc4 : CodeAt Verify.image (pcOf (p+4)) dHead := by
    simpa [dProWordsOf, dHint] using hsub (dProWordsOf ra ++ dHint) dHead (dLow ++ dHigh) (by simp [prefixWordsOf])
  have hc6 : CodeAt Verify.image (pcOf (p+6)) dLow := by
    simpa [dProWordsOf, dHint, dHead] using
      hsub (dProWordsOf ra ++ dHint ++ dHead) dLow dHigh (by simp [prefixWordsOf])
  have hc12 : CodeAt Verify.image (pcOf (p+12)) dHigh := by
    simpa [dProWordsOf, dHint, dHead, dLow] using
      hsub (dProWordsOf ra ++ dHint ++ dHead ++ dLow) dHigh [] (by simp [prefixWordsOf])
  have hhint : (extractByte (s.getMem 25232#64) 0).getLsbD 7 = high := hhint
  have hal : 15336 ≤ ra ∧ ra ≤ 15528 := by
    simp only [aVals, List.mem_cons, List.not_mem_nil, or_false] at hra; omega
  -- `ld t1,232(s1); addi s0,a0,K`
  have hm : s.getMem (s.getReg .x9 + 232#64) = 520192#64 := by rw [h9]; exact hmask
  have e0 := symRun_sound (dPro_run ra hra (pcOf p)) hc0 s hpc (by
    simp [dProRes, dProRegs, dProBase.res, rv_simp, h9, accessValid_iff, MEMORY_BYTES, TOPB9])
  let u := (dProRes ra (pcOf p)).toState s
  have ru : RegsExcept s u [.x6,.x8] := by
    intro r hr; cases r <;> simp at hr <;> simp [u, dProRes, dProRegs, dProBase.res, rv_simp] <;> rfl
  have fu : Frame s u (fun _ => False) := by
    intro A _ _; simp [u, dProRes, dProRegs, dProBase.res, rv_simp]
  have pu : u.pc = pcOf (p+2) := by
    simp [u, dProRes, rv_simp, pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
  have u6 : u.getReg .x6 = 520192#64 := by
    simp only [u, Result.toState_getReg, dProRes, dProRegs, dProBase.res, RegFile.get, RegFile.set, E.eval]
    exact hm
  have u8 : u.getReg .x8 = 14128#64 := by
    simp only [u, Result.toState_getReg, dProRes, dProRegs, RegFile.get, RegFile.set, E.eval, BinOp.eval, h10]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have h12u : u.getReg .x12 = BitVec.ofNat 64 d := (ru.get (by decide)).trans h12
  have h4u : u.getReg .x4 = 24704#64 := (ru.get (by decide)).trans h4
  have hmemu : u.getMem 25232#64 = s.getMem 25232#64 := fu.get (A := 25232) (by omega) (by simp)
  -- `lb gp,528(tp); bge gp,zero,LOW`
  have e1 := symRun_sound (dHint_run (pcOf (p+2))) hc2 u pu (by
    simp [dHintRes, dHintBase.res, rv_simp, h4u, accessValid_iff, MEMORY_BYTES])
  let v := (dHintRes (pcOf (p+2))).toState u
  have rv : RegsExcept u v [.x3] := by
    intro r hr; cases r <;> simp_all [v, dHintRes, dHintBase.res, rv_simp] <;> rfl
  have fv : Frame u v (fun _ => False) := by
    intro A _ _; simp [v, dHintRes, dHintBase.res, rv_simp]
  have hhb : hintByte.eval u = (extractByte (s.getMem 25232#64) 0).signExtend 64 := by
    simp only [hintByte, E.eval, UnOp.eval, LoadKind.fromWord, BinOp.eval]
    rw [show (u.getReg Reg.x4 + 528) = 25232#64 by rw [h4u]; rfl, hmemu]
  have hcmp : CmpOp.ge.eval (hintByte.eval u) ((E.c 0).eval u) = !high := by
    simp only [CmpOp.eval, E.eval]; rw [hhb, lb_ge_zero, hhint]
  have pv : v.pc = if high then pcOf (p+4) else pcOf (p+6) := by
    simp only [v, Result.toState_pc, dHintRes]
    simp only [E.eval] at hcmp ⊢
    simp only [hcmp]
    cases high
    · simp [pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
    · simp [pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
  have h12v : v.getReg .x12 = BitVec.ofNat 64 d := (rv.get (by decide)).trans h12u
  have h6v : v.getReg .x6 = 520192#64 := (rv.get (by decide)).trans u6
  have h8v : v.getReg .x8 = 14128#64 := (rv.get (by decide)).trans u8
  have fsv : Frame s v (fun _ => False) := (fu.trans fv).mono (by simp)
  have dig : ∀ (x : MachineState) (o : Nat) (half : BitVec 128), Frame s x (fun _ => False) → DigAt s (d+o) half →
      o ≤ 16 → DigAt x (d+o) half := fun x o half hf hh ho =>
    hh.frame hf (by omega) (by simp) (by simp)
  cases high with
  | false =>
    rw [if_neg (by simp)] at pv
    obtain ⟨t, et, pt, t16, t17, rt, ft⟩ := prefix_end_spec v false (a.extractLsb' 0 128) d (p+6) pv
      (by simpa using hc6) h12v hd (by simpa using dig v 0 _ fsv (by simpa using hlo) (by omega))
    have hr : T3.TopChoice.read false a = a.extractLsb' 0 128 := T3.TopChoice.read_false a
    refine ⟨t, by rw [show selCost false a + 5 = 2 + 2 + 5 from rfl]; exact (e0.trans e1).trans et,
      by rw [pt, hr], by rw [t16, hr], by rw [t17, hr],
      by rw [rt.get (by decide), h8v], by rw [rt.get (by decide), h6v],
      ((ru.trans rv).trans rt).mono (by decide), ((fu.trans fv).trans ft).mono (by simp)⟩
  | true =>
    rw [if_pos rfl] at pv
    -- `lbu gp,15(a2); bgeu gp,a1,HIGH`
    have hlo1 : v.getMem (v.getReg .x12 + 8#64) = (a.extractLsb' 0 128).extractLsb' 64 64 := by
      rw [h12v, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat, fsv.get (by omega) (by simp), hlo.2]
    have e2 := symRun_sound (dHead_run (pcOf (p+4))) hc4 v pv (by
      simp [dHeadRes, dHeadBase.res, rv_simp, h12v, accessValid_iff, MEMORY_BYTES]; omega)
    let w := (dHeadRes (pcOf (p+4))).toState v
    have rw' : RegsExcept v w [.x3] := by
      intro r hr; cases r <;> simp_all [w, dHeadRes, dHeadBase.res, rv_simp] <;> rfl
    have fw : Frame v w (fun _ => False) := by
      intro A _ _; simp [w, dHeadRes, dHeadBase.res, rv_simp]
    have hb : headByte.eval v = (extractByte ((a.extractLsb' 0 128).extractLsb' 64 64) 7).zeroExtend 64 := by
      simp only [headByte, E.eval, UnOp.eval, LoadKind.fromWord, BinOp.eval]
      rw [show (v.getReg Reg.x12 + 8) = v.getReg .x12 + 8#64 from rfl, hlo1]
    have h11v : v.getReg .x11 = 64#64 := (rv.get (by decide)).trans ((ru.get (by decide)).trans h11)
    have hcmp : CmpOp.geu.eval (headByte.eval v) ((E.reg .x11).eval v) =
        !decide (T3.TopChoice.blocked (a.extractLsb' 0 128)) := by
      simp only [CmpOp.eval, E.eval]; rw [hb, h11v, byte7_ult]
    have pw : w.pc = if T3.TopChoice.blocked (a.extractLsb' 0 128) then pcOf (p+6) else pcOf (p+12) := by
      simp only [w, Result.toState_pc, dHeadRes]
      simp only [E.eval] at hcmp ⊢
      simp only [hcmp]
      by_cases hbl : T3.TopChoice.blocked (a.extractLsb' 0 128)
      · simp [hbl, pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
      · simp [hbl, pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
    have h12w : w.getReg .x12 = BitVec.ofNat 64 d := (rw'.get (by decide)).trans h12v
    have h6w : w.getReg .x6 = 520192#64 := (rw'.get (by decide)).trans h6v
    have h8w : w.getReg .x8 = 14128#64 := (rw'.get (by decide)).trans h8v
    have fsw : Frame s w (fun _ => False) := (fsv.trans fw).mono (by simp)
    by_cases hbl : T3.TopChoice.blocked (a.extractLsb' 0 128)
    · rw [if_pos hbl] at pw
      obtain ⟨t, et, pt, t16, t17, rt, ft⟩ := prefix_end_spec w false (a.extractLsb' 0 128) d (p+6) pw
        (by simpa using hc6) h12w hd (by simpa using dig w 0 _ fsw (by simpa using hlo) (by omega))
      have hr : T3.TopChoice.read true a = a.extractLsb' 0 128 := T3.TopChoice.read_blocked true hbl
      refine ⟨t, by rw [show selCost true a + 5 = 2 + 2 + 2 + 5 from rfl]; exact ((e0.trans e1).trans e2).trans et,
        by rw [pt, hr], by rw [t16, hr], by rw [t17, hr],
        by rw [rt.get (by decide), h8w], by rw [rt.get (by decide), h6w],
        (((ru.trans rv).trans rw').trans rt).mono (by decide), (((fu.trans fv).trans fw).trans ft).mono (by simp)⟩
    · rw [if_neg hbl] at pw
      obtain ⟨t, et, pt, t16, t17, rt, ft⟩ := prefix_end_spec w true (a.extractLsb' 128 128) d (p+12) pw
        (by simpa using hc12) h12w hd (by simpa using dig w 16 _ fsw hhi (by omega))
      have hr : T3.TopChoice.read true a = a.extractLsb' 128 128 := by
        simp [T3.TopChoice.read, T3.TopChoice.lowHalf, T3.TopChoice.highHalf, hbl]
      refine ⟨t, by rw [show selCost true a + 5 = 2 + 2 + 2 + 5 from rfl]; exact ((e0.trans e1).trans e2).trans et,
        by rw [pt, hr], by rw [t16, hr], by rw [t17, hr],
        by rw [rt.get (by decide), h8w], by rw [rt.get (by decide), h6w],
        (((ru.trans rv).trans rw').trans rt).mono (by decide), (((fu.trans fv).trans fw).trans ft).mono (by simp)⟩
end SigGolfCandidate.T3M.Verify.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
def rejectJumpCode : List (BitVec 32) := [0xea8fa06f]
sym_block rejectJumpBase := symRun { noAlias := true } rejectJumpCode (pcOf 9147) 20
theorem rejectJump_at : CodeAt Verify.image (pcOf 9147) rejectJumpCode := by
  have h := codeAt_from 9147 (by decide +kernel)
  have hp : rejectJumpCode <+: codeFrom 9147 := by decide +kernel
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, hp.trans h.2.2.2⟩
def rejectExitCode : List (BitVec 32) := [1049235,1049875]
sym_block rejectExitBase := symRun { noAlias := true } rejectExitCode (pcOf 3429) 20
theorem rejectExit_at : CodeAt Verify.image (pcOf 3429) rejectExitCode := by
  have h := codeAt_from 3429 (by decide +kernel)
  have hp : rejectExitCode <+: codeFrom 3429 := by decide +kernel
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, hp.trans h.2.2.2⟩
theorem reject_halt (s : MachineState) (hpc : s.pc = pcOf 9147) :
    ∃ t, Steps Verify.image s 3 3 t ∧ fetch Verify.image t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧ t.getReg .x10 = 1 := by
  have e1 := symRun_sound rejectJumpBase rejectJump_at s hpc (by simp [rejectJumpBase.res, rv_simp])
  have p1 : (rejectJumpBase.res.toState s).pc = pcOf 3429 := by simp [rejectJumpBase.res, rv_simp, pcOf]
  have e2 := symRun_sound rejectExitBase rejectExit_at (rejectJumpBase.res.toState s) p1
    (by simp [rejectExitBase.res, rv_simp])
  refine ⟨_, e1.trans e2, ?_, ?_, ?_⟩
  · have h : CodeAt Verify.image (pcOf 3431) [0x00000073] := by
      have h := codeAt_from 3431 (by decide +kernel)
      have hp : [0x00000073] <+: codeFrom 3431 := by decide +kernel
      exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, hp.trans h.2.2.2⟩
    exact h.fetch _ (by simp [rejectExitBase.res, rv_simp, pcOf])
  · simp [rejectExitBase.res, rv_simp]
  · simp [rejectExitBase.res, rv_simp]
end SigGolfCandidate.T3M.Verify.Nonbinary
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
/-- Configuration (1)+(2): the selector also writes `gp` (x3) and `a2` (x12); both are dead after the head. -/
def topEntryRegs : List Reg := [.x16,.x17,.x29,.x6,.x8,.x14,.x3,.x12]
structure TopEntry (u : MachineState) (v : Digest) (p : Nat) (s : MachineState) : Prop where
  /-- Campaign T51: the head's dispatch target (the g0 cell of the low byte of `v`). -/
  pc : s.pc = Nonbinary.g0Target v
  ra : s.getReg .x9 = BitVec.ofNat 64 TOPB9
  lo : s.getReg .x16 = v.extractLsb' 0 64
  hi : s.getReg .x17 = v.extractLsb' 64 64
  s3 : s.getReg .x8 = 14128#64
  mask : s.getReg .x6 = 520192#64
  table : s.getReg .x2 = 0x7fc00#64
  regs : RegsExcept u s topEntryRegs
  frame : Frame u s (fun A => A = 25160)
def topRowA (c : Nat) : Nat := rowA 0 c
theorem prefix_slots : (List.range 128).all (fun c => decide (topRowA c ∈ Nonbinary.aVals) &&
    (Nonbinary.prefixWordsOf (topRowA c)).isPrefixOf (codeFrom (trPc 0 c + 6))) = true := by
  decide +kernel

theorem topRowA_mem (c : Nat) (hc : c < 128) : topRowA c ∈ Nonbinary.aVals := by
  have h := List.all_eq_true.mp prefix_slots c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1
theorem prefix_at (c : Nat) (hc : c < 128) :
    CodeAt image (pcOf (trPc 0 c + 6)) (Nonbinary.prefixWordsOf (topRowA c)) := by
  have hp := trPc_lt 0 c
  have h := codeAt_from (trPc 0 c + 6) (by omega)
  have h2 := List.all_eq_true.mp prefix_slots c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  have hpre : Nonbinary.prefixWordsOf (topRowA c) <+: codeFrom (trPc 0 c + 6) :=
    List.isPrefixOf_iff_prefix.mp h2.2
  refine ⟨?_, ?_, ?_, hpre.trans h.2.2.2⟩
  · unfold pcOf; simp only [BitVec.toNat_ofNat]; omega
  · unfold pcOf; simp only [BitVec.toNat_ofNat]; omega
  · unfold pcOf
    simp only [BitVec.toNat_ofNat, Nonbinary.prefixWordsOf, List.length_append,
      Nonbinary.dProWordsOf, Nonbinary.dHint, Nonbinary.dHead, Nonbinary.dLow, Nonbinary.dHigh,
      List.length_cons, List.length_nil]
    omega
theorem prefix_sub_at (c : Nat) (hc : c < 128) (pre seg post : List (BitVec 32))
    (he : Nonbinary.prefixWordsOf (topRowA c) = pre ++ seg ++ post) :
    CodeAt image (pcOf (trPc 0 c + 6 + pre.length)) seg := by
  have h := prefix_at c hc
  rw [he] at h
  have h' := CodeAt.drop_prefix (pre := pre) (seg := seg) (post := post) h
  rwa [pcOf, ofNat_add_ofNat,
    show 0x1000 + 4 * (trPc 0 c + 6) + 4 * pre.length =
      0x1000 + 4 * (trPc 0 c + 6 + pre.length) by ring] at h'
/-- The witness choice byte (rel 21104, abs 25232) is the low byte of its witness word. -/
theorem extractByte_wword_choice (w : ClaudeWCT.W9.T3M.WBytes) :
    extractByte (wword w (ClaudeWCT.W9.T3M.choiceOff / 8)) 0 = ClaudeWCT.W9.T3M.wchoice w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, wword, ClaudeWCT.W9.T3M.wchoice, ClaudeWCT.W9.T3M.choiceOff, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', Nat.zero_mul, Nat.zero_add]
  simp [hi, show i < 64 by omega]
theorem topTransition (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : BC.EncPre w pk index 0 c t) (a : BitVec 256) :
    ∃ n s, Steps image (writeHash t a) n n s ∧ n ≤ 11 ∧
      n = Verify.Nonbinary.selCost (ClaudeWCT.W9.T3M.wtopHigh w) a + 5 ∧
      TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 15272 ≤ topRowA c ∧ topRowA c ≤ 15528 ∧ topRowA c % 8 = 0 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d, h12, hd⟩ := ht.dst (by decide +kernel)
  change (d + 16 = topRowA c ∧ WIT + BC.layerEnd 0 + 16 ≤ topRowA c) ∨ d = topRowA c + 48 at hd
  have hdA : d % 8 = 0 ∧ 0x1000 ≤ d ∧ d + 32 ≤ 0x7000 := by omega
  have hk : KnownOK (BC.bK 0 c) (writeHash t a) := fun p hp => by rw [writeHash_getReg]; exact ht.glob.1 p hp
  have hpc : (writeHash t a).pc = pcOf (trPc 0 c + 6) := by
    rw [writeHash_pc, ht.pc]
    change pcOf (trPc 0 c + 5) + 4 = pcOf (trPc 0 c + 6)
    simpa only [Nat.add_assoc] using pcOf_add4 (trPc 0 c + 5)
  have hglob := Glob_writeHash ht.glob a d h12 (safeDest_hi d (by unfold WLO WIT; omega) hdA.1 (by omega))
  have hv := DigAt.writeHash_lo t a d h12 (by omega)
  have h12s : (writeHash t a).getReg .x12 = BitVec.ofNat 64 d := by rw [writeHash_getReg]; exact h12
  have hD := hglob.2.2.2.2.2
  have h10 : (writeHash t a).getReg .x10 = BitVec.ofNat 64 (topRowA c) :=
    hk (.x10, BitVec.ofNat 64 (rowA 0 c)) (by simp [BC.bK])
  have hra : (writeHash t a).getReg .x9 = BitVec.ofNat 64 TOPB9 :=
    hk (.x9, BitVec.ofNat 64 TOPB9) (by simp [BC.bK, T3M.bK, layK])
  have h15 : (writeHash t a).getReg .x2 = 0x7fc00#64 :=
    hk (.x2, 0x7fc00#64) (by simp [BC.bK, T3M.bK, layK])
  have h4 : (writeHash t a).getReg .x4 = 24704#64 :=
    hk (.x4, 24704#64) (by simp [BC.bK, T3M.bK, layK, bufferBias])
  have h11 : (writeHash t a).getReg .x11 = 64#64 :=
    hk (.x11, 64#64) (by simp [BC.bK, T3M.bK, layK])
  have hmask : (writeHash t a).getMem 0xffbff8#64 = 520192#64 := hD.mask
  have hhi := DigAt.writeHash_hi t a d h12 (by omega)
  -- the choice hint byte (witness rel 21104 = abs 25232) is still the original witness byte
  have hhint : (extractByte ((writeHash t a).getMem 25232#64) 0).getLsbD Nonbinary.selHintBit =
      ClaudeWCT.W9.T3M.wtopHigh w := by
    have ho := Orig_writeHash ht.bufferOrig a d h12 (by omega)
    have hw := ho.word ClaudeWCT.W9.T3M.choiceOff (by decide) (by unfold WX; decide)
      ⟨⟨by norm_num [BC.bufferStart, ClaudeWCT.W9.T3M.choiceOff], by norm_num [ClaudeWCT.W9.T3M.choiceOff]⟩,
        Or.inr (by unfold WIT ClaudeWCT.W9.T3M.choiceOff; omega)⟩
    rw [show (25232#64 : Word) = BitVec.ofNat 64 (WIT + ClaudeWCT.W9.T3M.choiceOff) from rfl, hw,
      extractByte_wword_choice]
    rfl
  obtain ⟨z, ez, pz, lo, hi, s3, mask, rz, fz⟩ := Verify.Nonbinary.prefix_head_spec
    (writeHash t a) a (ClaudeWCT.W9.T3M.wtopHigh w) (topRowA c) d (trPc 0 c + 6) ha hpc (prefix_at c hc')
    h12s hdA h11 h4 hra hmask h10 hhint hv hhi
  have hn := Verify.Nonbinary.selCost_le (ClaudeWCT.W9.T3M.wtopHigh w) a
  unfold Verify.Nonbinary.selMax at hn
  refine ⟨_,z,ez,by omega,rfl,⟨pz,?_,lo,hi,s3,mask,?_,?_,?_⟩⟩
  · rw [rz.get (by decide),hra]
  · rw [rz.get (by decide),h15]
  · exact rz.mono (by simp [topEntryRegs])
  · exact fz.mono (by simp)
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route coreDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
/-- Campaign T51: the top context's digits: the 50 data digits of the selected half `v`, then the checksum digit
`min 5 (152 - data sum)` (the decoded checksum whenever it is in range), then 0. -/
def topDig (v : Digest) (i : Nat) : Nat :=
  if i < 50 then coreDigit 0 v i else if i = 50 then min 5 (T3.target 0 - (T3.dataDigits 0 v).sum) else 0
def nctxOf (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) : NCtx :=
  ⟨w, (route index 0).2, (route index 0).1, 14128, topDig v, p + 8⟩
/-- The context's digits through a symbolic index (a `show` at a literal index makes the unifier evaluate
`min 5 (target 0 - sum)`). -/
theorem nctxOf_dig (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p i : Nat) :
    (nctxOf w index v p).dig i = topDig v i := rfl
theorem nctx_digits (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    (nctxOf w index v p).DigitsOk := by
  intro i hi
  rw [nctxOf_dig, Nonbinary.NCtx.topMax_eq]
  unfold topDig
  by_cases h50 : i < 50
  · rw [if_pos h50]; exact SigGolfCandidate.T3.Nonbinary.coreDigit_le 0 v i
  · rw [if_neg h50, if_pos (by omega), show i = 50 by omega]
    simp [T3.maxDigit]
theorem nctx_dataSum (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    ((List.range 50).map (nctxOf w index v p).dig).sum = (T3.dataDigits 0 v).sum := by
  have h : (List.range 50).map (nctxOf w index v p).dig = T3.dataDigits 0 v := by
    unfold T3.dataDigits
    show (List.range 50).map _ = (List.range 50).map (coreDigit 0 v)
    apply List.map_congr_left
    intro i hi
    have := List.mem_range.mp hi
    rw [nctxOf_dig]
    simp [topDig, this]
  rw [h]
theorem nctx_ok (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (c : Nat) (hidx : index < 2 ^ 31) :
    (nctxOf w index v (trPc 0 c)).ok := by
  have hp := trPc_lt 0 c
  have ht : (route index 0).2 = 0 := by rw [route_snd]; exact Nat.div_eq_of_lt hidx
  exact ⟨ht, leaf_lt index 0, by norm_num [nctxOf], by norm_num [nctxOf, Verify.WIT], by norm_num [nctxOf], by dsimp [nctxOf]; omega⟩
theorem hyperWord_top_prefix (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    T3.hyperWord 0 (index / 2 ^ below 0) = BitVec.ofNat 64 ((nctxOf w index v p).prefix + 385) := by
  have h1 : (route index 0).1 = index / 2 ^ 19 % 2 ^ 12 := route_fst index 0
  have h2 : (route index 0).2 = index / 2 ^ (19 + 12) := route_snd index 0
  unfold T3.hyperWord NCtx.prefix
  simp only [nctxOf, h1, h2, show below 0 = 19 from rfl]
  congr 1
  norm_num
  omega
theorem nctx_known (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (t s : MachineState) (a : BitVec 256)
    (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s) :
    KnownOK (nctxOf w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c)).known s := by
  have hprefix : s.getReg .x28 =
      BitVec.ofNat 64 ((nctxOf w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c)).prefix + 385) := by
    rw [he.regs.get (by simp [topEntryRegs]), writeHash_getReg, ht.word]
    exact hyperWord_top_prefix w index _ _
  intro p hp
  simp only [NCtx.known, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact he.s3
  all_goals try exact he.ra
  all_goals try exact hprefix
  all_goals rw [he.regs.get (by simp [topEntryRegs]), writeHash_getReg]
  all_goals exact ht.glob.1 _ (by simp [BC.bK, T3M.bK, layK, baseK, bufferBias])
theorem topEntry_orig (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t s : MachineState) (a : BitVec 256)
    (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s) :
    Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd 0) s := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 15272 ≤ topRowA c ∧ topRowA c ≤ 15528 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d, h12, hd⟩ := ht.dst (by decide +kernel)
  change (d + 16 = topRowA c ∧ WIT + BC.layerEnd 0 + 16 ≤ topRowA c) ∨ d = topRowA c + 48 at hd
  rw [show BC.layerEnd 0 = 11144 from rfl] at hd
  have ho := Orig_writeHash ht.orig a d h12 (by omega)
  have hu : Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd 0) (writeHash t a) :=
    fun j hj hp => ho j hj ⟨hp, Or.inl (by
      have hp2 := hp.2
      have hle : layerEnd 0 = 11144 := rfl
      rw [hle] at hp2
      unfold WIT at *; omega)⟩
  exact hu.frame (fun j hj hp => he.frame.get (by unfold WIT WX at *; omega) (by norm_num [WIT, layerEnd] at *; omega))
theorem topEntry_bufferOrig (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t s : MachineState) (a : BitVec 256)
    (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s) :
    Verify.Orig w (fun o => BC.bufferStart 0 ≤ o ∧ o < 21984) s := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 15272 ≤ topRowA c ∧ topRowA c ≤ 15528 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d, h12, hd⟩ := ht.dst (by decide +kernel)
  change (d + 16 = topRowA c ∧ WIT + BC.layerEnd 0 + 16 ≤ topRowA c) ∨ d = topRowA c + 48 at hd
  have ho := Orig_writeHash ht.bufferOrig a d h12 (by omega)
  have hu : Verify.Orig w (fun o => BC.bufferStart 0 ≤ o ∧ o < 21984) (writeHash t a) :=
    fun j hj hp => ho j hj ⟨hp, Or.inr (by
      have hp1 := hp.1
      norm_num [BC.bufferStart] at hp1
      unfold WIT; omega)⟩
  exact hu.frame (fun j hj hp => he.frame.get (by unfold WIT WX at *; omega) (by norm_num [WIT, BC.bufferStart] at *; omega))
theorem nctx_orig (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (s : MachineState)
    (ho : Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd 0) s)
    (hb : Verify.Orig w (fun o => BC.bufferStart 0 ≤ o ∧ o < 21984) s) (hD : DataOK s) :
    (nctxOf w index v p).Orig0 s := by
  refine ⟨⟨?_, ?_⟩, hD⟩
  · intro i hi k hk
    have hts := NCtx.topSlot_props i hi
    apply origW_of ho _
    all_goals simp only [NCtx.blk, nctxOf]
    all_goals norm_num [WIT, WX, layerEnd] at *
    all_goals omega
  · intro i hi k hk
    have hs := NCtx.slot_props i hi
    apply origW_of hb _
    all_goals norm_num [WIT, WX, BC.bufferStart] at *
    all_goals omega
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route coreDigit dataDigits maxDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
/-! ### Campaign T51: the top chains as the source program (moved here from `Compose`). -/
theorem nctx_block (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p i : Nat) :
    (nctxOf w index v p).blk i - Verify.WIT = ClaudeWCT.W9.T3M.chainBlock 0 i := by
  change 14128 - 1664 + Nonbinary.topSlot i - Verify.WIT = 7664 + 16 * 42 + ClaudeWCT.W9.T3M.chainSlot 0 i
  rw [← NCtx.topSlot_eq]
  unfold Verify.WIT; omega
/-- `bufferSafe_source` from the agreement on digits `j ≤ i` only (a rejected word runs data chains only). -/
theorem bufferSafe_source_le (c : NCtx) (digits : List Nat) (i : Nat) (hi : i < 51)
    (hd : ∀ j, j ≤ i → digits.getD j 0 = c.dig j) :
    c.bufferSafe i ↔ ClaudeWCT.WCT9.safeZeroCopy 0 digits i := by
  unfold NCtx.bufferSafe ClaudeWCT.WCT9.safeZeroCopy
  rw [hd i le_rfl, NCtx.topMax_eq]
  by_cases hz : i = 0
  · simp [hz]
  · rw [hd (i-1) (by omega), NCtx.topMax_eq]
    simp [hz]
theorem bufferVal_source_le (c : NCtx) (digits : List Nat) (hS : c.S3 = 14128) (i : Nat) (hi : i < 51)
    (hd : ∀ j, j ≤ i → digits.getD j 0 = c.dig j) :
    c.bufferVal i = ClaudeWCT.W9.T3M.wvalueFor c.w 0 digits i := by
  unfold NCtx.bufferVal ClaudeWCT.W9.T3M.wvalueFor
  simp only [← bufferSafe_source_le c digits i hi hd, NCtx.bufferSlot_source]
  split
  · rfl
  · unfold NCtx.val ClaudeWCT.W9.T3M.wvalue
    apply congrArg (ClaudeWCT.W9.T3M.wdig c.w)
    have hv : ClaudeWCT.W9.T3M.valueOff 0 i = 48 * (i % 2) := by
      unfold ClaudeWCT.W9.T3M.valueOff; rw [← NCtx.topG_isG, NCtx.topG_lt i hi]
      by_cases h : i % 2 = 0 <;> simp [h] <;> omega
    rw [hv]
    simp only [NCtx.vAt, NCtx.blk, hS, ClaudeWCT.W9.T3M.chainBlock, ClaudeWCT.W9.T3M.layerBase,
      ClaudeWCT.W9.T3M.pathSlots, Matrix.cons_val_zero, Verify.WIT, ← NCtx.topSlot_eq]
    omega
/-- Campaign T51: chain `i` of the top source program for the digit list `ds` (decoded: 50 data digits + checksum;
rejected: the data digits). -/
def srcChain (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (ds : List Nat) (i : Nat) : T3.M Digest :=
  ClaudeWCT.W9.T3M.chainPW 0 (route index 0).2 (route index 0).1 i (ds.getD i 0)
    (maxDigit 0 i - ds.getD i 0) (ClaudeWCT.W9.T3M.wchainPads w 0 i).1
    (ClaudeWCT.W9.T3M.wchainPads w 0 i).2 (ClaudeWCT.W9.T3M.wchainHeaderPad w 0 i) (ClaudeWCT.W9.T3M.wvalueFor w 0 ds i)
theorem nctx_chain_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (ds : List Nat)
    (i : Nat) (hi : i < 51) (hds : ∀ j, j ≤ i → ds.getD j 0 = (nctxOf w index v p).dig j) :
    let c := nctxOf w index v p
    ClaudeWCT.W9.T3M.chainPW 0 c.tree c.leaf i (c.dig i) (NCtx.topMax i - c.dig i) (c.pad0 i) (c.pad1 i)
      (c.padHeader i) (c.bufferVal i) = srcChain w index ds i := by
  have hbuf := bufferVal_source_le (nctxOf w index v p) ds rfl i hi hds
  dsimp only
  unfold srcChain
  rw [← hds i (le_refl _), NCtx.topMax_eq, hbuf]
  have hp0 : (nctxOf w index v p).pad0At i - Verify.WIT =
      ClaudeWCT.W9.T3M.chainBlock 0 i + ClaudeWCT.W9.T3M.pad0Off 0 i := by
    rw [← nctx_block w index v p i]
    unfold NCtx.pad0At ClaudeWCT.W9.T3M.pad0Off; rw [← NCtx.topG_isG, NCtx.topG_lt i hi]
    simp only [NCtx.blk, nctxOf, Verify.WIT]
    by_cases h : i % 2 = 0 <;> simp [h] <;> omega
  have hp1 : (nctxOf w index v p).pad1At i - Verify.WIT =
      ClaudeWCT.W9.T3M.chainBlock 0 i + ClaudeWCT.W9.T3M.pad1Off 0 i := by
    rw [← nctx_block w index v p i]
    unfold NCtx.pad1At ClaudeWCT.W9.T3M.pad1Off; rw [← NCtx.topG_isG, NCtx.topG_lt i hi]
    simp only [NCtx.blk, nctxOf, Verify.WIT]
    by_cases h : i % 2 = 0 <;> simp [h] <;> omega
  unfold NCtx.pad0 NCtx.pad1 NCtx.padHeader
  rw [nctx_block, hp0, hp1]
  rfl
/-- Campaign T51: before a top rejection only data chains (`i < 50`) run, with their data digits. -/
theorem topRejectChains_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (m : Nat) (hm : m ≤ 50)
    (hL : ClaudeWCT.WCT9.topRejectLength v = m) :
    ClaudeWCT.WCT9.topRejectChains (ClaudeWCT.W9.T3M.topChainP w (route index 0).2 (route index 0).1 (dataDigits 0 v)) v =
      (List.range' 0 m).mapM (srcChain w index (dataDigits 0 v)) := by
  unfold ClaudeWCT.WCT9.topRejectChains
  rw [hL]
  refine (TopSource.take_mapM (fun n => ClaudeWCT.W9.T3M.chainPW 0 (route index 0).2 (route index 0).1 n
    (ClaudeWCT.WCT9.topRunDigit v n) (maxDigit 0 n - ClaudeWCT.WCT9.topRunDigit v n)
    (ClaudeWCT.W9.T3M.wchainPads w 0 n).1 (ClaudeWCT.W9.T3M.wchainPads w 0 n).2
    (ClaudeWCT.W9.T3M.wchainHeaderPad w 0 n) (ClaudeWCT.W9.T3M.wvalueFor w 0 (dataDigits 0 v) n)) m (by omega)).trans ?_
  apply mapM_congr'
  intro n hn
  have hn' := List.mem_range'_1.mp hn
  unfold srcChain ClaudeWCT.WCT9.topRunDigit
  rw [if_pos (by omega)]
/-- The context's data digits are the word's data digits (the reject path's agreement). -/
theorem nctx_data_digits (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p j : Nat) (hj : j < 50) :
    (dataDigits 0 v).getD j 0 = (nctxOf w index v p).dig j := by
  rw [nctxOf_dig, ClaudeWCT.WCT9.dataDigits_top_getD v hj]
  unfold topDig; rw [if_pos hj]
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest Layer route)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def topChainRegs : List Reg := [.x10,.x12,.x25,.x3,.x14,.x15,.x24,.x29,.x18]
/-- Campaign T51: the top chains write chain 0's terminal 32 bytes at `[25200, 25232)` (c0hi: the high half is
`end_0` at 25216, the junk low half on the dead L1 leaf-buffer tail), the ends of chains 1..50 from 25248 on, and the
chain blocks. The leaf tweak `[25232, 25248)` is never written. -/
def topChainWrites (A : Nat) : Prop := (25200 ≤ A ∧ A < 25232) ∨ (25248 ≤ A ∧ A < 26064) ∨ (12464 ≤ A ∧ A < 15288)
/-- Campaign T51: the top leaf's known registers (`leafK 0` keeps `t0 = 0` but not main's `s2 = 0xFFF`: the g0 body
loads `s2 = 856064`). -/
theorem topLeafK_of (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (t s0 s : MachineState)
    (a : BitVec 256) (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s0)
    (hr : RegsExcept s0 s topChainRegs) (_h15 : s.getReg .x2 = 0x7fc00#64) : KnownOK (leafK 0) s := by
  intro p hp
  simp only [leafK, gkL, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals rw [hr.get (by simp [topChainRegs])]
  all_goals try exact he.mask
  all_goals rw [he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
  all_goals exact ht.glob.1 _ (by simp [BC.bK, T3M.bK, layK, baseK])
/-- Digit constants and leaf globals survive both the top entry and all chains. -/
theorem topLeafKeepK_of (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat)
    (t s0 s : MachineState) (a : BitVec 256) (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s0)
    (hr : RegsExcept s0 s topChainRegs) : KnownOK (lfKeepK 0) s := by
  intro p hp
  simp [lfKeepK] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [hr.get (by simp [topChainRegs])]
  all_goals try exact he.s3
  all_goals try exact he.ra
  all_goals try exact he.table
  all_goals rw [he.regs.get (by simp [topEntryRegs]), writeHash_getReg]
  all_goals exact ht.glob.1 _ (by simp [BC.bK, T3M.bK, layK, baseK])
/-- Campaign T51: at the final tail `ckTail d50` after the 51 top chains, the top leaf is ready: 51 ends at
`slotT j`, and the tweak high word is witness memory as found. -/
theorem topLeafReady_of (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t s0 s : MachineState) (a : BitVec 256) (ends : List Digest) (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s0)
    (hp : s.pc = pcOf (Nonbinary.ckTail
      ((nctxOf w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c)).dig 50)))
    (hr : RegsExcept s0 s topChainRegs) (hf : Frame s0 s topChainWrites) (h15 : s.getReg .x2 = 0x7fc00#64)
    (hlen : ends.length = 51) (hend : ∀j<51, DigAt s (slotT j) (ends.getD j 0)) :
    TopLeafReady w pk index c ends s := by
  have hk := topLeafK_of w pk index c t s0 s a ht he hr h15
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 15272 ≤ topRowA c ∧ topRowA c ≤ 15528 ∧ topRowA c % 8 = 0 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d,h12,hd⟩ := ht.dst (by decide +kernel)
  change (d + 16 = topRowA c ∧ WIT + BC.layerEnd 0 + 16 ≤ topRowA c) ∨ d = topRowA c + 48 at hd
  have hg := Glob_writeHash ht.glob a d h12 (safeDest_hi d (by unfold WLO WIT; omega) (by omega) (by omega))
  have hfr : Frame (writeHash t a) s (fun A => A = 25160 ∨ topChainWrites A) :=
    he.frame.trans hf
  have hglob : Glob (leafK 0) w pk s := glob_frame hg hfr (by
    intro A h
    unfold topChainWrites at h
    rcases h with h | h | h | h <;> omega) hk
  have hreg : ∀ r, r ∉ topChainRegs → r ∉ topEntryRegs → s.getReg r = t.getReg r := fun r h1 h2 => by
    rw [hr.get h1, he.regs.get h2, writeHash_getReg]
  have hy : (nctxOf w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c)).dig 50 < 6 := by
    rw [nctxOf_dig]
    unfold topDig
    rw [if_neg (by omega), if_pos rfl]
    omega
  refine ⟨⟨_,hy,hp⟩,hglob,?_,?_,?_,?_,hlen,hend,?_,?_⟩
  · exact topLeafKeepK_of w pk index c t s0 s a ht he hr
  · rw [hreg .x23 (by decide +kernel) (by decide +kernel)]
    exact ht.s7 0 rfl (by decide)
  · rw [hreg .x31 (by decide +kernel) (by decide +kernel)]
    exact (ht.t5 0 rfl).2 rfl
  · rw [hreg .x28 (by decide +kernel) (by decide +kernel), ht.word]
    exact hyperWord_top_prefix w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) |>.trans (by
      congr 1
      simp only [Nonbinary.NCtx.prefix, nctxOf, show T3.height 0 = 12 from rfl, Fin.val_zero]
      omega)
  · have ho := topEntry_orig w pk index c hc t s0 a ht he
    apply (ho.mono (fun o h => ⟨h.1, by
      norm_num [ClaudeWCT.W9.T3M.layerBase, ClaudeWCT.W9.T3M.pathSlots, layerEnd] at *; omega⟩)).frame
    intro j hj hp
    exact hf.get (by unfold WIT WX at *;omega) (by
      norm_num [ClaudeWCT.W9.T3M.layerBase, ClaudeWCT.W9.T3M.pathSlots] at hp
      unfold topChainWrites WIT
      omega)
  · -- C3: the top leaf tweak's high word is witness memory
    have h1 : s.getMem (BitVec.ofNat 64 25240) = t.getMem (BitVec.ofNat 64 25240) := by
      rw [hf.get (by omega) (by unfold topChainWrites; omega), he.frame.get (by omega) (by omega),
        writeHash_frame t a d 25240 h12 (by omega) (by omega) (Or.inr (by omega))]
    have hlb0 : ClaudeWCT.W9.T3M.leafBufferBase 0 = 21088 := rfl
    have hhi := ht.bufferOrig.hi 21104 (by decide) (by unfold WX; decide) ⟨by decide, by decide⟩
    unfold ClaudeWCT.W9.T3M.wleafHigh; rw [hlb0]
    exact h1.trans hhi
end SigGolfCandidate.T3M
end
