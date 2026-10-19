import SigGolfCandidate.T3M.Verify.Nonbinary.LayerPrefix
import SigGolfCandidate.T3M.Verify.Nonbinary.TopAlias
import SigGolfCandidate.T3M.Verify.LayerSem
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatchCtx
import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.T3.Nonbinary.LowerLayout

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
/-- Exact cycle cost of the e7b top-half selector: hint clear 4, hint set with LOW forced 6, HIGH 7. -/
def selCost (high : Bool) (a : BitVec 256) : Nat :=
  if high then (if T3.TopChoice.blocked (a.extractLsb' 0 128) then 6 else 7) else 4
def selMax : Nat := 7
theorem selCost_le (high : Bool) (a : BitVec 256) : selCost high a ≤ selMax := by
  unfold selCost selMax; split_ifs <;> omega
theorem prefix_select_spec {image : Image} (s : MachineState) (a : BitVec 256) (high : Bool) (d p : Nat)
    (hpc : s.pc = pcOf p)
    (hc : CodeAt image (pcOf p) prefixSel)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 d)
    (hd : d % 8 = 0 ∧ 0x1000 ≤ d ∧ d + 32 ≤ 0x7000)
    (h11 : s.getReg .x11 = 64#64) (h4 : s.getReg .x4 = 24688#64)
    (hhint : (extractByte (s.getMem 25216#64) 0).getLsbD selHintBit = high)
    (hlo : DigAt s d (a.extractLsb' 0 128))
    (hhi : DigAt s (d+16) (a.extractLsb' 128 128)) :
    ∃ t, Steps image s (selCost high a) (selCost high a) t ∧ t.pc = pcOf (p+selLen) ∧
      t.getReg .x16 = (T3.TopChoice.read high a).extractLsb' 0 64 ∧
      t.getReg .x17 = (T3.TopChoice.read high a).extractLsb' 64 64 ∧
      (∃ e, t.getReg .x12 = BitVec.ofNat 64 e ∧ (e = d ∨ e = d + 16)) ∧
      RegsExcept s t [.x3,.x12,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  have hsub : ∀ (pre seg post : List (BitVec 32)), prefixSel = pre ++ seg ++ post →
      CodeAt image (pcOf (p + pre.length)) seg := by
    intro pre seg post he
    have h := hc
    rw [he] at h
    have h' := CodeAt.drop_prefix (pre := pre) (seg := seg) (post := post) h
    rwa [pcOf, ofNat_add_ofNat, show 0x1000 + 4 * p + 4 * pre.length = 0x1000 + 4 * (p + pre.length) by ring] at h'
  have hc0 : CodeAt image (pcOf p) prefixHint := by
    simpa using hsub [] prefixHint (prefixHead ++ prefixHigh ++ prefixLoad) (by simp [prefixSel])
  have hc2 : CodeAt image (pcOf (p+2)) prefixHead := by
    simpa [prefixHint] using hsub prefixHint prefixHead (prefixHigh ++ prefixLoad) (by simp [prefixSel])
  have hc4 : CodeAt image (pcOf (p+4)) prefixHigh := by
    simpa [prefixHint, prefixHead] using hsub (prefixHint ++ prefixHead) prefixHigh prefixLoad (by simp [prefixSel])
  have hc5 : CodeAt image (pcOf (p+5)) prefixLoad := by
    simpa [prefixHint, prefixHead, prefixHigh] using
      hsub (prefixHint ++ prefixHead ++ prefixHigh) prefixLoad [] (by simp [prefixSel])
  have hhint : (extractByte (s.getMem 25216#64) 0).getLsbD 7 = high := hhint
  -- the final loads `ld a7,8(a2); ld a6,0(a2)` from a state whose `a2` points at the selected half
  have load : ∀ (v : MachineState) (e : Nat) (hv : v.pc = pcOf (p+5)) (hve : v.getReg .x12 = BitVec.ofNat 64 e)
      (he : e = d ∨ e = d + 16) (hfr : Frame s v (fun _ => False)) (half : BitVec 128) (hh : DigAt s e half),
      ∃ t, Steps image v 2 2 t ∧ t.pc = pcOf (p+selLen) ∧ t.getReg .x16 = half.extractLsb' 0 64 ∧
        t.getReg .x17 = half.extractLsb' 64 64 ∧ t.getReg .x12 = BitVec.ofNat 64 e ∧
        RegsExcept v t [.x16,.x17] ∧ Frame v t (fun _ => False) := by
    intro v e hv hve he hfr half hh
    have ec := symRun_sound (prefixLoad_run (pcOf (p+5))) hc5 v hv (by
      simp [prefixLoadRes, prefixLoadBase.res, rv_simp, hve, accessValid_iff, MEMORY_BYTES]; omega)
    let t := (prefixLoadRes (pcOf (p+5))).toState v
    have rt : RegsExcept v t [.x16,.x17] := by
      intro r hr; cases r <;> simp_all [t, prefixLoadRes, prefixLoadBase.res, rv_simp] <;> rfl
    have ft : Frame v t (fun _ => False) := by
      intro A _ _; simp [t, prefixLoadRes, prefixLoadBase.res, rv_simp]
    have m0 : v.getMem (BitVec.ofNat 64 e) = half.extractLsb' 0 64 := (hfr.get (by omega) (by simp)).trans hh.1
    have m8 : v.getMem (BitVec.ofNat 64 (e + 8)) = half.extractLsb' 64 64 :=
      (hfr.get (by omega) (by simp)).trans hh.2
    refine ⟨t, ec, ?_, ?_, ?_, (rt.get (by decide)).trans hve, rt, ft⟩
    · simp [t, prefixLoadRes, prefixLoadBase.res, rv_simp, pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc, selLen]
    · simpa [t, prefixLoadRes, prefixLoadBase.res, rv_simp, hve] using m0
    · simp only [t, prefixLoadRes, prefixLoadBase.res, Result.toState_getReg, RegFile.get, E.eval, BinOp.eval]
      rw [hve, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat]; exact m8
  -- hint block `lb gp,528(tp); bge gp,zero,L`
  have ho0 : ∀ o ∈ prefixHintBase.res.st.obl, o.holds s := by
    simp [prefixHintBase.res, rv_simp, h4, accessValid_iff, MEMORY_BYTES]
  have e0 := symRun_sound (prefixHint_run (pcOf p)) hc0 s hpc ((Oblig.all_iff _ _).mpr ho0)
  let u := (prefixHintRes (pcOf p)).toState s
  have ru : RegsExcept s u [.x3] := by
    intro r hr; cases r <;> simp_all [u, prefixHintRes, prefixHintBase.res, rv_simp] <;> rfl
  have fu : Frame s u (fun _ => False) := by
    intro A _ _; simp [u, prefixHintRes, prefixHintBase.res, rv_simp]
  have hhb : hintByte.eval s = (extractByte (s.getMem 25216#64) 0).signExtend 64 := by
    simp only [hintByte, E.eval, UnOp.eval, LoadKind.fromWord, BinOp.eval]
    rw [show (s.getReg Reg.x4 + 528) = 25216#64 by rw [h4]; rfl]
  have hcmp : CmpOp.ge.eval (hintByte.eval s) ((E.c 0).eval s) = !high := by
    simp only [CmpOp.eval, E.eval]; rw [hhb, lb_ge_zero, hhint]
  have pu : u.pc = if high then pcOf (p+2) else pcOf (p+5) := by
    simp only [u, Result.toState_pc, prefixHintRes]
    simp only [E.eval] at hcmp ⊢
    simp only [hcmp]
    cases high
    · simp [pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
    · simp [pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
  have h12u : u.getReg .x12 = BitVec.ofNat 64 d := (ru.get (by decide)).trans h12
  cases high with
  | false =>
    rw [if_neg (by simp)] at pu
    obtain ⟨t, et, pt, t16, t17, t12, rt, ft⟩ := load u d pu h12u (Or.inl rfl) fu _ hlo
    have hr : T3.TopChoice.read false a = a.extractLsb' 0 128 := T3.TopChoice.read_false a
    refine ⟨t, by rw [show selCost false a = 4 from rfl]; exact e0.trans et, pt, by rw [t16, hr], by rw [t17, hr],
      ⟨d, t12, Or.inl rfl⟩, (ru.trans rt).mono (by decide), (fu.trans ft).mono (by simp)⟩
  | true =>
    rw [if_pos rfl] at pu
    -- `lbu gp,15(a2); bltu gp,a1,L`: LOW forced iff its top byte < 64
    have hlo1 : u.getMem (u.getReg .x12 + 8#64) = (a.extractLsb' 0 128).extractLsb' 64 64 := by
      rw [h12u, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat, fu.get (by omega) (by simp), hlo.2]
    have ho1 : ∀ o ∈ prefixHeadBase.res.st.obl, o.holds u := by
      simp [prefixHeadBase.res, rv_simp, h12u, accessValid_iff, MEMORY_BYTES]
      omega
    have e1 := symRun_sound (prefixHead_run (pcOf (p+2))) hc2 u pu ((Oblig.all_iff _ _).mpr ho1)
    let v := (prefixHeadRes (pcOf (p+2))).toState u
    have rv : RegsExcept u v [.x3] := by
      intro r hr; cases r <;> simp_all [v, prefixHeadRes, prefixHeadBase.res, rv_simp] <;> rfl
    have fv : Frame u v (fun _ => False) := by
      intro A _ _; simp [v, prefixHeadRes, prefixHeadBase.res, rv_simp]
    have hb : headByte.eval u = (extractByte ((a.extractLsb' 0 128).extractLsb' 64 64) 7).zeroExtend 64 := by
      simp only [headByte, E.eval, UnOp.eval, LoadKind.fromWord, BinOp.eval]
      rw [show (u.getReg Reg.x12 + 8) = u.getReg .x12 + 8#64 from rfl, hlo1]
    have h11u : u.getReg .x11 = 64#64 := (ru.get (by decide)).trans h11
    have hcmp : CmpOp.ltu.eval (headByte.eval u) ((E.reg .x11).eval u) =
        decide (T3.TopChoice.blocked (a.extractLsb' 0 128)) := by
      simp only [CmpOp.eval, E.eval]; rw [hb, h11u, byte7_ult]
    have pv : v.pc = if T3.TopChoice.blocked (a.extractLsb' 0 128) then pcOf (p+5) else pcOf (p+4) := by
      simp only [v, Result.toState_pc, prefixHeadRes]
      simp only [E.eval] at hcmp ⊢
      simp only [hcmp]
      by_cases hbl : T3.TopChoice.blocked (a.extractLsb' 0 128)
      · simp [hbl, pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
      · simp [hbl, pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
    have h12v : v.getReg .x12 = BitVec.ofNat 64 d := (rv.get (by decide)).trans h12u
    have fsv : Frame s v (fun _ => False) := (fu.trans fv).mono (by simp)
    by_cases hbl : T3.TopChoice.blocked (a.extractLsb' 0 128)
    · rw [if_pos hbl] at pv
      obtain ⟨t, et, pt, t16, t17, t12, rt, ft⟩ := load v d pv h12v (Or.inl rfl) fsv _ hlo
      have hr : T3.TopChoice.read true a = a.extractLsb' 0 128 := T3.TopChoice.read_blocked true hbl
      refine ⟨t, by rw [show selCost true a = 6 by simp [selCost, hbl]]; exact (e0.trans e1).trans et, pt,
        by rw [t16, hr], by rw [t17, hr], ⟨d, t12, Or.inl rfl⟩,
        ((ru.trans rv).trans rt).mono (by decide), ((fu.trans fv).trans ft).mono (by simp)⟩
    · rw [if_neg hbl] at pv
      -- `addi a2,a2,16`
      have e2 := symRun_sound (prefixHigh_run (pcOf (p+4))) hc4 v pv (by simp [prefixHighRes, prefixHighBase.res, rv_simp])
      let w := (prefixHighRes (pcOf (p+4))).toState v
      have rw' : RegsExcept v w [.x12] := by
        intro r hr; cases r <;> simp_all [w, prefixHighRes, prefixHighBase.res, rv_simp] <;> rfl
      have fw : Frame v w (fun _ => False) := by
        intro A _ _; simp [w, prefixHighRes, prefixHighBase.res, rv_simp]
      have pw : w.pc = pcOf (p+5) := by
        simp [w, prefixHighRes, prefixHighBase.res, rv_simp, pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
      have h12w : w.getReg .x12 = BitVec.ofNat 64 (d + 16) := by
        simp [w, prefixHighRes, prefixHighBase.res, rv_simp, h12v, ofNat_add_ofNat]
      obtain ⟨t, et, pt, t16, t17, t12, rt, ft⟩ :=
        load w (d+16) pw h12w (Or.inr rfl) ((fsv.trans fw).mono (by simp)) _ hhi
      have hr : T3.TopChoice.read true a = a.extractLsb' 128 128 := by
        simp [T3.TopChoice.read, T3.TopChoice.lowHalf, T3.TopChoice.highHalf, hbl]
      refine ⟨t, by rw [show selCost true a = 7 by simp [selCost, hbl]]; exact ((e0.trans e1).trans e2).trans et, pt,
        by rw [t16, hr], by rw [t17, hr], ⟨d + 16, t12, Or.inr rfl⟩,
        (((ru.trans rv).trans rw').trans rt).mono (by decide), (((fu.trans fv).trans fw).trans ft).mono (by simp)⟩

end SigGolfCandidate.T3M.Verify.Nonbinary
end


section
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
/-- Campaign R6: the g0 dispatch target of the prologue's `slli a4,a6,56; srli a4,a4,45; jalr -744(a4)` (a6 = the
low half of the selected word). -/
def prologueTarget (v : Digest) : Word :=
  ((((v.extractLsb' 0 64) <<< 56) >>> 45) + BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64
/-- Campaign R6 prologue tail (spare bit clear): `blt a7,zero` falls through, then the 7 words load the r5 mask t1,
the r6 mask t4 (data word 16), the table base s2, s0 = 13432 and jump into group 0's column (8 cycles). -/
theorem prefix_tail_spec (s : MachineState) (v : Digest) (a p : Nat) (ha : a ∈ aVals)
    (hpc : s.pc = pcOf p) (hcode : CodeAt Verify.image (pcOf p) (prefixTailWordsOf a))
    (h0 : s.getReg .x16 = v.extractLsb' 0 64) (h1 : s.getReg .x17 = v.extractLsb' 64 64)
    (hra : s.getReg .x9 = BitVec.ofNat 64 TOPB9)
    (hmask : s.getMem 0xffbff8#64 = 520192#64) (hmask6 : s.getMem (BitVec.ofNat 64 (TOPB9 - 288)) = 65280#64)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 a) (hsp : v.toNat / 2 ^ 127 % 2 = 0) :
    ∃ t, Steps Verify.image s 8 8 t ∧ t.pc = prologueTarget v ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧ t.getReg .x17 = v.extractLsb' 64 64 ∧
      t.getReg .x29 = 65280#64 ∧ t.getReg .x18 = 856064#64 ∧
      t.getReg .x8 = 13432#64 ∧ t.getReg .x6 = 520192#64 ∧
      RegsExcept s t [.x16,.x17,.x29,.x6,.x8,.x14,.x18] ∧
      Frame s t (fun _ => False) := by
  have hcs : CodeAt Verify.image (pcOf p) prefixSpare := by
    have h := CodeAt.drop_prefix (pre := []) (seg := prefixSpare) (post := prefixRestWordsOf a)
      (by simpa [prefixTailWordsOf] using hcode)
    simpa using h
  have hcr : CodeAt Verify.image (pcOf (p+1)) (prefixRestWordsOf a) := by
    have h := CodeAt.drop_prefix (pre := prefixSpare) (seg := prefixRestWordsOf a) (post := [])
      (by simpa [prefixTailWordsOf] using hcode)
    rwa [show pcOf p + BitVec.ofNat 64 (4 * prefixSpare.length) = pcOf (p+1) from pcOf_add4 p] at h
  obtain ⟨t, st, pt, t16, t17, t29, t18, t8, t6, rt, ft⟩ :=
    (prefix_tail_spec6 s v a p ha hpc hcs hcr h0 h1 (by rw [hra]; rfl) hmask hmask6 h10).2 hsp
  exact ⟨t, st, pt, t16, t17, t29, t18, t8, t6, fun r hr => rt r (by simp at hr ⊢; tauto), ft⟩
/-- Campaign R6: a set spare bit (bit 127 of the selected word) takes `blt a7,zero` to a zero word. -/
theorem prefix_spare_fault (s : MachineState) (v : Digest) (a p : Nat)
    (hpc : s.pc = pcOf p) (hcode : CodeAt Verify.image (pcOf p) (prefixTailWordsOf a))
    (h1 : s.getReg .x17 = v.extractLsb' 64 64) (hsp : v.toNat / 2 ^ 127 % 2 = 1) :
    ∃ t, Steps Verify.image s 1 1 t ∧ t.pc = pcOf p + 32#64 := by
  have hcs : CodeAt Verify.image (pcOf p) prefixSpare := by
    have h := CodeAt.drop_prefix (pre := []) (seg := prefixSpare) (post := prefixRestWordsOf a)
      (by simpa [prefixTailWordsOf] using hcode)
    simpa using h
  refine ⟨_, symRun_sound (prefixSpare_run (pcOf p)) hcs s hpc
    (by simp [Result.obligs, Oblig.all, prefixSpareRes, prefixSpareBase.res]), ?_⟩
  rw [Result.toState_pc, prefixSpare_pc s (pcOf p) v h1, if_pos hsp]
  rfl
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
/-- Configuration (1)+(2): the selector also writes `gp` (x3) and `a2` (x12); both are dead after the head. Campaign R6:
the prologue also loads the r6 mask t4 (x29) and the table base s2 (x18). -/
def topEntryRegs : List Reg := [.x16,.x17,.x29,.x6,.x8,.x14,.x3,.x12,.x18]
/-- Campaign R6: the top region entry (after the head and the prologue, spare bit clear): pc at the g0 column target,
the selected half unflipped in a6/a7, t4 = 0xFF00, s2 = 856064, t1 = 0x7F000. -/
structure TopEntry (u : MachineState) (v : Digest) (p : Nat) (s : MachineState) : Prop where
  pc : s.pc = Nonbinary.prologueTarget v
  ra : s.getReg .x9 = BitVec.ofNat 64 TOPB9
  lo : s.getReg .x16 = v.extractLsb' 0 64
  hi : s.getReg .x17 = v.extractLsb' 64 64
  mask6 : s.getReg .x29 = 65280#64
  base6 : s.getReg .x18 = 856064#64
  s3 : s.getReg .x8 = 13432#64
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
      Nonbinary.prefixSel, Nonbinary.prefixHead, Nonbinary.prefixHint, Nonbinary.prefixHigh, Nonbinary.prefixLoad,
      Nonbinary.prefixTailWordsOf, Nonbinary.prefixSpare, Nonbinary.prefixRestWordsOf,
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
/-- The witness choice byte (rel 22312, abs 25216) is the low byte of its witness word. -/
theorem extractByte_wword_choice (w : ClaudeWCT.W9.T3M.WBytes) :
    extractByte (wword w (ClaudeWCT.W9.T3M.choiceOff / 8)) 0 = ClaudeWCT.W9.T3M.wchoice w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, wword, ClaudeWCT.W9.T3M.wchoice, ClaudeWCT.W9.T3M.choiceOff, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', Nat.zero_mul, Nat.zero_add]
  simp [hi, show i < 64 by omega]
theorem trPc_top_all : (List.range 128).all (fun c => trPc 0 c == 1064 + 1024 * c) = true := by decide +kernel
theorem trPc_top (c : Nat) (hc : c < 128) : trPc 0 c = 1064 + 1024 * c := by
  have h := List.all_eq_true.mp trPc_top_all c (List.mem_range.mpr hc)
  simpa using h
theorem topTransition (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : BC.EncPre w pk index 0 c t) (a : BitVec 256) :
    ((T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a).toNat / 2 ^ 127 % 2 = 0 →
      ∃ n s, Steps image (writeHash t a) n n s ∧ n ≤ 15 ∧
        n = Verify.Nonbinary.selCost (ClaudeWCT.W9.T3M.wtopHigh w) a + 8 ∧
        TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s) ∧
    ((T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a).toNat / 2 ^ 127 % 2 = 1 →
      ∃ n s, Steps image (writeHash t a) n n s ∧
        n = Verify.Nonbinary.selCost (ClaudeWCT.W9.T3M.wtopHigh w) a + 1 ∧ fetch image s = none) := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 15224 ≤ topRowA c ∧ topRowA c ≤ 15480 ∧ topRowA c % 8 = 0 := by
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
  have h4 : (writeHash t a).getReg .x4 = 24688#64 :=
    hk (.x4, 24688#64) (by simp [BC.bK, T3M.bK, layK, bufferBias])
  have h11 : (writeHash t a).getReg .x11 = 64#64 :=
    hk (.x11, 64#64) (by simp [BC.bK, T3M.bK, layK])
  have hmask : (writeHash t a).getMem 0xffbff8#64 = 520192#64 := hD.mask
  have hhi := DigAt.writeHash_hi t a d h12 (by omega)
  -- the choice hint byte (witness rel 22312 = abs 25216) is still the original witness byte
  have hhint : (extractByte ((writeHash t a).getMem 25216#64) 0).getLsbD Nonbinary.selHintBit =
      ClaudeWCT.W9.T3M.wtopHigh w := by
    have ho := Orig_writeHash ht.bufferOrig a d h12 (by omega)
    have hw := ho.word ClaudeWCT.W9.T3M.choiceOff (by decide) (by unfold WX; decide)
      ⟨⟨by norm_num [BC.bufferStart, ClaudeWCT.W9.T3M.choiceOff], by norm_num [ClaudeWCT.W9.T3M.choiceOff]⟩,
        Or.inr (by unfold WIT ClaudeWCT.W9.T3M.choiceOff; omega)⟩
    rw [show (25216#64 : Word) = BitVec.ofNat 64 (WIT + ClaudeWCT.W9.T3M.choiceOff) from rfl, hw,
      extractByte_wword_choice]
    rfl
  obtain ⟨u,eu,pu,lu,hu,⟨e,he12,he⟩,ru,fu⟩ := Verify.Nonbinary.prefix_select_spec
    (writeHash t a) a (ClaudeWCT.W9.T3M.wtopHigh w) d (trPc 0 c + 6) hpc
    (by simpa using (prefix_sub_at c hc' [] Nonbinary.prefixSel (Nonbinary.prefixTailWordsOf (topRowA c))
      (by simp [Nonbinary.prefixWordsOf])))
    h12s hdA h11 h4 hhint hv hhi
  have hcode : CodeAt Verify.image (pcOf (trPc 0 c + 6 + Nonbinary.selLen)) (Nonbinary.prefixTailWordsOf (topRowA c)) := by
    simpa [Nonbinary.prefixSel_length] using
      (prefix_sub_at c hc' Nonbinary.prefixSel (Nonbinary.prefixTailWordsOf (topRowA c)) []
        (by simp [Nonbinary.prefixWordsOf]))
  have hn := Verify.Nonbinary.selCost_le (ClaudeWCT.W9.T3M.wtopHigh w) a
  unfold Verify.Nonbinary.selMax at hn
  refine ⟨fun hsp => ?_, fun hsp => ?_⟩
  · obtain ⟨z, ez, pz, lo, hi, m6, b6, s3, mask, rz, fz⟩ :=
      Verify.Nonbinary.prefix_tail_spec u (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (topRowA c)
        (trPc 0 c + 6 + Nonbinary.selLen) ha pu hcode lu hu
        ((ru.get (by decide)).trans hra)
        (by rw [fu.get (by decide) (by simp)]; exact hmask)
        (by rw [fu.get (by unfold TOPB9; decide) (by simp)]; exact hD.mask6)
        ((ru.get (by decide)).trans h10) hsp
    refine ⟨_,z,eu.trans ez,by omega,rfl,⟨pz,?_,lo,hi,m6,b6,s3,mask,?_,?_,?_⟩⟩
    · rw [rz.get (by decide),ru.get (by decide),hra]
    · rw [rz.get (by decide),ru.get (by decide),h15]
    · exact (ru.trans rz).mono (by simp [topEntryRegs])
    · exact (fu.trans fz).mono (by simp)
  · obtain ⟨z, ez, pz⟩ :=
      Verify.Nonbinary.prefix_spare_fault u (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (topRowA c)
        (trPc 0 c + 6 + Nonbinary.selLen) pu hcode hu hsp
    refine ⟨_,z,eu.trans ez,rfl,?_⟩
    have ht := trPc_top c hc'
    have hf := Nonbinary.spare_fault c hc' z (by
      rw [pz, ht]; unfold Nonbinary.selLen
      rw [show 1064 + 1024 * c + 6 + 7 = (1064 + 1024 * c) + 13 by omega,
        Nonbinary.spare_target _ (by omega), show (1064 + 1024 * c) + 21 = 1085 + 1024 * c by omega])
    exact hf
/-- Campaign R6: the top entry carries the machine registers of the r6/r5 dispatch (`Encoded6`). -/
theorem topEntry_encoded6 {u s : MachineState} {v : Digest} {p : Nat} (he : TopEntry u v p s) :
    Nonbinary.NCtx.Encoded6 v s :=
  ⟨he.lo, he.hi, he.mask6, he.base6, he.mask⟩
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
/-- Campaign R6: the chain digits of a top word: the 51 data digits, then the checksum digit (clamped to 7, the machine
only reaches chain 51 when `target 0 - sum` lies in `0..7`). -/
def topDig (v : Digest) (i : Nat) : Nat :=
  if i < 51 then coreDigit 0 v i else if i = 51 then min 7 (T3.target 0 - (T3.dataDigits 0 v).sum) else 0
def nctxOf (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) : NCtx :=
  ⟨w, (route index 0).2, (route index 0).1, 13432, topDig v, p + 8⟩
/-- Campaign R6: the context's digits through a symbolic index (a `show` at a literal index makes the unifier
evaluate `min 7 (target 0 - sum)`). -/
theorem nctxOf_dig (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p i : Nat) :
    (nctxOf w index v p).dig i = topDig v i := rfl
theorem nctx_fit6 (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    (nctxOf w index v p).Fit6 v := fun i hi => by
  show topDig v i = _
  simp [topDig, hi]
theorem nctx_digits (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    (nctxOf w index v p).DigitsOk := by
  intro i hi
  by_cases h51 : i < 51
  · exact (nctxOf w index v p).fit6_le (nctx_fit6 w index v p) i h51
  · show topDig v i ≤ _
    by_cases h : i = 51
    · subst h; rw [Nonbinary.NCtx.topMax_hi 51 (by omega)]; simp [topDig]
    · simp [topDig, h51, h]
theorem nctx_dataSum (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    ((List.range 51).map (nctxOf w index v p).dig).sum = (T3.dataDigits 0 v).sum := by
  have h : (List.range 51).map (nctxOf w index v p).dig = T3.dataDigits 0 v := by
    unfold T3.dataDigits
    show (List.range 51).map _ = (List.range 51).map (coreDigit 0 v)
    apply List.map_congr_left
    intro i hi
    have := List.mem_range.mp hi
    show topDig v i = _
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
    Verify.Orig w (fun o => 8096 ≤ o ∧ o < layerEnd 0) s := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 15224 ≤ topRowA c ∧ topRowA c ≤ 15480 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d, h12, hd⟩ := ht.dst (by decide +kernel)
  change (d + 16 = topRowA c ∧ WIT + BC.layerEnd 0 + 16 ≤ topRowA c) ∨ d = topRowA c + 48 at hd
  rw [show BC.layerEnd 0 = 12320 from rfl] at hd
  have ho := Orig_writeHash ht.orig a d h12 (by omega)
  have hu : Verify.Orig w (fun o => 8096 ≤ o ∧ o < layerEnd 0) (writeHash t a) :=
    fun j hj hp => ho j hj ⟨hp, Or.inl (by
      have hp2 := hp.2
      have hle : layerEnd 0 = 12320 := rfl
      rw [hle] at hp2
      unfold WIT at *; omega)⟩
  exact hu.frame (fun j hj hp => he.frame.get (by unfold WIT WX at *; omega) (by norm_num [WIT, layerEnd] at *; omega))
theorem topEntry_bufferOrig (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t s : MachineState) (a : BitVec 256)
    (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s) :
    Verify.Orig w (fun o => BC.bufferStart 0 ≤ o ∧ o < 23208) s := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 15224 ≤ topRowA c ∧ topRowA c ≤ 15480 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d, h12, hd⟩ := ht.dst (by decide +kernel)
  change (d + 16 = topRowA c ∧ WIT + BC.layerEnd 0 + 16 ≤ topRowA c) ∨ d = topRowA c + 48 at hd
  have ho := Orig_writeHash ht.bufferOrig a d h12 (by omega)
  have hu : Verify.Orig w (fun o => BC.bufferStart 0 ≤ o ∧ o < 23208) (writeHash t a) :=
    fun j hj hp => ho j hj ⟨hp, Or.inr (by
      have hp1 := hp.1
      norm_num [BC.bufferStart] at hp1
      unfold WIT; omega)⟩
  exact hu.frame (fun j hj hp => he.frame.get (by unfold WIT WX at *; omega) (by norm_num [WIT, BC.bufferStart] at *; omega))
theorem nctx_orig (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (s : MachineState)
    (ho : Verify.Orig w (fun o => 8096 ≤ o ∧ o < layerEnd 0) s)
    (hb : Verify.Orig w (fun o => BC.bufferStart 0 ≤ o ∧ o < 23208) s) (hD : DataOK s) :
    (nctxOf w index v p).Orig0 s := by
  refine ⟨⟨?_, ?_⟩, hD⟩
  · intro i hi k hk
    apply origW_of ho _
    all_goals simp only [NCtx.blk, nctxOf]
    all_goals norm_num [WIT, WX, layerEnd] at *
    all_goals omega
  · intro i hi k hk
    apply origW_of hb _
    all_goals norm_num [Nonbinary.slot, WIT, WX, BC.bufferStart] at *
    all_goals omega
end SigGolfCandidate.T3M
end
