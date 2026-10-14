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
theorem prefix_select_spec {image : Image} (s : MachineState) (a : BitVec 256) (d p : Nat)
    (hpc : s.pc = pcOf p)
    (hc0 : CodeAt image (pcOf p) prefixHead)
    (hc2 : CodeAt image (pcOf (p+2)) prefixLow)
    (hc4 : CodeAt image (pcOf (p+4)) prefixHigh)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 d)
    (hd : d % 8 = 0 ∧ 0x1000 ≤ d ∧ d + 32 ≤ 0x7000)
    (hlo : DigAt s d (a.extractLsb' 0 128))
    (hhi : DigAt s (d+16) (a.extractLsb' 128 128)) :
    ∃ k t, Steps image s k k t ∧ k ≤ 4 ∧ t.pc = pcOf (p+6) ∧
      t.getReg .x16 = (T3.TopDualHalf.select a).extractLsb' 0 64 ∧
      t.getReg .x17 = (T3.TopDualHalf.select a).extractLsb' 64 64 ∧
      RegsExcept s t [.x16,.x17] ∧ Frame s t (fun _ => False) := by
  have hm0 : s.getMem (s.getReg .x12) = (a.extractLsb' 0 128).extractLsb' 0 64 := by rw [h12]; exact hlo.1
  have hm1 : s.getMem (s.getReg .x12 + 8#64) = (a.extractLsb' 0 128).extractLsb' 64 64 := by
    rw [h12, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat]; exact hlo.2
  have hm2 : s.getMem (s.getReg .x12 + 16#64) = (a.extractLsb' 128 128).extractLsb' 0 64 := by
    rw [h12, show (16#64 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]; exact hhi.1
  have hm3 : s.getMem (s.getReg .x12 + 24#64) = (a.extractLsb' 128 128).extractLsb' 64 64 := by
    rw [h12, show (24#64 : Word) = BitVec.ofNat 64 24 from rfl, ofNat_add_ofNat]
    simpa [Nat.add_assoc] using hhi.2
  have ho : ∀ o ∈ prefixHeadBase.res.st.obl, o.holds s := by
    simp [prefixHeadBase.res, rv_simp, h12, accessValid_iff, MEMORY_BYTES]
    omega
  have es := symRun_sound (prefixHead_run (pcOf p)) hc0 s hpc ((Oblig.all_iff _ _).mpr ho)
  let u := (prefixHeadRes (pcOf p)).toState s
  have ru : RegsExcept s u [.x17] := by
    intro r hr; cases r <;> simp_all [u, prefixHeadRes, prefixHeadBase.res, rv_simp] <;> rfl
  have fu : Frame s u (fun _ => False) := by
    intro A _ _; simp [u, prefixHeadRes, prefixHeadBase.res, rv_simp]
  have pu : u.pc = if T3.TopDualHalf.gate (a.extractLsb' 0 128) then pcOf (p+2) else pcOf (p+4) := by
    change (if (!(s.getMem (s.getReg .x12 + 8#64)).slt (0#64)) = true then
      pcOf p + 4 + 12 else pcOf p + 4 + 4) = _
    rw [hm1,BitVec.slt_zero_eq_msb,BitVec.msb_extractLsb',BitVec.getMsbD_eq_getLsbD]
    change (if (!(a.extractLsb' 0 128).getLsbD 127) = true then
      pcOf p + 4 + 12 else pcOf p + 4 + 4) = _
    by_cases hg : T3.TopDualHalf.gate (a.extractLsb' 0 128)
    · have hb := (T3.TopDualHalf.gate_iff_getLsbD (a.extractLsb' 0 128)).mp hg
      rw [hb,if_pos hg]
      simp [pcOf,ofNat_add_ofNat,Nat.mul_add,Nat.add_assoc] <;> congr 1 <;> omega
    · have hb : (a.extractLsb' 0 128).getLsbD 127 = false := by
        cases hbit : (a.extractLsb' 0 128).getLsbD 127
        · rfl
        · exact False.elim (hg ((T3.TopDualHalf.gate_iff_getLsbD (a.extractLsb' 0 128)).mpr hbit))
      rw [hb,if_neg hg]
      simp [pcOf,ofNat_add_ofNat,Nat.mul_add,Nat.add_assoc] <;> congr 1 <;> omega
  have h12u : u.getReg .x12 = BitVec.ofNat 64 d := (ru.get (by decide)).trans h12
  by_cases hg : T3.TopDualHalf.gate (a.extractLsb' 0 128)
  · rw [if_pos hg] at pu
    have ec := symRun_sound (prefixLow_run (pcOf (p+2))) hc2 u pu (by
      simp [prefixLowRes, prefixLowBase.res, rv_simp, h12u, accessValid_iff, MEMORY_BYTES]; omega)
    let t := (prefixLowRes (pcOf (p+2))).toState u
    have rt : RegsExcept u t [.x16] := by
      intro r hr; cases r <;> simp_all [t, prefixLowRes, prefixLowBase.res, rv_simp] <;> rfl
    have ft : Frame u t (fun _ => False) := by
      intro A _ _; simp [t, prefixLowRes, prefixLowBase.res, rv_simp]
    refine ⟨4,t,es.trans ec,by omega,?_,?_,?_,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
    · simp [t, prefixLowRes, prefixLowBase.res, rv_simp, pcOf, ofNat_add_ofNat] <;> congr 1 <;> omega
    · simp only [T3.TopDualHalf.select,T3.TopDualHalf.selectPair,if_pos hg]
      simpa [t,u,prefixLowRes,prefixLowBase.res,prefixHeadRes,prefixHeadBase.res,rv_simp] using hm0
    · simp only [T3.TopDualHalf.select,T3.TopDualHalf.selectPair,if_pos hg]
      rw [rt.get (by decide)]
      simpa [u,prefixHeadRes,prefixHeadBase.res,rv_simp] using hm1
  · rw [if_neg hg] at pu
    have ec := symRun_sound (prefixHigh_run (pcOf (p+4))) hc4 u pu (by
      simp [prefixHighRes, prefixHighBase.res, rv_simp, h12u, accessValid_iff, MEMORY_BYTES]; omega)
    let t := (prefixHighRes (pcOf (p+4))).toState u
    have rt : RegsExcept u t [.x16,.x17] := by
      intro r hr; cases r <;> simp_all [t, prefixHighRes, prefixHighBase.res, rv_simp] <;> rfl
    have ft : Frame u t (fun _ => False) := by
      intro A _ _; simp [t, prefixHighRes, prefixHighBase.res, rv_simp]
    refine ⟨4,t,es.trans ec,by omega,?_,?_,?_,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
    · simp [t, prefixHighRes, prefixHighBase.res, rv_simp, pcOf, ofNat_add_ofNat] <;> congr 1 <;> omega
    · simp only [T3.TopDualHalf.select,T3.TopDualHalf.selectPair,if_neg hg]
      simpa [t,u,prefixHighRes,prefixHighBase.res,prefixHeadRes,prefixHeadBase.res,rv_simp] using hm2
    · simp only [T3.TopDualHalf.select,T3.TopDualHalf.selectPair,if_neg hg]
      simpa [t,u,prefixHighRes,prefixHighBase.res,prefixHeadRes,prefixHeadBase.res,rv_simp] using hm3


end SigGolfCandidate.T3M.Verify.Nonbinary
end


section
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
theorem prefix_run (a : Nat) (ha : a ∈ aVals) (pc : Word) :
    symRun { noAlias := true } (prefixTailWordsOf a) pc 200 = some (prefixRes a) := by
  simp only [aVals, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem tail_field (v : Digest) : (v.extractLsb' 64 64 >>> 58) = BitVec.ofNat 64 (v.toNat / 2 ^ 122) := by
  apply BitVec.eq_of_toNat_eq
  have hv := v.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  omega
def prefixTarget (v : Digest) : Word := BitVec.ofNat 64 (4096 * (v.toNat % 128) + 1168)
theorem prefix_tail_spec (s : MachineState) (v : Digest) (a d p : Nat) (ha : a ∈ aVals)
    (hpc : s.pc = pcOf p) (hcode : CodeAt Verify.image (pcOf p) (prefixTailWordsOf a))
    (h12 : s.getReg .x12 = BitVec.ofNat 64 d) (hd : d % 8 = 0 ∧ 0x1000 ≤ d ∧ d + 16 ≤ 0x7000)
    (h0 : s.getReg .x16 = v.extractLsb' 0 64) (h1 : s.getReg .x17 = v.extractLsb' 64 64) (hra : s.getReg .x9 = BitVec.ofNat 64 TOPB9)
    (hmask : s.getMem 0xffbff8#64 = 520192#64) (h4 : s.getReg .x4 = 24592#64) (h10 : s.getReg .x10 = BitVec.ofNat 64 a) :
    ∃ t, Steps Verify.image s 6 6 t ∧ t.pc = prefixTarget v ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧ t.getReg .x17 = v.extractLsb' 64 64 ∧
      t.getReg .x29 = BitVec.ofNat 64 (v.toNat / 2 ^ 122) ∧
      t.getReg .x8 = 11808#64 ∧ t.getReg .x6 = 520192#64 ∧
      RegsExcept s t [.x16,.x17,.x29,.x6,.x8,.x14] ∧
      Frame s t (fun A => A = 25064) := by
  have hm : s.getMem (s.getReg .x9 + 232#64) = 520192#64 := by
    rw [hra]; exact hmask
  have hobl : ∀ o ∈ (prefixRes a).st.obl, o.holds s := by
    intro o ho
    simp [prefixRes, prefixRegs, prefixBase.res] at ho
    rcases ho with rfl
    all_goals simp [Oblig.holds, rv_simp, accessValid_iff, MEMORY_BYTES, hra, h12, h4, TOPB9]
    all_goals omega
  have hal : 13600 ≤ a ∧ a ≤ 13856 := by
    simp only [aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  refine ⟨_, symRun_sound (prefix_run a ha (pcOf p)) hcode s hpc ((Oblig.all_iff _ _).mpr hobl),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, prefixRes, prefixRegs, prefixBase.res, E.eval, BinOp.eval, h0, hm]
    have e1 : (12#64 : Word).toNat % 64 = (BitVec.ofNat 64 12).toNat := by decide +kernel
    have e2 : (18446744073709551614#64 : Word) = ~~~1#64 := by decide +kernel
    have hx : (v.extractLsb' 0 64).toNat % 128 = v.toNat % 128 := by
      simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
      exact Nat.mod_mod_of_dvd _ (show 128 ∣ 2 ^ 64 by decide +kernel)
    have e3 : (1168#64 : Word) = BitVec.ofNat 64 (1168) := by norm_num
    rw [e1, e2, e3, SigGolfCandidate.T3M.Nonbinary.prologue_value, prefixTarget, hx]
  · simp only [Result.toState_getReg, prefixRes, prefixRegs, prefixBase.res, RegFile.get, RegFile.set, E.eval, BinOp.eval, h0]
  · simp only [Result.toState_getReg, prefixRes, prefixRegs, prefixBase.res, RegFile.get, RegFile.set, E.eval, BinOp.eval, h1]
  · simp only [Result.toState_getReg, prefixRes, prefixRegs, prefixBase.res, RegFile.get, RegFile.set, E.eval, BinOp.eval, h1]
    exact tail_field v
  · simp only [Result.toState_getReg, prefixRes, prefixRegs, RegFile.get, RegFile.set, E.eval, BinOp.eval, h10]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · simp only [Result.toState_getReg, prefixRes, prefixRegs, prefixBase.res, RegFile.get, RegFile.set, E.eval, BinOp.eval, hm]
  · intro r hr; cases r <;> simp at hr <;> simp [prefixRes, prefixRegs, prefixBase.res, rv_simp] <;> rfl
  · intro A hA hne
    have hn : BitVec.ofNat 64 A ≠ 25064#64 := by
      intro he
      have he' := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at he'
      omega
    simp [prefixRes, prefixRegs, prefixBase.res, rv_simp, h4, memEval, Addr.eval, hn]
theorem testBit_topMask (i : Nat) : (2 ^ 119 - 1 : Nat).testBit i = decide (i < 119) := by
  rw [Nat.testBit_two_pow_sub_one]
theorem flip_getLsbD (v : Digest) (i : Nat) (hi : i < 128) :
    (T3.topFlip v).getLsbD i = (v.getLsbD i ^^ decide (i < 119)) := by
  unfold T3.topFlip T3.topMask
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_ofNat, testBit_topMask]
  simp [hi]
theorem flip_lo (v : Digest) : ~~~((T3.topFlip v).extractLsb' 0 64) = v.extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_not, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', flip_getLsbD v _ (by omega)]
  simp [hi, show i < 119 by omega]
theorem flip_hi (v : Digest) :
    ~~~((T3.topFlip v).extractLsb' 64 64) ^^^ SigGolfCandidate.T3M.Nonbinary.hiMask = v.extractLsb' 64 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_not, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb',
    flip_getLsbD v _ (by omega)]
  unfold SigGolfCandidate.T3M.Nonbinary.hiMask
  rw [BitVec.getLsbD_ofNat, show (2 : Nat) ^ 64 - 2 ^ 55 = 2 ^ 55 * (2 ^ 9 - 1) by norm_num, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one]
  by_cases h : i < 55
  · simp [hi, h, show 64 + i < 119 by omega, show ¬ 55 ≤ i by omega]
  · simp [hi, h, show ¬ 64 + i < 119 by omega, show i - 55 < 9 by omega, show 55 ≤ i by omega]
theorem flip_toNat (v : Digest) : (T3.topFlip v).toNat = v.toNat ^^^ (2 ^ 119 - 1) := by
  unfold T3.topFlip T3.topMask
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)]
theorem flip_tail (v : Digest) : (T3.topFlip v).toNat / 2 ^ 122 = v.toNat / 2 ^ 122 := by
  rw [flip_toNat]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor, testBit_topMask]
  simp [show ¬ (j + 122 < 119) by omega]
theorem flip_low7 (v : Digest) : (T3.topFlip v).toNat % 128 = 127 - v.toNat % 128 := by
  rw [flip_toNat, show (v.toNat ^^^ (2 ^ 119 - 1)) % 128 = (v.toNat ^^^ (2 ^ 119 - 1)) % 2 ^ 7 from rfl,
    show v.toNat % 128 = v.toNat % 2 ^ 7 from rfl, Nat.xor_mod_two_pow,
    show (2 ^ 119 - 1) % 2 ^ 7 = 127 by norm_num]
  have hl := Nat.mod_lt v.toNat (show 0 < 2 ^ 7 by decide +kernel)
  generalize v.toNat % 2 ^ 7 = y at hl ⊢
  interval_cases y <;> rfl
theorem prefixTarget_flip (v : Digest) :
    prefixTarget v = BitVec.ofNat 64 (4096 * (127 - (T3.topFlip v).toNat % 128) + 1168) := by
  unfold prefixTarget
  rw [flip_low7]
  congr 2
  have := Nat.mod_lt v.toNat (show 0 < 128 by decide +kernel)
  omega
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
def topEntryRegs : List Reg := [.x16,.x17,.x29,.x6,.x8,.x14]
structure TopEntry (u : MachineState) (v : Digest) (p : Nat) (s : MachineState) : Prop where
  pc : s.pc = Nonbinary.prefixTarget v
  ra : s.getReg .x9 = BitVec.ofNat 64 TOPB9
  lo : s.getReg .x16 = v.extractLsb' 0 64
  hi : s.getReg .x17 = v.extractLsb' 64 64
  tail : s.getReg .x29 = BitVec.ofNat 64 (v.toNat / 2 ^ 122)
  s3 : s.getReg .x8 = 11808#64
  mask : s.getReg .x6 = 520192#64
  table : s.getReg .x2 = 0x7fc00#64
  regs : RegsExcept u s topEntryRegs
  frame : Frame u s (fun A => A = 25064)
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
      Nonbinary.prefixHead, Nonbinary.prefixHigh, Nonbinary.prefixLow, Nonbinary.prefixTailWordsOf,
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
theorem topTransition (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : BC.EncPre w pk index 0 c t) (a : BitVec 256) :
    ∃ n s, Steps image (writeHash t a) n n s ∧ n ≤ 10 ∧
      TopEntry (writeHash t a) (T3.TopDualHalf.select a) (trPc 0 c) s := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 13600 ≤ topRowA c ∧ topRowA c ≤ 13856 ∧ topRowA c % 16 = 0 := by
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
  have h4 : (writeHash t a).getReg .x4 = 24592#64 :=
    hk (.x4, 24592#64) (by simp [BC.bK, T3M.bK, layK, bufferBias])
  have hmask : (writeHash t a).getMem 0xffbff8#64 = 520192#64 := hD.mask
  have hhi := DigAt.writeHash_hi t a d h12 (by omega)
  obtain ⟨n,u,eu,hn,pu,lu,hu,ru,fu⟩ := Verify.Nonbinary.prefix_select_spec
    (writeHash t a) a d (trPc 0 c + 6) hpc
    (by simpa [Nonbinary.prefixHead] using (prefix_sub_at c hc' [] Nonbinary.prefixHead
      (Nonbinary.prefixLow ++ Nonbinary.prefixHigh ++ Nonbinary.prefixTailWordsOf (topRowA c))
      (by simp [Nonbinary.prefixWordsOf,List.append_assoc])))
    (by simpa [Nonbinary.prefixHead,Nat.add_assoc] using (prefix_sub_at c hc' Nonbinary.prefixHead
      Nonbinary.prefixLow (Nonbinary.prefixHigh ++ Nonbinary.prefixTailWordsOf (topRowA c))
      (by simp [Nonbinary.prefixWordsOf,List.append_assoc])))
    (by simpa [Nonbinary.prefixHead,Nonbinary.prefixLow,Nat.add_assoc] using (prefix_sub_at c hc'
      (Nonbinary.prefixHead ++ Nonbinary.prefixLow) Nonbinary.prefixHigh
      (Nonbinary.prefixTailWordsOf (topRowA c)) (by simp [Nonbinary.prefixWordsOf,List.append_assoc])))
    h12s hdA hv hhi
  obtain ⟨z, ez, pz, lo, hi, tl, s3, mask, rz, fz⟩ :=
    Verify.Nonbinary.prefix_tail_spec u (T3.TopDualHalf.select a) (topRowA c) d (trPc 0 c + 12) ha
      (by simpa [Nat.add_assoc] using pu)
      (by simpa [Nonbinary.prefixHead,Nonbinary.prefixLow,Nonbinary.prefixHigh,Nat.add_assoc] using
        (prefix_sub_at c hc' (Nonbinary.prefixHead ++ Nonbinary.prefixLow ++ Nonbinary.prefixHigh)
          (Nonbinary.prefixTailWordsOf (topRowA c)) [] (by simp [Nonbinary.prefixWordsOf,List.append_assoc])))
      ((ru.get (by decide)).trans h12s) (by omega) lu hu
      ((ru.get (by decide)).trans hra)
      (by rw [fu.get (by decide) (by simp)]; exact hmask)
      ((ru.get (by decide)).trans h4) ((ru.get (by decide)).trans h10)
  refine ⟨n+6,z,eu.trans ez,by omega,⟨pz,?_,lo,hi,tl,s3,mask,?_,?_,?_⟩⟩
  · rw [rz.get (by decide),ru.get (by decide),hra]
  · rw [rz.get (by decide),ru.get (by decide),h15]
  · exact (ru.trans rz).mono (by simp [topEntryRegs])
  · exact (fu.trans fz).mono (by simp)
theorem topEntry_encoded {u s : MachineState} {v : Digest} {p : Nat} (he : TopEntry u v p s) :
    Nonbinary.NCtx.Encoded (T3.topFlip v) s :=
  ⟨by rw [he.lo, Verify.Nonbinary.flip_lo], by rw [he.hi, Verify.Nonbinary.flip_hi],
    by rw [he.tail, Verify.Nonbinary.flip_tail], he.mask, he.table⟩
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
def nctxOf (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) : NCtx :=
  ⟨w, (route index 0).2, (route index 0).1, 11808, coreDigit 0 v, p + 8⟩
theorem nctx_ok (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (c : Nat) (hidx : index < 2 ^ 31) :
    (nctxOf w index v (trPc 0 c)).ok := by
  have hp := trPc_lt 0 c
  have ht : (route index 0).2 = 0 := by rw [route_snd]; exact Nat.div_eq_of_lt hidx
  exact ⟨ht, leaf_lt index 0, by norm_num [nctxOf], by norm_num [nctxOf], by norm_num [nctxOf], by dsimp [nctxOf]; omega⟩
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
    (he : TopEntry (writeHash t a) (T3.TopDualHalf.select a) (trPc 0 c) s) :
    KnownOK (nctxOf w index (T3.TopDualHalf.select a) (trPc 0 c)).known s := by
  have hprefix : s.getReg .x28 =
      BitVec.ofNat 64 ((nctxOf w index (T3.TopDualHalf.select a) (trPc 0 c)).prefix + 385) := by
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
    (he : TopEntry (writeHash t a) (T3.TopDualHalf.select a) (trPc 0 c) s) :
    Verify.Orig w (fun o => 8256 ≤ o ∧ o < layerEnd 0) s := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 13600 ≤ topRowA c ∧ topRowA c ≤ 13856 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d, h12, hd⟩ := ht.dst (by decide +kernel)
  change (d + 16 = topRowA c ∧ WIT + BC.layerEnd 0 + 16 ≤ topRowA c) ∨ d = topRowA c + 48 at hd
  rw [show BC.layerEnd 0 = 12384 from rfl] at hd
  have ho := Orig_writeHash ht.orig a d h12 (by omega)
  have hu : Verify.Orig w (fun o => 8256 ≤ o ∧ o < layerEnd 0) (writeHash t a) :=
    fun j hj hp => ho j hj ⟨hp, Or.inl (by
      have hp2 := hp.2
      have hle : layerEnd 0 = 12384 := rfl
      rw [hle] at hp2
      unfold WIT at *; omega)⟩
  exact hu.frame (fun j hj hp => he.frame.get (by unfold WIT WX at *; omega) (by norm_num [WIT, layerEnd] at *; omega))
theorem topEntry_bufferOrig (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t s : MachineState) (a : BitVec 256)
    (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopDualHalf.select a) (trPc 0 c) s) :
    Verify.Orig w (fun o => BC.bufferStart 0 ≤ o ∧ o < 24800) s := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 13600 ≤ topRowA c ∧ topRowA c ≤ 13856 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d, h12, hd⟩ := ht.dst (by decide +kernel)
  change (d + 16 = topRowA c ∧ WIT + BC.layerEnd 0 + 16 ≤ topRowA c) ∨ d = topRowA c + 48 at hd
  have ho := Orig_writeHash ht.bufferOrig a d h12 (by omega)
  have hu : Verify.Orig w (fun o => BC.bufferStart 0 ≤ o ∧ o < 24800) (writeHash t a) :=
    fun j hj hp => ho j hj ⟨hp, Or.inr (by
      have hp1 := hp.1
      norm_num [BC.bufferStart] at hp1
      unfold WIT; omega)⟩
  exact hu.frame (fun j hj hp => he.frame.get (by unfold WIT WX at *; omega) (by norm_num [WIT, BC.bufferStart] at *; omega))
theorem nctx_orig (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (s : MachineState)
    (ho : Verify.Orig w (fun o => 8256 ≤ o ∧ o < layerEnd 0) s)
    (hb : Verify.Orig w (fun o => BC.bufferStart 0 ≤ o ∧ o < 24800) s) (hD : DataOK s) :
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
