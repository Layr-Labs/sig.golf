import SigGolfCandidate.T3M.Search.TopUnpack
import SigGolfCandidate.T3.Nonbinary.LowerLayout

section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def setupCode : List (BitVec 32) := [197907,230803,1555,17828371]
def preCode : List (BitVec 32) := [0x7f57e13,3022355,32378419]
def loadCode : List (BitVec 32) := [0x83e4e03]
def postCode : List (BitVec 32) := [29754931,7689491,60136979,29713715,7722387,0xfffa0a13,0xfc0a1ce3]
def tailCode : List (BitVec 32) := [0x757e13,0xffae0e13,1981971,29754931,0x355513,0x757e13,0xffae0e13,1981971,29754931,0x355513,0xffa50e13,1981971,29754931,9846291,0xa0e1e63]
def okCode : List (BitVec 32) := [2579,0xf11ff06f]
def h0Code : List (BitVec 32) := [0x960410e3]
def luiCode : List (BitVec 32) := [0xffff37]
/-- R6 expand (EXP image swap): `b + 425 = 779` is `j 354` (top counter exhaustion rejects). -/
def luiCode354 : List (BitVec 32) := [0x95dff06f]
def luiCodeB (b : Nat) : List (BitVec 32) := if b = 354 then luiCode354 else luiCode
def flagCode : List (BitVec 32) := [662654467]
def beqCode : List (BitVec 32) := [0x940e0ae3]
def ld1Code : List (BitVec 32) := [663696131]
def ld2Code : List (BitVec 32) := [672084867]
def dumCode354 : List (BitVec 32) := [0x8100c93,2579,0xeedff06f]
/-- R6 sign exhaustion tail: `li t3, 1` (d51 of the R6 dummy word), `j 1758` (unpacker), dead `j b+363`. -/
def dumCode543 : List (BitVec 32) := [0x100e13,0x4410006f,0xeedff06f]
def dumCode (b : Nat) : List (BitVec 32) := if b = 354 then dumCode354 else dumCode543
def alignCode : List (BitVec 32) := [1281555,66985491,29573939,1282963,2347923]
def cfLayout (b : Nat) : Rv.Layout := [(0,setupCode),(4,preCode),(7,loadCode),(8,postCode),(15,tailCode),(30,okCode),(32,h0Code),
  (33,luiCodeB b),(34,flagCode),(35,beqCode),(36,ld1Code),(37,ld2Code),(38,dumCode b),(41,alignCode)]
theorem cfLayout_ok {b : Nat} (hb : b = 354 ∨ b = 543) : layoutOk 0 (cfLayout b) = true := by
  rcases hb with rfl | rfl <;> decide +kernel
theorem cfLayout_code {b : Nat} (hb : b = 354 ∨ b = 543) : topSeg392 b = layoutCode (cfLayout b) := by
  rcases hb with rfl | rfl <;> decide +kernel
theorem code_cf {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (i o : Nat) (seg : List (BitVec 32))
    (h : (cfLayout b)[i]? = some (o, seg)) : CodeAt image (pcOf (b + 392 + o)) seg := by
  have hc := codeAt_top392 hK
  rw [cfLayout_code hK.2.1] at hc
  exact codeAt_sublayout hc (cfLayout_ok hK.2.1) (i := i) (o := o) (seg := seg) h
theorem code_h0 {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 424)) h0Code := by
  simpa [Nat.add_assoc] using code_cf hK 6 32 h0Code (by rfl)
theorem code_luiB {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 425)) (luiCodeB b) := by
  simpa [Nat.add_assoc] using code_cf hK 7 33 (luiCodeB b) (by rfl)
theorem code_lui {image : Image} {rewardCondition : Prop} (hK : KernAt image 543 rewardCondition) : CodeAt image (pcOf (543 + 425)) luiCode :=
  code_luiB hK
theorem code_lui354 {image : Image} {rewardCondition : Prop} (hK : KernAt image 354 rewardCondition) : CodeAt image (pcOf (354 + 425)) luiCode354 :=
  code_luiB hK
theorem code_flag {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 426)) flagCode := by
  simpa [Nat.add_assoc] using code_cf hK 8 34 flagCode (by rfl)
theorem code_beq {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 427)) beqCode := by
  simpa [Nat.add_assoc] using code_cf hK 9 35 beqCode (by rfl)
theorem code_align {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 433)) alignCode := by
  simpa [Nat.add_assoc] using code_cf hK 13 41 alignCode (by rfl)
sym_block ch354 := symRun {noAlias:=true} h0Code (pcOf (354+424)) 200
sym_block ch543 := symRun {noAlias:=true} h0Code (pcOf (543+424)) 200
def h0End (b : Nat) : E := rebase ch354.res.pc (pcOf (b+0)) (pcOf (b+425))
theorem run_h0 {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} h0Code (pcOf (b+424)) 200 =
      some ⟨ch354.res.st,h0End b,ch354.res.stop,ch354.res.steps,ch354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact ch354.trans (congrArg some (by kernel_rfl))
  · exact ch543.trans (congrArg some (by kernel_rfl))
sym_block cl543 := symRun {noAlias:=true} luiCode (pcOf (543+425)) 200
sym_block cj354 := symRun {noAlias:=true} luiCode354 (pcOf (354+425)) 200
sym_block cb354 := symRun {noAlias:=true} beqCode (pcOf (354+427)) 200
sym_block cb543 := symRun {noAlias:=true} beqCode (pcOf (543+427)) 200
def beqEnd (b : Nat) : E := rebase cb354.res.pc (pcOf (b+0)) (pcOf (b+428))
theorem run_beq {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} beqCode (pcOf (b+427)) 200 =
      some ⟨cb354.res.st,beqEnd b,cb354.res.stop,cb354.res.steps,cb354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact cb354.trans (congrArg some (by kernel_rfl))
  · exact cb543.trans (congrArg some (by kernel_rfl))
end SigGolfCandidate.T3M.Search.Credit
end
section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
variable {image : Image} {b : Nat}
theorem lui_spec {rewardCondition : Prop} (hK : KernAt image 543 rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (543 + 425)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (543 + 426) ∧ t.getReg .x30 = BitVec.ofNat 64 TOP_DATA ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound cl543 (code_lui hK) s hpc (by simp [cl543.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [cl543.res, rv_simp, TOP_DATA]
  · intro r hr; simp at hr; cases r <;> simp_all [cl543.res, rv_simp] <;> rfl
  · intro A _ _; simp [cl543.res, rv_simp]
/-- R6 expand: the top exhaustion word `354 + 425` is `j 354` (reject). -/
theorem jrej354_spec {rewardCondition : Prop} (hK : KernAt image 354 rewardCondition) (s : MachineState)
    (hpc : s.pc = pcOf (354 + 425)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (354 + 0) ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound cj354 (code_lui354 hK) s hpc (by simp [cj354.res, rv_simp]), ?_, ?_, ?_⟩
  · rfl
  · intro r hr; cases r <;> simp_all [cj354.res, rv_simp] <;> rfl
  · intro A _ _; simp [cj354.res, rv_simp]
theorem h0_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (b + 424)) (lay : Nat)
    (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if lay = 0 then pcOf (b + 425) else pcOf (b + 0)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_h0 hK.2.1) (code_h0 hK) s hpc (by simp [ch354.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, h0End, rebase, ch354.res, E.eval, CmpOp.eval, h8]
    by_cases h : lay = 0
    · subst h; simp
    · have h' : BitVec.ofNat 64 lay ≠ 0#64 := by rw [ne_eq, ofNat_eq_iff]; omega
      simp [h', h]
  · intro r hr; cases r <;> simp_all [ch354.res, rv_simp] <;> rfl
  · intro A _ _; simp [ch354.res, rv_simp]
theorem beq_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (b + 427)) (f : Nat)
    (hf : f < 256) (h28 : s.getReg .x28 = BitVec.ofNat 64 f) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if f = 0 then pcOf (b + 0) else pcOf (b + 428)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_beq hK.2.1) (code_beq hK) s hpc (by simp [cb354.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, beqEnd, rebase, cb354.res, E.eval, CmpOp.eval, h28]
    by_cases h : f = 0
    · subst h; simp
    · have : (BitVec.ofNat 64 f == 0#64) = false := by
        rw [beq_eq_false_iff_ne, ne_eq, ofNat_eq_iff]; omega
      simp [this, h]
  · intro r hr; cases r <;> simp_all [cb354.res, rv_simp] <;> rfl
  · intro A _ _; simp [cb354.res, rv_simp]
end SigGolfCandidate.T3M.Search.Credit
end
section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
variable {image : Image} {b : Nat}
theorem flag_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (b + 426))
    (h30 : s.getReg .x30 = BitVec.ofNat 64 TOP_DATA) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 427) ∧
      t.getReg .x28 = (s.getByte (BitVec.ofNat 64 (TOP_DATA + 631))).zeroExtend 64 ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have he : signExtend12 (631 : BitVec 12) = (631 : Word) := rfl
  have ha : s.getReg .x30 + signExtend12 631 = BitVec.ofNat 64 (TOP_DATA + 631) := by
    rw [h30, he]; exact ofNat_add_ofNat _ 631
  have hv : accessValid (s.getReg .x30 + signExtend12 631) 1 = true := by
    rw [ha]
    simp only [accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt (show TOP_DATA + 631 < 2 ^ 64 by unfold TOP_DATA; omega),
      Nat.mod_one, and_true, true_and]
    unfold TOP_DATA; omega
  have hd : decodeInstruction (662654467 : BitVec 32) = some (.base (.LBU .x28 .x30 631)) := rfl
  have hs := steps_lbu (code_flag hK) hpc hd hv
  rw [ha] at hs
  refine ⟨_, hs, ?_, ?_, ?_, ?_⟩
  · change s.pc + 4 = _; rw [hpc, pcOf_add4]
  · change (s.setReg .x28 _).getReg .x28 = _
    exact MachineState.getReg_setReg_eq (by decide : Reg.x28 ≠ Reg.x0)
  · intro q hq; simp only [List.mem_singleton] at hq
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hq)
  · intro A _ _; simp [MachineState.setReg, MachineState.setPC, MachineState.getMem]
end SigGolfCandidate.T3M.Search.Credit
end
section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
variable {image : Image} {b : Nat}
end SigGolfCandidate.T3M.Search.Credit
end
section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
variable {image : Image} {b : Nat}
end SigGolfCandidate.T3M.Search.Credit
end
section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
variable {image : Image} {b : Nat}
theorem zext_ofNat8 (c : Nat) (hc : c < 256) : (BitVec.ofNat 8 c).zeroExtend 64 = BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
end SigGolfCandidate.T3M.Search.Credit
end
section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option linter.unusedSimpArgs false
variable {image : Image} {b : Nat}
sym_block ca354 := symRun {noAlias:=true} alignCode (pcOf (354+433)) 200
sym_block ca543 := symRun {noAlias:=true} alignCode (pcOf (543+433)) 200
theorem run_align {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} alignCode (pcOf (b+433)) 200 =
      some ⟨ca354.res.st,.c (pcOf (b+438)),ca354.res.stop,ca354.res.steps,ca354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact ca354.trans (congrArg some (by kernel_rfl))
  · exact ca543.trans (congrArg some (by kernel_rfl))
theorem getLsbD_add_one_zero (x : BitVec 64) : (x + 1#64).getLsbD 0 = !x.getLsbD 0 := by
  simp only [BitVec.getLsbD, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.testBit_zero, Nat.testBit_zero]
  have h : (x.toNat + 1 % 2 ^ 64) % 2 ^ 64 % 2 = (x.toNat + 1) % 2 := by
    rw [show 1 % 2 ^ 64 = 1 from rfl, Nat.mod_mod_of_dvd _ (by norm_num)]
  rw [h]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h0 | h0 <;> simp [Nat.add_mod, h0]
theorem align_lo (v : Digest) (hv : T3.lowerSpare v) :
    v.extractLsb' 0 64 ^^^ (v.extractLsb' 64 64 + 1#64) <<< 63 =
      (BitVec.ofNat 128 (T3.lowerWord v)).extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, T3.testBit_lowerWord]
  simp only [hj, decide_true, Bool.true_and, show j < 128 from by omega]
  by_cases h63 : j = 63
  · subst h63
    have hb := getLsbD_add_one_zero (v.extractLsb' 64 64)
    simp only [Nat.sub_self] at hb ⊢
    rw [hb, BitVec.getLsbD_extractLsb']
    have h63 : v.toNat.testBit 63 = true := by
      unfold T3.lowerSpare at hv
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two, hv.1]
      rfl
    simp [BitVec.getElem_eq_testBit_toNat, h63]
  · have hlt : j < 63 := by omega
    simp [hlt, BitVec.getLsbD]
    intro _; omega
theorem align_hi (v : Digest) :
    v.extractLsb' 64 64 <<< 1 >>> 2 =
      (BitVec.ofNat 128 (T3.lowerWord v)).extractLsb' 64 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, T3.testBit_lowerWord]
  simp only [hj, decide_true, Bool.true_and, show 64 + j < 128 from by omega, show ¬ 64 + j < 63 from by omega,
    if_false]
  by_cases h62 : j < 62
  · simp [show 2 + j < 64 from by omega, show ¬ 2 + j < 1 from by omega, show 64 + j < 126 from by omega,
      BitVec.getLsbD, show 1 + j < 64 from by omega, show 64 + (1 + j) = 64 + j + 1 from by omega]
  · simp [show ¬ 2 + j < 64 from by omega, show ¬ 64 + j < 126 from by omega]
theorem align_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (b + 433)) (v : Digest)
    (hv : T3.lowerSpare v) (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pcOf (b + 438) ∧
      t.getReg .x6 = (BitVec.ofNat 128 (T3.lowerWord v)).extractLsb' 0 64 ∧
      t.getReg .x7 = (BitVec.ofNat 128 (T3.lowerWord v)).extractLsb' 64 64 ∧
      RegsExcept s t [.x6, .x7, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_align hK.2.1) (code_align hK) s hpc (by simp [ca354.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [Result.toState_getReg, ca354.res]
    simp only [rv_simp, h6, h7]
    rw [← align_lo v hv]
    rfl
  · simp only [Result.toState_getReg, ca354.res]
    simp only [rv_simp, h7]
    rw [← align_hi v]
    rfl
  · intro r hr; simp at hr; cases r <;> simp_all [ca354.res, rv_simp] <;> rfl
  · intro A _ _; simp [ca354.res, rv_simp]
end SigGolfCandidate.T3M.Search.Credit
end
section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
variable {image : Image}
/-- Campaign R6 (sign, b = 543): counter exhaustion with only the choice flag byte known (`CfFlagOK`; the cf
block's dummy word is the R6 one). Same machine path as `exhaust_fail`. -/
theorem exhaust_failF {rewardCondition : Prop} (hK : KernAt image 543 rewardCondition) (s : MachineState)
    (hpc : s.pc = pcOf (543 + 424)) (lay : Nat) (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay)
    (flag : Nat) (hf : flag < 256) (hcf : CfFlagOK flag s) (hfl : lay ≠ 0 ∨ flag = 0) :
    ∃ n t, n ≤ 4 ∧ Steps image s n n t ∧ t.pc = pcOf (543 + 0) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ := h0_spec hK s hpc lay hl h8
  by_cases hz : lay = 0
  · rw [if_pos hz] at p0
    have hf0 : flag = 0 := by rcases hfl with h | h; exact absurd hz h; exact h
    obtain ⟨t1, s1, p1, g30, r1, f1⟩ := lui_spec hK t0 p0
    obtain ⟨t2, s2, p2, g28, r2, f2⟩ := flag_spec hK t1 p1 g30
    have hcf2 : CfFlagOK flag t1 := hcf.frame (W := fun _ => False) ((f0.trans f1).mono (by simp))
      (by intro j _ _ h; exact h)
    have hb : (t1.getByte (BitVec.ofNat 64 (TOP_DATA + 631))).zeroExtend 64 = BitVec.ofNat 64 flag := by
      rw [hcf2]; exact zext_ofNat8 flag hf
    rw [hb] at g28
    obtain ⟨t3, s3, p3, r3, f3⟩ := beq_spec hK t2 p2 flag hf g28
    rw [if_pos hf0] at p3
    refine ⟨4, t3, le_rfl, (s0.trans (s1.trans (s2.trans s3))).of_eq (by norm_num) (by norm_num), p3, ?_, ?_⟩
    · exact (((r0.trans r1).trans r2).trans r3).mono (by decide)
    · exact (((f0.trans f1).trans f2).trans f3).mono (by simp)
  · rw [if_neg hz] at p0
    exact ⟨1, t0, by omega, s0, p0, r0.mono (by decide), f0⟩
end SigGolfCandidate.T3M.Search.Credit
end
