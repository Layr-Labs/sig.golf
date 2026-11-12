import SigGolfCandidate.ExpandLabel
import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge045
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge059
import SigGolfCandidate.Merge060
import SigGolfCandidate.Merge070
import SigGolfCandidate.Merge075
import SigGolfCandidate.Merge076.P1
import SigGolfCandidate.Merge076.P2
import SigGolfCandidate.Merge076.P4
import SigGolfCandidate.Merge076.P5
import SigGolfCandidate.Merge076.P6
import SigGolfCandidate.Merge076.P7

set_option debug.skipKernelTC false
set_option linter.all false

-- ==== merged from T3M_Expand_LayerBlocks ====
section

section
namespace SigGolfCandidate.T3M.Expand.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
end SigGolfCandidate.T3M.Expand.BCBlocks
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
section blocks
variable (s : MachineState)
end blocks
end SigGolfCandidate.T3M.Expand
end

namespace SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand.BCBlocks
variable {im : Image} [Code im]
end SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
/-! img-v6 top-node nonce routine (words 43195 .. 43249, hooked at 1139 `jal 43195`; topfold-v6, NOTES V49). -/
variable {im : Image} [Code im]
variable                    [PackedBlocks.Code im]
variable (s : MachineState)
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
variable {im : Image} [Code im] (s : MachineState)
theorem fetch_1072 (hpc : s.pc = pcOf 1072) : fetch im s = some (.base .ECALL) :=
  ((Code.codeAt_1072 (im := im)).fetch s hpc).trans rfl
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace Grind
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (NODE NOUT)
open SigGolfCandidate.T3 (Digest nonceBytes pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.WCT9 (lowerZeroBits lowerNonceCap lowerZeroOk lowerNodeInputN lowerNodeHashN lowerNonceSearch
  lowerNodeAt)
section blocks
variable {im : Image} [Code im] (s : MachineState)

theorem b4b_spec (hpc : s.pc = pcOf 54826) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 60108 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl (Code.codeAt_stub (im := im)) 54826 54827 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound gB4b hc s hpc (by simp [gB4b.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [gB4b.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [gB4b.res, rv_simp] <;> rfl
  · intro A _ _; simp [gB4b.res, rv_simp]

/-! E11 grind tiers (60108..60127): `t4 = b` for heaps 16..31 (1), 8..15 (2), 4..7 (3), 2..3 (4; 3 on layer 1),
heaps `≥ 32` to 54875. -/
theorem tA_spec (hpc : s.pc = pcOf 60108) :
    ∃ t, Steps im s 4 4 t ∧
      t.pc = (if ((s.getReg .x31 &&& 255#64) + 0xffffffffffffff80#64).ult 32#64 = true then pcOf 60112 else pcOf 60127) ∧
      t.getReg .x7 = (s.getReg .x31 &&& 255#64) + 0xffffffffffffff80#64 ∧
      RegsExcept s t [.x7, .x28] ∧ Frame s t (fun _ => False) := by
  have hc := code_slE (Code.codeAt_e11s (im := im)) 60108 60112 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound tA hc s hpc (by simp [tA.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    by_cases hc : ((s.getReg .x31 &&& 255#64) + 0xffffffffffffff80#64).ult 32#64 = true <;>
      simp [tA.res, E.eval, CmpOp.eval, BinOp.eval, hc]
  · simp only [Result.toState_getReg, tA.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [tA.res, rv_simp] <;> rfl
  · intro A _ _; simp [tA.res, rv_simp]

theorem tB_spec (hpc : s.pc = pcOf 60112) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if (s.getReg .x7).ult 16#64 = true then pcOf 60115 else pcOf 60126) ∧
      t.getReg .x29 = 1#64 ∧ RegsExcept s t [.x28, .x29] ∧ Frame s t (fun _ => False) := by
  have hc := code_slE (Code.codeAt_e11s (im := im)) 60112 60115 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound tB hc s hpc (by simp [tB.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    by_cases hc : (s.getReg .x7).ult 16#64 = true <;> simp [tB.res, E.eval, CmpOp.eval, hc]
  · simp only [Result.toState_getReg, tB.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [tB.res, rv_simp] <;> rfl
  · intro A _ _; simp [tB.res, rv_simp]

theorem tC0_spec (hpc : s.pc = pcOf 60115) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 60968 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hc := code_slE (Code.codeAt_e11s (im := im)) 60115 60116 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound tC0 hc s hpc (by simp [tC0.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [tC0.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [tC0.res, rv_simp] <;> rfl
  · intro A _ _; simp [tC0.res, rv_simp]
theorem tC1_spec (hpc : s.pc = pcOf 60968) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if (s.getReg .x7).ult 8#64 = true then pcOf 60118 else pcOf 60971) ∧
      t.getReg .x29 = 2#64 ∧ RegsExcept s t [.x28, .x29] ∧ Frame s t (fun _ => False) := by
  have hc := code_slB (Code.codeAt_brule (im := im)) 60968 60971 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound tC1 hc s hpc (by simp [tC1.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    by_cases hc : (s.getReg .x7).ult 8#64 = true <;> simp [tC1.res, E.eval, CmpOp.eval, hc]
  · simp only [Result.toState_getReg, tC1.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [tC1.res, rv_simp] <;> rfl
  · intro A _ _; simp [tC1.res, rv_simp]
theorem tC2_spec (hpc : s.pc = pcOf 60971) :
    ∃ t, Steps im s 3 3 t ∧ (t.pc = pcOf 60126 ∨ t.pc = pcOf 60974) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have hc := code_slB (Code.codeAt_brule (im := im)) 60971 60974 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound tC2 hc s hpc (by simp [tC2.res, rv_simp]), ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    -- A70Y4 (Ta2 fix2): words 60971/60972 test the Y4 marker (`t6 >> 28 - 1`), as `tE`.
    by_cases hb : (s.getReg .x31 >>> 28) + 18446744073709551615#64 = 0#64 <;>
      simp [tC2.res, E.eval, CmpOp.eval, BinOp.eval, hb]
  · intro r hr; simp at hr; cases r <;> simp_all [tC2.res, rv_simp] <;> rfl
  · intro A _ _; simp [tC2.res, rv_simp]
theorem tC3_spec (hpc : s.pc = pcOf 60974) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 60126 ∧ t.getReg .x29 = 2#64 ∧ RegsExcept s t [.x29] ∧
      Frame s t (fun _ => False) := by
  have hc := code_slB (Code.codeAt_brule (im := im)) 60974 60976 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound tC3 hc s hpc (by simp [tC3.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [tC3.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, tC3.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [tC3.res, rv_simp] <;> rfl
  · intro A _ _; simp [tC3.res, rv_simp]
/-- N7g tier C: `jal 60968`; heaps `< 8` back to 60118, heaps 8..15 to 60126 with `t4 = 2` (4 to 9 steps). -/
theorem tC_spec (hpc : s.pc = pcOf 60115) :
    ∃ t k, Steps im s k k t ∧ ((s.getReg .x7).ult 8#64 = true → k = 4) ∧ k ≤ 9 ∧
      t.pc = (if (s.getReg .x7).ult 8#64 = true then pcOf 60118 else pcOf 60126) ∧
      t.getReg .x29 = 2#64 ∧ RegsExcept s t [.x28, .x29] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ := tC0_spec (im := im) s hpc
  obtain ⟨t1, s1, p1, x1, r1, f1⟩ := tC1_spec (im := im) t0 p0
  have e7 : t0.getReg .x7 = s.getReg .x7 := r0.get (by decide)
  rw [e7] at p1
  by_cases h8 : (s.getReg .x7).ult 8#64 = true
  · rw [if_pos h8] at p1
    exact ⟨t1, _, s0.trans s1, fun _ => rfl, by omega, by rw [p1, if_pos h8], x1, (r0.trans r1).mono (by decide),
      (f0.trans f1).mono (fun _ _ h => by rcases h with h | h <;> exact h)⟩
  rw [if_neg h8] at p1
  obtain ⟨t2, s2, p2, r2, f2⟩ := tC2_spec (im := im) t1 p1
  have x2 : t2.getReg .x29 = 2#64 := by rw [r2.get (by decide)]; exact x1
  rcases p2 with p2 | p2
  · exact ⟨t2, _, (s0.trans s1).trans s2, fun h => absurd h h8, by omega, by rw [p2, if_neg h8], x2,
      ((r0.trans r1).trans r2).mono (by decide),
      ((f0.trans f1).trans f2).mono (fun _ _ h => by rcases h with (h | h) | h <;> exact h)⟩
  obtain ⟨t3, s3, p3, x3, r3, f3⟩ := tC3_spec (im := im) t2 p2
  exact ⟨t3, _, ((s0.trans s1).trans s2).trans s3, fun h => absurd h h8, by omega, by rw [p3, if_neg h8], x3,
    (((r0.trans r1).trans r2).trans r3).mono (by decide),
    (((f0.trans f1).trans f2).trans f3).mono (fun _ _ h => by rcases h with ((h | h) | h) | h <;> exact h)⟩

theorem tD_spec (hpc : s.pc = pcOf 60118) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if (s.getReg .x7).ult 4#64 = true then pcOf 60121 else pcOf 60126) ∧
      t.getReg .x29 = 3#64 ∧ RegsExcept s t [.x28, .x29] ∧ Frame s t (fun _ => False) := by
  have hc := code_slE (Code.codeAt_e11s (im := im)) 60118 60121 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound tD hc s hpc (by simp [tD.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    by_cases hc : (s.getReg .x7).ult 4#64 = true <;> simp [tD.res, E.eval, CmpOp.eval, hc]
  · simp only [Result.toState_getReg, tD.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [tD.res, rv_simp] <;> rfl
  · intro A _ _; simp [tD.res, rv_simp]

theorem tE_spec (hpc : s.pc = pcOf 60121) :
    ∃ t, Steps im s 4 4 t ∧
      t.pc = (if (s.getReg .x31 >>> 28) + 18446744073709551615#64 = 0#64 then pcOf 60125 else pcOf 60126) ∧
      t.getReg .x29 = 4#64 ∧ RegsExcept s t [.x28, .x29] ∧ Frame s t (fun _ => False) := by
  have hc := code_slE (Code.codeAt_e11s (im := im)) 60121 60125 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound tE hc s hpc (by simp [tE.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    by_cases hc : (s.getReg .x31 >>> 28) + 18446744073709551615#64 = 0#64 <;>
      simp [tE.res, E.eval, CmpOp.eval, BinOp.eval, hc]
  · simp only [Result.toState_getReg, tE.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [tE.res, rv_simp] <;> rfl
  · intro A _ _; simp [tE.res, rv_simp]

theorem tF_spec (hpc : s.pc = pcOf 60125) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 54838 ∧ t.getReg .x29 = 4#64 ∧ RegsExcept s t [.x29] ∧
      Frame s t (fun _ => False) := by
  have hc := code_slE (Code.codeAt_e11s (im := im)) 60125 60127 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound tF hc s hpc (by simp [tF.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [tF.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, tF.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [tF.res, rv_simp] <;> rfl
  · intro A _ _; simp [tF.res, rv_simp]

theorem tJ_spec (hpc : s.pc = pcOf 60126) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 54838 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hc := code_slE (Code.codeAt_e11s (im := im)) 60126 60127 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound tJ hc s hpc (by simp [tJ.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [tJ.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [tJ.res, rv_simp] <;> rfl
  · intro A _ _; simp [tJ.res, rv_simp]

theorem tK_spec (hpc : s.pc = pcOf 60127) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 54875 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hc := code_slE (Code.codeAt_e11s (im := im)) 60127 60128 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound tK hc s hpc (by simp [tK.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [tK.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [tK.res, rv_simp] <;> rfl
  · intro A _ _; simp [tK.res, rv_simp]

theorem l4_spec (hpc : s.pc = pcOf 54855) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 54847 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hcd := code_sl (Code.codeAt_stub (im := im)) 54855 54856 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound gL4 hcd s hpc (by simp [gL4.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [gL4.res, Result.toState_pc, E.eval]
  · intro r _; cases r <;> simp_all [gL4.res, rv_simp] <;> rfl
  · intro A _ _; simp [gL4.res, rv_simp]

theorem pE_spec (hpc : s.pc = pcOf 60140) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 54872 ∧ t.getReg .x30 = s.getReg .x30 + s.getReg .x29 ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  have hc := code_slE (Code.codeAt_e11s (im := im)) 60140 60142 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound pE hc s hpc (by simp [pE.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [pE.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, pE.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [pE.res, rv_simp] <;> rfl
  · intro A _ _; simp [pE.res, rv_simp]

end blocks

/-! U16b grind stub: tweak-word arithmetic. -/

theorem lowTw_lt47 (lay tree heap : Nat) (h1 : 1 ≤ lay) (h3 : lay ≤ 3)
    (ht : tree < 2 ^ T3.hyperW (lay - 1)) (hh : heap < 128) :
    lowTw lay tree heap < 2 ^ 47 := by
  unfold lowTw
  have hW : T3.hyperW (lay - 1) ≤ 25 := by interval_cases lay <;> decide
  have h2 : 2 ^ T3.hyperW (lay - 1) ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) hW
  rw [pow_add]
  have : tree * 2 ^ 16 + 2 ^ 16 ≤ 2 ^ T3.hyperW (lay - 1) * 2 ^ 16 := by
    have := Nat.mul_le_mul_right (2 ^ 16) (Nat.succ_le_of_lt ht); rw [Nat.succ_mul] at this; exact this
  have : 2 ^ T3.hyperW (lay - 1) * 2 ^ 16 ≤ 2 ^ 25 * 2 ^ 16 := Nat.mul_le_mul_right _ h2
  norm_num at * <;> omega
theorem lowTw_dec (lay tree heap : Nat) (h1 : 1 ≤ lay) (h3 : lay ≤ 3)
    (ht : tree < 2 ^ T3.hyperW (lay - 1)) (hh : heap < 128) :
    decW (BitVec.ofNat 64 (lowTw lay tree heap)) = BitVec.ofNat 64 (lay - 1) := by
  have hl := lowTw_lt47 lay tree heap h1 h3 ht hh
  have hl' : lowTw lay tree heap < 2 ^ 64 := lt_of_lt_of_le hl (by norm_num)
  unfold decW
  rw [ofNat_shr _ 35 hl', ofNat_shr _ 41 hl', ofNat_shr _ 47 hl',
    ult0D _ (lt_of_le_of_lt (Nat.div_le_self _ _) hl'), ult0D _ (lt_of_le_of_lt (Nat.div_le_self _ _) hl'),
    Nat.div_eq_of_lt hl]
  interval_cases lay
  · have h12 : T3.hyperW (1 - 1) = 12 := rfl
    rw [h12] at ht
    have : lowTw 1 tree heap < 2 ^ 35 := by unfold lowTw; rw [h12]; omega
    rw [Nat.div_eq_of_lt this, Nat.div_eq_of_lt (lt_of_lt_of_le this (by norm_num))]; rfl
  · have h12 : T3.hyperW (2 - 1) = 19 := rfl
    rw [h12] at ht
    have h35 : lowTw 2 tree heap / 2 ^ 35 = 1 := by
      unfold lowTw; rw [h12]; apply Nat.div_eq_of_lt_le <;> omega
    have h41 : lowTw 2 tree heap / 2 ^ 41 = 0 := by
      unfold lowTw; rw [h12]; apply Nat.div_eq_of_lt; omega
    rw [h35, h41]; rfl
  · have h12 : T3.hyperW (3 - 1) = 25 := rfl
    rw [h12] at ht
    have h35 : 0 < lowTw 3 tree heap / 2 ^ 35 := by
      unfold lowTw; rw [h12]; apply Nat.div_pos <;> omega
    have h41 : lowTw 3 tree heap / 2 ^ 41 = 1 := by
      unfold lowTw; rw [h12]; apply Nat.div_eq_of_lt_le <;> omega
    rw [h41, decide_eq_true h35]; rfl
theorem lowTw_ge (lay tree heap : Nat) (h1 : 1 ≤ lay) (h3 : lay ≤ 3) : 2 ^ 28 ≤ lowTw lay tree heap := by
  have : 2 ^ 28 ≤ 2 ^ (T3.hyperW (lay - 1) + 16) :=
    Nat.pow_le_pow_right (by norm_num) (by have := T3.hyperW_ge (lay := lay - 1) (by omega); omega)
  unfold lowTw; omega
theorem lowTw_hi (lay tree heap : Nat) (h1 : 1 ≤ lay) (h3 : lay ≤ 3)
    (ht : tree < 2 ^ T3.hyperW (lay - 1)) (hh : heap < 128) :
    (BitVec.ofNat 64 (lowTw lay tree heap) >>> 28 = 0#64) = False := by
  have hl := lowTw_lt47 lay tree heap h1 h3 ht hh
  have hg := lowTw_ge lay tree heap h1 h3
  rw [ofNat_shr _ _ (lt_of_lt_of_le hl (by norm_num)), show (0#64 : Word) = BitVec.ofNat 64 0 from rfl,
    ofNat_inj (lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_lt_of_le hl (by norm_num))) (by norm_num)]
  simp only [eq_iff_iff, iff_false]
  intro h
  have := (Nat.div_eq_zero_iff_lt (by norm_num)).1 h
  omega
theorem lowTw_t0 (lay tree heap : Nat) (h1 : 1 ≤ lay) (h3 : lay ≤ 3)
    (ht : tree < 2 ^ T3.hyperW (lay - 1)) (hh : heap < 128) :
    (BitVec.ofNat 64 (lowTw lay tree heap) >>> 28) + 18446744073709551615#64 = 0#64 ↔ lay = 1 := by
  have hl := lowTw_lt47 lay tree heap h1 h3 ht hh
  rw [ofNat_shr _ _ (lt_of_lt_of_le hl (by norm_num)), ofNat_add_ofNat,
    show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ofNat_eq_iff]
  interval_cases lay
  · have h12 : T3.hyperW (1 - 1) = 12 := rfl
    rw [h12] at ht
    have : lowTw 1 tree heap / 2 ^ 28 = 1 := by unfold lowTw; rw [h12]; apply Nat.div_eq_of_lt_le <;> omega
    rw [this]; decide
  · have h12 : T3.hyperW (2 - 1) = 19 := rfl
    rw [h12] at ht
    have hq : 2 ^ 7 ≤ lowTw 2 tree heap / 2 ^ 28 := by
      apply (Nat.le_div_iff_mul_le (by norm_num)).2; unfold lowTw; rw [h12]; omega
    have hq2 : lowTw 2 tree heap / 2 ^ 28 < 2 ^ 47 := lt_of_le_of_lt (Nat.div_le_self _ _) hl
    omega
  · have h12 : T3.hyperW (3 - 1) = 25 := rfl
    rw [h12] at ht
    have hq : 2 ^ 13 ≤ lowTw 3 tree heap / 2 ^ 28 := by
      apply (Nat.le_div_iff_mul_le (by norm_num)).2; unfold lowTw; rw [h12]; omega
    have hq2 : lowTw 3 tree heap / 2 ^ 28 < 2 ^ 47 := lt_of_le_of_lt (Nat.div_le_self _ _) hl
    omega
theorem lowTw_byte1 (lay tree heap : Nat) (h1 : 1 ≤ lay) (h3 : lay ≤ 3)
    (ht : tree < 2 ^ T3.hyperW (lay - 1)) (hh : heap < 128) :
    (BitVec.ofNat 64 (lowTw lay tree heap) >>> 8 &&& 255#64 != 7#64) = false := by
  have hl := lowTw_lt47 lay tree heap h1 h3 ht hh
  have hM : 2 ^ (T3.hyperW (lay - 1) + 16) = 2 ^ T3.hyperW (lay - 1) * 65536 := by
    rw [pow_add]; rfl
  have : BitVec.ofNat 64 (lowTw lay tree heap) >>> 8 &&& 255#64 = 7#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (255#64 : Word).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_of_lt_of_le hl (by norm_num))]
    unfold lowTw; rw [hM]; norm_num; omega
  simp [this]
theorem lowTw_heap (lay tree heap : Nat) (h1 : 1 ≤ lay) (h3 : lay ≤ 3)
    (ht : tree < 2 ^ T3.hyperW (lay - 1)) (hh : heap < 128) :
    (BitVec.ofNat 64 (lowTw lay tree heap) &&& 255#64) + 0xffffffffffffff80#64 = BitVec.ofNat 64 heap := by
  have hl := lowTw_lt47 lay tree heap h1 h3 ht hh
  have hM : 2 ^ (T3.hyperW (lay - 1) + 16) = 2 ^ T3.hyperW (lay - 1) * 65536 := by
    rw [pow_add]; rfl
  have e : (BitVec.ofNat 64 (lowTw lay tree heap) &&& 255#64) = BitVec.ofNat 64 (128 + heap) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (255#64 : Word).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le hl (by norm_num)), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 128 + heap < 2 ^ 64 by omega)]
    unfold lowTw; rw [hM]; norm_num; omega
  rw [e, ofNat_add_ofNat, ofNat_eq_iff]
  omega
theorem lowTw_lt (lay tree heap : Nat) (h1 : 1 ≤ lay) (h3 : lay ≤ 3) (ht : tree < 2 ^ T3.hyperW (lay - 1))
    (hh : heap < 128) : lowTw lay tree heap < 2 ^ 64 :=
  lt_of_lt_of_le (lowTw_lt47 lay tree heap h1 h3 ht hh) (by norm_num)
section cls
variable {im : Image} [Code im]

/-- E11: the tier code (60108..60127) from a lower node word: heaps `≥ 32` go to 54875, the others to 54838 with
`t4 = lowerZeroBits`. -/
theorem tiers_spec (u : MachineState) (hpc : u.pc = pcOf 60108) (lay tree heap : Nat) (h1 : 1 ≤ lay) (h3 : lay ≤ 3)
    (ht : tree < 2 ^ T3.hyperW (lay - 1)) (hh2 : 2 ≤ heap) (hh : heap < 128)
    (h31 : u.getReg .x31 = BitVec.ofNat 64 (lowTw lay tree heap)) :
    ∃ v k, Steps im u k k v ∧ (k ≤ 19 ∨ (lay = 1 ∧ heap < 4 ∧ k ≤ 20)) ∧ v.pc = (if 32 ≤ heap then pcOf 54875 else pcOf 54838) ∧
      v.getReg .x7 = BitVec.ofNat 64 heap ∧
      (heap < 32 → v.getReg .x29 = BitVec.ofNat 64 (ClaudeWCT.WCT9.lowerZeroBits lay heap)) ∧
      RegsExcept u v [.x7, .x28, .x29] ∧ Frame u v (fun _ => False) := by
  obtain ⟨v1, s1, p1, x7, r1, f1⟩ := tA_spec (im := im) u hpc
  rw [h31, lowTw_heap lay tree heap h1 h3 ht hh, ult_ofNat heap 32 (by omega) (by omega)] at p1
  rw [h31, lowTw_heap lay tree heap h1 h3 ht hh] at x7
  have g31 : v1.getReg .x31 = BitVec.ofNat 64 (lowTw lay tree heap) := by rw [r1.get (by decide)]; exact h31
  by_cases h32 : 32 ≤ heap
  · rw [if_neg (by simp; omega)] at p1
    obtain ⟨v2, s2, p2, r2, f2⟩ := tK_spec (im := im) v1 p1
    refine ⟨v2, 5, s1.trans s2, Or.inl (by omega), by rw [p2, if_pos h32], by rw [r2.get (by decide)]; exact x7,
      fun h => absurd h32 (by omega), (r1.trans r2).mono (by decide),
      (f1.trans f2).mono (fun _ _ h => by rcases h with h | h <;> exact h)⟩
  rw [if_pos (by simp; omega)] at p1
  have zb : ∀ v : MachineState, v.getReg .x29 = BitVec.ofNat 64 (ClaudeWCT.WCT9.lowerZeroBits lay heap) →
      (heap < 32 → v.getReg .x29 = BitVec.ofNat 64 (ClaudeWCT.WCT9.lowerZeroBits lay heap)) := fun _ h _ => h
  obtain ⟨v2, s2, p2, x29a, r2, f2⟩ := tB_spec (im := im) v1 p1
  rw [x7, ult_ofNat heap 16 (by omega) (by omega)] at p2
  have g7 : v2.getReg .x7 = BitVec.ofNat 64 heap := by rw [r2.get (by decide)]; exact x7
  by_cases h16 : 16 ≤ heap
  · rw [if_neg (by simp; omega)] at p2
    obtain ⟨v3, s3, p3, r3, f3⟩ := tJ_spec (im := im) v2 p2
    refine ⟨v3, 8, (s1.trans s2).trans s3, Or.inl (by omega), by rw [p3, if_neg h32], by rw [r3.get (by decide)]; exact g7,
      zb _ ?_, ((r1.trans r2).trans r3).mono (by decide),
      ((f1.trans f2).trans f3).mono (fun _ _ h => by rcases h with (h | h) | h <;> exact h)⟩
    rw [r3.get (by decide), x29a]; simp [ClaudeWCT.WCT9.lowerZeroBits, show ¬ heap < 2 by omega, h16, h32,
      show lay ≠ 0 by omega]
  rw [if_pos (by simp; omega)] at p2
  obtain ⟨v3, k3, s3, hk3e, hk3, p3, x29b, r3, f3⟩ := tC_spec (im := im) v2 p2
  rw [g7, ult_ofNat heap 8 (by omega) (by omega)] at p3 hk3e
  have g7' : v3.getReg .x7 = BitVec.ofNat 64 heap := by rw [r3.get (by decide)]; exact g7
  by_cases h8 : 8 ≤ heap
  · rw [if_neg (by simp; omega)] at p3
    obtain ⟨v4, s4, p4, r4, f4⟩ := tJ_spec (im := im) v3 p3
    refine ⟨v4, _, ((s1.trans s2).trans s3).trans s4, Or.inl (by omega), by rw [p4, if_neg h32],
      by rw [r4.get (by decide)]; exact g7', zb _ ?_, (((r1.trans r2).trans r3).trans r4).mono (by decide),
      (((f1.trans f2).trans f3).trans f4).mono (fun _ _ h => by rcases h with ((h | h) | h) | h <;> exact h)⟩
    rw [r4.get (by decide), x29b]; simp [ClaudeWCT.WCT9.lowerZeroBits, show ¬ heap < 2 by omega, h16, h32, h8,
      show lay ≠ 0 by omega]
  have hk3' : k3 = 4 := hk3e (by simp; omega)
  subst hk3'
  rw [if_pos (by simp; omega)] at p3
  obtain ⟨v4, s4, p4, x29c, r4, f4⟩ := tD_spec (im := im) v3 p3
  rw [g7', ult_ofNat heap 4 (by omega) (by omega)] at p4
  have g7'' : v4.getReg .x7 = BitVec.ofNat 64 heap := by rw [r4.get (by decide)]; exact g7'
  by_cases h4 : 4 ≤ heap
  · rw [if_neg (by simp; omega)] at p4
    obtain ⟨v5, s5, p5, r5, f5⟩ := tJ_spec (im := im) v4 p4
    refine ⟨v5, _, (((s1.trans s2).trans s3).trans s4).trans s5, Or.inl (by omega), by rw [p5, if_neg h32],
      by rw [r5.get (by decide)]; exact g7'', zb _ ?_, ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by decide),
      ((((f1.trans f2).trans f3).trans f4).trans f5).mono (fun _ _ h => by
        rcases h with (((h | h) | h) | h) | h <;> exact h)⟩
    rw [r5.get (by decide), x29c]; simp [ClaudeWCT.WCT9.lowerZeroBits, show ¬ heap < 2 by omega, h16, h32, h8, h4,
      show lay ≠ 0 by omega]
  rw [if_pos (by simp; omega)] at p4
  obtain ⟨v5, s5, p5, x29d, r5, f5⟩ := tE_spec (im := im) v4 p4
  have g31' : v4.getReg .x31 = BitVec.ofNat 64 (lowTw lay tree heap) := by
    rw [r4.get (by decide), r3.get (by decide), r2.get (by decide)]; exact g31
  rw [g31'] at p5
  have g7''' : v5.getReg .x7 = BitVec.ofNat 64 heap := by rw [r5.get (by decide)]; exact g7''
  by_cases hl1 : lay = 1
  · subst hl1
    rw [if_pos ((lowTw_t0 1 tree heap le_rfl (by omega) ht hh).2 rfl)] at p5
    obtain ⟨v6, s6, p6, x29e, r6, f6⟩ := tF_spec (im := im) v5 p5
    refine ⟨v6, _, ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6, Or.inr ⟨rfl, by omega, by omega⟩,
      by rw [p6, if_neg h32],
      by rw [r6.get (by decide)]; exact g7''', zb _ ?_,
      (((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).mono (by decide),
      (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).mono (fun _ _ h => by
        rcases h with ((((h | h) | h) | h) | h) | h <;> exact h)⟩
    rw [x29e]; simp [ClaudeWCT.WCT9.lowerZeroBits, show ¬ heap < 2 by omega, h16, h32, h8, h4]
  · rw [if_neg (fun h => hl1 ((lowTw_t0 lay tree heap h1 h3 ht hh).1 h))] at p5
    obtain ⟨v6, s6, p6, r6, f6⟩ := tJ_spec (im := im) v5 p5
    refine ⟨v6, _, ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6, Or.inl (by omega), by rw [p6, if_neg h32],
      by rw [r6.get (by decide)]; exact g7''', zb _ ?_,
      (((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).mono (by decide),
      (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).mono (fun _ _ h => by
        rcases h with ((((h | h) | h) | h) | h) | h <;> exact h)⟩
    rw [r6.get (by decide), x29d]; simp [ClaudeWCT.WCT9.lowerZeroBits, show ¬ heap < 2 by omega, h16, h32, h8, h4,
      hl1, show lay ≠ 0 by omega]

end cls

/-! U16b grind stub: loop setup and the zero test. -/

section setup
variable {im : Image} [Code im]

end setup

/-! U16b grind stub: node input, zero test, trial invariant. -/

section sim
variable {im : Image} {sk : BitVec 256}
end sim

section found
variable {im : Image} [Code im]

end found

/-! U16b grind stub: the search loop and the whole stub (word 1138 -> 1139). -/

section loop
variable {im : Image} [Code im] (sk : BitVec 256)

end loop

/-! U16b grind stub: the pass-through of a non-lower node (top tree). -/

section pass
variable {im : Image} [Code im] {sk : BitVec 256}

end pass

end Grind


end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_Basic ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
section tb
variable {image : Image} {sk : BitVec 256}
end tb
end SigGolfCandidate.T3M.Expand
end
-- ==== merged from T3M_Expand_LayerChain ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chain chainInput shortHash pad64 zero16 header)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS)
set_option autoImplicit false
section chain
variable {sk : BitVec 256}
theorem not_ChW_hdr {lay : T3.Layer} {WC k A : Nat} (hW : WC + 64 ≤ LEAFPK) (h : A = LEAFPK + 16 ∨ A = LEAFPK + 24)
    (hk : k ≤ 54) : ¬ ChW lay WC k A := by
  rcases h with h | h
  · unfold ChW StepW
    rintro (h' | ⟨c, hc, h' | h'⟩ | ⟨c, _, h' | h'⟩) <;> simp only [CHAIN, LEAFPK] at h h' hW <;>
      first | omega | (unfold slotOff at h'; split_ifs at h' <;> omega)
  · unfold ChW StepW
    rintro (h' | ⟨c, hc, h' | h'⟩ | ⟨c, _, h' | h'⟩) <;> simp only [CHAIN, LEAFPK] at h h' hW <;>
      first | omega | (unfold slotOff at h'; split_ifs at h' <;> omega)
end chain
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Expand
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
open ClaudeWCT
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} [Code im]                    [PackedBlocks.Code im] {sk : BitVec 256}
theorem chainInputW_blocks (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (toQ (pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i step v))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [ClaudeWCT.WCT9.chainInputW_length]),
    blocks_toQ ⟨by rw [ClaudeWCT.WCT9.chainInputW_length]; omega, by rw [ClaudeWCT.WCT9.chainInputW_length]⟩,
    ClaudeWCT.WCT9.chainInputW_length]
end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_LayersBlocks ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
set_option autoImplicit false
set_option maxRecDepth 8192
section blocks
variable (s : MachineState)
-- [h2 lane] removed c342_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
open SigGolfCandidate.T3M.Expand
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} [EntryCode im]
section
variable (s : MachineState)
end
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
end SigGolfCandidate.T3M.Expand.SharedRecover

/-! ## T51 KCOPY (54522..54531, from 331 `jal ra, 54522`): copy the 1,896-byte shared kernel table window
`0xFF9E00 .. 0xFFA568` (237 doublewords; the 1,892-byte block + 4 bytes) to RAM `0xA0000`, then `j 457`. -/
namespace SigGolfCandidate.T3M.Expand.KCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

end SigGolfCandidate.T3M.Expand.KCopy
end
-- ==== merged from T3M_Search_DigestSearch ====
section

section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
section blocks
variable {image : Image} {b : Nat}
end blocks
section sort
variable {image : Image} {b : Nat}
end sort
section loop
variable {image : Image} {b : Nat}
end loop
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer HashOutput)
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem wordsOf_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    wordsOf (T3.pad64 (T3.digestInput rho m c)) =
      [rho.extractLsb' 0 64, rho.extractLsb' 64 64, BitVec.ofNat 64 25984,
        BitVec.ofNat 64 c.toNat, m.extractLsb' 0 64, m.extractLsb' 64 64, m.extractLsb' 128 64,
        m.extractLsb' 192 64] := by
  rw [pad64_digestInput]
  unfold T3.digestInput
  rw [wordsOf_append _ _ (by simp only [List.length_append, SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp only [SphincsSecurity.bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16,
    wordsOf_bytesLE32, T3.digestHeader_low, T3.digestHeader_high]
  rfl
section blocks
variable {image : Image} {d b : Nat}
end blocks
def DsPostS (b d : Nat) (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => FailedAt b t
  | some (_, N), t => t.pc = pcOf (d + 19) ∧ t.getReg .x5 = 0 ∧ T3.admissible (T3.selections N) = true ∧
      OutAt t NBUF N ∧ SelRows t N ∧ RegsExcept s t dsRegs ∧ Frame s t DsW
section loop
variable {image : Image} {d b : Nat} {sk : BitVec 256}
end loop
end SigGolfCandidate.T3M.Search
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Defs ====
section

namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC FailedAt KernAt)
open SigGolfCandidate.T3M.Expand (IDXV)
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_ExpSearch ====
section

section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Search (DIG NBUF)
open SigGolfCandidate.T3M.Expand (IDXV)
open ClaudeWCT.W9.Machine.Sign (run)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE)
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Expand.ESearch
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF OutAt FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF OutAt FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Sign (run memEval_cons_ofNat)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE costByte costChk
  costChk_getD costByte_lt piece regs_rfs shl0_shr33 sll_eval srl_eval fieldE_eval psum psum_succ psum_le fieldN_lt
  psum_nine digestInput_length' pad64_digestInput' wordsOf_digestInput' blocks_digestInput' childN childN_lt childE_eval)
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
section pieces
variable {im : Image}
end pieces
section loop
variable {im : Image} {sk : BitVec 256}
end loop
end ClaudeWCT.W9.Machine.Expand.ESearch
end
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Base ====
section

section
namespace ClaudeWCT.W9.Machine.Expand
open Lean Meta Elab Tactic
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_DrvBits ====
section

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIG NBUF ENC)
set_option autoImplicit false
set_option maxRecDepth 8192
section blocks
variable (s : MachineState)
-- [h2 lane] removed s0_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
end SigGolfCandidate.T3M.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Expand (IDXV)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.Driver
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 16384
end ClaudeWCT.W9.Machine.Expand.Driver
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
set_option linter.unusedSimpArgs false
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Merkle_ChildDefs ====
section

namespace ClaudeWCT.W9.Machine.Merkle
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64)
open SphincsSecurity (bytesLE)
end ClaudeWCT.W9.Machine.Merkle
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Region ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput readDigest readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_full window_zeros zeros)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (chainBytes leafBytes)
set_option linter.unusedSimpArgs false
section windows
variable (c : Nat) (op : WCT9.Opening)
end windows
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_LayoutCode ====
section

/-! Pairing stage 1: code tables of the leaf / digest layout block 48100 .. 49225 (proofs in `LayoutBlock`). -/
namespace ClaudeWCT.W9.Machine.Expand.Layout
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
/-! Generated by pair1-expand (from sol-pair1/img-candidate/expand.code, words 48119 .. 49224).
T51 (VERA2, round 2; regenerated from the T51 expand image t51/sign/img/t51e, words 48119 .. 49225): the top group
keeps the 51 items of values 0..50 (item 129, value 0: `sd t1,-32(a1)`, so `xK 129 = 2^64 - 32` and its slot is
`(dK + xK) % 2^64 = 25200`; item 129 + i: `X = 16 (i - 1)`). #938's items 180..182 (values 51..53) lost their
stores (`nop`): with the return word they form the straight tail `cRet` (49207 .. 49225, 19 words). -/
end ClaudeWCT.W9.Machine.Expand.Layout
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactCode ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib

def compactLook (n : Nat) : Option (BitVec 32) := if compactScope n then expLook n else none
namespace PairCopy
/-! Pairing stage 1: the lower-chain pair copy block at 48000 (outside the compact lookup scope). -/
end PairCopy
def compactWindowOK (n : Nat) (ws : List (BitVec 32)) : Bool :=
  (List.range ws.length).all fun i=>compactLook (n+i)==ws[i]?
end ClaudeWCT.W9.Machine.Expand

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
section code
variable {im : Image}                        
-- (include dropped in this part)
end code
end ClaudeWCT.W9.Machine.Expand.Compact

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Compact2Lv ====
section

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
section code
variable {im : Image}                                                    
-- (include dropped in this part)
end code
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
section eval
variable {s : MachineState} {r : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 r) (hr : r < 2 ^ 7)
include h19 hr
end eval
theorem pbE_eval {s : MachineState} {lay r : Nat} (hl : 1 ≤ lay ∧ lay < 4) (hr : r < 2 ^ lvH lay)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow lay r)) (hp : LPlanAt s) (j : Nat) (hj : j < lvH lay) :
    (pbE j).eval s = BitVec.ofNat 64 (plan lay r j) := by
  have hrow : lvRow lay r < 192 := by
    unfold lvRow lvH at *; split <;> simp_all <;> omega
  simp only [pbE, E.eval, UnOp.eval, h20]
  rw [hp _ hrow, (plan_ok lay r j hl hr hj).1]
section
variable {im : Image}                                                    
-- (include dropped in this part)
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section
namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
/-! C3 (FULL, E6): the root level of each lower layer runs in three pieces: `cLvA` (Z low word copy, then
`jal rtAt`), the trampoline `cRT` (Z high word copy, LE64(1) at window + 24, `jal` back) and `cLvB` (sibling copy). -/
section
variable {im : Image}                                                    
-- (include dropped in this part)
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end
end
