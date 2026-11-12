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
import SigGolfCandidate.Merge076.P4
import SigGolfCandidate.Merge076.P6

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

theorem hd_spec (hpc : s.pc = pcOf 54800) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 54805 ∧ RegsExcept s t [] ∧
      t.getMem (BitVec.ofNat 64 1000) = s.getReg .x7 ∧ t.getMem (BitVec.ofNat 64 1008) = s.getReg .x28 ∧
      t.getMem (BitVec.ofNat 64 1016) = s.getReg .x29 ∧ t.getMem (BitVec.ofNat 64 1024) = s.getReg .x30 ∧
      t.getMem (BitVec.ofNat 64 1032) = s.getReg .x31 ∧ Frame s t (fun A => 1000 ≤ A ∧ A < 1040) ∧
      fetch im t = some (.base .ECALL) := by
  have hc := code_sl (Code.codeAt_stub (im := im)) 54800 54806 le_rfl (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound gHd hc s hpc (by simp [gHd.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    symRun_ecall gHd hc s (by simp [gHd.res, rv_simp]) rfl⟩
  · simp [gHd.res, Result.toState_pc, E.eval]
  · intro r _; cases r <;> simp [gHd.res, rv_simp] <;> rfl
  all_goals try (simp only [Result.toState_getMem, gHd.res]; t3n [])
  · intro A hA hn
    simp only [Result.toState_getMem, gHd.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem b1_spec (hpc : s.pc = pcOf 54806) (h10 : s.getReg .x10 = BitVec.ofNat 64 NODE) :
    ∃ t, Steps im s 5 5 t ∧
      t.pc = (if (s.getMem (BitVec.ofNat 64 (NODE + 16)) >>> 8 &&& 255#64) != 7#64 then pcOf 54875 else pcOf 54811) ∧
      t.getReg .x31 = s.getMem (BitVec.ofNat 64 (NODE + 16)) ∧ RegsExcept s t [.x7, .x28, .x31] ∧
      Frame s t (fun _ => False) := by
  have hc := code_sl (Code.codeAt_stub (im := im)) 54806 54811 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound gB1 hc s hpc (by simp only [gB1.res]; t3n [h10, NODE]; norm_num), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gB1.res, E.eval, CmpOp.eval, BinOp.eval, h10]
    t3n []
  · simp only [Result.toState_getReg, gB1.res]; t3n [h10]
  · intro r hr; simp at hr; cases r <;> simp_all [gB1.res, rv_simp] <;> rfl
  · intro A _ _; simp [gB1.res, rv_simp]

theorem b3_spec (hpc : s.pc = pcOf 54814) :
    ∃ t, Steps im s 16 16 t ∧
      t.pc = (if decW (s.getReg .x31) <<< 5 != 0#64 then pcOf 54824 else pcOf 54823) ∧
      t.getReg .x7 = (s.getReg .x31 &&& 255#64) + 0xffffffffffffff80#64 ∧
      t.getReg .x28 = decW (s.getReg .x31) <<< 5 ∧ t.getReg .x29 = 32#64 ∧
      t.getReg .x30 = decW (s.getReg .x31) <<< 5 + 0x700000#64 ∧
      RegsExcept s t [.x7, .x28, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl (Code.codeAt_stub (im := im)) 54814 54823 (by norm_num) (by norm_num) (by norm_num)
  have hc3 := code_sl (Code.codeAt_stub (im := im)) 54818 54823 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, LH.chain3_sound gB3 hc hpc (by rfl) gB3T (Code.codeAt_dec1 (im := im)) (by rfl) gB3R hc3
    (by simp [gB3R.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gB3R.res, E.eval, CmpOp.eval, BinOp.eval]
    t3n []
    rfl
  all_goals try (simp only [Result.toState_getReg, gB3R.res]; t3n []; done)
  all_goals try (simp only [Result.toState_getReg, gB3R.res]; t3n []; rfl)
  · intro r hr; simp at hr; cases r <;> simp_all [gB3R.res, rv_simp] <;> rfl
  · intro A _ _; simp [gB3R.res, rv_simp]

theorem b4a_spec (hpc : s.pc = pcOf 54825) (R : Nat) (h30 : s.getReg .x30 = BitVec.ofNat 64 R)
    (hR : R % 8 = 0) (hR' : R + 32 ≤ 2 ^ 24) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 60108 ∧
      t.getMem (BitVec.ofNat 64 (R + 24)) = s.getReg .x7 ∧
      RegsExcept s t [] ∧ Frame s t (fun A => A = R + 24) := by
  have hc := code_sl (Code.codeAt_stub (im := im)) 54825 54827 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound gB4a hc s hpc (by simp only [gB4a.res]; t3n [h30]; omega), ?_, ?_, ?_, ?_⟩
  · simp [gB4a.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, gB4a.res]; t3n [h30]
  · intro r hr; cases r <;> simp_all [gB4a.res, rv_simp] <;> rfl
  · intro A hA hn; simp only [Result.toState_getMem, gB4a.res]; t3n [h30]; rw [if_neg (by omega)]

theorem lc_spec (hpc : s.pc = pcOf 54847) (K : Nat) (hK : K = 15 ∨ K = 31) (B : Nat)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 B) (hB : B % 8 = 0) (hB' : B + 32 ≤ 2 ^ 24)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 (B + K)) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if (extractByte (s.getMem (BitVec.ofNat 64 (B + K - 7))) 7).zeroExtend 64 >>> ((s.getReg .x29).toNat % 64)
        = 0#64 then pcOf 54856 else pcOf 54850) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl (Code.codeAt_stub (im := im)) 54847 54850 (by norm_num) (by norm_num) (by norm_num)
  have h30' : s.getReg .x30 = s.getReg .x12 + BitVec.ofNat 64 K := by rw [h30, h12, ofNat_add_ofNat]
  rcases hK with rfl | rfl
  · have hob : ∀ o ∈ gLc15.res.st.obl, o.holds s := by
      simp only [gLc15.res, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Oblig.holds,
        Addr.eval, E.eval, h12]
      t3n []
      omega
    have key := (symRunAux_sound cfgS im s (sl 54847 54850) (pcOf 54847) 20 (σK 15) gLc15.res gLc15 hc hob).1
    rw [← hpc, σK_toState 15 s h30'] at key
    refine ⟨_, key, ?_, ?_, ?_⟩
    · rw [Result.toState_pc]
      simp only [gLc15.res, E.eval, CmpOp.eval, BinOp.eval, UnOp.eval, LoadKind.fromWord]
      t3n [h12]
      rw [show B + 15 - 7 = B + 8 by omega]
      split_ifs <;> simp_all
    · intro r hr; simp at hr; cases r <;> simp_all [gLc15.res, rv_simp] <;> rfl
    · intro A _ _; simp [gLc15.res, rv_simp]
  · have hob : ∀ o ∈ gLc31.res.st.obl, o.holds s := by
      simp only [gLc31.res, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Oblig.holds,
        Addr.eval, E.eval, h12]
      t3n []
      omega
    have key := (symRunAux_sound cfgS im s (sl 54847 54850) (pcOf 54847) 20 (σK 31) gLc31.res gLc31 hc hob).1
    rw [← hpc, σK_toState 31 s h30'] at key
    refine ⟨_, key, ?_, ?_, ?_⟩
    · rw [Result.toState_pc]
      simp only [gLc31.res, E.eval, CmpOp.eval, BinOp.eval, UnOp.eval, LoadKind.fromWord]
      t3n [h12]
      rw [show B + 31 - 7 = B + 24 by omega]
      split_ifs <;> simp_all
    · intro r hr; simp at hr; cases r <;> simp_all [gLc31.res, rv_simp] <;> rfl
    · intro A _ _; simp [gLc31.res, rv_simp]

theorem l2_spec (hpc : s.pc = pcOf 54850) (h10 : s.getReg .x10 = BitVec.ofNat 64 NODE) (n c : Nat)
    (hn : n + 1 < 2 ^ 64) (hc : c < 2 ^ 64)
    (hpad : s.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n) (h31 : s.getReg .x31 = BitVec.ofNat 64 c) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if c ≤ n + 1 then pcOf 54856 else pcOf 54853) ∧
      t.getReg .x7 = BitVec.ofNat 64 (n + 1) ∧ RegsExcept s t [.x7] ∧ Frame s t (fun _ => False) := by
  have hcd := code_sl (Code.codeAt_stub (im := im)) 54850 54853 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound gL2 hcd s hpc (by simp only [gL2.res]; t3n [h10, NODE]; norm_num), ?_, ?_, ?_, ?_⟩
  · rw [Result.toState_pc]
    simp only [gL2.res, E.eval, CmpOp.eval, BinOp.eval]
    t3n [h10, h31]
    rw [show (131584 : Nat) + 32 = NODE + 32 from rfl, hpad, ofNat_add_ofNat, nb_ult' (n + 1) c hn hc]
    by_cases h : c ≤ n + 1
    · simp [h, show ¬ n + 1 < c by omega]
    · simp [h, show n + 1 < c by omega]
  · simp only [Result.toState_getReg, gL2.res]; t3n [h10]
    rw [show (131584 : Nat) + 32 = NODE + 32 from rfl, hpad, ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [gL2.res, rv_simp] <;> rfl
  · intro A _ _; simp [gL2.res, rv_simp]

theorem l3_spec (hpc : s.pc = pcOf 54853) (h10 : s.getReg .x10 = BitVec.ofNat 64 NODE) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 54854 ∧ t.getMem (BitVec.ofNat 64 (NODE + 32)) = s.getReg .x7 ∧
      RegsExcept s t [] ∧ Frame s t (fun A => A = NODE + 32) ∧ fetch im t = some (.base .ECALL) := by
  have hcd := code_sl (Code.codeAt_stub (im := im)) 54853 54855 (by norm_num) (by norm_num) (by norm_num)
  have hob : gL3.res.obligs s := by simp only [gL3.res]; t3n [h10, NODE]; norm_num
  refine ⟨_, symRun_sound gL3 hcd s hpc hob, ?_, ?_, ?_, ?_, symRun_ecall gL3 hcd s hob rfl⟩
  · simp [gL3.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, gL3.res]; t3n [h10]
  · intro r _; cases r <;> simp_all [gL3.res, rv_simp] <;> rfl
  · intro A hA hn; simp only [Result.toState_getMem, gL3.res]; t3n [h10]
    rw [if_neg (by simp only [NODE] at hn ⊢; omega)]

theorem f1_spec (hpc : s.pc = pcOf 54856) (h10 : s.getReg .x10 = BitVec.ofNat 64 NODE) :
    ∃ t, Steps im s 14 14 t ∧ t.pc = pcOf 60128 ∧
      t.getReg .x31 = s.getMem (BitVec.ofNat 64 (NODE + 16)) ∧
      t.getReg .x30 = decW (s.getMem (BitVec.ofNat 64 (NODE + 16))) <<< 5 + 0x700000#64 ∧
      RegsExcept s t [.x28, .x30, .x31] ∧ Frame s t (fun _ => False) := by
  have hcd := code_sl (Code.codeAt_stub (im := im)) 54856 54863 (by norm_num) (by norm_num) (by norm_num)
  have hc3 := code_sl (Code.codeAt_stub (im := im)) 54859 54863 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, LH.chain3_sound gF1 hcd hpc (by rfl) gF1T (Code.codeAt_dec2 (im := im)) (by rfl) gF1R hc3
    (by simp only [gF1R.res]; t3n [h10, NODE]; norm_num; simp only [h10, NODE, BitVec.toNat_ofNat]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
  · simp [gF1R.res, Result.toState_pc, E.eval]
  all_goals try (simp only [Result.toState_getReg, gF1R.res]; t3n [h10]; done)
  all_goals try (simp only [Result.toState_getReg, gF1R.res]; t3n [h10]; rfl)
  · intro r hr; simp at hr; cases r <;> simp_all [gF1R.res, rv_simp] <;> rfl
  · intro A _ _; simp [gF1R.res, rv_simp]

/-! E11 post-grind nonce slot (60128..60141): `t5 += 0x100` (heaps 16..31), `0` (2..3), `8` (4..7), `16` (8..15). -/
theorem dn_spec (hpc : s.pc = pcOf 54875) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf 1139 ∧
      t.getReg .x7 = s.getMem (BitVec.ofNat 64 1000) ∧ t.getReg .x28 = s.getMem (BitVec.ofNat 64 1008) ∧
      t.getReg .x29 = s.getMem (BitVec.ofNat 64 1016) ∧ t.getReg .x30 = s.getMem (BitVec.ofNat 64 1024) ∧
      t.getReg .x31 = s.getMem (BitVec.ofNat 64 1032) ∧
      (∀ k, k < 5 → t.getMem (BitVec.ofNat 64 (1000 + 8 * k)) = 0) ∧
      RegsExcept s t [.x7, .x28, .x29, .x30, .x31] ∧ Frame s t SaveW := by
  have hcd := code_sl (Code.codeAt_stub (im := im)) 54875 54886 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, symRun_sound gDn hcd s hpc (by simp [gDn.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gDn.res, Result.toState_pc, E.eval]
  all_goals try (simp only [Result.toState_getReg, gDn.res]; t3n []; done)
  · intro k hk
    simp only [Result.toState_getMem, gDn.res]
    interval_cases k <;> t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [gDn.res, rv_simp] <;> rfl
  · intro A hA hn; unfold SaveW at hn; simp only [Result.toState_getMem, gDn.res]; t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem f3b_spec (hpc : s.pc = pcOf 54872) (h10 : s.getReg .x10 = BitVec.ofNat 64 NODE) (R : Nat)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 R) (hRc : R % 8 = 0)
    (hR1 : 0x700000 ≤ R) (hR2 : R < 0x700160) :
    ∃ t, Steps im s 14 14 t ∧ t.pc = pcOf 1139 ∧
      t.getMem (BitVec.ofNat 64 R) = s.getMem (BitVec.ofNat 64 (NODE + 32)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 ∧
      t.getReg .x7 = s.getMem (BitVec.ofNat 64 1000) ∧ t.getReg .x28 = s.getMem (BitVec.ofNat 64 1008) ∧
      t.getReg .x29 = s.getMem (BitVec.ofNat 64 1016) ∧ t.getReg .x30 = s.getMem (BitVec.ofNat 64 1024) ∧
      t.getReg .x31 = s.getMem (BitVec.ofNat 64 1032) ∧
      (∀ k, k < 5 → t.getMem (BitVec.ofNat 64 (1000 + 8 * k)) = 0) ∧
      RegsExcept s t [.x7, .x28, .x29, .x30, .x31] ∧
      Frame s t (fun A => A = R ∨ A = NODE + 32 ∨ SaveW A) := by
  have hcd := code_sl (Code.codeAt_stub (im := im)) 54872 54886 (by norm_num) (by norm_num) (by norm_num)
  have hob : gF3b.res.obligs s := by
    simp only [gF3b.res]; t3n [h10, h30, NODE]
    simp only [not_false_eq_true, true_and, and_true]
    omega
  refine ⟨_, symRun_sound gF3b hcd s hpc hob, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gF3b.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, gF3b.res]; t3n [h10, h30]
    simp only [NODE]; split_ifs <;> first | rfl | (exfalso; omega)
  · simp only [Result.toState_getMem, gF3b.res]; t3n [h10, h30]
    simp only [NODE]; split_ifs <;> first | rfl | (exfalso; omega)
  all_goals try (simp only [Result.toState_getReg, gF3b.res]; t3n [h10, h30]; done)
  · intro k hk
    simp only [Result.toState_getMem, gF3b.res]
    interval_cases k <;> (t3n [h10, h30]; try (simp only [NODE]; split_ifs <;> first | rfl | (exfalso; omega)))
  · intro r hr; simp at hr; cases r <;> simp_all [gF3b.res, rv_simp] <;> rfl
  · intro A hA hn; unfold SaveW at hn; simp only [Result.toState_getMem, gF3b.res]; t3n [h10, h30]
    simp only [NODE] at hn ⊢; split_ifs <;> first | rfl | (exfalso; omega)
end blocks

/-! U16b grind stub: tweak-word arithmetic. -/

section cls
variable {im : Image} [Code im]

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
variable {im : Image}               
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

theorem loop_step {im : Image} (hc : CodeAt im (pcOf 54526) loopWords)
    (s : MachineState) (hpc : s.pc = pcOf 54526) (S D F : Nat)
    (hS8 : S % 8 = 0) (hD8 : D % 8 = 0) (hS : S + 8 ≤ 2 ^ 24) (hD : D + 8 ≤ 2 ^ 24) (hF : F < 2 ^ 64)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 F) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = (if S + 8 < F then pcOf 54526 else pcOf 54531) ∧
      t.getReg .x28 = BitVec.ofNat 64 (S + 8) ∧ t.getReg .x29 = BitVec.ofNat 64 (D + 8) ∧
      t.getMem (BitVec.ofNat 64 D) = s.getMem (BitVec.ofNat 64 S) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => A = D) := by
  refine ⟨_, symRun_sound loopRun hc s hpc ?_, ?_, ?_, ?_, ?_, loop_regs s, ?_⟩
  · simp [loopRun.res, rv_simp, h28, h29, accessValid_iff, MEMORY_BYTES]
    omega
  · have hlt : (BitVec.ofNat 64 (S + 8)).ult (BitVec.ofNat 64 F) = decide (S + 8 < F) := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show S + 8 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt hF]
    simp only [Result.toState_pc, loopRun.res, E.eval, BinOp.eval, CmpOp.eval, h28, h30, ofNat_add_ofNat,
      ofNat_add8, ofNat_add8', hlt]
    by_cases h : S + 8 < F <;> simp [h] <;> rfl
  · simp only [Result.toState_getReg, loopRun.res, rv_simp, h28, ofNat_add_ofNat, ofNat_add8, ofNat_add8']
  · simp only [Result.toState_getReg, loopRun.res, rv_simp, h29, ofNat_add_ofNat, ofNat_add8, ofNat_add8']
  · simp only [Result.toState_getMem, loopRun.res]
    t3n [h28, h29]
    simp
  · intro A hA hne
    simp only [Result.toState_getMem, loopRun.res]
    t3n [h29]
    split_ifs with he
    · exfalso; apply hne; omega
    · rfl

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
theorem so9_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 9))
    (c : Nat) (hc : c < 7) (h20 : s.getReg .x20 = BitVec.ofNat 64 c) (N : BitVec 256) (hN : NAt s N) :
    ∃ t, Steps image s 22 22 t ∧ t.pc = pcOf (b + 31) ∧
      t.getReg .x28 = BitVec.ofNat 64 (selWin N c) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_9 hK.2.1) (codeAt_k_9 hK) s hpc ?_, ?_, ?_, ?_, ?_⟩
  · interval_cases c <;> simp [st_9, blk354_9.res, rv_simp, h20, accessValid_iff, MEMORY_BYTES]
  · simp [pcE_9, blk354_9.res, E.eval]
  · simp only [Result.toState_getReg, st_9, blk354_9.res]
    interval_cases c <;> simpa [rv_simp, h20] using window_mem s N hN _ hc
  · intro r hr; simp at hr; cases r <;> simp_all [st_9, blk354_9.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_9, blk354_9.res, rv_simp]
theorem so53_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 53))
    (a y z R S P c : Nat) (ha : a < 256) (hy : y < 256) (hz : z < 256)
    (hP : P + 24 ≤ 2 ^ 24) (hP8 : P % 8 = 0)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 a) (h23 : s.getReg .x23 = BitVec.ofNat 64 y)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 z) (h6 : s.getReg .x6 = BitVec.ofNat 64 R)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 S) (h25 : s.getReg .x25 = BitVec.ofNat 64 P)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 44 44 t ∧ t.pc = pcOf (b + 7) ∧
      t.getReg .x21 = BitVec.ofNat 64 (S + ((a ^^^ y).log2 + 1) + ((y ^^^ z).log2 + 1) + 4) ∧
      t.getMem (BitVec.ofNat 64 P) = BitVec.ofNat 64 (R + a) ∧
      t.getMem (BitVec.ofNat 64 (P + 8)) = BitVec.ofNat 64 (R + y) ∧
      t.getMem (BitVec.ofNat 64 (P + 16)) = BitVec.ofNat 64 (R + z) ∧
      t.getReg .x25 = BitVec.ofNat 64 (P + 24) ∧ t.getReg .x20 = BitVec.ofNat 64 (c + 1) ∧
      RegsExcept s t [.x7, .x20, .x21, .x25, .x28, .x29] ∧
      Frame s t (fun A => A = P ∨ A = P + 8 ∨ A = P + 16) := by
  have hay : a ^^^ y < 256 := Nat.xor_lt_two_pow (n := 8) ha hy
  have hyz : y ^^^ z < 256 := Nat.xor_lt_two_pow (n := 8) hy hz
  refine ⟨_, symRun_sound (run_53 hK.2.1) (codeAt_k_53 hK) s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [st_53, blk354_53.res, rv_simp, h25, accessValid_iff, MEMORY_BYTES]; omega
  · simp [pcE_53, blk354_53.res, E.eval]
  · simp only [Result.toState_getReg, st_53, blk354_53.res]
    simp only [rv_simp, h22, h23, h24, h21, ofNat_xor a y (by omega) (by omega),
      ofNat_xor y z (by omega) (by omega)]
    rw [bitlen_word _ hay, bitlen_word _ hyz]
    t3n []
  · simp only [Result.toState_getMem, st_53, blk354_53.res]
    t3n [h25, h22, h6]
    all_goals (split_ifs <;> first | omega | rfl)
  · simp only [Result.toState_getMem, st_53, blk354_53.res]
    t3n [h25, h23, h6]
    split_ifs <;> first | omega | rfl
  · simp only [Result.toState_getMem, st_53, blk354_53.res]
    t3n [h25, h24, h6]
  · simp only [Result.toState_getReg, st_53, blk354_53.res]
    t3n [h25]
  · simp only [Result.toState_getReg, st_53, blk354_53.res]
    t3n [h20]
  · intro r hr; simp at hr; cases r <;> simp_all [st_53, blk354_53.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, st_53, blk354_53.res]
    t3n [h25]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
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
theorem gate_head_spec {image : Image} {b : Nat} (hK : KernAt image b) (hG : GateAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (gatePc b)) (N : BitVec 256) (hN : NAt s N) :
    ∃ t, Steps image s 5 5 t ∧
      t.pc = (if N.toNat / 2 ^ 206 % 8 = 0 then pcOf (gatePc b + 5) else pcOf (b + 101)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_gate hK.2.1) (codeAt_gateHead hG) s hpc
    (by simp [gateSt, blkGateE.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_⟩
  · have hw := hN 3 (by decide)
    have hh : s.getMem 131448#64 >>> 14 &&& 7#64 = BitVec.ofNat 64 (N.toNat / 2 ^ 206 % 8) := by
      simpa only [NBUF] using hw ▸ gate_word N
    simp only [Result.toState_pc, gateEnd, rebase, blkGateE.res, E.eval, BinOp.eval, CmpOp.eval]
    change (if (s.getMem 131448#64 >>> 14 &&& 7#64 != 0#64) = true then pcOf (b + 101) else pcOf (gatePc b + 5)) = _
    rw [hh]
    have he : (BitVec.ofNat 64 (N.toNat / 2 ^ 206 % 8) = 0#64) ↔ N.toNat / 2 ^ 206 % 8 = 0 :=
      ofNat_inj (by have := Nat.mod_lt (N.toNat / 2 ^ 206) (show 0 < 8 by decide); omega) (by decide)
    simp only [bne_iff_ne, ne_eq, he, ite_not]
  · intro r hr; simp at hr; cases r <;> simp_all [gateSt, blkGateE.res, rv_simp] <;> rfl
  · intro A _ _; simp [gateSt, blkGateE.res, rv_simp]
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
section blocks
variable {image : Image} {d b : Nat}
theorem ds2_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 2)) (i : Nat)
    (hi : i < 2 ^ 20) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf (d + 14) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 16)) = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 (DIG + 24)) = BitVec.ofNat 64 i ∧
      t.getReg .x10 = BitVec.ofNat 64 DIG ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NBUF ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = DIG + 16 ∨ A = DIG + 24) := by
  refine ⟨_, symRun_sound (run_ds2 hD.2) (codeAt_ds_2 hD) s hpc
    (by simp [stds_2, blkds30_2.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcEds_2, E.eval]
  · simp only [Result.toState_getMem, stds_2, blkds30_2.res]
    t3n [DIG]
  · simp only [Result.toState_getMem, stds_2, blkds30_2.res]
    t3n [h19, DIG]
    rw [Nat.mul_one]
  · simp [stds_2, blkds30_2.res, rv_simp]
  · simp [stds_2, blkds30_2.res, rv_simp]
  · simp [stds_2, blkds30_2.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_2, blkds30_2.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, stds_2, blkds30_2.res]
    t3n []
    simp only [DIG] at hn
    rw [if_neg (by omega), if_neg (by omega)]
end blocks
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
open SigGolfCandidate.T3M.Search (DIG NBUF FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF FailedAt)
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

namespace PairCopy
/-! Pairing stage 1: the lower-chain pair copy block at 48000 (outside the compact lookup scope). -/
end PairCopy
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
-- (open dropped: nothing it names is in this part)
section code
variable {im : Image}                                                    
-- (include dropped in this part)
end code
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
-- (open dropped: nothing it names is in this part)
set_option linter.unusedSimpArgs false
section eval
variable {s : MachineState} {r : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 r) (hr : r < 2 ^ 7)
include h19 hr
end eval
section
variable {im : Image}                                                    
-- (include dropped in this part)
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section
namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
-- (open dropped: nothing it names is in this part)
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
