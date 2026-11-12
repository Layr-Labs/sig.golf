import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge074
import SigGolfCandidate.Merge076
import SigGolfCandidate.Merge077
import SigGolfCandidate.Merge078.P1

set_option debug.skipKernelTC true
set_option linter.all false

-- ==== merged from T3M_Expand_Layers ====
section

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Signature chainCount height)
open SigGolfCandidate.T3M.Search (NODE NOUT ENC)
end SigGolfCandidate.T3M.Expand
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Signature chain chainInput shortHash pad64 zero16 header chainCount height
  width maxDigit route recoverLayer leafHash nodeHash)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC csN4)
open ClaudeWCT
set_option maxHeartbeats 2000000
end SigGolfCandidate.T3M.Expand
end
section
namespace SigGolfCandidate.T3M.Expand.BC
open OracleComp SigGolfCandidate.T3
open ClaudeWCT
end SigGolfCandidate.T3M.Expand.BC
end
section
namespace SigGolfCandidate.T3M.Expand.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route height chainCount target width maxDigit counterLimit decode)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT csN4 CsW csRegs csT csOk
  KernAt topDigits lowDigits decode_top decode_low)
open SigGolfCandidate.T3M.Search.BC (CsArgs CsPre CsPost)
open ClaudeWCT
set_option autoImplicit false
end SigGolfCandidate.T3M.Expand.BC
end
section
namespace SigGolfCandidate.T3M.Expand.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route chainCount height)
open SigGolfCandidate.T3M.Search (ENC)
open ClaudeWCT
end SigGolfCandidate.T3M.Expand.BC
end
section
namespace SigGolfCandidate.T3M.Expand.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest route height chainCount target width maxDigit counterLimit decode)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT csN4 CsW csRegs csT csOk
  KernAt topDigits lowDigits decode_top decode_low)
open SigGolfCandidate.T3M.Search.BC (CsArgs CsPre CsPost)
open ClaudeWCT
set_option autoImplicit false
section step
variable {sk : BitVec 256}
end step
end SigGolfCandidate.T3M.Expand.BC
end
section
namespace SigGolfCandidate.T3M.Expand
end SigGolfCandidate.T3M.Expand
end

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Expand.BC
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC csN4)
open ClaudeWCT
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} [Code im] [BCBlocks.Code im] [PackedBlocks.Code im] {sk : BitVec 256}
end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_ComposeBack ====
section

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option autoImplicit false
end SigGolfCandidate.T3M.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC OutAt FailedAt TOP_DATA TableOK)
open SigGolfCandidate.T3M.Expand (IDXV)
open ClaudeWCT.W9.T3M (sigDig sigDec sigDigests)
set_option linter.unusedSimpArgs false
section init
variable {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5312)
include hd
end init
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput Layer LayerSignature height chainCount)
open SigGolfCandidate.T3M.Expand (lWC lWM RlWit sideOff height_le)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M Layer height chainCount route)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC OutAt FailedAt TOP_DATA TableOK)
open SigGolfCandidate.T3M.Expand (IDXV)
open SigGolfCandidate.T3M (window window_flatMap_const zeros)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_PrePassInit ====
section

/-! # T51 DEC from the real initial state

E8 (P1): word 0 is `j 60734` (the pre-pass, 185 steps, then `j 54569` = DEC). From `w9init` with the 5,188-byte signature
`b`, the pre-pass rebuilds DEC's T1 layout (`unpackB b`) and DEC writes the expander's inflated slot layout
`SharedCodec.inflatedRead 0 (SharedCodec.digC b)` (332 slots at `0x7000`) and the hint at `0x66000`, zeroes its
temporaries and jumps to word 1 (`dec_init_r6`, at most 2,347 cycles; N7g 2,271). NBZ5R (NB): DEC (NR2) divides
the field `N` by 88 and rejects a non-canonical `N ≥ nCanon = R * 88` at `j 354` (`dec_reject_nc`), which is exactly
a decoded hint `≥ 8464`. -/

namespace ClaudeWCT.W9.Machine.Expand.PrePass
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M
-- (open dropped: nothing it names is in this part)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

end ClaudeWCT.W9.Machine.Expand.PrePass
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactLoop ====
section

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
def copied (s0 : MachineState) (src dst i : Nat) (A : Nat) : Word :=
  if dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0 then s0.getMem (BitVec.ofNat 64 (src + (A - dst)))
  else s0.getMem (BitVec.ofNat 64 A)
def zeroed (s0 : MachineState) (dst i : Nat) (A : Nat) : Word :=
  if dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0 then 0 else s0.getMem (BitVec.ofNat 64 A)
theorem ofNat_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) + 18446744073709551615#64 = BitVec.ofNat 64 n := by
  rw [show (18446744073709551615#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 1) from rfl, ofNat_add_ofNat,
    show n + 1 + (2 ^ 64 - 1) = n + 2 ^ 64 by omega]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.add_mod_right]
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem copy_iter (s : MachineState) (hpc : s.pc = pcOf 42130) (src dst n : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (n + 1)) (hn : n + 1 < 2 ^ 32)
    (hs : src % 8 = 0) (hs' : src + 8 ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 8 ≤ MEMORY_BYTES) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = (if n = 0 then pcOf 42136 else pcOf 42130) ∧
      t.getReg .x10 = BitVec.ofNat 64 (src + 8) ∧ t.getReg .x11 = BitVec.ofNat 64 (dst + 8) ∧
      t.getReg .x12 = BitVec.ofNat 64 n ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = dst then s.getMem (BitVec.ofNat 64 src) else s.getMem (BitVec.ofNat 64 A)) := by
  have hS : MEMORY_BYTES < 2 ^ 64 := by decide
  refine ⟨_, symRun_sound RCopy (code_cCopy hc) s hpc (by
    simp [RCopy.res, rv_simp, accessValid_iff, h10, h11, BitVec.toNat_ofNat]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RCopy.res, E.eval, CmpOp.eval, BinOp.eval, h12]
    rw [ofNat_sub_one n]
    by_cases h0 : n = 0
    · subst h0; simp
    · have : (BitVec.ofNat 64 n != 0#64) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h; apply h0
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        omega
      simp [this, h0]
  · simp [RCopy.res, rv_simp, h10, ofNat_add_ofNat]
  · simp [RCopy.res, rv_simp, h11, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, RCopy.res, RegFile.get, E.eval, BinOp.eval, h12]
    rw [ofNat_sub_one]
  · c_regs RCopy.res
  · intro A hA
    simp only [Result.toState_getMem, RCopy.res, memEval_cons, memEval_nil, Addr.eval, E.eval, h10, h11]
    by_cases hA' : A = dst
    · subst hA'; simp [BitVec.add_zero]
    · rw [if_neg hA', if_neg]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, BitVec.toNat_add] at this
      omega
theorem copy_ret (s : MachineState) (hpc : s.pc = pcOf 42136) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf ret ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RCopyRet (code_copyRet hc) s hpc (by simp [RCopyRet.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RCopyRet.res, E.eval, h1]
    exact pcOf_and_not1 ret
  · intro r _; cases r <;> simp [RCopyRet.res, rv_simp] <;> rfl
  · intro A _ _; rfl
structure CopyInv (s : MachineState) (src dst n i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if i < n then pcOf 42130 else pcOf 42136)
  x10 : t.getReg .x10 = BitVec.ofNat 64 (src + 8 * i)
  x11 : t.getReg .x11 = BitVec.ofNat 64 (dst + 8 * i)
  x12 : t.getReg .x12 = BitVec.ofNat 64 (n - i)
  regs : RegsExcept s t [.x6, .x10, .x11, .x12]
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = copied s src dst i A
theorem copy_loop (s : MachineState) (hpc : s.pc = pcOf 42130) (src dst n : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 n) (hn : 0 < n) (hn' : n < 2 ^ 32)
    (hs : src % 8 = 0) (hs' : src + 8 * n ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 8 * n ≤ MEMORY_BYTES)
    (hov : dst ≤ src ∨ src + 8 * n ≤ dst) :
    ∀ i, i ≤ n → ∃ t, Steps im s (6 * i) (6 * i) t ∧ CopyInv s src dst n i t := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, ⟨by rw [hpc, if_pos hn], by simpa using h10, by simpa using h11,
      by simpa using h12, fun r _ => rfl, fun A _ => ?_⟩⟩
    unfold copied; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf 42130 := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u10, u11, u12, ru, mu⟩ := copy_iter hc t hpc' (src + 8 * i) (dst + 8 * i) (n - i - 1)
      hI.x10 hI.x11 (by rw [hI.x12]; congr 1; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : n - i - 1 = 0
      · rw [if_pos h, if_neg (by omega)]
      · rw [if_neg h, if_pos (by omega)]
    · rw [u10, show src + 8 * i + 8 = src + 8 * (i + 1) by ring]
    · rw [u11, show dst + 8 * i + 8 = dst + 8 * (i + 1) by ring]
    · rw [u12, show n - i - 1 = n - (i + 1) by omega]
    · exact (hI.regs.trans ru).mono (by decide)
    · intro A hA
      have hsrc : t.getMem (BitVec.ofNat 64 (src + 8 * i)) = s.getMem (BitVec.ofNat 64 (src + 8 * i)) := by
        rw [hI.mem _ (by omega)]; unfold copied; rw [if_neg (by omega)]
      rw [mu A hA, hsrc, hI.mem A hA]
      unfold copied
      by_cases hA' : A = dst + 8 * i
      · subst hA'; rw [if_pos rfl, if_pos (by omega), show dst + 8 * i - dst = 8 * i by omega]
      · rw [if_neg hA']
        by_cases hin : dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]
theorem copy_spec (s : MachineState) (hpc : s.pc = pcOf 42130) (src dst n ret : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 n) (h1 : s.getReg .x1 = pcOf ret) (hn : 0 < n) (hn' : n < 2 ^ 32)
    (hs : src % 8 = 0) (hs' : src + 8 * n ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 8 * n ≤ MEMORY_BYTES)
    (hov : dst ≤ src ∨ src + 8 * n ≤ dst) :
    ∃ t, Steps im s (6 * n + 1) (6 * n + 1) t ∧ t.pc = pcOf ret ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = copied s src dst n A) := by
  obtain ⟨t, st, hI⟩ := copy_loop hc s hpc src dst n h10 h11 h12 hn hn' hs hs' hd hd' hov n le_rfl
  have hpc' : t.pc = pcOf 42136 := by rw [hI.pc, if_neg (by omega)]
  obtain ⟨u, su, pu, ru, fu⟩ := copy_ret hc t hpc' ret (by rw [hI.regs.get (by decide), h1])
  exact ⟨u, st.trans su, pu, (hI.regs.trans ru).mono (by decide), fun A hA => by
    rw [fu A hA (fun h => h), hI.mem A hA]⟩
set_option maxRecDepth 20000 in
theorem zero_iter (s : MachineState) (hpc : s.pc = pcOf 42137) (dst n : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 (n + 1))
    (hn : n + 1 < 2 ^ 32) (hd : dst % 8 = 0) (hd' : dst + 8 ≤ MEMORY_BYTES) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = (if n = 0 then pcOf 42141 else pcOf 42137) ∧
      t.getReg .x11 = BitVec.ofNat 64 (dst + 8) ∧ t.getReg .x12 = BitVec.ofNat 64 n ∧
      RegsExcept s t [.x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = if A = dst then 0 else s.getMem (BitVec.ofNat 64 A)) := by
  have hS : MEMORY_BYTES < 2 ^ 64 := by decide
  refine ⟨_, symRun_sound RZero (code_cZero hc) s hpc (by
    simp [RZero.res, rv_simp, accessValid_iff, h11, BitVec.toNat_ofNat]
    refine ⟨?_, ?_⟩ <;> omega), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RZero.res, E.eval, CmpOp.eval, BinOp.eval, h12]
    rw [ofNat_sub_one n]
    by_cases h0 : n = 0
    · subst h0; simp
    · have : (BitVec.ofNat 64 n != 0#64) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h; apply h0
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        omega
      simp [this, h0]
  · simp [RZero.res, rv_simp, h11, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, RZero.res, RegFile.get, E.eval, BinOp.eval, h12]
    rw [ofNat_sub_one]
  · c_regs RZero.res
  · intro A hA
    simp only [Result.toState_getMem, RZero.res, memEval_cons, memEval_nil, Addr.eval, E.eval, h11]
    by_cases hA' : A = dst
    · subst hA'; simp [BitVec.add_zero]
    · rw [if_neg hA', if_neg]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, BitVec.toNat_add] at this
      omega
theorem zero_ret (s : MachineState) (hpc : s.pc = pcOf 42141) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf ret ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RZeroRet (code_zeroRet hc) s hpc (by simp [RZeroRet.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RZeroRet.res, E.eval, h1]
    exact pcOf_and_not1 ret
  · intro r _; cases r <;> simp [RZeroRet.res, rv_simp] <;> rfl
  · intro A _ _; rfl
structure ZeroInv (s : MachineState) (dst n i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if i < n then pcOf 42137 else pcOf 42141)
  x11 : t.getReg .x11 = BitVec.ofNat 64 (dst + 8 * i)
  x12 : t.getReg .x12 = BitVec.ofNat 64 (n - i)
  regs : RegsExcept s t [.x11, .x12]
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = zeroed s dst i A
theorem zero_loop (s : MachineState) (hpc : s.pc = pcOf 42137) (dst n : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 n) (hn : 0 < n)
    (hn' : n < 2 ^ 32) (hd : dst % 8 = 0) (hd' : dst + 8 * n ≤ MEMORY_BYTES) :
    ∀ i, i ≤ n → ∃ t, Steps im s (4 * i) (4 * i) t ∧ ZeroInv s dst n i t := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, ⟨by rw [hpc, if_pos hn], by simpa using h11, by simpa using h12,
      fun r _ => rfl, fun A _ => ?_⟩⟩
    unfold zeroed; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf 42137 := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u11, u12, ru, mu⟩ := zero_iter hc t hpc' (dst + 8 * i) (n - i - 1)
      hI.x11 (by rw [hI.x12]; congr 1; omega) (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : n - i - 1 = 0
      · rw [if_pos h, if_neg (by omega)]
      · rw [if_neg h, if_pos (by omega)]
    · rw [u11, show dst + 8 * i + 8 = dst + 8 * (i + 1) by ring]
    · rw [u12, show n - i - 1 = n - (i + 1) by omega]
    · exact (hI.regs.trans ru).mono (by decide)
    · intro A hA
      rw [mu A hA, hI.mem A hA]
      unfold zeroed
      by_cases hA' : A = dst + 8 * i
      · subst hA'; rw [if_pos rfl, if_pos (by omega)]
      · rw [if_neg hA']
        by_cases hin : dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]
theorem zero_spec (s : MachineState) (hpc : s.pc = pcOf 42137) (dst n ret : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 n)
    (h1 : s.getReg .x1 = pcOf ret) (hn : 0 < n) (hn' : n < 2 ^ 32) (hd : dst % 8 = 0)
    (hd' : dst + 8 * n ≤ MEMORY_BYTES) :
    ∃ t, Steps im s (4 * n + 1) (4 * n + 1) t ∧ t.pc = pcOf ret ∧ RegsExcept s t [.x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = zeroed s dst n A) := by
  obtain ⟨t, st, hI⟩ := zero_loop hc s hpc dst n h11 h12 hn hn' hd hd' n le_rfl
  have hpc' : t.pc = pcOf 42141 := by rw [hI.pc, if_neg (by omega)]
  obtain ⟨u, su, pu, ru, fu⟩ := zero_ret hc t hpc' ret (by rw [hI.regs.get (by decide), h1])
  exact ⟨u, st.trans su, pu, (hI.regs.trans ru).mono (by decide), fun A hA => by
    rw [fu A hA (fun h => h), hI.mem A hA]⟩
end
end ClaudeWCT.W9.Machine.Expand.Compact
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactCoord ====
section

section


namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt planBytes)
open ClaudeWCT.W9.T3M (authBase authRoot)
set_option linter.unusedSimpArgs false
/-- r3w: the staging slot of sibling level `l` (levels `0..4` from the plan table, level 5 the fixed staging block
`+832`, as the compaction code writes it; the witness layer's own `authSibOff 5` moved to `784`). -/
def authSibOff (c l : Nat) : Nat :=
  if l < 5 then ClaudeWCT.W9.T3M.authSibOff c l else 832 + 48 * (1 - c / 2 ^ 5 % 2)
def bitE (l : Nat) : E :=
  if l < 6 then .bin .and (.bin .srl (.reg .x19) (.c (BitVec.ofNat 64 l))) (.c 1#64)
  else .bin .srl (.reg .x19) (.c (BitVec.ofNat 64 l))
def nbE (l : Nat) : E := .bin .xor (bitE l) (.c 1#64)
def t6E (l : Nat) : E := .bin .add (.bin .sll (nbE l) (.c 4#64)) (.bin .sll (nbE l) (.c 5#64))
def hwE (l : Nat) : E :=
  .un (.ld .hu (2 * (l % 4))) (if l < 4 then (E.reg .x20).ld else (E.bin .add (.reg .x20) (.c 8#64)).ld)
/-- Nested FTS (r1-1): level 5 targets the fixed staging block `+832` (`addi t3,zero,832`, no plan load). -/
def dstE (l : Nat) : E :=
  if l < 5 then .bin .add (.bin .add (.reg .x9) (hwE l)) (t6E l)
  else if l = 5 then .bin .add (.bin .add (.reg .x9) (.c 832#64)) (t6E l) else .bin .add (.reg .x9) (hwE l)
def a3E (l : Nat) : E := .bin .add (.reg .x8) (t6E l)
def srcE (l o : Nat) : E :=
  if 64 * (6 - l) + o = 0 then a3E l else .bin .add (a3E l) (.c (BitVec.ofNat 64 (64 * (6 - l) + o)))
def sibRegs (l : Nat) : RegFile :=
  ((((RegFile.init.set .x13 (a3E l)).set .x28 (dstE l)).set .x29 (srcE l 0).ld).set .x30 (srcE l 8).ld).set .x31
    (t6E l)
/-- r3w (witness stack): store shift of sibling level `l` of coordinate `k` (`sd t4,-sh(t3)`; level 5 one block
further down). The FTS content of the staging is dead (rebuilt by the finish pass), only the frame matters. -/
def sh (k l : Nat) : Nat := if k = 0 then 0 else if l < 5 then 48 * (k - 1) else 48 * k
def shOff (k l o : Nat) : BitVec 64 := BitVec.ofNat 64 (2 ^ 64 - sh k l + o)
theorem sh_le (k l : Nat) : sh k l ≤ 48 * k ∧ sh k l % 16 = 0 := by
  unfold sh; split_ifs <;> omega
theorem ofNat_shOff (X k l o : Nat) (hk : k < 9) (h : sh k l ≤ X) :
    BitVec.ofNat 64 X + shOff k l o = BitVec.ofNat 64 (X - sh k l + o) := by
  have := sh_le k l
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  unfold shOff
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h64]
  omega
/-- r3w: destination of sibling level `l` of coordinate `k` (region base `D`). -/
def sdst (c D k l : Nat) : Nat := D - sh k l + authSibOff c l
def sibMem (k l : Nat) : SymMem :=
  [(⟨some (dstE l), shOff k l 8⟩, (srcE l 8).ld), (⟨some (dstE l), shOff k l 0⟩, (srcE l 0).ld)]
def sibObl4 (k l : Nat) : List Oblig :=
  [.valid ⟨some (dstE l), shOff k l 8⟩ 8, .valid ⟨some (dstE l), shOff k l 0⟩ 8,
    .valid ⟨some (a3E l), BitVec.ofNat 64 (64 * (6 - l) + 8)⟩ 8, .valid ⟨some (a3E l), BitVec.ofNat 64 (64 * (6 - l))⟩ 8]
def sibOblP (l : Nat) : List Oblig := [.align8 (.reg .x20), .valid ⟨some (.reg .x20), BitVec.ofNat 64 (2 * l)⟩ 2]
def sibObl (k l : Nat) : List Oblig := sibObl4 k l ++ (if l = 5 then [] else sibOblP l)
set_option maxRecDepth 20000 in
theorem run_sib (k l : Nat) (hk : k < 9) (hl : l < 6) : symRun cfgC (cSib k l) (pcOf (sibAt k l)) 40 =
    some ⟨⟨sibRegs l, sibMem k l, sibObl k l⟩, .c (pcOf (sibAt k l + sibLen l)), .endOfCode, sibLen l, sibLen l⟩ := by
  interval_cases k <;> interval_cases l <;> kernel_rfl
def srcOff (c l : Nat) : Nat := 64 * (6 - l) + 48 * (1 - c / 2 ^ l % 2)
def planHW (c l : Nat) : Nat := if l < 6 then authBase c l else authRoot c
set_option maxRecDepth 100000 in
theorem planHW_ok : ∀ r < 64, ∀ l < 5,
    LoadKind.hu.fromWord (bytesToWordLE ((planBytes.drop (8 * (2 * r + l / 4))).take 8)) (2 * (l % 4)) =
      BitVec.ofNat 64 (planHW r l) := by
  decide +kernel
theorem authSibOff_ok : ∀ c < 128, ∀ l < 5, authSibOff c l % 16 = 0 ∧ authSibOff c l + 16 ≤ 320 := by
  decide +kernel
theorem authSibOff_five (c : Nat) : authSibOff c 5 = 832 + 48 * (1 - c / 2 ^ 5 % 2) := by
  unfold authSibOff; rw [if_neg (by norm_num)]
theorem auth6_ok (c : Nat) (hc : c < 128) (l : Nat) (hl : l < 6) :
    authSibOff c l % 16 = 0 ∧ authSibOff c l + 16 ≤ 896 ∧ (l < 5 → authSibOff c l + 16 ≤ 320) ∧
      (l = 5 → 832 ≤ authSibOff c l) := by
  by_cases h : l < 5
  · have := authSibOff_ok c hc l h
    exact ⟨this.1, by omega, fun _ => this.2, fun h5 => by omega⟩
  · obtain rfl : l = 5 := by omega
    rw [authSibOff_five]
    have : c / 2 ^ 5 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    refine ⟨by omega, by omega, fun h => by omega, fun _ => by omega⟩
theorem planHW_mod (c l : Nat) : planHW (c % 64) l = planHW c l := by
  unfold planHW authBase authRoot; rw [Nat.mod_mod]
section eval
variable {s : MachineState} {c : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 c) (hc : c < 128)
include h19 hc
theorem bitE_eval (l : Nat) (hl : l < 7) : (bitE l).eval s = BitVec.ofNat 64 (c / 2 ^ l % 2) := by
  apply BitVec.eq_of_toNat_eq
  unfold bitE
  split
  · simp only [E.eval, BinOp.eval, h19, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show l < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show l < 64 by omega), show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod,
      Nat.mod_eq_of_lt (show c / 2 ^ l % 2 < 2 ^ 64 from lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num))]
  · have hl6 : l = 6 := by omega
    subst hl6
    simp only [E.eval, BinOp.eval, h19, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
    norm_num
    omega
theorem nbE_eval (l : Nat) (hl : l < 7) : (nbE l).eval s = BitVec.ofNat 64 (1 - c / 2 ^ l % 2) := by
  have hb := bitE_eval h19 hc l hl
  simp only [nbE, E.eval, BinOp.eval, hb]
  have : c / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (show c / 2 ^ l % 2 = 0 ∨ c / 2 ^ l % 2 = 1 by omega) with h | h <;> rw [h] <;> decide
theorem t6E_eval (l : Nat) (hl : l < 7) : (t6E l).eval s = BitVec.ofNat 64 (48 * (1 - c / 2 ^ l % 2)) := by
  have hb := nbE_eval h19 hc l hl
  simp only [t6E, E.eval, BinOp.eval, hb]
  have : c / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (show c / 2 ^ l % 2 = 0 ∨ c / 2 ^ l % 2 = 1 by omega) with h | h <;> rw [h] <;> decide
theorem a3E_eval (l : Nat) (hl : l < 7) {S : Nat} (h8 : s.getReg .x8 = BitVec.ofNat 64 S) :
    (a3E l).eval s = BitVec.ofNat 64 (S + 48 * (1 - c / 2 ^ l % 2)) := by
  simp only [a3E, E.eval, BinOp.eval, h8, t6E_eval h19 hc l hl, ofNat_add_ofNat]
theorem srcE_eval (l : Nat) (hl : l < 7) {S : Nat} (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (o : Nat) :
    (srcE l o).eval s = BitVec.ofNat 64 (S + srcOff c l + o) := by
  unfold srcE srcOff
  split
  · rw [a3E_eval h19 hc l hl h8]; congr 1; omega
  · simp only [E.eval, BinOp.eval, a3E_eval h19 hc l hl h8, ofNat_add_ofNat]; congr 1; omega
end eval
theorem hwE_eval {s : MachineState} {c : Nat} (hc : c < 128)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64))) (hp : PlanAt s) (l : Nat) (hl : l < 5) :
    (hwE l).eval s = BitVec.ofNat 64 (planHW c l) := by
  have hr : c % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hw : (if l < 4 then (E.reg .x20).ld else (E.bin .add (.reg .x20) (.c 8#64)).ld).eval s =
      bytesToWordLE ((planBytes.drop (8 * (2 * (c % 64) + l / 4))).take 8) := by
    split
    · simp only [E.eval, h20]
      rw [show l / 4 = 0 by omega, show PLAN + 16 * (c % 64) = PLAN + 8 * (2 * (c % 64) + 0) by ring]
      exact hp _ (by omega)
    · simp only [E.eval, BinOp.eval, h20, ofNat_add_ofNat]
      rw [show l / 4 = 1 by omega, show PLAN + 16 * (c % 64) + 8 = PLAN + 8 * (2 * (c % 64) + 1) by ring]
      exact hp _ (by omega)
  simp only [hwE, E.eval, UnOp.eval]
  rw [hw, planHW_ok (c % 64) hr l hl, planHW_mod]
theorem authSibOff_eq (c l : Nat) (hl : l < 5) :
    authSibOff c l = if l < 6 then planHW c l + 48 * (1 - c / 2 ^ l % 2) else planHW c l := by
  unfold authSibOff ClaudeWCT.W9.T3M.authSibOff planHW SigGolfCandidate.T3M.sibOff
  rw [if_pos hl]
  have : c / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by norm_num)
  split_ifs <;> omega
theorem dstE_eval {s : MachineState} {c D : Nat} (hc : c < 128) (h19 : s.getReg .x19 = BitVec.ofNat 64 c)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64))) (hp : PlanAt s)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 D) (l : Nat) (hl : l < 6) :
    (dstE l).eval s = BitVec.ofNat 64 (D + authSibOff c l) := by
  by_cases hl5 : l < 5
  · rw [authSibOff_eq c l (by omega), if_pos (show l < 6 by omega)]
    simp only [dstE, if_pos hl5, E.eval, BinOp.eval, h9, hwE_eval hc h20 hp l hl5, t6E_eval h19 hc l (by omega),
      ofNat_add_ofNat]
    rw [Nat.add_assoc]
  · obtain rfl : l = 5 := by omega
    rw [authSibOff_five]
    simp only [dstE, show ¬ (5 : Nat) < 5 by decide, if_false, if_true, E.eval, BinOp.eval, h9,
      t6E_eval h19 hc 5 (by omega), ofNat_add_ofNat]
    rw [Nat.add_assoc]
theorem srcOff_bound (c l : Nat) : srcOff c l + 16 ≤ 448 ∧ srcOff c l % 16 = 0 := by
  unfold srcOff
  have : c / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by norm_num)
  constructor <;> omega
theorem sibRegs_get (l : Nat) (s : MachineState) (r : Reg) (hr : r ∉ [.x13, .x28, .x29, .x30, .x31]) :
    ((sibRegs l).get r).eval s = s.getReg r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h13, h28, h29, h30, h31⟩ := hr
  cases r <;> first | rfl | (exfalso; simp_all)
/-! Nested FTS (r1-1): level 6. The word at `sibAt k 6` jumps to the trampoline `P6(k)` (words
`33000 + 13 k`), which loads coordinate `k`'s top sibling from the scratch region (`x8 + 48 (1 - bit6)`) and
stores it with the flag `1 - bit6` to the hold slot `0x380000 + 32 k`; the final assembly places it. -/
def cJ6s : List (BitVec 32) := [4187975791,3776933999,3365892207,2954850415,2543808623,4279201903,3868160111,3457118319,3046076527]
def cP6s : List (List (BitVec 32)) := [[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,31338531,32388131,33437731,109084783],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,64892963,65942563,66992163,520126575],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,98447395,99496995,100546595,931168367],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,132001827,133051427,134101027,1342210159],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,165556259,166605859,167655459,1753251951],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,199110691,200160291,201209891,17858671],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,232665123,233714723,234764323,428900463],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,266219555,267269155,268318755,839942255],[6938515,2084755,6264467,5217939,30836403,8816307,441987,8830723,3673655,299773987,300823587,301873187,1250984047]]
def cJ6 (k : Nat) : List (BitVec 32) := [cJ6s.getD k 0]
def cP6 (k : Nat) : List (BitVec 32) := cP6s.getD k []
def p6At (k : Nat) : Nat := 33000 + 13 * k
def p6tE : E := .bin .add (.bin .sll (nbE 6) (.c 5#64)) (.bin .sll (nbE 6) (.c 4#64))
def a6E : E := .bin .add p6tE (.reg .x8)
def p6Regs : RegFile :=
  ((((RegFile.init.set .x13 a6E).set .x28 (.c 0x380000#64)).set .x29 (E.ld a6E)).set .x30
    (E.ld (.bin .add a6E (.c 8#64)))).set .x31 (nbE 6)
def p6Mem (k : Nat) : SymMem :=
  [(⟨none, BitVec.ofNat 64 (holdAt k + 16)⟩, nbE 6), (⟨none, BitVec.ofNat 64 (holdAt k + 8)⟩, E.ld (.bin .add a6E (.c 8#64))),
    (⟨none, BitVec.ofNat 64 (holdAt k)⟩, E.ld a6E)]
def p6Obl : List Oblig := [.valid ⟨some a6E, 8#64⟩ 8, .valid ⟨some a6E, 0#64⟩ 8]
theorem run_j6 (k : Nat) (hk : k < 9) : symRun cfgC (cJ6 k) (pcOf (sibAt k 6)) 40 =
    some ⟨⟨RegFile.init, [], []⟩, .c (pcOf (p6At k)), .jump, 1, 1⟩ := by
  interval_cases k <;> kernel_rfl
theorem run_p6 (k : Nat) (hk : k < 9) : symRun cfgC (cP6 k) (pcOf (p6At k)) 40 =
    some ⟨⟨p6Regs, p6Mem k, p6Obl⟩, .c (pcOf (coordAt k + 109)), .jump, 13, 13⟩ := by
  interval_cases k <;> kernel_rfl
theorem p6Regs_get (s : MachineState) (r : Reg) (hr : r ∉ [.x13, .x28, .x29, .x30, .x31]) :
    (p6Regs.get r).eval s = s.getReg r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h13, h28, h29, h30, h31⟩ := hr
  cases r <;> first | rfl | (exfalso; simp_all)
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem sib_spec (k l : Nat) (hk : k < 9) (hl : l < 6) (s : MachineState) (hpc : s.pc = pcOf (sibAt k l))
    (c S D : Nat) (hcl : c < 128) (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (h9 : s.getReg .x9 = BitVec.ofNat 64 D)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 c) (h20 : s.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64)))
    (hp : PlanAt s) (hS : S % 16 = 0) (hS' : S + 448 ≤ MEMORY_BYTES) (hD : D % 16 = 0)
    (hD' : D + 896 ≤ MEMORY_BYTES) (hsh : 48 * k ≤ D) :
    ∃ t, Steps im s (sibLen l) (sibLen l) t ∧ t.pc = pcOf (sibAt k l + sibLen l) ∧
      RegsExcept s t [.x13, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = sdst c D k l + 8 then s.getMem (BitVec.ofNat 64 (S + srcOff c l + 8))
        else if A = sdst c D k l then s.getMem (BitVec.ofNat 64 (S + srcOff c l))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  have ha := auth6_ok c hcl l hl
  have hso := srcOff_bound c l
  have hd := dstE_eval hcl h19 h20 hp h9 l hl
  have hs0 := srcE_eval h19 hcl l (by omega) h8 0
  have hs8 := srcE_eval h19 hcl l (by omega) h8 8
  have ha3 := a3E_eval h19 hcl l (by omega) h8
  have hrun := run_sib k l hk hl
  have hshl := sh_le k l
  have e8 := ofNat_shOff (D + authSibOff c l) k l 8 hk (by omega)
  have e0 := ofNat_shOff (D + authSibOff c l) k l 0 hk (by omega)
  have hobl : Oblig.all s (sibObl k l) := by
    rw [Oblig.all_iff]
    intro o ho
    unfold sibObl at ho
    rw [List.mem_append] at ho
    rcases ho with ho | ho
    swap
    · split at ho
      · simp at ho
      · simp only [sibOblP, List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl
        · simp only [Oblig.holds, E.eval, h20, BitVec.toNat_ofNat]; unfold PLAN; omega
        · simp only [Oblig.holds, Addr.eval, E.eval, h20, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
          unfold PLAN; omega
    simp only [sibObl4, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, hd, e8, accessValid_iff, BitVec.toNat_ofNat]; omega
    · simp only [Oblig.holds, Addr.eval, hd, e0, accessValid_iff, BitVec.toNat_ofNat]; omega
    · simp only [Oblig.holds, Addr.eval, ha3, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      rw [show S + 48 * (1 - c / 2 ^ l % 2) + (64 * (6 - l) + 8) = S + srcOff c l + 8 by unfold srcOff; omega]
      omega
    · simp only [Oblig.holds, Addr.eval, ha3, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      rw [show S + 48 * (1 - c / 2 ^ l % 2) + 64 * (6 - l) = S + srcOff c l by unfold srcOff; omega]
      omega
  refine ⟨_, symRun_sound hrun (code_cSib hc k l hk hl) s hpc hobl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, E.eval]
  · intro r hr
    rw [Result.toState_getReg]
    exact sibRegs_get l s r hr
  · intro A hA
    unfold sdst
    simp only [Result.toState_getMem, sibMem, memEval_cons, memEval_nil, Addr.eval, E.eval, hd, hs0, hs8, e8, e0,
      Nat.add_zero]
    have hbig : D - sh k l + authSibOff c l + 8 < 2 ^ 64 := by omega
    have q8 : D + authSibOff c l - sh k l + 8 = D - sh k l + authSibOff c l + 8 := by omega
    have q0 : D + authSibOff c l - sh k l = D - sh k l + authSibOff c l := by omega
    rw [q8, q0]
    by_cases h1 : A = D - sh k l + authSibOff c l + 8
    · subst h1; simp
    · rw [if_neg (fun h => h1 ((ofNat_inj hA hbig).mp h)), if_neg h1]
      by_cases h2 : A = D - sh k l + authSibOff c l
      · subst h2; simp
      · rw [if_neg (fun h => h2 ((ofNat_inj hA (by omega)).mp h)), if_neg h2]
theorem code_cJ6 (k : Nat) (hk : k < 9) : CodeAt im (pcOf (sibAt k 6)) (cJ6 k) := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cP6 (k : Nat) (hk : k < 9) : CodeAt im (pcOf (p6At k)) (cP6 k) := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem sib6_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (sibAt k 6)) (c S : Nat)
    (hcl : c < 128) (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (h19 : s.getReg .x19 = BitVec.ofNat 64 c)
    (hS : S % 16 = 0) (hS' : S + 448 ≤ MEMORY_BYTES) :
    ∃ t, Steps im s 14 14 t ∧ t.pc = pcOf (coordAt k + 109) ∧ RegsExcept s t [.x13, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = holdAt k + 16 then BitVec.ofNat 64 (1 - c / 2 ^ 6 % 2)
        else if A = holdAt k + 8 then s.getMem (BitVec.ofNat 64 (S + srcOff c 6 + 8))
        else if A = holdAt k then s.getMem (BitVec.ofNat 64 (S + srcOff c 6))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  obtain ⟨t1, hj, r1, m1, p1⟩ : ∃ t1, Steps im s 1 1 t1 ∧ (∀ r, t1.getReg r = s.getReg r) ∧
      (∀ A, t1.getMem A = s.getMem A) ∧ t1.pc = pcOf (p6At k) := by
    refine ⟨_, symRun_sound (run_j6 k hk) (code_cJ6 hc k hk) s hpc (by simp [rv_simp]), ?_, ?_, ?_⟩
    · intro r; rw [Result.toState_getReg]; cases r <;> rfl
    · intro A; simp [rv_simp]
    · simp [Result.toState_pc, E.eval]
  have hnb := nbE_eval (s := t1) (by rw [r1]; exact h19) hcl 6 (by omega)
  have h48 : p6tE.eval t1 = BitVec.ofNat 64 (48 * (1 - c / 2 ^ 6 % 2)) := by
    simp only [p6tE, E.eval, BinOp.eval, hnb]
    have : c / 2 ^ 6 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rcases (show c / 2 ^ 6 % 2 = 0 ∨ c / 2 ^ 6 % 2 = 1 by omega) with h | h <;> rw [h] <;> decide
  have hso := srcOff_bound c 6
  have ha6 : a6E.eval t1 = BitVec.ofNat 64 (S + srcOff c 6) := by
    simp only [a6E, E.eval, BinOp.eval, h48, r1, h8, ofNat_add_ofNat]
    congr 1; unfold srcOff; omega
  have ha8 : (E.bin .add a6E (.c 8#64)).eval t1 = BitVec.ofNat 64 (S + srcOff c 6 + 8) := by
    simp only [E.eval, BinOp.eval, ha6, ofNat_add_ofNat]
  have hobl : Oblig.all t1 p6Obl := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [p6Obl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · simp only [Oblig.holds, Addr.eval, ha6, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]; omega
    · simp only [Oblig.holds, Addr.eval, ha6, BitVec.add_zero, accessValid_iff, BitVec.toNat_ofNat]; omega
  have hp := symRun_sound (run_p6 k hk) (code_cP6 hc k hk) t1 p1 hobl
  refine ⟨_, (hj.trans hp).of_eq rfl rfl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, E.eval]
  · intro r hr
    rw [Result.toState_getReg, p6Regs_get t1 r hr, r1]
  · intro A hA
    simp only [Result.toState_getMem, p6Mem, memEval_cons, memEval_nil, Addr.eval, hnb, ha6, ha8, E.eval, BinOp.eval,
      ofNat_add_ofNat, m1]
    have hH : holdAt k + 16 < 2 ^ 64 := by unfold holdAt; omega
    by_cases e1 : A = holdAt k + 16
    · subst e1; simp
    · rw [if_neg (fun h => e1 ((ofNat_inj hA hH).mp h)), if_neg e1]
      by_cases e2 : A = holdAt k + 8
      · subst e2; simp
      · rw [if_neg (fun h => e2 ((ofNat_inj hA (by omega)).mp h)), if_neg e2]
        by_cases e3 : A = holdAt k
        · subst e3; simp
        · rw [if_neg (fun h => e3 ((ofNat_inj hA (by omega)).mp h)), if_neg e3]
end
end ClaudeWCT.W9.Machine.Expand.Compact
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt child_bits)
set_option linter.unusedSimpArgs false
def SNAP : Nat := 0x200000
def rHead (k : Nat) : Result :=
  [RHead0.res, RHead1.res, RHead2.res, RHead3.res, RHead4.res, RHead5.res, RHead6.res, RHead7.res, RHead8.res].getD k
    RHead0.res
def rMid (k : Nat) : Result :=
  [RMid0.res, RMid1.res, RMid2.res, RMid3.res, RMid4.res, RMid5.res, RMid6.res, RMid7.res, RMid8.res].getD k RMid0.res
theorem run_head (k : Nat) (hk : k < 9) : symRun cfgC (cHead k) (pcOf (coordAt k)) 40 = some (rHead k) := by
  interval_cases k
  exacts [RHead0, RHead1, RHead2, RHead3, RHead4, RHead5, RHead6, RHead7, RHead8]
theorem run_mid (k : Nat) (hk : k < 9) : symRun cfgC (cMid k) (pcOf (coordAt k + 6)) 40 = some (rMid k) := by
  interval_cases k
  exacts [RMid0, RMid1, RMid2, RMid3, RMid4, RMid5, RMid6, RMid7, RMid8]
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem start_spec (s : MachineState) (hpc : s.pc = pcOf 41108) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf 42130 ∧ t.getReg .x10 = BitVec.ofNat 64 0x840 ∧
      t.getReg .x11 = BitVec.ofNat 64 SNAP ∧ t.getReg .x12 = BitVec.ofNat 64 1152 ∧ t.getReg .x1 = pcOf 41115 ∧
      RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RStart (code_cStart hc) s hpc (by simp [RStart.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [Result.toState_pc, RStart.res, E.eval]
  · simp [RStart.res, rv_simp]
  · simp [RStart.res, rv_simp]; rfl
  · simp [RStart.res, rv_simp]
  · simp [RStart.res, rv_simp]
  · c_regs RStart.res
  · intro A _ _; rfl
theorem regs_spec (s : MachineState) (hpc : s.pc = pcOf 41115) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf (coordAt 0) ∧ t.getReg .x8 = BitVec.ofNat 64 SNAP ∧
      t.getReg .x9 = BitVec.ofNat 64 0x840 ∧ t.getReg .x18 = BitVec.ofNat 64 PLAN ∧
      RegsExcept s t [.x8, .x9, .x18] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RRegs (code_cRegs hc) s hpc (by simp [RRegs.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, RRegs.res, E.eval, coordAt]
  · simp [RRegs.res, rv_simp]; rfl
  · simp [RRegs.res, rv_simp]
  · simp [RRegs.res, rv_simp]; rfl
  · c_regs RRegs.res
  · intro A _ _; rfl
theorem final_spec (s : MachineState) (hpc : s.pc = pcOf 42120) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf 42130 ∧ t.getReg .x10 = BitVec.ofNat 64 (0x800 + 9280) ∧
      t.getReg .x11 = BitVec.ofNat 64 (0x800 + 8128) ∧ t.getReg .x12 = BitVec.ofNat 64 1713 ∧
      t.getReg .x1 = pcOf 42127 ∧ RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RFinal (code_cFinal hc) s hpc (by simp [RFinal.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [Result.toState_pc, RFinal.res, E.eval]
  · simp [RFinal.res, rv_simp]
  · simp [RFinal.res, rv_simp]
  · simp [RFinal.res, rv_simp]
  · simp [RFinal.res, rv_simp]
  · c_regs RFinal.res
  · intro A _ _; rfl
theorem halt_spec (s : MachineState) (hpc : s.pc = pcOf 42127) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 42142 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RHalt (code_cHalt hc) s hpc (by simp [RHalt.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, RHalt.res, E.eval]
  · c_regs RHalt.res
  · intro A _ _; rfl
end
def headX6 (k : Nat) : E :=
  .bin .srl (E.c (BitVec.ofNat 64 (0x60 + 8 * (WCT9.childBase k / 64)))).ld (.c (BitVec.ofNat 64 (WCT9.childBase k % 64)))
def headRegs (k : Nat) : RegFile :=
  ((((RegFile.init.set .x6 (headX6 k)).set .x19 (.bin .and (headX6 k) (.c 127#64))).set .x11 (.reg .x9)).set .x12
    (.c 40#64)).set .x1 (.c (pcOf (coordAt k + 6)))
def midRegs (k : Nat) : RegFile :=
  (((RegFile.init.set .x10 (.bin .add (.reg .x8) (.c 448#64))).set .x11 (.bin .add (.reg .x9) (.c 320#64))).set .x12
    (.c 72#64)).set .x1 (.c (pcOf (coordAt k + 10)))
theorem rHead_eq (k : Nat) (hk : k < 9) : rHead k = ⟨⟨headRegs k, [], []⟩, .c (pcOf 42137), .jump, 6, 6⟩ := by
  interval_cases k <;> kernel_rfl
theorem rMid_eq (k : Nat) (hk : k < 9) : rMid k = ⟨⟨midRegs k, [], []⟩, .c (pcOf 42130), .jump, 4, 4⟩ := by
  interval_cases k <;> kernel_rfl
theorem headRegs_get (k : Nat) (s : MachineState) (r : Reg) (hr : r ∉ [.x1, .x6, .x11, .x12, .x19]) :
    ((headRegs k).get r).eval s = s.getReg r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h6, h11, h12, h19⟩ := hr
  cases r <;> first | rfl | (exfalso; simp_all)
theorem midRegs_get (k : Nat) (s : MachineState) (r : Reg) (hr : r ∉ [.x1, .x10, .x11, .x12]) :
    ((midRegs k).get r).eval s = s.getReg r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h10, h11, h12⟩ := hr
  cases r <;> first | rfl | (exfalso; simp_all)
theorem childBase_shift (k : Nat) (hk : k < 9) : WCT9.childBase k % 64 + 7 ≤ 64 ∧ WCT9.childBase k / 64 < 4 := by
  interval_cases k <;> decide
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem head_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k)) (N : HashOutput)
    (hN : OutAt s 0x60 N) (D : Nat) (h9 : s.getReg .x9 = BitVec.ofNat 64 D) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 42137 ∧
      t.getReg .x19 = BitVec.ofNat 64 (N.toNat / 2 ^ WCT9.childBase k % 128) ∧
      t.getReg .x11 = BitVec.ofNat 64 D ∧ t.getReg .x12 = BitVec.ofNat 64 40 ∧ t.getReg .x1 = pcOf (coordAt k + 6) ∧
      RegsExcept s t [.x1, .x6, .x11, .x12, .x19] ∧ Frame s t (fun _ => False) := by
  have hrun := run_head k hk
  rw [rHead_eq k hk] at hrun
  obtain ⟨hsh, hw⟩ := childBase_shift k hk
  refine ⟨_, symRun_sound hrun (code_cHead hc k hk) s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, headRegs, headX6, RegFile.set, RegFile.get, E.eval, BinOp.eval]
    have hm := hN (WCT9.childBase k / 64) hw
    rw [hm]
    apply BitVec.eq_of_toNat_eq
    have := child_bits N (WCT9.childBase k / 64) (WCT9.childBase k % 64) hsh
    rw [Nat.div_add_mod] at this
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show WCT9.childBase k % 64 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show WCT9.childBase k % 64 < 64 by omega)]
    rw [this, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num) : N.toNat / 2 ^ WCT9.childBase k % 128 < 2 ^ 64)]
  · simp [headRegs, RegFile.set, RegFile.get, E.eval, h9]
  · simp [headRegs, RegFile.set, RegFile.get, E.eval]
  · simp [headRegs, RegFile.set, RegFile.get, E.eval]
  · intro r hr; rw [Result.toState_getReg]; exact headRegs_get k s r hr
  · intro A _ _; rfl
theorem mid_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k + 6)) (S D : Nat)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (h9 : s.getReg .x9 = BitVec.ofNat 64 D) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 42130 ∧ t.getReg .x10 = BitVec.ofNat 64 (S + 448) ∧
      t.getReg .x11 = BitVec.ofNat 64 (D + 320) ∧ t.getReg .x12 = BitVec.ofNat 64 72 ∧
      t.getReg .x1 = pcOf (coordAt k + 10) ∧ RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  have hrun := run_mid k hk
  rw [rMid_eq k hk] at hrun
  refine ⟨_, symRun_sound hrun (code_cMid hc k hk) s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, midRegs, RegFile.set, RegFile.get, E.eval, BinOp.eval, h8, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, midRegs, RegFile.set, RegFile.get, E.eval, BinOp.eval, h9, ofNat_add_ofNat]
  · simp [midRegs, RegFile.set, RegFile.get, E.eval]
  · simp [midRegs, RegFile.set, RegFile.get, E.eval]
  · intro r hr; rw [Result.toState_getReg]; exact midRegs_get k s r hr
  · intro A _ _; rfl
theorem row_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k + 10)) (c : Nat)
    (hcl : c < 128) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) (h18 : s.getReg .x18 = BitVec.ofNat 64 PLAN) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf (coordAt k + 13) ∧ t.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64)) ∧
      RegsExcept s t [.x7, .x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_row k hk) (code_cRow hc k hk) s hpc (by simp [RRow.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, RRow.res, RegFile.get, E.eval, BinOp.eval, h19, h18]
    rw [show (63#64 : Word) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl, SigGolfCandidate.T3M.Search.ofNat_and_mask c 6 (by norm_num)]
    rw [show (4#64 : Word).toNat % 64 = 4 from rfl, ofNat_shl, ofNat_add_ofNat]
    congr 1; ring
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h7, h20⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
set_option maxRecDepth 20000 in
theorem step_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k + 109)) (S D : Nat)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 S) (h9 : s.getReg .x9 = BitVec.ofNat 64 D) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf (coordAt k + 111) ∧ t.getReg .x8 = BitVec.ofNat 64 (S + 1024) ∧
      t.getReg .x9 = BitVec.ofNat 64 (D + 896) ∧ RegsExcept s t [.x8, .x9] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_step k hk) (code_cStep hc k hk) s hpc (by simp [RStep.res, rv_simp]), ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, RStep.res, RegFile.get, E.eval, BinOp.eval, h8, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, RStep.res, RegFile.get, E.eval, BinOp.eval, h9, ofNat_add_ofNat]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h8', h9'⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
end
end ClaudeWCT.W9.Machine.Expand.Compact
end

section

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt)
set_option linter.unusedSimpArgs false
def sibLev (c j : Nat) : Option Nat :=
  (List.range 6).find? fun l => authSibOff c l = 8 * j ∨ authSibOff c l + 8 = 8 * j
def sibSrc (c j : Nat) : Option Nat :=
  (sibLev c j).map fun l => if authSibOff c l = 8 * j then srcOff c l else srcOff c l + 8
/-- The hold slot of coordinate `k`: its top sibling and the flag `1 - bit6`. -/
def holdMem (M : Nat → Word) (c S k : Nat) (A : Nat) (rest : Word) : Word :=
  if A = holdAt k + 16 then BitVec.ofNat 64 (1 - c / 2 ^ 6 % 2)
  else if A = holdAt k + 8 then M (S + srcOff c 6 + 8)
  else if A = holdAt k then M (S + srcOff c 6) else rest
def sibsMem (M : Nat → Word) (c S D k L : Nat) (A : Nat) : Word :=
  match (List.range L).find? (fun l => A = sdst c D k l ∨ A = sdst c D k l + 8) with
  | some l => if A = sdst c D k l then M (S + srcOff c l) else M (S + srcOff c l + 8)
  | none => M A
theorem find_range_succ (p : Nat → Bool) (L : Nat) :
    (List.range (L + 1)).find? p = match (List.range L).find? p with
      | some l => some l
      | none => if p L then some L else none := by
  rw [List.range_succ, List.find?_append]
  cases h : (List.range L).find? p with
  | some l => rfl
  | none => simp only [List.find?_cons, List.find?_nil, Option.none_or]; cases hp : p L <;> simp [hp]
theorem find_some {p : Nat → Bool} {L l : Nat} (h : (List.range L).find? p = some l) : l < L ∧ p l = true :=
  ⟨List.mem_range.mp (List.mem_of_find?_eq_some h), List.find?_some h⟩
theorem auth_disj (c : Nat) (hc : c < 128) (l l' : Nat) (hl : l < 6) (hl' : l' < 6) (hne : l ≠ l') :
    authSibOff c l + 16 ≤ authSibOff c l' ∨ authSibOff c l' + 16 ≤ authSibOff c l := by
  by_cases h : l < 5 ∧ l' < 5
  · have e1 : authSibOff c l = ClaudeWCT.W9.T3M.authSibOff c l := if_pos h.1
    have e2 : authSibOff c l' = ClaudeWCT.W9.T3M.authSibOff c l' := if_pos h.2
    rw [e1, e2]
    exact ClaudeWCT.W9.T3M.auth_sib_disjoint c hc l h.1 l' h.2 hne
  · have a := auth6_ok c hc l hl
    have b := auth6_ok c hc l' hl'
    rcases (show l = 5 ∨ l' = 5 by omega) with e | e
    · have := a.2.2.2 e; have := b.2.2.1 (by omega); omega
    · have := b.2.2.2 e; have := a.2.2.1 (by omega); omega
theorem sdst_disj (c D k : Nat) (hc : c < 128) (hk : 48 * k ≤ D) (l l' : Nat) (hl : l < 6) (hl' : l' < 6)
    (hne : l ≠ l') : sdst c D k l + 16 ≤ sdst c D k l' ∨ sdst c D k l' + 16 ≤ sdst c D k l := by
  have a := auth6_ok c hc l hl
  have b := auth6_ok c hc l' hl'
  have hd := auth_disj c hc l l' hl hl' hne
  have A1 : (l < 5 ∧ authSibOff c l + 16 ≤ 320) ∨ (l = 5 ∧ 832 ≤ authSibOff c l) := by
    by_cases h : l < 5
    · exact Or.inl ⟨h, a.2.2.1 h⟩
    · exact Or.inr ⟨by omega, a.2.2.2 (by omega)⟩
  have B1 : (l' < 5 ∧ authSibOff c l' + 16 ≤ 320) ∨ (l' = 5 ∧ 832 ≤ authSibOff c l') := by
    by_cases h : l' < 5
    · exact Or.inl ⟨h, b.2.2.1 h⟩
    · exact Or.inr ⟨by omega, b.2.2.2 (by omega)⟩
  unfold sdst sh
  rcases A1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases B1 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> split_ifs <;> omega
theorem sdst_bound (c D k l : Nat) (hc : c < 128) (hk : 48 * k ≤ D) (hl : l < 6) :
    D - 48 * k ≤ sdst c D k l ∧ sdst c D k l + 16 ≤ D + 896 ∧ sdst c D k l % 16 = (D - sh k l) % 16 := by
  obtain ⟨a1, a2, -, -⟩ := auth6_ok c hc l hl
  have := sh_le k l
  unfold sdst
  omega
theorem sibsMem_succ (M : Nat → Word) (c S D k L : Nat) (hc : c < 128) (hk : 48 * k ≤ D) (hL : L < 6) (A : Nat) :
    sibsMem M c S D k (L + 1) A =
      if A = sdst c D k L + 8 then M (S + srcOff c L + 8)
      else if A = sdst c D k L then M (S + srcOff c L) else sibsMem M c S D k L A := by
  unfold sibsMem
  rw [find_range_succ]
  cases h : (List.range L).find? (fun l => decide (A = sdst c D k l ∨ A = sdst c D k l + 8)) with
  | some l =>
    obtain ⟨hl, hp⟩ := find_some h
    simp only [decide_eq_true_eq] at hp
    have hd := sdst_disj c D k hc hk l L (by omega) hL (by omega)
    simp only
    rw [if_neg (show ¬ A = sdst c D k L + 8 by omega), if_neg (show ¬ A = sdst c D k L by omega)]
  | none =>
    simp only
    by_cases h1 : A = sdst c D k L + 8
    · have h2 : ¬ A = sdst c D k L := by omega
      rw [if_pos (show decide (A = sdst c D k L ∨ A = sdst c D k L + 8) = true by simp [h1]),
        if_pos h1]
      simp only
      rw [if_neg h2]
    · by_cases h2 : A = sdst c D k L
      · rw [if_pos (show decide (A = sdst c D k L ∨ A = sdst c D k L + 8) = true by simp [h2]),
          if_neg h1, if_pos h2]
        simp only
        rw [if_pos h2]
      · rw [if_neg (show ¬ decide (A = sdst c D k L ∨ A = sdst c D k L + 8) = true by simp [h1, h2]),
          if_neg h1, if_neg h2]
def zcMem (M : Nat → Word) (S D : Nat) (A : Nat) : Word :=
  if D + 320 ≤ A ∧ A < D + 896 ∧ (A - D - 320) % 8 = 0 then M (S + 448 + (A - D - 320))
  else if D ≤ A ∧ A < D + 320 ∧ (A - D) % 8 = 0 then 0 else M A
/-- Staging region of coordinate `k` after its zero/copy calls and its six sibling stores (r3w: the sibling
stores of coordinate `k ≥ 2` land below `D`, in the previous region). -/
def coordMem (M : Nat → Word) (c S D k : Nat) (A : Nat) : Word := sibsMem (zcMem M S D) c S D k 6 A
theorem sibsMem_out (M : Nat → Word) (c S D k L : Nat) (hc : c < 128) (hk : 48 * k ≤ D) (hL : L ≤ 6) (A : Nat)
    (hA : A < D - 48 * k ∨ D + 896 ≤ A) : sibsMem M c S D k L A = M A := by
  unfold sibsMem
  cases h : (List.range L).find? (fun l => decide (A = sdst c D k l ∨ A = sdst c D k l + 8)) with
  | some l =>
    obtain ⟨hl, hp⟩ := find_some h
    simp only [decide_eq_true_eq] at hp
    have := sdst_bound c D k l hc hk (by omega)
    omega
  | none => rfl
def sibsCyc (L : Nat) : Nat := 14 * L
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem sibs_spec (k : Nat) (hk : k < 9) (c S D : Nat) (hcl : c < 128) (hS : S % 16 = 0)
    (hS' : S + 448 ≤ MEMORY_BYTES) (hD : D % 16 = 0) (hDS : D + 896 ≤ S) (hDP : D + 896 ≤ PLAN)
    (hsh : 48 * k ≤ D) (u : MachineState) (M0 : Nat → Word) (hM : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = M0 A)
    (hpc : u.pc = pcOf (coordAt k + 13)) (h8 : u.getReg .x8 = BitVec.ofNat 64 S)
    (h9 : u.getReg .x9 = BitVec.ofNat 64 D) (h19 : u.getReg .x19 = BitVec.ofNat 64 c)
    (h20 : u.getReg .x20 = BitVec.ofNat 64 (PLAN + 16 * (c % 64))) (hp : PlanAt u) :
    ∀ L ≤ 6, ∃ t, Steps im u (sibsCyc L) (sibsCyc L) t ∧ t.pc = pcOf (coordAt k + 13 + sibsCyc L) ∧
      RegsExcept u t [.x13, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = sibsMem M0 c S D k L A := by
  have hMB : MEMORY_BYTES = 16777216 := rfl
  have hPL : PLAN = 0xff9a00 := rfl
  intro L hL
  induction L with
  | zero => exact ⟨u, Steps.refl u, by simpa [sibsCyc] using hpc, RegsExcept.refl u _, fun A hA => hM A hA⟩
  | succ L ih =>
    obtain ⟨t, st, pt, rt, mt⟩ := ih (by omega)
    have hpL : t.pc = pcOf (sibAt k L) := by
      rw [pt, show coordAt k + 13 + sibsCyc L = sibAt k L by unfold sibAt sibsCyc; omega]
    have hpt : PlanAt t := fun j hj => by
      rw [mt _ (by omega), sibsMem_out M0 c S D k L hcl hsh (by omega) _ (by omega), ← hM _ (by omega)]
      exact hp j hj
    obtain ⟨t', st', pt', rt', mt'⟩ := sib_spec hc k L hk (by omega) t hpL c S D hcl
      (by rw [rt.get (by decide), h8]) (by rw [rt.get (by decide), h9]) (by rw [rt.get (by decide), h19])
      (by rw [rt.get (by decide), h20]) hpt hS hS' hD (by omega) hsh
    have hcyc : sibsCyc L + sibLen L = sibsCyc (L + 1) := by unfold sibsCyc sibLen; split <;> omega
    refine ⟨t', (st.trans st').of_eq hcyc hcyc, ?_, (rt.trans rt').mono (by decide), fun A hA => ?_⟩
    · rw [pt', show sibAt k L + sibLen L = coordAt k + 13 + sibsCyc (L + 1) by
        unfold sibAt; rw [← hcyc]; unfold sibsCyc; omega]
    · have hso := srcOff_bound c L
      rw [mt' A hA, sibsMem_succ M0 c S D k L hcl hsh (by omega) A, mt (S + srcOff c L + 8) (by omega),
        mt (S + srcOff c L) (by omega), mt A hA,
        sibsMem_out M0 c S D k L hcl hsh (by omega) (S + srcOff c L + 8) (Or.inr (by omega)),
        sibsMem_out M0 c S D k L hcl hsh (by omega) (S + srcOff c L) (Or.inr (by omega))]
set_option maxRecDepth 20000 in
theorem coord_spec (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (coordAt k)) (N : HashOutput)
    (hN : OutAt s 0x60 N) (hp : PlanAt s) (S D : Nat) (h8 : s.getReg .x8 = BitVec.ofNat 64 S)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 D) (h18 : s.getReg .x18 = BitVec.ofNat 64 PLAN)
    (hS : S % 16 = 0) (hD : D % 16 = 0) (hDS : D + 896 ≤ S) (hS' : S + 1024 ≤ MEMORY_BYTES)
    (hDP : D + 896 ≤ PLAN) (hsh : 48 * k ≤ D) :
    ∃ t, Steps im s 707 707 t ∧ t.pc = pcOf (coordAt k + 111) ∧
      t.getReg .x8 = BitVec.ofNat 64 (S + 1024) ∧ t.getReg .x9 = BitVec.ofNat 64 (D + 896) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x19, .x20, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        holdMem (fun B => s.getMem (BitVec.ofNat 64 B)) (N.toNat / 2 ^ WCT9.childBase k % 128) S k A
          (coordMem (fun B => s.getMem (BitVec.ofNat 64 B)) (N.toNat / 2 ^ WCT9.childBase k % 128) S D k A) := by
  have hMB : MEMORY_BYTES = 16777216 := rfl
  have hPL : PLAN = 0xff9a00 := rfl
  obtain ⟨c, hcdef⟩ : ∃ c, c = N.toNat / 2 ^ WCT9.childBase k % 128 := ⟨_, rfl⟩
  rw [← hcdef]
  have hcl : c < 128 := by rw [hcdef]; exact Nat.mod_lt _ (by norm_num)
  obtain ⟨t1, s1, p1, r19, r11, r12, r1, g1, f1⟩ := head_spec hc k hk s hpc N hN D h9
  rw [← hcdef] at r19
  obtain ⟨t2, s2, p2, g2, m2⟩ := zero_spec hc t1 p1 D 40 (coordAt k + 6) r11 r12 r1 (by norm_num) (by norm_num)
    (by omega) (by omega)
  obtain ⟨t3, s3, p3, q10, q11, q12, q1, g3, f3⟩ := mid_spec hc k hk t2 p2 S D
    (by rw [g2.get (by decide), g1.get (by decide), h8]) (by rw [g2.get (by decide), g1.get (by decide), h9])
  obtain ⟨t4, s4, p4, g4, m4⟩ := copy_spec hc t3 p3 (S + 448) (D + 320) 72 (coordAt k + 10) q10 q11 q12 q1
    (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
  obtain ⟨t5, s5, p5, w20, g5, f5⟩ := row_spec hc k hk t4 p4 c hcl
    (by rw [g4.get (by decide), g3.get (by decide), g2.get (by decide), r19])
    (by rw [g4.get (by decide), g3.get (by decide), g2.get (by decide), g1.get (by decide), h18])
  have hz : ∀ X < 2 ^ 64, t3.getMem (BitVec.ofNat 64 X) = zeroed t1 D 40 X := fun X hX => by
    rw [f3 X hX (fun h => h), m2 X hX]
  have hM5 : ∀ A < 2 ^ 64, t5.getMem (BitVec.ofNat 64 A) =
      zcMem (fun B => s.getMem (BitVec.ofNat 64 B)) S D A := by
    intro A hA
    rw [f5 A hA (fun h => h), m4 A hA]
    unfold copied zcMem
    by_cases h1 : D + 320 ≤ A ∧ A < D + 896 ∧ (A - D - 320) % 8 = 0
    · rw [if_pos (show D + 320 ≤ A ∧ A < D + 320 + 8 * 72 ∧ (A - (D + 320)) % 8 = 0 by omega), if_pos h1,
        hz _ (by omega)]
      unfold zeroed
      rw [if_neg (by omega), f1 _ (by omega) (fun h => h),
        show S + 448 + (A - (D + 320)) = S + 448 + (A - D - 320) by omega]
    · rw [if_neg (show ¬ (D + 320 ≤ A ∧ A < D + 320 + 8 * 72 ∧ (A - (D + 320)) % 8 = 0) by omega), if_neg h1,
        hz A hA]
      unfold zeroed
      by_cases h2 : D ≤ A ∧ A < D + 320 ∧ (A - D) % 8 = 0
      · rw [if_pos (show D ≤ A ∧ A < D + 8 * 40 ∧ (A - D) % 8 = 0 by omega), if_pos h2]
      · rw [if_neg (show ¬ (D ≤ A ∧ A < D + 8 * 40 ∧ (A - D) % 8 = 0) by omega), if_neg h2,
          f1 A hA (fun h => h)]
  have hp5 : PlanAt t5 := fun j hj => by
    rw [hM5 _ (by omega)]
    unfold zcMem
    rw [if_neg (show ¬ (D + 320 ≤ PLAN + 8 * j ∧ PLAN + 8 * j < D + 896 ∧ (PLAN + 8 * j - D - 320) % 8 = 0) by omega),
      if_neg (show ¬ (D ≤ PLAN + 8 * j ∧ PLAN + 8 * j < D + 320 ∧ (PLAN + 8 * j - D) % 8 = 0) by omega)]
    exact hp j hj
  have e8 : t5.getReg .x8 = BitVec.ofNat 64 S := by
    rw [g5.get (by decide), g4.get (by decide), g3.get (by decide), g2.get (by decide), g1.get (by decide), h8]
  have e9 : t5.getReg .x9 = BitVec.ofNat 64 D := by
    rw [g5.get (by decide), g4.get (by decide), g3.get (by decide), g2.get (by decide), g1.get (by decide), h9]
  have e19 : t5.getReg .x19 = BitVec.ofNat 64 c := by
    rw [g5.get (by decide), g4.get (by decide), g3.get (by decide), g2.get (by decide), r19]
  obtain ⟨t6, s6, p6, g6, m6⟩ := sibs_spec hc k hk c S D hcl hS (by omega) hD (by omega) (by omega) hsh t5 _ hM5
    p5 e8 e9 e19 w20 hp5 6 le_rfl
  obtain ⟨t6', s6', p6', g6', m6'⟩ := sib6_spec hc k hk t6
    (by rw [p6, show coordAt k + 13 + sibsCyc 6 = sibAt k 6 by unfold sibsCyc sibAt; omega]) c S hcl
    (by rw [g6.get (by decide), e8]) (by rw [g6.get (by decide), e19]) hS (by omega)
  obtain ⟨t7, s7, p7, w8, w9, g7, f7⟩ := step_spec hc k hk t6' p6' S D
    (by rw [g6'.get (by decide), g6.get (by decide), e8]) (by rw [g6'.get (by decide), g6.get (by decide), e9])
  have hzS : ∀ o, o < 448 → t6.getMem (BitVec.ofNat 64 (S + o)) = s.getMem (BitVec.ofNat 64 (S + o)) := by
    intro o ho
    rw [m6 _ (by omega), sibsMem_out _ c S D k 6 hcl hsh le_rfl _ (Or.inr (by omega))]
    unfold zcMem; rw [if_neg (by omega), if_neg (by omega)]
  have hso := srcOff_bound c 6
  refine ⟨t7, (((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s6').trans s7).of_eq
    (by unfold sibsCyc; omega) (by unfold sibsCyc; omega), p7, w8, w9,
    (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g6').trans g7).mono (by decide),
    fun A hA => ?_⟩
  rw [f7 A hA (fun h => h), m6' A hA]
  unfold holdMem
  split_ifs
  · rfl
  · rw [show S + srcOff c 6 + 8 = S + (srcOff c 6 + 8) by omega, hzS _ (by omega)]
  · rw [hzS _ (by omega)]
  · rw [m6 A hA]; rfl
end
end ClaudeWCT.W9.Machine.Expand.Compact
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactRun ====
section

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt)
set_option linter.unusedSimpArgs false
/-- Hold word `j` (0, 1: top sibling; 2: flag `1 - bit6`) of coordinate `k`, read from the snapshot. -/
def holdW (M : Nat → Word) (cs : Nat → Nat) (k j : Nat) : Word :=
  if j = 0 then M (SNAP + 1024 * k + srcOff (cs k) 6)
  else if j = 1 then M (SNAP + 1024 * k + srcOff (cs k) 6 + 8)
  else BitVec.ofNat 64 (1 - cs k / 2 ^ 6 % 2)
/-- The written hold words of the first `K` coordinates. -/
abbrev InHold (K A : Nat) : Prop :=
  0x380000 ≤ A ∧ A < 0x380000 + 32 * K ∧ (A - 0x380000) % 8 = 0 ∧ (A - 0x380000) % 32 < 24
/-- Memory after the first `K` coordinates (r3w: recursive; coordinate `k ≥ 2` also writes into region `k - 1`). -/
def allMem (M : Nat → Word) (cs : Nat → Nat) : Nat → Nat → Word
  | 0, A => M A
  | K + 1, A => holdMem (allMem M cs K) (cs K) (SNAP + 1024 * K) K A
      (coordMem (allMem M cs K) (cs K) (SNAP + 1024 * K) (0x840 + 896 * K) K A)
def finalWord (M : Nat → Word) (cs : Nat → Nat) (i : Nat) : Word :=
  if i < 8 then M (0x800 + 8 * i)
  else if i < 1016 then
    match sibSrc (cs ((i - 8) / 112)) ((i - 8) % 112) with
    | some o => M (0x840 + 1024 * ((i - 8) / 112) + o)
    | none => if (i - 8) % 112 < 40 then 0 else M (0x840 + 1024 * ((i - 8) / 112) + 448 + 8 * ((i - 8) % 112 - 40))
  else M (0x800 + 8 * (i + 144))
theorem sibSrc_lt {c j o : Nat} (h : sibSrc c j = some o) : o + 8 ≤ 448 ∧ o % 8 = 0 := by
  unfold sibSrc at h
  cases hl : sibLev c j with
  | none => rw [hl] at h; simp at h
  | some l =>
    rw [hl] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have := srcOff_bound c l
    split at h <;> omega
theorem coordMem_congr (M M' : Nat → Word) (c S D k A : Nat) (hDS : D + 896 ≤ S)
    (hS : ∀ o < 1024, M (S + o) = M' (S + o)) (hA : M A = M' A) :
    coordMem M c S D k A = coordMem M' c S D k A := by
  have hz : ∀ o < 1024, zcMem M S D (S + o) = zcMem M' S D (S + o) := fun o ho => by
    unfold zcMem; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; exact hS o ho
  have hzA : zcMem M S D A = zcMem M' S D A := by
    unfold zcMem
    split_ifs
    · rw [Nat.add_assoc]; exact hS _ (by omega)
    · rfl
    · exact hA
  unfold coordMem sibsMem
  split
  · rename_i l hl
    have := srcOff_bound c l
    split
    · exact hz _ (by omega)
    · rw [Nat.add_assoc]; exact hz _ (by omega)
  · exact hzA
theorem coordMem_out (M : Nat → Word) (c S D k A : Nat) (hc : c < 128) (hk : 48 * k ≤ D)
    (h : A < D - 48 * k ∨ D + 896 ≤ A) : coordMem M c S D k A = M A := by
  unfold coordMem
  rw [sibsMem_out _ c S D k 6 hc hk le_rfl A h]
  unfold zcMem; rw [if_neg (by omega), if_neg (by omega)]
theorem holdMem_congr (M M' : Nat → Word) (c S k A : Nat) (r r' : Word)
    (h1 : M (S + srcOff c 6) = M' (S + srcOff c 6)) (h2 : M (S + srcOff c 6 + 8) = M' (S + srcOff c 6 + 8))
    (hr : r = r') : holdMem M c S k A r = holdMem M' c S k A r' := by
  unfold holdMem; rw [h1, h2, hr]
theorem allMem_out (M : Nat → Word) (cs : Nat → Nat) (hcs : ∀ k, cs k < 128) (K : Nat) (hK : K ≤ 9) (A : Nat)
    (hA : A < 0x840 ∨ 0x840 + 896 * K ≤ A) (hH : ¬ InHold K A) : allMem M cs K A = M A := by
  induction K with
  | zero => rfl
  | succ K ih =>
    have hh : holdAt K = 0x380000 + 32 * K := rfl
    simp only [allMem]
    unfold holdMem
    rw [if_neg (fun e => hH (by unfold InHold; omega)), if_neg (fun e => hH (by unfold InHold; omega)),
      if_neg (fun e => hH (by unfold InHold; omega)),
      coordMem_out _ _ _ _ _ _ (hcs K) (by omega) (by omega)]
    exact ih (by omega) (by omega) (fun h => hH (by unfold InHold at h ⊢; omega))
theorem allMem_hold (M : Nat → Word) (cs : Nat → Nat) (hcs : ∀ k, cs k < 128) :
    ∀ K ≤ 9, ∀ k < K, ∀ j < 3, allMem M cs K (holdAt k + 8 * j) = holdW M cs k j := by
  have hSN : SNAP = 0x200000 := rfl
  intro K hK
  induction K with
  | zero => intro k hk; omega
  | succ K ih =>
    intro k hk j hj
    have hh : ∀ k, holdAt k = 0x380000 + 32 * k := fun _ => rfl
    have hso := srcOff_bound (cs K) 6
    simp only [allMem]
    unfold holdMem
    by_cases hkK : k = K
    · rw [hkK]
      unfold holdW
      interval_cases j
      · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos rfl,
          allMem_out _ _ hcs K (by omega) _ (Or.inr (by omega)) (by unfold InHold; omega)]
      · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos rfl,
          allMem_out _ _ hcs K (by omega) _ (Or.inr (by omega)) (by unfold InHold; omega)]
      · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg (by simp only [hh]; omega), if_neg (by simp only [hh]; omega), if_neg (by simp only [hh]; omega),
        coordMem_out _ _ _ _ _ _ (hcs K) (by omega) (Or.inr (by simp only [hh]; omega))]
      exact ih (by omega) k (by omega) j hj
/-- Hold word `j` of coordinate `k` in terms of the first-pass scratch regions at `0x840`. -/
def holdVal (M : Nat → Word) (cs : Nat → Nat) (k j : Nat) : Word :=
  if j = 0 then M (0x840 + 1024 * k + srcOff (cs k) 6)
  else if j = 1 then M (0x840 + 1024 * k + srcOff (cs k) 6 + 8)
  else BitVec.ofNat 64 (1 - cs k / 2 ^ 6 % 2)
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem coords_spec (N : HashOutput) (s : MachineState) (hpc : s.pc = pcOf (coordAt 0)) (hN : OutAt s 0x60 N)
    (hp : PlanAt s) (h8 : s.getReg .x8 = BitVec.ofNat 64 SNAP) (h9 : s.getReg .x9 = BitVec.ofNat 64 0x840)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 PLAN) :
    ∀ K ≤ 9, ∃ t, Steps im s (707 * K) (707 * K) t ∧ t.pc = pcOf (coordAt K) ∧
      t.getReg .x8 = BitVec.ofNat 64 (SNAP + 1024 * K) ∧ t.getReg .x9 = BitVec.ofNat 64 (0x840 + 896 * K) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x19, .x20, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        allMem (fun B => s.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) K A := by
  have hMB : MEMORY_BYTES = 16777216 := rfl
  have hPL : PLAN = 0xff9a00 := rfl
  have hSN : SNAP = 0x200000 := rfl
  intro K hK
  induction K with
  | zero =>
    exact ⟨s, Steps.refl s, hpc, by simpa using h8, by simpa using h9, RegsExcept.refl s _, fun A hA => rfl⟩
  | succ K ih =>
    obtain ⟨t, st, pt, t8, t9, rt, mt⟩ := ih (by omega)
    have hcs : ∀ k, N.toNat / 2 ^ WCT9.childBase k % 128 < 128 := fun _ => Nat.mod_lt _ (by norm_num)
    have hNt : OutAt t 0x60 N := fun j hj => by
      rw [mt _ (by omega), allMem_out _ _ hcs K (by omega) _ (Or.inl (by omega)) (by unfold InHold; omega)]
      exact hN j hj
    have hpt : PlanAt t := fun j hj => by
      rw [mt _ (by omega), allMem_out _ _ hcs K (by omega) _ (Or.inr (by omega)) (by unfold InHold; omega)]
      exact hp j hj
    obtain ⟨t', st', pt', t8', t9', rt', mt'⟩ := coord_spec hc K (by omega) t pt N hNt hpt (SNAP + 1024 * K)
      (0x840 + 896 * K) t8 t9 (by rw [rt.get (by decide), h18]) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    refine ⟨t', (st.trans st').of_eq (by ring) (by ring), ?_, ?_, ?_, (rt.trans rt').mono (by decide),
      fun A hA => ?_⟩
    · rw [pt', show coordAt K + 111 = coordAt (K + 1) by unfold coordAt; ring]
    · rw [t8', show SNAP + 1024 * K + 1024 = SNAP + 1024 * (K + 1) by ring]
    · rw [t9', show 0x840 + 896 * K + 896 = 0x840 + 896 * (K + 1) by ring]
    · have e := coordMem_congr (fun B => t.getMem (BitVec.ofNat 64 B))
        (allMem (fun B => s.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) K)
        (N.toNat / 2 ^ WCT9.childBase K % 128) (SNAP + 1024 * K) (0x840 + 896 * K) K A (by omega)
        (fun o ho => mt _ (by omega)) (mt A hA)
      have hso := srcOff_bound (N.toNat / 2 ^ WCT9.childBase K % 128) 6
      rw [mt' A hA, holdMem_congr _ (allMem (fun B => s.getMem (BitVec.ofNat 64 B))
        (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) K) _ _ _ _ _ _ (mt _ (by omega)) (mt _ (by omega)) e]
      rfl
end
end ClaudeWCT.W9.Machine.Expand.Compact


namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem run_spec_framed (N : HashOutput) (s : MachineState) (hpc : s.pc = pcOf 41108) (hN : OutAt s 0x60 N)
    (hp : PlanAt s) :
    ∃ t, Steps im s 23576 23576 t ∧ t.pc = pcOf 42142 ∧ RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x10, .x11, .x12,
        .x13, .x18, .x19, .x20, .x28, .x29, .x30, .x31] ∧
      (∀ i < 2729, (i < 8 ∨ 1016 ≤ i) → t.getMem (BitVec.ofNat 64 (0x800 + 8 * i)) =
        finalWord (fun B => s.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) i) ∧
      (∀ k < 9, ∀ j < 3, t.getMem (BitVec.ofNat 64 (holdAt k + 8 * j)) =
        holdVal (fun B => s.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) k j) ∧
      ∀ A < 2 ^ 64, (A < 0x800 ∨ 0x800 + 8 * 2729 ≤ A) →
        (A < SNAP ∨ SNAP + 9216 ≤ A) → ¬ InHold 9 A →
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  have hMB : MEMORY_BYTES = 16777216 := rfl
  have hPL : PLAN = 0xff9a00 := rfl
  have hSN : SNAP = 0x200000 := rfl
  have hcs : ∀ k, N.toNat / 2 ^ WCT9.childBase k % 128 < 128 := fun _ => Nat.mod_lt _ (by norm_num)
  obtain ⟨u1, s1, p1, a10, a11, a12, a1, g1, f1⟩ := start_spec hc s hpc
  obtain ⟨u2, s2, p2, g2, m2⟩ := copy_spec hc u1 p1 0x840 SNAP 1152 41115 a10 a11 a12 a1 (by norm_num)
    (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (Or.inr (by omega))
  obtain ⟨u3, s3, p3, b8, b9, b18, g3, f3⟩ := regs_spec hc u2 p2
  have hM3 : ∀ A < 2 ^ 64, u3.getMem (BitVec.ofNat 64 A) = copied u1 0x840 SNAP 1152 A := fun A hA => by
    rw [f3 A hA (fun h => h), m2 A hA]
  have hlo : ∀ A < SNAP, u3.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA => by
    rw [hM3 A (by omega)]; unfold copied; rw [if_neg (by omega), f1 A (by omega) (fun h => h)]
  have hsn : ∀ o, o < 9216 → o % 8 = 0 →
      u3.getMem (BitVec.ofNat 64 (SNAP + o)) = s.getMem (BitVec.ofNat 64 (0x840 + o)) := fun o ho ho' => by
    rw [hM3 _ (by omega)]; unfold copied
    rw [if_pos (by omega), f1 _ (by omega) (fun h => h), show SNAP + o - SNAP = o by omega]
  have hN3 : OutAt u3 0x60 N := fun j hj => by rw [hlo _ (by omega)]; exact hN j hj
  have hp3 : PlanAt u3 := fun j hj => by
    rw [hM3 _ (by omega)]; unfold copied
    rw [if_neg (by omega), f1 _ (by omega) (fun h => h)]; exact hp j hj
  obtain ⟨u4, s4, p4, c8, c9, g4, m4⟩ := coords_spec hc N u3 p3 hN3 hp3 b8 b9 b18 9 le_rfl
  obtain ⟨u5, s5, p5, d10, d11, d12, d1, g5, f5⟩ := final_spec hc u4 (by rw [p4]; rfl)
  obtain ⟨u6, s6, p6, g6, m6⟩ := copy_spec hc u5 p5 (0x800 + 9280) (0x800 + 8128) 1713 42127 d10 d11 d12 d1
    (by norm_num) (by norm_num) (by norm_num) (by omega) (by norm_num) (by omega) (Or.inl (by norm_num))
  obtain ⟨u7, s7, p7, g7, f7⟩ := halt_spec hc u6 p6
  have h4 : ∀ A < 2 ^ 64, u5.getMem (BitVec.ofNat 64 A) =
      allMem (fun B => u3.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) 9 A :=
    fun A hA => by rw [f5 A hA (fun h => h), m4 A hA]
  refine ⟨u7, ((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).of_eq (by norm_num)
    (by norm_num), p7, (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).mono (by decide)),
    fun i hi hi' => ?_, fun k hk j hj => ?_, fun A hA hA' hSnap hH => ?_⟩
  rotate_left
  · have hH : holdAt k = 0x380000 + 32 * k := rfl
    have hso := srcOff_bound (N.toNat / 2 ^ WCT9.childBase k % 128) 6
    rw [f7 _ (by omega) (fun h => h), m6 _ (by omega)]
    unfold copied
    rw [if_neg (by omega), h4 _ (by omega), allMem_hold _ _ hcs 9 le_rfl k hk j hj]
    unfold holdW holdVal
    beta_reduce
    split_ifs
    · try dsimp only
      rw [show SNAP + 1024 * k + srcOff (N.toNat / 2 ^ WCT9.childBase k % 128) 6 =
          SNAP + (1024 * k + srcOff (N.toNat / 2 ^ WCT9.childBase k % 128) 6) by omega,
        hsn _ (by omega) (by omega)]
      congr 2; omega
    · try dsimp only
      rw [show SNAP + 1024 * k + srcOff (N.toNat / 2 ^ WCT9.childBase k % 128) 6 + 8 =
          SNAP + (1024 * k + srcOff (N.toNat / 2 ^ WCT9.childBase k % 128) 6 + 8) by omega,
        hsn _ (by omega) (by omega)]
      congr 2; omega
    · rfl
  · rw [f7 A hA (fun h => h), m6 A hA]
    unfold copied
    rw [if_neg (by omega), h4 A hA, allMem_out _ _ hcs 9 le_rfl A (by omega) hH, hM3 A hA]
    unfold copied
    rw [if_neg (by omega), f1 A hA (fun h => h)]
  rw [f7 _ (by omega) (fun h => h), m6 _ (by omega)]
  unfold copied finalWord
  by_cases ht : 1016 ≤ i
  · rw [if_pos (show 0x800 + 8128 ≤ 0x800 + 8 * i ∧ 0x800 + 8 * i < 0x800 + 8128 + 8 * 1713 ∧
        (0x800 + 8 * i - (0x800 + 8128)) % 8 = 0 by omega), if_neg (show ¬ i < 8 by omega),
      if_neg (show ¬ i < 1016 by omega), h4 _ (by omega),
      allMem_out _ _ hcs 9 le_rfl _ (Or.inr (by omega)) (by unfold InHold; omega)]
    rw [hlo _ (by omega),
      show 0x800 + 9280 + (0x800 + 8 * i - (0x800 + 8128)) = 0x800 + 8 * (i + 144) by omega]
  · have h8 : i < 8 := by omega
    rw [if_neg (show ¬ (0x800 + 8128 ≤ 0x800 + 8 * i ∧ 0x800 + 8 * i < 0x800 + 8128 + 8 * 1713 ∧
        (0x800 + 8 * i - (0x800 + 8128)) % 8 = 0) by omega), h4 _ (by omega), if_pos h8,
      allMem_out _ _ hcs 9 le_rfl _ (Or.inl (by omega)) (by unfold InHold; omega), hlo _ (by omega)]
end
end ClaudeWCT.W9.Machine.Expand.Compact
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_PairCopy ====
section

/-! # Pairing stage 1: the lower-chain pair copy block (expand words 48000 .. 48017)

The witness constructor's lower-layer chain copy (`jal ra,48000` at 42241 / 42414 / 42563, with `a0` = the staging
chain area of the layer (43 blocks of 64 bytes, chain 42 first, value at block offset 48) and `a1` = the final paired
chain area) runs

```
48000  addi a2,zero,21
48001  ld t1,48(a0);  sd t1,88(a1)     -- F chain 2p+2's value  -> pair offset 88
       ld t1,56(a0);  sd t1,96(a1)
       ld t1,112(a0); sd t1,16(a1)     -- G chain 2p+1's value  -> pair offset 16
       ld t1,120(a0); sd t1,24(a1)
       addi a0,a0,128; addi a1,a1,104; addi a2,a2,-1; bne a2,zero,48001
48013  ld t1,48(a0); sd t1,48(a1); ld t1,56(a0); sd t1,56(a1)   -- chain 0's value at offset 48 of its F block
       jalr zero,0(ra)
```

It writes only value words; the pair gaps keep the constructor's zero fill. -/

namespace ClaudeWCT.W9.Machine.Expand.PairCopy
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC ofNat_sub_one)
set_option linter.unusedSimpArgs false

sym_block RPC0 := symRun cfgC cPC0 (pcOf 48000) 40
sym_block RPCL := symRun cfgC cPCL (pcOf 48001) 40
sym_block RPCT := symRun cfgC cPCT (pcOf 48013) 40

/-- Source offset (in a 128-byte staging block pair) of a written pair offset. -/
def srcOff (r : Nat) : Nat := if r = 16 then 112 else if r = 24 then 120 else if r = 88 then 48 else 56
/-- Memory after `i` loop iterations. -/
def pcMem (M : Nat → Word) (src dst i A : Nat) : Word :=
  if dst ≤ A ∧ A < dst + 104 * i ∧ isVal ((A - dst) % 104) then
    M (src + 128 * ((A - dst) / 104) + srcOff ((A - dst) % 104)) else M A
/-- Memory after the whole block (21 pairs and chain 0's value). -/
def pairCopyMem (M : Nat → Word) (src dst A : Nat) : Word :=
  if A = dst + 104 * 21 + 48 then M (src + 128 * 21 + 48)
  else if A = dst + 104 * 21 + 56 then M (src + 128 * 21 + 56)
  else pcMem M src dst 21 A

section
variable {im : Image} (hc : Code im)
include hc
set_option maxRecDepth 20000 in
theorem pc_iter (s : MachineState) (hpc : s.pc = pcOf 48001) (src dst n : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (n + 1)) (hn : n + 1 < 2 ^ 32)
    (hs : src % 8 = 0) (hs' : src + 128 ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 104 ≤ MEMORY_BYTES)
    (hov : dst + 104 ≤ src) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = (if n = 0 then pcOf 48013 else pcOf 48001) ∧
      t.getReg .x10 = BitVec.ofNat 64 (src + 128) ∧ t.getReg .x11 = BitVec.ofNat 64 (dst + 104) ∧
      t.getReg .x12 = BitVec.ofNat 64 n ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = dst + 24 then s.getMem (BitVec.ofNat 64 (src + 120))
        else if A = dst + 16 then s.getMem (BitVec.ofNat 64 (src + 112))
        else if A = dst + 96 then s.getMem (BitVec.ofNat 64 (src + 56))
        else if A = dst + 88 then s.getMem (BitVec.ofNat 64 (src + 48))
        else s.getMem (BitVec.ofNat 64 A)) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  refine ⟨_, symRun_sound RPCL hc.cL s hpc (by
    simp [RPCL.res, rv_simp, accessValid_iff, h10, h11, BitVec.toNat_ofNat, ofNat_add_ofNat]
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, hM]; omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RPCL.res, E.eval, CmpOp.eval, BinOp.eval, h12]
    rw [ofNat_sub_one n]
    by_cases h0 : n = 0
    · subst h0; simp
    · have : (BitVec.ofNat 64 n != 0#64) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h; apply h0
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        omega
      simp [this, h0]
  · simp [RPCL.res, rv_simp, h10, ofNat_add_ofNat]
  · simp [RPCL.res, rv_simp, h11, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, RPCL.res, RegFile.get, E.eval, BinOp.eval, h12]
    rw [ofNat_sub_one]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    cases r <;> simp_all [rv_simp, RPCL.res] <;> rfl
  · intro A hA
    have k24 := ofNat_inj hA (show dst + 24 < 2 ^ 64 by omega)
    have k16 := ofNat_inj hA (show dst + 16 < 2 ^ 64 by omega)
    have k96 := ofNat_inj hA (show dst + 96 < 2 ^ 64 by omega)
    have k88 := ofNat_inj hA (show dst + 88 < 2 ^ 64 by omega)
    simp only [Result.toState_getMem, RPCL.res, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval, h10, h11,
      ofNat_add_ofNat, k24, k16, k96, k88]

structure PCInv (s : MachineState) (src dst i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if i < 21 then pcOf 48001 else pcOf 48013)
  x10 : t.getReg .x10 = BitVec.ofNat 64 (src + 128 * i)
  x11 : t.getReg .x11 = BitVec.ofNat 64 (dst + 104 * i)
  x12 : t.getReg .x12 = BitVec.ofNat 64 (21 - i)
  regs : RegsExcept s t [.x6, .x10, .x11, .x12]
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = pcMem (fun B => s.getMem (BitVec.ofNat 64 B)) src dst i A

theorem pc_loop (s : MachineState) (hpc : s.pc = pcOf 48001) (src dst : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 21)
    (hs : src % 8 = 0) (hs' : src + 128 * 22 ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hov : dst + 104 * 22 ≤ src) :
    ∀ i, i ≤ 21 → ∃ t, Steps im s (12 * i) (12 * i) t ∧ PCInv s src dst i t := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, ⟨by rw [hpc, if_pos (by omega)], by simpa using h10, by simpa using h11,
      by simpa using h12, fun r _ => rfl, fun A _ => ?_⟩⟩
    unfold pcMem; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf 48001 := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u10, u11, u12, ru, mu⟩ := pc_iter hc t hpc' (src + 128 * i) (dst + 104 * i) (20 - i)
      hI.x10 hI.x11 (by rw [hI.x12]; congr 1; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : 20 - i = 0
      · rw [if_pos h, if_neg (by omega)]
      · rw [if_neg h, if_pos (by omega)]
    · rw [u10, show src + 128 * i + 128 = src + 128 * (i + 1) by ring]
    · rw [u11, show dst + 104 * i + 104 = dst + 104 * (i + 1) by ring]
    · rw [u12, show 20 - i = 21 - (i + 1) by omega]
    · exact (hI.regs.trans ru).mono (by decide)
    · intro A hA
      have hsrc : ∀ x, x < 128 → t.getMem (BitVec.ofNat 64 (src + 128 * i + x)) =
          s.getMem (BitVec.ofNat 64 (src + 128 * i + x)) := fun x hx => by
        rw [hI.mem _ (by omega)]; unfold pcMem; rw [if_neg (by omega)]
      rw [mu A hA, hsrc 120 (by omega), hsrc 112 (by omega), hsrc 56 (by omega), hsrc 48 (by omega), hI.mem A hA]
      unfold pcMem
      by_cases hn : dst + 104 * i ≤ A ∧ A < dst + 104 * i + 104
      · have hq : (A - dst) / 104 = i := by omega
        have hr : (A - dst) % 104 = A - (dst + 104 * i) := by omega
        by_cases a24 : A = dst + 104 * i + 24
        · subst a24; rw [if_pos rfl, if_pos ⟨by omega, by omega, by unfold isVal; omega⟩, hq, hr]
          simp [srcOff]
        rw [if_neg a24]
        by_cases a16 : A = dst + 104 * i + 16
        · subst a16; rw [if_pos rfl, if_pos ⟨by omega, by omega, by unfold isVal; omega⟩, hq, hr]
          simp [srcOff]
        rw [if_neg a16]
        by_cases a96 : A = dst + 104 * i + 96
        · subst a96; rw [if_pos rfl, if_pos ⟨by omega, by omega, by unfold isVal; omega⟩, hq, hr]
          simp [srcOff]
        rw [if_neg a96]
        by_cases a88 : A = dst + 104 * i + 88
        · subst a88; rw [if_pos rfl, if_pos ⟨by omega, by omega, by unfold isVal; omega⟩, hq, hr]
          simp [srcOff]
        rw [if_neg a88, if_neg (fun h => by unfold isVal at h; omega), if_neg (fun h => by unfold isVal at h; omega)]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        by_cases hin : dst ≤ A ∧ A < dst + 104 * i ∧ isVal ((A - dst) % 104)
        · rw [if_pos hin, if_pos ⟨hin.1, by omega, hin.2.2⟩]
        · rw [if_neg hin, if_neg (fun h => hin ⟨h.1, by omega, h.2.2⟩)]

set_option maxRecDepth 100000 in
/-- The whole pair copy block: from 48000 back to `ret` (`ra`), 1 + 12 * 21 + 5 = 258 steps. -/
theorem pairCopy_spec (s : MachineState) (hpc : s.pc = pcOf 48000) (src dst ret : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 src) (h11 : s.getReg .x11 = BitVec.ofNat 64 dst)
    (h1 : s.getReg .x1 = pcOf ret)
    (hs : src % 8 = 0) (hs' : src + 128 * 22 ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hov : dst + 104 * 22 ≤ src) :
    ∃ t, Steps im s 258 258 t ∧ t.pc = pcOf ret ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      (∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = pairCopyMem (fun B => s.getMem (BitVec.ofNat 64 B)) src dst A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  obtain ⟨u, su, pu, u12, ur, uf⟩ : ∃ u, Steps im s 1 1 u ∧ u.pc = pcOf 48001 ∧
      u.getReg .x12 = BitVec.ofNat 64 21 ∧ RegsExcept s u [.x12] ∧ Frame s u (fun _ => False) := by
    refine ⟨_, symRun_sound RPC0 hc.c0 s hpc (by simp [RPC0.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [RPC0.res, E.eval]
    · simp [RPC0.res, rv_simp] <;> rfl
    · intro r hr; simp at hr; cases r <;> simp_all [RPC0.res, rv_simp] <;> rfl
    · intro A _ _; simp [RPC0.res, rv_simp]
  obtain ⟨t, st, hI⟩ := pc_loop hc u pu src dst (by rw [ur.get (by simp)]; exact h10)
    (by rw [ur.get (by simp)]; exact h11) u12 hs hs' hd hov 21 le_rfl
  have tpc : t.pc = pcOf 48013 := by rw [hI.pc, if_neg (by omega)]
  have hobl : Oblig.all t RPCT.res.st.obl := by
    simp [RPCT.res, rv_simp, accessValid_iff, hI.x10, hI.x11, BitVec.toNat_ofNat, ofNat_add_ofNat]
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, hM]; omega
  have sT := symRun_sound RPCT hc.cT t tpc hobl
  have hmu : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => uf.get hA (by simp)
  refine ⟨_, ((su.trans st).trans sT).of_eq (by simp [RPCT.res]) (by simp [RPCT.res]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RPCT.res, E.eval]
    rw [hI.regs.get (by simp), ur.get (by simp), h1]
    exact pcOf_and_not1 ret
  · have r3 : RegsExcept t (RPCT.res.toState t) [.x6] := by
      intro r hr; simp at hr; cases r <;> simp_all [RPCT.res, rv_simp] <;> rfl
    exact ((ur.trans hI.regs).trans r3).mono (by simp)
  · intro A hA
    have k48 := ofNat_inj hA (show dst + 104 * 21 + 48 < 2 ^ 64 by omega)
    have k56 := ofNat_inj hA (show dst + 104 * 21 + 56 < 2 ^ 64 by omega)
    have e : ∀ x, x < 128 → t.getMem (BitVec.ofNat 64 (src + 128 * 21 + x)) =
        s.getMem (BitVec.ofNat 64 (src + 128 * 21 + x)) := fun x hx => by
      rw [hI.mem _ (by omega)]; unfold pcMem; rw [if_neg (by omega)]; exact hmu _ (by omega)
    simp only [Result.toState_getMem, RPCT.res, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval, hI.x10,
      hI.x11, ofNat_add_ofNat, k48, k56]
    rw [show src + 128 * 21 + 56 = src + 128 * 21 + 56 from rfl, e 56 (by omega), e 48 (by omega), hI.mem A hA]
    unfold pairCopyMem pcMem
    have hso : srcOff ((A - dst) % 104) ≤ 120 := by unfold srcOff; split_ifs <;> omega
    split_ifs <;> first | rfl | (exact hmu _ (by omega)) | omega
end
end ClaudeWCT.W9.Machine.Expand.PairCopy
end
