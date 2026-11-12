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

set_option debug.skipKernelTC false
set_option linter.all false

-- ==== merged from T3M_Expand_LayerBlocks ====
section

section
namespace SigGolfCandidate.T3M.Expand.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
abbrev ENC : Nat := 0x20260
end SigGolfCandidate.T3M.Expand.BCBlocks
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
abbrev CHAIN : Nat := 0x201A0
abbrev LEAFPK : Nat := 0x20600
def e_slT : List (BitVec 32) := [34475539,0xc40d706f]
sym_block eb_slT := symRun { noAlias := true } e_slT (pcOf 42763) 30
/-- C3 (FULL): extra steps of the chain tail trampoline over the old `addi s4; jal` (2 steps). -/
def trXE (lay i m : Nat) : Nat := if i ≠ 0 then 2 else if lay = 0 then 3 else if m = 6 then 10 else 5
theorem trXE_le (lay i m : Nat) : trXE lay i m ≤ 10 := by unfold trXE; split_ifs <;> omega
def slotOff (_lay : T3.Layer) (c : Nat) : Nat := if c = 0 then 0 else 16 * c + 16
def slK (_lay : T3.Layer) (i : Nat) : Nat := if i = 0 then 5 else 6
section blocks
variable (s : MachineState)
/-- the node tweak words written at `NODE + 16` / `NODE + 24`: `WCT9.merkleTweak` (C2 packed word for lower layers). -/
theorem merkleTweak_words_top (tree heap : Nat) (h1 : 1 ≤ heap) (hh : heap < 4096) :
    (ClaudeWCT.WCT9.merkleTweak 0 tree heap).extractLsb' 0 64 = BitVec.ofNat 64 (if heap = 1 then 856064 else if heap = 7 then 520192 else heap) ∧
    (ClaudeWCT.WCT9.merkleTweak 0 tree heap).extractLsb' 64 64 = 0 := by
  rw [ClaudeWCT.WCT9.merkleTweak_top_low, ClaudeWCT.WCT9.merkleTweak_top_high, T3.topNodeWord_eq h1 hh]
  exact ⟨rfl, rfl⟩
end blocks
end SigGolfCandidate.T3M.Expand
end

namespace SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand.BCBlocks
variable {im : Image}          
end SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
/-! img-v6 top-node nonce routine (words 43195 .. 43249, hooked at 1139 `jal 43195`; topfold-v6, NOTES V49). -/
def nonce_E : List (BitVec 32) := [0x4000e13,0x40ee0e33,0xfff00f93,0x1cf9fb3,0xb00e13,0x1c69663]
def expHdrK (lay : T3.Layer) : Nat := if lay.val = 0 then 32 else if lay.val = 1 then 35 else 36
theorem expHdrK_le (lay : T3.Layer) : expHdrK lay ≤ 36 := by unfold expHdrK; split_ifs <;> omega
variable {im : Image}          
variable                    [PackedBlocks.Code im]
variable (s : MachineState)
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
variable {im : Image}           (s : MachineState)
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
theorem nonce_words_aux (n : Nat) (hn : n < 2 ^ 64) : wordsOf (nonceBytes n) = [BitVec.ofNat 64 n, 0] := by
  unfold nonceBytes
  rw [wordsOf_bytesLE16]
  congr 1
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    have h0 : n % 2 ^ 64 % 2 ^ 128 / 2 ^ 64 = 0 := by omega
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h0, Nat.zero_mod]
    rfl
theorem frame_readWordsG {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (A : Nat) :
    ∀ m, A + 8 * m ≤ 2 ^ 64 → (∀ i < m, ¬ W (A + 8 * i)) →
      t.readWords (BitVec.ofNat 64 A) m = s.readWords (BitVec.ofNat 64 A) m
  | 0, _, _ => rfl
  | m + 1, hA, hW => by
    rw [readWords_add, readWords_add, frame_readWordsG h A m (by omega) (fun i hi => hW i (by omega)),
      readWords_one, readWords_one, h.get (by omega) (hW m (by omega))]
/-! U16b expand grind stub (words 54800..54885): block specs. -/

section blocks
variable {im : Image}           (s : MachineState)

end blocks

/-! U16b grind stub: tweak-word arithmetic. -/

/-- The lower node word as a number (`lowerNodeWord (lay - 1) tree heap`, heaps `< 128`; L-hyper A: the marker
`2 ^ (hyperW (lay - 1) + 16)`, honest trees). -/
def lowTw (lay tree heap : Nat) : Nat := 1920 + heap + tree * 2 ^ 16 + 2 ^ (T3.hyperW (lay - 1) + 16)
theorem ult0D (q : Nat) (hq : q < 2 ^ 64) : (0#64 : Word).ult (BitVec.ofNat 64 q) = decide (0 < q) := by
  have h : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  simp [BitVec.ult, h]
section cls
variable {im : Image}          

end cls

/-! U16b grind stub: loop setup and the zero test. -/

section setup
variable {im : Image}          

end setup

/-! U16b grind stub: node input, zero test, trial invariant. -/

theorem inputN_length (lay tree heap n : Nat) (l r : Digest) : (lowerNodeInputN lay tree heap n l r).length = 64 := by
  simp [lowerNodeInputN, nonceBytes, bytesLE_length]

section sim
variable {im : Image} {sk : BitVec 256}
end sim

theorem inputN_blocks (lay tree heap n : Nat) (l r : Digest) :
    (toQ (pad64 (lowerNodeInputN lay tree heap n l r))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [inputN_length]),
    blocks_toQ ⟨by rw [inputN_length]; omega, by rw [inputN_length]⟩, inputN_length]

section found
variable {im : Image}          

end found

/-! U16b grind stub: the search loop and the whole stub (word 1138 -> 1139). -/

section loop
variable {im : Image}           (sk : BitVec 256)

/-- Cycles of the stub on a lower node (word 1138 to 1139): E11: 65 off the ground; on a ground heap at most
`104 + 16 (cap - 1)` (16 per failed trial). -/
def stubW (lay heap : Nat) : Nat :=
  if lowerZeroBits lay heap = 0 then 72 else 118 + 16 * (lowerNonceCap lay heap - 1)

end loop

/-! U16b grind stub: the pass-through of a non-lower node (top tree). -/

section pass
variable {im : Image}           {sk : BitVec 256}

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
theorem tb_shortHash_bind' {β : Type} {s : MachineState} {input : List UInt8} {W : Nat}
    {f : T3.Digest → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (T3.pad64 input))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim image sk s (8 * (toQ (T3.pad64 input)).blocks + W) (T3.shortHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_shortHash, map_eq_bind_pure_comp, bind_assoc]
  refine Sim.query_bind hf ht0 hv hq (fun a => ?_)
  have := h a
  unfold TBSim at this
  simpa only [Function.comp, pure_bind] using this
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
structure ChainCtx (lay tree leaf i : Nat) (t : MachineState) : Prop where
  x5 : t.getReg .x5 = 0
  x8 : t.getReg .x8 = BitVec.ofNat 64 lay
  x9 : t.getReg .x9 = BitVec.ofNat 64 tree
  x18 : t.getReg .x18 = BitVec.ofNat 64 leaf
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  z0 : t.getMem (BitVec.ofNat 64 CHAIN) = 0
  z8 : t.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
/-- Pairing stage 1: a chain step writes the header words and `CHAIN+32 .. CHAIN+112` (G: pads, header copy and the
interior output at `CHAIN+32`; F: the pad `CHAIN+32/40`, the output at `CHAIN+48`). -/
def StepW (A : Nat) : Prop := (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 112)
section chain
variable {sk : BitVec 256}
def oneRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x23, .x28, .x29, .x30]
def OneW (lay : T3.Layer) (i W : Nat) (A : Nat) : Prop :=
  StepW A ∨ A = LEAFPK + slotOff lay i ∨ A = LEAFPK + slotOff lay i + 8 ∨ A = W + 48 ∨ A = W + 56
def ChW (lay : T3.Layer) (WC k : Nat) (A : Nat) : Prop :=
  StepW A ∨ (∃ c < k, A = LEAFPK + slotOff lay c ∨ A = LEAFPK + slotOff lay c + 8) ∨
    (∃ c < k, A = WC - 64 * c + 48 ∨ A = WC - 64 * c + 56)
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
variable {im : Image}                              [PackedBlocks.Code im] {sk : BitVec 256}
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
def lR1 (lay : Layer) : Nat := ![332, 308, 285, 262] lay
def lP (lay : Layer) : Nat := ![0x7890, 0x7cb0, 0x7fd0, 0x82e0] lay
theorem route_fst (index : Nat) (lay : Layer) :
    (route index lay).1 = index / 2 ^ ((![19, 12, 6, 0] : Layer → Nat) lay) % 2 ^ height lay := rfl
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
theorem so47_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 47)) (x y : Nat)
    (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) (hhi : s.getReg .x23 = BitVec.ofNat 64 x)
    (hlo : s.getReg .x22 = BitVec.ofNat 64 y) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if y ≤ x then pcOf (b + 51) else pcOf (b + 48)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_47 hK.2.1) (codeAt_k_47 hK) s hpc (by simp [st_47, blk354_47.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_47, rebase, blk354_47.res, E.eval, CmpOp.eval, hhi, hlo]
    rw [ofNat_slt _ _ hx hy]
    by_cases h : y ≤ x
    · simp [h, show ¬ x < y by omega]
    · simp [h, show x < y by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_47, blk354_47.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_47, blk354_47.res, rv_simp]
theorem so48_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 48)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 51) ∧ t.getReg .x22 = s.getReg .x23 ∧
      t.getReg .x23 = s.getReg .x22 ∧ RegsExcept s t [.x7, .x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_48 hK.2.1) (codeAt_k_48 hK) s hpc (by simp [st_48, blk354_48.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_48, blk354_48.res, E.eval]
  · simp [st_48, blk354_48.res, rv_simp]
  · simp [st_48, blk354_48.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_48, blk354_48.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_48, blk354_48.res, rv_simp]
theorem so51_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 51)) (x y : Nat)
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h1 : s.getReg .x22 = BitVec.ofNat 64 x)
    (h2 : s.getReg .x23 = BitVec.ofNat 64 y) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if x = y then pcOf (b + 101) else pcOf (b + 52)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_51 hK.2.1) (codeAt_k_51 hK) s hpc (by simp [st_51, blk354_51.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_51, rebase, blk354_51.res, E.eval, CmpOp.eval, h1, h2]
    by_cases h : x = y
    · simp [h]
    · simp [h, ofNat_inj hx hy]
  · intro r hr; simp at hr; cases r <;> simp_all [st_51, blk354_51.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_51, blk354_51.res, rv_simp]
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
section blocks
variable {image : Image} {d b : Nat}
theorem ds14_fetch (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 14)) :
    fetch image s = some (.base .ECALL) :=
  ((codeAt_ds_14 hD).fetch s hpc).trans rfl
theorem ds15_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 15)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (gatePc b) ∧ t.getReg .x1 = pcOf (d + 16) ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds15 hD.2) (codeAt_ds_15 hD) s hpc
    (by simp [stds_15, blkds30_15.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [pcEds_15, E.eval]
  · simp [stds_15, blkds30_15.res, rv_simp, RegFile.set]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_15, blkds30_15.res, rv_simp, RegFile.set] <;> rfl
  · intro A _ _; simp [stds_15, blkds30_15.res, rv_simp]
theorem ds17_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 17)) (i : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (d + 0) ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds17 hD.2) (codeAt_ds_17 hD) s hpc
    (by simp [stds_17, blkds30_17.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [pcEds_17, E.eval]
  · simp only [Result.toState_getReg, stds_17, blkds30_17.res]
    t3n [h19]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_17, blkds30_17.res, rv_simp] <;> rfl
  · intro A _ _; simp [stds_17, blkds30_17.res, rv_simp]
end blocks
abbrev dsRegs : List Reg :=
  [.x1, .x6, .x7, .x10, .x11, .x12, .x13, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x28, .x29, .x30]
def DsW (X : Nat) : Prop :=
  X = DIG + 16 ∨ X = DIG + 24 ∨ (NBUF ≤ X ∧ X < NBUF + 32) ∨ (SEL ≤ X ∧ X < SEL + 168)
def selEntry (N : HashOutput) (c j : Nat) : Nat :=
  ((T3.selections N).getD c ⟨0, []⟩).bucket * 128 + ((T3.selections N).getD c ⟨0, []⟩).leaves.getD j 0
def SelRows (t : MachineState) (N : HashOutput) : Prop :=
  ∀ c < 7, ∀ j < 3, t.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * j)) = BitVec.ofNat 64 (selEntry N c j)
def OutAt (t : MachineState) (A : Nat) (N : BitVec 256) : Prop :=
  ∀ k < 4, t.getMem (BitVec.ofNat 64 (A + 8 * k)) = N.extractLsb' (64 * k) 64
def DsPost (b d : Nat) (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => FailedAt b t
  | some (c, N), t => t.pc = pcOf (d + 19) ∧ t.getReg .x5 = 0 ∧ T3.admissible (T3.selections N) = true ∧
      OutAt t NBUF N ∧ SelRows t N ∧ RegsExcept s t dsRegs ∧ Frame s t DsW ∧
      c.toNat < 2 ^ 20 ∧ t.getReg .x19 = BitVec.ofNat 64 c.toNat
theorem selEntry_eq (N : HashOutput) (c j : Nat) (hc : c < 7) :
    selEntry N c j = selBucket N c * 128 + (selRow N c).getD j 0 := by
  simp [selEntry, selections_eq, List.getD_eq_getElem?_getD, hc]
section loop
variable {image : Image} {d b : Nat} {sk : BitVec 256}
structure DsInv (d : Nat) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (d + 0)
  hi : i ≤ 2 ^ 20
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  regs : RegsExcept s0 t dsRegs
  frame : Frame s0 t DsW
-- Unused legacy digest-search simulation theorems removed.
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
-- (open dropped: nothing it names is in this part)
def zeroBlk : List (BitVec 32) := [28343,0x9a0eb823,0x9a0ebc23,0x9c0eb023,0x9c0eb423,2451,0xce4d606f]
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_ExpSearch ====
section

section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Search (DIG NBUF)
-- (open dropped: nothing it names is in this part)
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
-- (open dropped: nothing it names is in this part)
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF OutAt FailedAt)
-- (open dropped: nothing it names is in this part)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Sign (run memEval_cons_ofNat)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE costByte costChk
  costChk_getD costByte_lt piece regs_rfs shl0_shr33 sll_eval srl_eval fieldE_eval psum psum_succ psum_le fieldN_lt
  psum_nine digestInput_length' pad64_digestInput' wordsOf_digestInput' blocks_digestInput' childN childN_lt childE_eval)
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000 in
/-- Expand joint-cost cap test `S < 790` (nested FTS joint cap 789). -/
def capE : E := .bin .sltu (.reg .x20) (cst 790)
def resCap (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, capE)], [], []⟩, if d then pcOf 41060 else pcOf 41054, false, 2, 2, [⟨.eq, capE, .c 0, d⟩], none⟩
theorem chk_cap : (optBeq (run expLook [41060, 41054] 41052 [.br true]) (resCap true) &&
    optBeq (run expLook [41060, 41054] 41052 [.br false]) (resCap false)) = true := by decide +kernel
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
theorem codeAt_of_look {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) (n : Nat)
    (ws : List (BitVec 32)) (hn : 0x1000 + 4 * n + 4 * ws.length < 2 ^ 64)
    (h : ∀ i, i < ws.length → look (n + i) = ws[i]?) : CodeAt im (pcOf n) ws := by
  have hpc : (pcOf n).toNat = 0x1000 + 4 * n := by
    rw [pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [hpc, show (0x1000 + 4 * n - 0x1000) / 4 = n by omega]
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < ws.length
  · rw [List.getElem?_take, if_pos (by simpa using hi), List.getElem?_drop]
    have := hl (n + i) (ws[i]) (by rw [h i hi]; simp [hi])
    rw [this]; simp [hi]
  · rw [List.getElem?_eq_none (by omega)]
    by_cases hd : i < (List.drop n im.code).length
    · have := h
      rw [List.getElem?_take, if_neg (by simp; omega)]
    · rw [List.getElem?_eq_none (by simp at hd ⊢; omega)]
theorem pcOf_add_lit (n m k : Nat) (h : (0x1000 + 4 * n + k) % 2 ^ 64 = (0x1000 + 4 * m) % 2 ^ 64) :
    pcOf n + BitVec.ofNat 64 k = pcOf m := by
  apply BitVec.eq_of_toNat_eq
  simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [← h]
  omega
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
-- (open dropped: nothing it names is in this part)
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
theorem wordsOf_getD (L : List UInt8) (m : Nat) (hL : L.length = 8 * m) (i : Nat) (hi : i < m) :
    (wordsOf L).getD i 0 = BitVec.ofNat 64 (readLE (window L (8 * i) 8)) := by
  rw [wordsOf_eq_range m L hL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have hw : readLE (window L (8 * i) 8) < 2 ^ 64 := by
    have := readLE_lt (window L (8 * i) 8)
    have hl : (window L (8 * i) 8).length ≤ 8 := by unfold window; simp
    calc readLE (window L (8 * i) 8) < 256 ^ (window L (8 * i) 8).length := this
      _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hl
      _ = 2 ^ 64 := by norm_num
  rw [Nat.mod_eq_of_lt hw, show 2 ^ (64 * i) = 256 ^ (8 * i) by rw [pow_mul, pow_mul]; norm_num,
    SigGolfCandidate.T3M.readLE_drop, show 2 ^ 64 = 256 ^ 8 by norm_num, SigGolfCandidate.T3M.readLE_take]
  rfl
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
def lbPc : List Nat := [48121,48127,48133,48139,48145,48151,48157,48163,48169,48175,48181,48187,48193,48199,48205,48211,48217,48223,48229,48235,48241,48247,48253,48259,48265,48271,48277,48283,48289,48295,48301,48307,48313,48319,48325,48331,48337,48343,48349,48355,48361,48367,48373,48381,48387,48393,48399,48405,48411,48417,48423,48429,48435,48441,48447,48453,48459,48465,48471,48477,48483,48489,48495,48501,48507,48513,48519,48525,48531,48537,48543,48549,48555,48561,48567,48573,48579,48585,48591,48597,48603,48609,48615,48621,48627,48633,48641,48647,48653,48659,48665,48671,48677,48683,48689,48695,48701,48707,48713,48719,48725,48731,48737,48743,48749,48755,48761,48767,48773,48779,48785,48791,48797,48803,48809,48815,48821,48827,48833,48839,48845,48851,48857,48863,48869,48875,48881,48887,48893,48901,48907,48913,48919,48925,48931,48937,48943,48949,48955,48961,48967,48973,48979,48985,48991,48997,49003,49009,49015,49021,49027,49033,49039,49045,49051,49057,49063,49069,49075,49081,49087,49093,49099,49105,49111,49117,49123,49129,49135,49141,49147,49153,49159,49165,49171,49177,49183,49189,49195,49201]
def lbS : List Nat := [22992,22856,22928,22752,22824,22648,22720,22544,22616,22440,22512,22336,22408,22232,22304,22128,22200,22024,22096,21920,21992,21816,21888,21712,21784,21608,21680,21504,21576,21400,21472,21296,21368,21192,21264,21088,21160,20984,21056,20880,20952,20776,20848,20424,20288,20360,20184,20256,20080,20152,19976,20048,19872,19944,19768,19840,19664,19736,19560,19632,19456,19528,19352,19424,19248,19320,19144,19216,19040,19112,18936,19008,18832,18904,18728,18800,18624,18696,18520,18592,18416,18488,18312,18384,18208,18280,17856,17720,17792,17616,17688,17512,17584,17408,17480,17304,17376,17200,17272,17096,17168,16992,17064,16888,16960,16784,16856,16680,16752,16576,16648,16472,16544,16368,16440,16264,16336,16160,16232,16056,16128,15952,16024,15848,15920,15744,15816,15640,15712,15208,15144,15080,15016,14952,14888,14824,14760,14696,14632,14568,14504,14440,14376,14312,14248,14184,14120,14056,13992,13928,13864,13800,13736,13672,13608,13544,13480,13416,13352,13288,13224,13160,13096,13032,12968,12904,12840,12776,12712,12648,12584,12520,12456,12392,12328,12264,12200,12136,12072,12008]
def lbX : List Nat := [0,32,48,64,80,96,112,128,144,160,176,192,208,224,240,256,272,288,304,320,336,352,368,384,400,416,432,448,464,480,496,512,528,544,560,576,592,608,624,640,656,672,688,0,32,48,64,80,96,112,128,144,160,176,192,208,224,240,256,272,288,304,320,336,352,368,384,400,416,432,448,464,480,496,512,528,544,560,576,592,608,624,640,656,672,688,0,32,48,64,80,96,112,128,144,160,176,192,208,224,240,256,272,288,304,320,336,352,368,384,400,416,432,448,464,480,496,512,528,544,560,576,592,608,624,640,656,672,688,18446744073709551584,0,16,32,48,64,80,96,112,128,144,160,176,192,208,224,240,256,272,288,304,320,336,352,368,384,400,416,432,448,464,480,496,512,528,544,560,576,592,608,624,640,656,672,688,704,720,736,752,768,784]
def lbD : List Nat := [23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232]
def lbHeadPc : List Nat := [48119,48379,48639,48899]
def lbHeadCodes : List (List (BitVec 32)) := [[26039,2651162003],[26039,3422913939],[26039,4194665875],[26039,688227731]]
def cTop : List (BitVec 32) := [0x00006537,0x9e050513,0x000065b7,0x60058593,0x00053303,0x0065b023,0x00853303,
  0x0065b423,0x01053303,0x0065b823,0x01853303,0x0065bc23]
def pcK (k : Nat) : Nat := lbPc.getD k 0
def sK (k : Nat) : Nat := lbS.getD k 0
def xK (k : Nat) : Nat := lbX.getD k 0
def dK (k : Nat) : Nat := lbD.getD k 0
def slotK (k : Nat) : Nat := (dK k + xK k) % 2 ^ 64
/-- Item `k` starts with a group head `li a1,D` (k = 0, 43, 86, 129). -/
def hdK (k : Nat) : Bool := k == 0 || k == 43 || k == 86 || k == 129
def grpK (k : Nat) : Nat := if k < 43 then 0 else if k < 86 then 1 else if k < 129 then 2 else 3
/-- Start pc of item `k` (its head, if any). -/
def itemPc (k : Nat) : Nat := if hdK k then pcK k - 2 else pcK k
def itemLen (k : Nat) : Nat := if hdK k then 8 else 6
theorem tab_facts : (∀ k < 180, pcK k + 6 = itemPc (k + 1) ∨ k = 179) ∧ pcK 179 + 6 = 49207 ∧ itemPc 0 = 48119 ∧
    (∀ k < 180, hdK k = true → (lbHeadPc.getD (grpK k) 0 = pcK k - 2)) ∧
    (∀ k < 180, hdK k = false → 0 < k ∧ dK k = dK (k - 1)) ∧
    (∀ k < 179, slotK k + 16 ≤ slotK (k + 1)) ∧ 23008 ≤ slotK 0 ∧ slotK 179 + 16 ≤ 26112 ∧
    (∀ k < 180, sK k % 8 = 0 ∧ sK k + 16 ≤ 23008 ∧ xK k % 8 = 0 ∧ xK k < 2 ^ 64 ∧ dK k % 8 = 0 ∧ dK k < 2 ^ 64) := by
  refine ⟨?_, by decide, by decide, ?_, ?_, ?_, by decide, by decide, ?_⟩ <;> decide
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
def sibLen (l : Nat) : Nat := if l < 6 then 14 else 12
/-- r3w (witness stack): the sibling blocks now differ per coordinate (store immediates `-sh k l`), index `6 k + l`. -/
def cSibs : List (List (BitVec 32)) :=[[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,31338531,32388131],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,31338531,32388131],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,31338531,32388131],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,31338531,32388131],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,31338531,32388131],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,31338531,32388131],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,31338531,32388131],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,31338531,32388131],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,31338531,32388131],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,31338531,32388131],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,31338531,32388131],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4259199011,4260248611],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4259199011,4260248611],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4259199011,4260248611],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4259199011,4260248611],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4259199011,4260248611],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4259199011,4260248611],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4225642531,4226692131],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4225642531,4226692131],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4225642531,4226692131],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4225642531,4226692131],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4225642531,4226692131],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4225642531,4226692131],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4158535715,4159585315],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4158535715,4159585315],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4158535715,4159585315],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4158535715,4159585315],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4158535715,4159585315],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4158535715,4159585315],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4124979235,4126028835],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4124979235,4126028835],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4124979235,4126028835],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4124979235,4126028835],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4124979235,4126028835],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4124979235,4126028835],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4057872419,4058922019],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4057872419,4058922019],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4057872419,4058922019],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4057872419,4058922019],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4057872419,4058922019],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4057872419,4058922019],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4024315939,4025365539],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4024315939,4025365539],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4024315939,4025365539],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4024315939,4025365539],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4024315939,4025365539],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4024315939,4025365539],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,3957209123,3958258723],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,3957209123,3958258723],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,3957209123,3958258723],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,3957209123,3958258723],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,3957209123,3958258723],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,3957209123,3958258723],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,3923652643,3924702243]]
def cSib (k l : Nat) : List (BitVec 32) := cSibs.getD (6 * k + l) []
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
def cCtr : List (BitVec 32) := [3212599,33883411,1241515411,2098707,1280344303]
def cPRegs : List (List (BitVec 32)) := [[3212599,67437843,9655,2055570835,117442067,1255178479],[3212599,1006961939,9655,1116046739,117442067,1230012655],[3212599,1946486035,9655,176522643,117442067,1204846831],[3216695,2886010131,9655,3531965843,117442067,1179681007],[3216695,3825534227,9655,2592441747,117442067,1154515183],[3216695,470091027,5559,1652917651,117442067,1129349359],[3216695,1409615123,5559,713393555,117442067,1104183535],[3220791,2349139219,5559,4068836755,117442067,1079017711],[3220791,3288663315,5559,3129312659,117442067,1053851887]]
def cPReg (c : Nat) : List (BitVec 32) := cPRegs.getD c []
def cTop : List (BitVec 32) := [3220791,4236576019,13751,2944763283,1591,554042899,3877630191]
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
/-- Line-A table (row `leaf % 64`, the six sibling slots of levels 0..5, stride 8) at `0xfffb80`. -/
def TOPA : Nat := 0xfffb80
/-- Line-B table (row `leaf / 64`, the six sibling slots of levels 6..11) at `0xfffd80`. -/
def TOPB : Nat := 0xfffd80
def topABytes : List (BitVec 8) := (SigGolfCandidate.T3M.Images.expandLegacyData.drop 2944).take 512
def topBBytes : List (BitVec 8) := (SigGolfCandidate.T3M.Images.expandLegacyData.drop 3456).take 512
def TopTabAt (t : MachineState) : Prop :=
  (∀ k < 64, t.getMem (BitVec.ofNat 64 (TOPA + 8 * k)) = bytesToWordLE ((topABytes.drop (8 * k)).take 8)) ∧
  ∀ k < 64, t.getMem (BitVec.ofNat 64 (TOPB + 8 * k)) = bytesToWordLE ((topBBytes.drop (8 * k)).take 8)
/-- Sibling slot (16-byte unit of the 48-slot top path area) of level `jj` in row `r` of line A (levels 0..5). -/
def slotA (r jj : Nat) : Nat := (ClaudeWCT.W9.Machine.Expand.OldW.topPlanA.getD r []).getD jj 0 + 3 * (1 - r / 2 ^ jj % 2)
/-- Sibling slot of level `jj + 6` in row `r` of line B. -/
def slotB (r jj : Nat) : Nat := (ClaudeWCT.W9.Machine.Expand.OldW.topPlanB.getD r []).getD jj 0 + 3 * (1 - r / 2 ^ jj % 2)
set_option maxRecDepth 100000 in
theorem topA_ok : ∀ r < 64, ∀ jj < 6,
    LoadKind.bu.fromWord (bytesToWordLE ((topABytes.drop (8 * r)).take 8)) jj = BitVec.ofNat 64 (slotA r jj) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem topB_ok : ∀ r < 64, ∀ jj < 6,
    LoadKind.bu.fromWord (bytesToWordLE ((topBBytes.drop (8 * r)).take 8)) jj = BitVec.ofNat 64 (slotB r jj) := by
  decide +kernel
set_option maxRecDepth 100000 in
/-- Line A's sibling slots lie in `[24, 47]`, line B's in `[0, 23]`; within a line they are pairwise distinct. -/
theorem slots_ok : (∀ r < 64, ∀ i < 6, 24 ≤ slotA r i ∧ slotA r i ≤ 47) ∧ (∀ r < 64, ∀ i < 6, slotB r i ≤ 23) ∧
    (∀ r < 64, ∀ i < 6, ∀ i' < 6, slotA r i = slotA r i' → i = i') ∧
    (∀ r < 64, ∀ i < 6, ∀ i' < 6, slotB r i = slotB r i' → i = i') := by
  decide +kernel
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
