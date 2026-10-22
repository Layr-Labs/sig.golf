import SigGolfCandidate.T3M_Search_CounterSearch
import SigGolfCandidate.T3M_Expand_LayerChain

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
set_option autoImplicit false
set_option maxRecDepth 8192
abbrev IDXV : Nat := 0x20550
theorem shr_and_mask (a k m : Nat) (ha : a < 2 ^ 64) (hm : m ≤ 64) :
    BitVec.ofNat 64 a >>> k &&& BitVec.ofNat 64 (2 ^ m - 1) = BitVec.ofNat 64 (a / 2 ^ k % 2 ^ m) := by
  rw [ofNat_shr _ _ ha, ofNat_and_mask _ _ hm]
section blocks
variable (s : MachineState)
-- [h2 lane] removed c342_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
def lE (lay : Layer) : Nat := ![318, 295, 272, 249] lay
def lK (lay : Layer) : Nat := ![14, 13, 13, 13] lay
def lR1 (lay : Layer) : Nat := ![332, 308, 285, 262] lay
def lR2 (lay : Layer) : Nat := ![342, 318, 295, 272] lay
def lD (lay : Layer) : Nat := ![0x3ce8, 0x4968, 0x55a8, 0x820] lay
def lk (lay : Layer) : Nat := ![0, 0, 0, 0] lay
def lP (lay : Layer) : Nat := ![0x7890, 0x7cb0, 0x7fd0, 0x82e0] lay
def lWC (lay : Layer) : Nat := ![0x3c88, 0x4908, 0x5548, 0x6188] lay
def lWM (lay : Layer) : Nat := ![0x2f08, 0x3e48, 0x4A88, 0x56C8] lay
theorem route_fst (index : Nat) (lay : Layer) :
    (route index lay).1 = index / 2 ^ ((![19, 12, 6, 0] : Layer → Nat) lay) % 2 ^ height lay := rfl
theorem route_snd (index : Nat) (lay : Layer) :
    (route index lay).2 = index / 2 ^ ((![19, 12, 6, 0] : Layer → Nat) lay + height lay) := rfl
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
open SigGolfCandidate.T3M.Expand
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def entryCode249 : List (BitVec 32) := seg_249.set 4 (0xc900893 : BitVec 32)
sym_block entryBlock249 := symRun {noAlias := true} entryCode249 (pcOf 249) 200
def entryCode272 : List (BitVec 32) := seg_272.set 4 (0xc900893 : BitVec 32)
sym_block entryBlock272 := symRun {noAlias := true} entryCode272 (pcOf 272) 200
class EntryCode (im : Image) : Prop where
  code249 : CodeAt im (pcOf 249) entryCode249
  code272 : CodeAt im (pcOf 272) entryCode272
  code295 : CodeAt im (pcOf 295) seg_295
  code318 : CodeAt im (pcOf 318) seg_318
  code262 : CodeAt im (pcOf 262) seg_262
  code285 : CodeAt im (pcOf 285) seg_285
  code308 : CodeAt im (pcOf 308) seg_308
  code332 : CodeAt im (pcOf 332) seg_332
variable {im : Image} [EntryCode im]
section
variable (s : MachineState)
theorem l249_spec (hpc : s.pc = pcOf 249) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf 262 ∧
      t.getReg .x8 = BitVec.ofNat 64 3 ∧ t.getReg .x15 = BitVec.ofNat 64 6 ∧
      t.getReg .x26 = BitVec.ofNat 64 43 ∧ t.getReg .x27 = BitVec.ofNat 64 0 ∧
      t.getReg .x17 = BitVec.ofNat 64 201 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 0 % 2 ^ 6) ∧ t.getReg .x9 = BitVec.ofNat 64 (index / 2 ^ 6) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound entryBlock249 (EntryCode.code249 (im := im)) s hpc (by simp [entryBlock249.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, entryBlock249.res, E.eval]
  · simp [entryBlock249.res, rv_simp]
  · simp [entryBlock249.res, rv_simp]
  · simp [entryBlock249.res, rv_simp]
  · simp [entryBlock249.res, rv_simp]
  · simp [entryBlock249.res, rv_simp]
  · simp [entryBlock249.res, rv_simp]
  · simp only [Result.toState_getReg, entryBlock249.res, rv_simp, hidx]
    t3n []
    rw [show (63#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl,
      shr_and_mask _ _ _ (by omega) (by decide)]
    norm_num
  · simp only [Result.toState_getReg, entryBlock249.res, rv_simp, hidx]
    t3n []
    rw [ofNat_shr _ _ (by omega)]
    norm_num
  · ex_regs entryBlock249.res
  · intro A _ _; simp [entryBlock249.res, rv_simp]

theorem l272_spec (hpc : s.pc = pcOf 272) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf 285 ∧
      t.getReg .x8 = BitVec.ofNat 64 2 ∧ t.getReg .x15 = BitVec.ofNat 64 6 ∧
      t.getReg .x26 = BitVec.ofNat 64 43 ∧ t.getReg .x27 = BitVec.ofNat 64 0 ∧
      t.getReg .x17 = BitVec.ofNat 64 201 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 6 % 2 ^ 6) ∧ t.getReg .x9 = BitVec.ofNat 64 (index / 2 ^ 12) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound entryBlock272 (EntryCode.code272 (im := im)) s hpc (by simp [entryBlock272.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, entryBlock272.res, E.eval]
  · simp [entryBlock272.res, rv_simp]
  · simp [entryBlock272.res, rv_simp]
  · simp [entryBlock272.res, rv_simp]
  · simp [entryBlock272.res, rv_simp]
  · simp [entryBlock272.res, rv_simp]
  · simp [entryBlock272.res, rv_simp]
  · simp only [Result.toState_getReg, entryBlock272.res, rv_simp, hidx]
    t3n []
    rw [show (63#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl,
      shr_and_mask _ _ _ (by omega) (by decide)]
    norm_num
  · simp only [Result.toState_getReg, entryBlock272.res, rv_simp, hidx]
    t3n []
    rw [ofNat_shr _ _ (by omega)]
    norm_num
  · ex_regs entryBlock272.res
  · intro A _ _; simp [entryBlock272.res, rv_simp]

theorem l295_spec (hpc : s.pc = pcOf 295) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf 308 ∧
      t.getReg .x8 = BitVec.ofNat 64 1 ∧ t.getReg .x15 = BitVec.ofNat 64 7 ∧
      t.getReg .x26 = BitVec.ofNat 64 43 ∧ t.getReg .x27 = BitVec.ofNat 64 0 ∧
      t.getReg .x17 = BitVec.ofNat 64 201 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 12 % 2 ^ 7) ∧ t.getReg .x9 = BitVec.ofNat 64 (index / 2 ^ 19) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_295 (EntryCode.code295 (im := im)) s hpc (by simp [eblk_295.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_295.res, E.eval]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_295.res, rv_simp, hidx]
    t3n []
    rw [show (127#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      shr_and_mask _ _ _ (by omega) (by decide)]
    norm_num
  · simp only [Result.toState_getReg, eblk_295.res, rv_simp, hidx]
    t3n []
    rw [ofNat_shr _ _ (by omega)]
    norm_num
  · ex_regs eblk_295.res
  · intro A _ _; simp [eblk_295.res, rv_simp]

theorem l318_spec (hpc : s.pc = pcOf 318) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps im s 14 14 t ∧ t.pc = pcOf 54522 ∧ t.getReg .x1 = pcOf 332 ∧
      t.getReg .x8 = BitVec.ofNat 64 0 ∧ t.getReg .x15 = BitVec.ofNat 64 12 ∧
      t.getReg .x26 = BitVec.ofNat 64 51 ∧ t.getReg .x27 = BitVec.ofNat 64 51 ∧
      t.getReg .x17 = BitVec.ofNat 64 152 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 19 % 2 ^ 12) ∧ t.getReg .x9 = BitVec.ofNat 64 (index / 2 ^ 31) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_318 (EntryCode.code318 (im := im)) s hpc (by simp [eblk_318.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_318.res, E.eval]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_318.res, rv_simp, hidx]
    t3n []
    rw [show (4095#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 12 - 1) from rfl,
      shr_and_mask _ _ _ (by omega) (by decide)]
    norm_num
  · simp only [Result.toState_getReg, eblk_318.res, rv_simp, hidx]
    t3n []
    rw [ofNat_shr _ _ (by omega)]
    norm_num
  · ex_regs eblk_318.res
  · intro A _ _; simp [eblk_318.res, rv_simp]

theorem l262_spec (hpc : s.pc = pcOf 262) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps im s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf 272 ∧
      t.getMem (BitVec.ofNat 64 0x820) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x820)) 0 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 0x82e0 ∧ t.getReg .x23 = BitVec.ofNat 64 0x6188 ∧
      t.getReg .x24 = BitVec.ofNat 64 0x56c8 ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = 0x820) := by
  refine ⟨_, symRun_sound eblk_262 (EntryCode.code262 (im := im)) s hpc (by simp [eblk_262.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_262.res, E.eval]
  · simp [eblk_262.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_262.res]
    t3n [h19]
  · simp [eblk_262.res, rv_simp]
  · simp [eblk_262.res, rv_simp]
  · simp [eblk_262.res, rv_simp]
  · ex_regs eblk_262.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_262.res]
    t3n []
    rw [if_neg (by omega)]

theorem l285_spec (hpc : s.pc = pcOf 285) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps im s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf 295 ∧
      t.getMem (BitVec.ofNat 64 0x55a8) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x55a8)) 0 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 0x7fd0 ∧ t.getReg .x23 = BitVec.ofNat 64 0x5548 ∧
      t.getReg .x24 = BitVec.ofNat 64 0x4a88 ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = 0x55a8) := by
  refine ⟨_, symRun_sound eblk_285 (EntryCode.code285 (im := im)) s hpc (by simp [eblk_285.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_285.res, E.eval]
  · simp [eblk_285.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_285.res]
    t3n [h19]
  · simp [eblk_285.res, rv_simp]
  · simp [eblk_285.res, rv_simp]
  · simp [eblk_285.res, rv_simp]
  · ex_regs eblk_285.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_285.res]
    t3n []
    rw [if_neg (by omega)]

theorem l308_spec (hpc : s.pc = pcOf 308) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps im s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf 318 ∧
      t.getMem (BitVec.ofNat 64 0x4968) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x4968)) 0 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 0x7cb0 ∧ t.getReg .x23 = BitVec.ofNat 64 0x4908 ∧
      t.getReg .x24 = BitVec.ofNat 64 0x3e48 ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = 0x4968) := by
  refine ⟨_, symRun_sound eblk_308 (EntryCode.code308 (im := im)) s hpc (by simp [eblk_308.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_308.res, E.eval]
  · simp [eblk_308.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_308.res]
    t3n [h19]
  · simp [eblk_308.res, rv_simp]
  · simp [eblk_308.res, rv_simp]
  · simp [eblk_308.res, rv_simp]
  · ex_regs eblk_308.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_308.res]
    t3n []
    rw [if_neg (by omega)]

theorem l332_spec (hpc : s.pc = pcOf 332) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps im s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf 342 ∧
      t.getMem (BitVec.ofNat 64 0x3ce8) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x3ce8)) 0 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 0x7890 ∧ t.getReg .x23 = BitVec.ofNat 64 0x3c88 ∧
      t.getReg .x24 = BitVec.ofNat 64 0x2f08 ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = 0x3ce8) := by
  refine ⟨_, symRun_sound eblk_332 (EntryCode.code332 (im := im)) s hpc (by simp [eblk_332.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_332.res, E.eval]
  · simp [eblk_332.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_332.res]
    t3n [h19]
  · simp [eblk_332.res, rv_simp]
  · simp [eblk_332.res, rv_simp]
  · simp [eblk_332.res, rv_simp]
  · ex_regs eblk_332.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_332.res]
    t3n []
    rw [if_neg (by omega)]
-- [h2 lane] removed c342_spec: a fact about the record's original expand word 0 / 342, which H2 replaces

end
theorem lentry_spec (lay : Layer) (s : MachineState) (hpc : s.pc = pcOf (lE lay)) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps im s (lK lay) (lK lay) t ∧ t.pc = pcOf (if lay=0 then 54522 else 457) ∧ t.getReg .x1 = pcOf (lR1 lay) ∧
      t.getReg .x8 = BitVec.ofNat 64 lay.val ∧ t.getReg .x15 = BitVec.ofNat 64 (height lay) ∧
      t.getReg .x26 = BitVec.ofNat 64 (chainCount lay) ∧ t.getReg .x27 = BitVec.ofNat 64 (csN4 lay) ∧
      t.getReg .x17 = BitVec.ofNat 64 (if lay=0 then 152 else 201) ∧
      t.getReg .x18 = BitVec.ofNat 64 (route index lay).1 ∧ t.getReg .x9 = BitVec.ofNat 64 (route index lay).2 ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  -- Campaign T51: the top entry (318) ends with `jal KCOPY` (54522); KCOPY then enters the counter search at 457.
  rw [route_fst, route_snd]
  fin_cases lay
  · exact l318_spec (im := im) s hpc index hi hidx
  · exact l295_spec (im := im) s hpc index hi hidx
  · exact l272_spec (im := im) s hpc index hi hidx
  · exact l249_spec (im := im) s hpc index hi hidx

theorem lpost_spec (lay : Layer) (s : MachineState) (hpc : s.pc = pcOf (lR1 lay)) (c : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps im s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf (lR2 lay) ∧
      t.getMem (BitVec.ofNat 64 (lD lay)) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 (lD lay))) (lk lay) ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 (lP lay) ∧ t.getReg .x23 = BitVec.ofNat 64 (lWC lay) ∧
      t.getReg .x24 = BitVec.ofNat 64 (lWM lay) ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = lD lay) := by
  fin_cases lay
  · exact l332_spec (im := im) s hpc c h19
  · exact l308_spec (im := im) s hpc c h19
  · exact l285_spec (im := im) s hpc c h19
  · exact l262_spec (im := im) s hpc c h19


end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_entry : EntryCode Images.expandImage := by
  constructor <;> apply codeAt_expand_current_chunk <;> decide +kernel

#print axioms installed_entry
end SigGolfCandidate.T3M.Expand.SharedRecover

/-! ## T51 KCOPY (54522..54531, from 331 `jal ra, 54522`): copy the 1,896-byte shared kernel table window
`0xFF9E00 .. 0xFFA568` (237 doublewords; the 1,892-byte block + 4 bytes) to RAM `0xA0000`, then `j 457`. -/
namespace SigGolfCandidate.T3M.Expand.KCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def headWords : List (BitVec 32) := [0x000a0eb7,0x00ffae37,0xe00e0e13,0x768e0f13]
def loopWords : List (BitVec 32) := [0xe3303,0x6eb023,0x8e0e13,0x8e8e93,0xffee68e3]
def tailWords : List (BitVec 32) := [0xb18cb06f]

sym_block loopRun := symRun { noAlias := true } loopWords (pcOf 54526) 50
sym_block headRun := symRun { noAlias := true } headWords (pcOf 54522) 10
sym_block tailRun := symRun { noAlias := true } tailWords (pcOf 54531) 10

theorem loop_regs (s : MachineState) :
    RegsExcept s (loopRun.res.toState s) [.x6,.x28,.x29] := by
  intro r hr; simp at hr; cases r <;> simp_all [loopRun.res, rv_simp] <;> rfl

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

/-- `n + 1` iterations of the copy loop, ascending, source `S`, destination `D`, end `S + 8 (n + 1)`. -/
theorem loop_copy {im : Image} (hc : CodeAt im (pcOf 54526) loopWords) :
    ∀ n (s : MachineState) (S D : Nat), S % 8 = 0 → D % 8 = 0 → S + 8 * (n + 1) ≤ 2 ^ 24 →
      D + 8 * (n + 1) ≤ S → s.pc = pcOf 54526 →
      s.getReg .x28 = BitVec.ofNat 64 S → s.getReg .x29 = BitVec.ofNat 64 D →
      s.getReg .x30 = BitVec.ofNat 64 (S + 8 * (n + 1)) →
      ∃ t, Steps im s (5 * (n + 1)) (5 * (n + 1)) t ∧ t.pc = pcOf 54531 ∧
        t.getReg .x28 = BitVec.ofNat 64 (S + 8 * (n + 1)) ∧
        t.getReg .x29 = BitVec.ofNat 64 (D + 8 * (n + 1)) ∧
        (∀ i, i ≤ n → t.getMem (BitVec.ofNat 64 (D + 8 * i)) = s.getMem (BitVec.ofNat 64 (S + 8 * i))) ∧
        RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => D ≤ A ∧ A < D + 8 * (n + 1)) := by
  intro n
  induction n with
  | zero =>
    intro s S D hS8 hD8 hS hD hpc h28 h29 h30
    obtain ⟨t, st, pt, r28, r29, mt, rt, ft⟩ := loop_step hc s hpc S D (S + 8 * (0 + 1))
      hS8 hD8 (by omega) (by omega) (by omega) h28 h29 h30
    refine ⟨t, st, by simpa using pt, by simpa using r28, by simpa using r29, ?_, rt, ft.mono (by intro A _ h; omega)⟩
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    simpa using mt
  | succ n ih =>
    intro s S D hS8 hD8 hS hD hpc h28 h29 h30
    obtain ⟨u, su, pu, u28, u29, mu, ru, fu⟩ := loop_step hc s hpc S D (S + 8 * (n + 1 + 1))
      hS8 hD8 (by omega) (by omega) (by omega) h28 h29 h30
    have hpu : u.pc = pcOf 54526 := by rw [pu, if_pos (by omega)]
    obtain ⟨t, ut, pt, t28, t29, mt, rt, ft⟩ := ih u (S + 8) (D + 8) (by omega) (by omega) (by omega) (by omega)
      hpu u28 u29 (by rw [ru.get (by decide), h30]; congr 1; ring)
    refine ⟨t, ?_, pt, by rw [t28]; congr 1; ring, by rw [t29]; congr 1; ring, ?_, (ru.trans rt).mono (by decide), ?_⟩
    · convert su.trans ut using 1 <;> ring
    · intro i hi
      rcases i with _ | i
      · rw [ft _ (by omega) (by omega)]
        simpa using mu
      · have h1 := mt i (by omega)
        rw [show D + 8 * (i + 1) = D + 8 + 8 * i by ring, h1, show S + 8 + 8 * i = S + 8 * (i + 1) by ring]
        exact fu _ (by omega) (by omega)
    · exact (fu.trans ft).mono (by intro A _ h; rcases h with h | h <;> omega)

theorem head_spec {im : Image} (hc : CodeAt im (pcOf 54522) headWords) (s : MachineState) (hpc : s.pc = pcOf 54522) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 54526 ∧ t.getReg .x28 = BitVec.ofNat 64 0xFF9E00 ∧
      t.getReg .x29 = BitVec.ofNat 64 0xA0000 ∧ t.getReg .x30 = BitVec.ofNat 64 0xFFA568 ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound headRun hc s hpc (by simp [headRun.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [headRun.res, rv_simp]
  · simp [headRun.res, rv_simp]
  · simp [headRun.res, rv_simp]
  · intro r hr; cases r <;> first | rfl | exact (hr (by decide)).elim
  · intro A _ _; simp [headRun.res, rv_simp]

theorem tail_spec {im : Image} (hc : CodeAt im (pcOf 54531) tailWords) (s : MachineState) (hpc : s.pc = pcOf 54531) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 457 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound tailRun hc s hpc (by simp [tailRun.res, rv_simp]), ?_, ?_, ?_⟩
  · rfl
  · intro r hr; cases r <;> rfl
  · intro A _ _; simp [tailRun.res, rv_simp]

/-- KCOPY's code (a class, so the layer-recovery sections can take it as an instance like `EntryCode`). -/
class Code (im : Image) : Prop where
  head : CodeAt im (pcOf 54522) headWords
  loop : CodeAt im (pcOf 54526) loopWords
  tail : CodeAt im (pcOf 54531) tailWords

/-- KCOPY: 1,190 steps from 54522 to the counter search entry 457, copying the 237 doublewords at `0xFF9E00` to RAM
`0xA0000 .. 0xA0768`. -/
theorem kcopy_spec {im : Image} [Code im] (s : MachineState) (hpc : s.pc = pcOf 54522) :
    ∃ u, Steps im s 1190 1190 u ∧ u.pc = pcOf 457 ∧
      (∀ k, k < 237 → u.getMem (BitVec.ofNat 64 (0xA0000 + 8 * k)) = s.getMem (BitVec.ofNat 64 (0xFF9E00 + 8 * k))) ∧
      RegsExcept s u [.x6,.x28,.x29,.x30] ∧ Frame s u (fun A => 0xA0000 ≤ A ∧ A < 0xA0768) := by
  obtain ⟨t0, s0, p0, a28, a29, a30, r0, f0⟩ := head_spec (Code.head (im := im)) s hpc
  obtain ⟨t1, s1, p1, b28, b29, m1, r1, f1⟩ := loop_copy (Code.loop (im := im)) 236 t0 0xFF9E00 0xA0000
    (by decide) (by decide) (by decide) (by decide) p0 a28 a29 (by rw [a30])
  obtain ⟨u, s4, p4, r4, f4⟩ := tail_spec (Code.tail (im := im)) t1 p1
  refine ⟨u, ((s0.trans s1).trans s4).of_eq (by norm_num) (by norm_num), p4, ?_, ?_, ?_⟩
  · intro k hk
    rw [f4.get (by omega) (by simp), m1 k (by omega), f0.get (by omega) (by simp)]
  · exact ((r0.trans r1).trans r4).mono (by decide)
  · exact ((f0.trans f1).trans f4).mono (fun A _ h => by
      rcases h with ((h | h) | h) <;> first | exact h.elim | omega)

theorem installed_code : Code Images.expandImage := by
  constructor <;> (apply codeAt_t51_at <;> decide)

#print axioms kcopy_spec
end SigGolfCandidate.T3M.Expand.KCopy
