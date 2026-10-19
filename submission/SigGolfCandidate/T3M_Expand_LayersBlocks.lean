import SigGolfCandidate.T3M_Search_CounterSearch
import SigGolfCandidate.T3M_Expand_LayerChain
set_option Elab.async false

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
    ∃ t, Steps im s 14 14 t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf 332 ∧
      t.getReg .x8 = BitVec.ofNat 64 0 ∧ t.getReg .x15 = BitVec.ofNat 64 12 ∧
      t.getReg .x26 = BitVec.ofNat 64 54 ∧ t.getReg .x27 = BitVec.ofNat 64 51 ∧
      t.getReg .x17 = BitVec.ofNat 64 146 ∧
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
    ∃ t, Steps im s (lK lay) (lK lay) t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf (lR1 lay) ∧
      t.getReg .x8 = BitVec.ofNat 64 lay.val ∧ t.getReg .x15 = BitVec.ofNat 64 (height lay) ∧
      t.getReg .x26 = BitVec.ofNat 64 (chainCount lay) ∧ t.getReg .x27 = BitVec.ofNat 64 (csN4 lay) ∧
      t.getReg .x17 = BitVec.ofNat 64 (if lay=0 then 146 else 201) ∧
      t.getReg .x18 = BitVec.ofNat 64 (route index lay).1 ∧ t.getReg .x9 = BitVec.ofNat 64 (route index lay).2 ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
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
