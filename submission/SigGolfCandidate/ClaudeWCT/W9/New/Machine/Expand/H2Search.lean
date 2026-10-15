import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.H2Front

/-! # H2 expander: the candidate search after the layers (words 342, 42795..42840)

At word 342 the old expander compared the root with the public key. Word 342 now jumps to 42795: candidate 0 is
that comparison; on a mismatch the code finds the top sibling's high word in the last hashed block (offset 8 or
56 by the top leaf's bit 11 = index bit 30), and for `c = 1, 2, ...` adds `2^48` to it, stores it, hashes the
block and compares the 16-byte answer with the key. On a match it stores the word at the sibling's witness slot
(0x2c48 + 8 or + 56) and goes to the success halt (351); after 65,535 candidates it goes to the failure halt
(354). -/

section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Expand (ex_valid ex_ne ex_beq tb_shortHash_bind')
open SigGolfCandidate.T3 (Digest HashOutput M Layer height route header zero16 pad64 shortHash)
open SigGolfCandidate.T3M.Search (ENC NODE NOUT)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000

def srchCode : List (BitVec 32) :=
  [134711, 638455315, 167775891, 964227, 9352963, 930563, 13834339, 9319171, 14881891, 2329763951, 134711,
    1426984467, 930563, 31675155, 1274643, 8389523, 201827, 58721171, 134711, 537792019, 8261171, 16311,
    3297742739, 8359859, 930691, 1050515, 50829203, 132407, 537199891, 67110291, 132663, 604374547, 1052435, 67767,
    15958963, 8269859, 115, 406275, 13833827, 8794883, 14878819, 2035475, 4280246499, 2199740527, 8368163,
    2178769007]
def srS1 : List (BitVec 32) := srchCode.take 7
def srS2 : List (BitVec 32) := (srchCode.drop 7).take 2
def srM1 : List (BitVec 32) := (srchCode.drop 10).take 7
def srM2 : List (BitVec 32) := (srchCode.drop 17).take 1
def srSD : List (BitVec 32) := (srchCode.drop 18).take 16
def srL1 : List (BitVec 32) := (srchCode.drop 34).take 2
def srL2 : List (BitVec 32) := (srchCode.drop 37).take 2
def srL3 : List (BitVec 32) := (srchCode.drop 39).take 2
def srL4 : List (BitVec 32) := (srchCode.drop 41).take 2
def srF1 : List (BitVec 32) := (srchCode.drop 44).take 1
def w342Word : BitVec 32 := 1967296623

/-- The search code and the new word 342 are in the image. -/
def SrchAt (im : Image) : Prop := CodeAt im (pcOf 342) [w342Word] ∧ CodeAt im (pcOf 42795) srchCode

section code
variable {im : Image} (hS : SrchAt im)
include hS
theorem codeAt_srch (k n : Nat) (hk : k + n ≤ 46) :
    CodeAt im (pcOf (42795 + k)) ((srchCode.drop k).take n) := by
  obtain ⟨h1, h2, h3, h4⟩ := hS.2
  have e1 : (pcOf 42795).toNat = 0x1000 + 4 * 42795 := by rw [pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e2 : (pcOf (42795 + k)).toNat = 0x1000 + 4 * (42795 + k) := by
    rw [pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hl : srchCode.length = 46 := rfl
  refine ⟨by omega, by omega, by simp only [List.length_take, List.length_drop, hl]; omega, ?_⟩
  rw [e2, show (0x1000 + 4 * (42795 + k) - 0x1000) / 4 = (0x1000 + 4 * 42795 - 0x1000) / 4 + k by omega,
    ← List.drop_drop]
  rw [e1] at h4
  obtain ⟨t, ht⟩ := h4
  refine ⟨((srchCode.drop k).drop n) ++ t, ?_⟩
  rw [← ht, List.drop_append_of_le_length (by rw [hl]; omega), ← List.append_assoc, List.take_append_drop]
end code

sym_block h2_S1 := symRun { noAlias := true } srS1 (pcOf 42795) 50
sym_block h2_S2 := symRun { noAlias := true } srS2 (pcOf 42802) 50
sym_block h2_M1 := symRun { noAlias := true } srM1 (pcOf 42805) 50
sym_block h2_M2 := symRun { noAlias := true } srM2 (pcOf 42812) 50
sym_block h2_SD := symRun { noAlias := true } srSD (pcOf 42813) 50
sym_block h2_L1 := symRun { noAlias := true } srL1 (pcOf 42829) 50
sym_block h2_L2 := symRun { noAlias := true } srL2 (pcOf 42832) 50
sym_block h2_L3 := symRun { noAlias := true } srL3 (pcOf 42834) 50
sym_block h2_L4 := symRun { noAlias := true } srL4 (pcOf 42836) 50
sym_block h2_F1 := symRun { noAlias := true } srF1 (pcOf 42839) 50

section specs
variable {im : Image} (hS : SrchAt im) (s : MachineState)
include hS

theorem w342_step (hpc : s.pc = pcOf 342) : Steps im s 1 1 (s.setPC (pcOf 42795)) := by
  obtain ⟨imm, hd, hoff⟩ := jalTo_sound (show jalTo w342Word 342 = some 42795 by decide)
  exact jal_x0_step hS.1 hd hoff s hpc

theorem jal_at (n m : Nat) (hn : 42795 ≤ n) (hn' : n < 42795 + 46) (w : BitVec 32)
    (hw : (srchCode.drop (n - 42795)).take 1 = [w]) (hj : jalTo w n = some m) (hpc : s.pc = pcOf n) :
    Steps im s 1 1 (s.setPC (pcOf m)) := by
  obtain ⟨imm, hd, hoff⟩ := jalTo_sound hj
  have hc := codeAt_srch hS (n - 42795) 1 (by omega)
  rw [hw, show 42795 + (n - 42795) = n by omega] at hc
  exact jal_x0_step hc hd hoff s hpc

theorem s1_spec (hpc : s.pc = pcOf 42795) :
    ∃ t, Steps im s 7 7 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 0xA0) then pcOf 42802 else pcOf 42805) ∧
      t.getReg .x28 = BitVec.ofNat 64 ENC ∧ t.getReg .x13 = s.getMem (BitVec.ofNat 64 0xA0) ∧
      t.getReg .x14 = s.getMem (BitVec.ofNat 64 0xA8) ∧
      RegsExcept s t [.x6, .x13, .x14, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_S1 (codeAt_srch hS 0 7 (by decide)) s hpc
    (by simp [h2_S1.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, h2_S1.res, E.eval, CmpOp.eval, rebase, rv_simp, ENC]
    split_ifs with h1 h2 h2 <;> simp_all
  · simp [h2_S1.res, rv_simp]
  · simp [h2_S1.res, rv_simp]
  · simp [h2_S1.res, rv_simp]
  · ex_regs h2_S1.res
  · intro A _ _; simp [h2_S1.res, rv_simp]

theorem s2_spec (hpc : s.pc = pcOf 42802) (h28 : s.getReg .x28 = BitVec.ofNat 64 ENC) :
    ∃ t, Steps im s 2 2 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getReg .x14 then pcOf 42804 else pcOf 42805) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_S2 (codeAt_srch hS 7 2 (by decide)) s hpc
    (by simp [h2_S2.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, ENC]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, h2_S2.res, E.eval, CmpOp.eval, rebase, rv_simp, ENC, h28]
    split_ifs with h1 h2 h2 <;> simp_all
  · ex_regs h2_S2.res
  · intro A _ _; simp [h2_S2.res, rv_simp]

theorem m1_spec (hpc : s.pc = pcOf 42805) :
    ∃ t, Steps im s 7 7 t ∧
      t.pc = (if (s.getMem (BitVec.ofNat 64 0x20550)) >>> 30 &&& 1 = 0 then pcOf 42812 else pcOf 42813) ∧
      t.getReg .x7 = BitVec.ofNat 64 8 ∧
      RegsExcept s t [.x6, .x7, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_M1 (codeAt_srch hS 10 7 (by decide)) s hpc
    (by simp [h2_M1.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, h2_M1.res, E.eval, CmpOp.eval, BinOp.eval, rebase, rv_simp]
    split_ifs with h1 h2 h2 <;> simp_all
  · simp [h2_M1.res, rv_simp]
  · ex_regs h2_M1.res
  · intro A _ _; simp [h2_M1.res, rv_simp]

theorem m2_spec (hpc : s.pc = pcOf 42812) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 42813 ∧ t.getReg .x7 = BitVec.ofNat 64 56 ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_M2 (codeAt_srch hS 17 1 (by decide)) s hpc
    (by simp [h2_M2.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, h2_M2.res, E.eval]
  · simp [h2_M2.res, rv_simp]
  · ex_regs h2_M2.res
  · intro A _ _; simp [h2_M2.res, rv_simp]

theorem sd_spec (hpc : s.pc = pcOf 42813) (off : Nat) (hoff : off = 8 ∨ off = 56)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 off) :
    ∃ t, Steps im s 16 16 t ∧ t.pc = pcOf 42829 ∧
      t.getReg .x28 = BitVec.ofNat 64 (NODE + off) ∧ t.getReg .x31 = BitVec.ofNat 64 (0x2c48 + off) ∧
      t.getReg .x7 = s.getMem (BitVec.ofNat 64 (NODE + off)) ∧
      t.getReg .x15 = BitVec.ofNat 64 (2 ^ 48) ∧ t.getReg .x10 = BitVec.ofNat 64 NODE ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧ t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      t.getReg .x30 = BitVec.ofNat 64 1 ∧ t.getReg .x17 = BitVec.ofNat 64 65536 ∧
      RegsExcept s t [.x7, .x10, .x11, .x12, .x15, .x17, .x28, .x30, .x31] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_SD (codeAt_srch hS 18 16 (by decide)) s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp only [h2_SD.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h7, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    t3n [h7]
    all_goals first | omega | skip
  · simp [Result.toState_pc, h2_SD.res, E.eval]
  · simp only [Result.toState_getReg, h2_SD.res]; t3n [h7]
    all_goals (try simp only [NODE]); all_goals (try rw [Nat.add_comm])
  · simp only [Result.toState_getReg, h2_SD.res]; t3n [h7]
    all_goals (try simp only [NODE]); all_goals (try rw [Nat.add_comm])
  · simp only [Result.toState_getReg, h2_SD.res]; t3n [h7]
    all_goals (try simp only [NODE]); all_goals (try rw [Nat.add_comm])
  · simp only [Result.toState_getReg, h2_SD.res]; t3n []
  · simp only [Result.toState_getReg, h2_SD.res]; t3n []
  · simp only [Result.toState_getReg, h2_SD.res]; t3n []
  · simp only [Result.toState_getReg, h2_SD.res]; t3n []
  · simp only [Result.toState_getReg, h2_SD.res]; t3n []
  · simp only [Result.toState_getReg, h2_SD.res]; t3n []
  · ex_regs h2_SD.res
  · intro A _ _; simp [h2_SD.res, rv_simp]

theorem l1_spec (hpc : s.pc = pcOf 42829) (B W D : Nat) (hB : B % 8 = 0) (hB' : B + 8 ≤ 2 ^ 24)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 B) (h7 : s.getReg .x7 = BitVec.ofNat 64 W)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 D) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 42831 ∧ t.getReg .x7 = BitVec.ofNat 64 (W + D) ∧
      t.getMem (BitVec.ofNat 64 B) = BitVec.ofNat 64 (W + D) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun A => A = B) := by
  refine ⟨_, symRun_sound h2_L1 (codeAt_srch hS 34 2 (by decide)) s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [h2_L1.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h28, h7, h15, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    t3n [h28, h7, h15]
    all_goals first | omega | skip
  · simp [Result.toState_pc, h2_L1.res, E.eval]
  · simp only [Result.toState_getReg, h2_L1.res]; t3n [h7, h15]
  · simp only [Result.toState_getMem, h2_L1.res]; t3n [h28, h7, h15]; simp
  · ex_regs h2_L1.res
  · intro A hA hn
    simp only [Result.toState_getMem, h2_L1.res]
    t3n [h28]
    rw [if_neg (by omega)]

theorem l2_spec (hpc : s.pc = pcOf 42832) (h12 : s.getReg .x12 = BitVec.ofNat 64 NOUT) :
    ∃ t, Steps im s 2 2 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 NOUT) = s.getReg .x13 then pcOf 42834 else pcOf 42836) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_L2 (codeAt_srch hS 37 2 (by decide)) s hpc
    (by simp [h2_L2.res, rv_simp, accessValid_iff, MEMORY_BYTES, h12, NOUT]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, h2_L2.res, E.eval, CmpOp.eval, rebase, rv_simp, NOUT, h12]
    split_ifs with h1 h2 h2 <;> simp_all
  · ex_regs h2_L2.res
  · intro A _ _; simp [h2_L2.res, rv_simp]

theorem l3_spec (hpc : s.pc = pcOf 42834) (h12 : s.getReg .x12 = BitVec.ofNat 64 NOUT) :
    ∃ t, Steps im s 2 2 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (NOUT + 8)) = s.getReg .x14 then pcOf 42839 else pcOf 42836) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_L3 (codeAt_srch hS 39 2 (by decide)) s hpc
    (by simp [h2_L3.res, rv_simp, accessValid_iff, MEMORY_BYTES, h12, NOUT]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, h2_L3.res, E.eval, CmpOp.eval, rebase, rv_simp, NOUT, h12]
    split_ifs with h1 h2 h2 <;> simp_all
  · ex_regs h2_L3.res
  · intro A _ _; simp [h2_L3.res, rv_simp]

theorem l4_spec (hpc : s.pc = pcOf 42836) (c : Nat) (hc : c < 65536)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 c) (h17 : s.getReg .x17 = BitVec.ofNat 64 65536) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if c + 1 < 65536 then pcOf 42829 else pcOf 42838) ∧
      t.getReg .x30 = BitVec.ofNat 64 (c + 1) ∧ RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_L4 (codeAt_srch hS 41 2 (by decide)) s hpc (by simp [h2_L4.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, h2_L4.res, E.eval, CmpOp.eval, BinOp.eval, rebase, rv_simp, h30, h17,
      ofNat_add_ofNat]
    have e : BitVec.ult (BitVec.ofNat 64 (c + 1)) (BitVec.ofNat 64 65536) = decide (c + 1 < 65536) := by
      simp only [BitVec.ult, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    split_ifs with h1 h2 h2 <;> simp_all
  · simp only [Result.toState_getReg, h2_L4.res]; t3n [h30]
  · ex_regs h2_L4.res
  · intro A _ _; simp [h2_L4.res, rv_simp]

theorem f1_spec (hpc : s.pc = pcOf 42839) (WW : Nat) (hW : WW % 8 = 0) (hW' : WW + 8 ≤ 2 ^ 24)
    (h31 : s.getReg .x31 = BitVec.ofNat 64 WW) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 42840 ∧ t.getMem (BitVec.ofNat 64 WW) = s.getReg .x7 ∧
      RegsExcept s t [] ∧ Frame s t (fun A => A = WW) := by
  refine ⟨_, symRun_sound h2_F1 (codeAt_srch hS 44 1 (by decide)) s hpc ?_, ?_, ?_, ?_, ?_⟩
  · simp only [h2_F1.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h31, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    t3n [h31]
    all_goals first | omega | skip
  · simp [Result.toState_pc, h2_F1.res, E.eval]
  · simp only [Result.toState_getMem, h2_F1.res]; t3n [h31]; simp
  · ex_regs h2_F1.res
  · intro A hA hn
    simp only [Result.toState_getMem, h2_F1.res]
    t3n [h31]
    rw [if_neg (by omega)]
end specs


/-! ### The searched block and the candidate words -/

def topHdr (index : Nat) : BitVec 128 :=
  SigGolfCandidate.T3.nodeTweak 3 (0 : Layer).val (route index 0).2
    (2 ^ (height 0 - WCT9.topJ.val - 1) + (route index 0).1 / 2 ^ (WCT9.topJ.val + 1))
/-- The input of the top layer's last node hash with sibling `o`. -/
def topIn (index : Nat) (v o : Digest) : List UInt8 :=
  let pair := if (route index 0).1 / 2 ^ WCT9.topJ.val % 2 = 0 then (v, o) else (o, v)
  bytesLE 16 pair.1 ++ bytesLE 16 (topHdr index) ++ zero16 ++ bytesLE 16 pair.2
theorem topNode_eq (index : Nat) (v o : Digest) : WCT9.topNode index v o = shortHash (topIn index v o) := rfl
theorem topIn_length (index : Nat) (v o : Digest) : (topIn index v o).length = 64 := by
  unfold topIn; simp [bytesLE_length, zero16]
def lo64 (d : Digest) : Word := d.extractLsb' 0 64
def hi64 (d : Digest) : Word := d.extractLsb' 64 64
def bitc (index : Nat) : Prop := (route index 0).1 / 2 ^ WCT9.topJ.val % 2 = 0
instance (index : Nat) : Decidable (bitc index) := by unfold bitc; infer_instance
def blkW (index : Nat) (v o : Digest) : List Word :=
  if bitc index then [lo64 v, hi64 v, lo64 (topHdr index), hi64 (topHdr index), 0, 0, lo64 o, hi64 o]
  else [lo64 o, hi64 o, lo64 (topHdr index), hi64 (topHdr index), 0, 0, lo64 v, hi64 v]
theorem wordsOf_topIn (index : Nat) (v o : Digest) : wordsOf (topIn index v o) = blkW index v o := by
  unfold topIn blkW bitc
  split <;>
  · rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]), wordsOf_append _ _ (by simp [bytesLE_length]),
      wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_zero16,
      wordsOf_bytesLE16]
    rename_i h
    simp only [h, ↓reduceIte, lo64, hi64, List.cons_append, List.nil_append]
/-- Offset of the sibling's high word in the block (and in its witness block). -/
def sOff (index : Nat) : Nat := if bitc index then 56 else 8
def bwi (index : Nat) : Nat := if bitc index then 7 else 1
theorem sOff_bwi (index : Nat) : sOff index = 8 * bwi index := by unfold sOff bwi; split <;> rfl
theorem blkW_hi (index : Nat) (v o : Digest) : (blkW index v o).getD (bwi index) 0 = hi64 o := by
  unfold blkW bwi; split <;> rfl
theorem blkW_other (index : Nat) (v o o' : Digest) (hlo : lo64 o = lo64 o') (i : Nat) (hi : i ≠ bwi index) :
    (blkW index v o).getD i 0 = (blkW index v o').getD i 0 := by
  unfold blkW; unfold bwi at hi
  split
  · rename_i h; rw [if_pos h] at hi
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp_all
  · rename_i h; rw [if_neg h] at hi
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp_all
theorem blkW_length (index : Nat) (v o : Digest) : (blkW index v o).length = 8 := by
  unfold blkW; split <;> rfl

theorem lo64_setTop (d : Digest) (c : Nat) : lo64 (WCT9.setTop d c) = lo64 d := by
  refine BitVec.eq_of_toNat_eq ?_
  unfold lo64
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.shiftRight_zero,
    WCT9.setTop_toNat]
  have e : (2 : Nat) ^ 112 = 2 ^ 64 * 2 ^ 48 := by rw [← pow_add]
  rw [e]
  generalize (2 : Nat) ^ 64 = A
  generalize (2 : Nat) ^ 48 = B
  rw [show c % 2 ^ 16 * (A * B) = (c % 2 ^ 16 * B) * A by rw [Nat.mul_comm A B, ← Nat.mul_assoc],
    Nat.add_mul_mod_self_right, Nat.mod_mul_right_mod]
/-- The candidate words: the sibling's high word with the omitted 16 bits set to `c`. -/
def wn (d : Digest) (c : Nat) : Nat := d.toNat % 2 ^ 112 / 2 ^ 64 + c * 2 ^ 48
theorem wn_lt (d : Digest) (c : Nat) (hc : c < 2 ^ 16) : wn d c < 2 ^ 64 := by
  unfold wn
  have h1 : d.toNat % 2 ^ 112 / 2 ^ 64 < 2 ^ 48 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    exact lt_of_lt_of_eq (Nat.mod_lt _ (by positivity)) (by norm_num)
  have h2 : c * 2 ^ 48 ≤ (2 ^ 16 - 1) * 2 ^ 48 := Nat.mul_le_mul_right _ (by omega)
  have h3 : (2 ^ 16 - 1) * 2 ^ 48 + 2 ^ 48 = (2 : Nat) ^ 64 := by norm_num
  omega
theorem hi64_setTop (d : Digest) (c : Nat) (hc : c < 2 ^ 16) :
    hi64 (WCT9.setTop d c) = BitVec.ofNat 64 (wn d c) := by
  refine BitVec.eq_of_toNat_eq ?_
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (wn_lt d c hc)]
  unfold hi64
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, WCT9.setTop_toNat, Nat.mod_eq_of_lt hc]
  have e : (2 : Nat) ^ 112 = 2 ^ 48 * 2 ^ 64 := by rw [← pow_add]
  rw [show c * 2 ^ 112 = (c * 2 ^ 48) * 2 ^ 64 by rw [e, Nat.mul_assoc],
    Nat.add_mul_div_right _ _ (by positivity)]
  exact Nat.mod_eq_of_lt (wn_lt d c hc)
theorem wn_succ (d : Digest) (c : Nat) : wn d c + 2 ^ 48 = wn d (c + 1) := by unfold wn; ring

/-- The sibling's high word sits 8 bytes past its witness slot offset. -/
theorem sOff_eq (index : Nat) :
    sOff index = SigGolfCandidate.T3M.Expand.sideOff (route index 0).1 11 + 8 := by
  unfold sOff SigGolfCandidate.T3M.Expand.sideOff
  have e : bitc index ↔ (route index 0).1 / 2 ^ 11 % 2 = 0 := Iff.rfl
  by_cases h : bitc index
  · rw [e] at h; rw [if_pos (e.mpr h), if_neg (by omega)]
  · rw [e] at h; rw [if_neg (fun h' => h (e.mp h')), if_pos (by omega)]
theorem bitc_iff (index : Nat) : bitc index ↔ index / 2 ^ 30 % 2 = 0 := by
  unfold bitc
  rw [show (route index 0).1 = index / 2 ^ 19 % 2 ^ 12 from rfl, show WCT9.topJ.val = 11 from rfl,
    show (2 : Nat) ^ 12 = 2 ^ 11 * 2 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod,
    Nat.div_div_eq_div_mul, ← pow_add]

/-! ### The loop -/

structure SInv (index : Nat) (v sib pk : Digest) (s8 : MachineState) (c : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 42829
  x5 : t.getReg .x5 = 0
  x30 : t.getReg .x30 = BitVec.ofNat 64 c
  x7 : t.getReg .x7 = BitVec.ofNat 64 (wn sib (c - 1))
  x28 : t.getReg .x28 = BitVec.ofNat 64 (NODE + sOff index)
  x31 : t.getReg .x31 = BitVec.ofNat 64 (0x2c48 + sOff index)
  x10 : t.getReg .x10 = BitVec.ofNat 64 NODE
  x11 : t.getReg .x11 = BitVec.ofNat 64 64
  x12 : t.getReg .x12 = BitVec.ofNat 64 NOUT
  x13 : t.getReg .x13 = lo64 pk
  x14 : t.getReg .x14 = hi64 pk
  x15 : t.getReg .x15 = BitVec.ofNat 64 (2 ^ 48)
  x17 : t.getReg .x17 = BitVec.ofNat 64 65536
  hc1 : 1 ≤ c
  hc2 : c < 65536
  blk : ∀ i < 8, t.getMem (BitVec.ofNat 64 (NODE + 8 * i)) = (blkW index v (WCT9.setTop sib (c - 1))).getD i 0
  frame : Frame s8 t (fun A => (NODE ≤ A ∧ A < NODE + 64) ∨ (NOUT ≤ A ∧ A < NOUT + 32))

def SQ (index : Nat) (sib : Digest) (s8 : MachineState) : Option Nat → MachineState → Prop
  | none, t => t.pc = pcOf 354
  | some c, t => t.pc = pcOf 351 ∧ (c = 0 → Frame s8 t (fun _ => False)) ∧
      (c ≠ 0 → c < 65536 ∧ t.getMem (BitVec.ofNat 64 (0x2c48 + sOff index)) = hi64 (WCT9.setTop sib c) ∧
        Frame s8 t (fun A => (NODE ≤ A ∧ A < NODE + 64) ∨ (NOUT ≤ A ∧ A < NOUT + 32) ∨
          A = 0x2c48 + sOff index))

theorem pk_split (root pk : Digest) : root = pk ↔ lo64 root = lo64 pk ∧ hi64 root = hi64 pk := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases h : i < 64
    · have := congrArg (fun x => x.getLsbD i) h0
      simpa [lo64, BitVec.getLsbD_extractLsb', h] using this
    · have := congrArg (fun x => x.getLsbD (i - 64)) h1
      simp [hi64, BitVec.getLsbD_extractLsb', show i - 64 < 64 by omega, show 64 + (i - 64) = i by omega] at this
      simpa using this

theorem a_lo (a : BitVec 256) : lo64 (a.extractLsb' 0 128) = a.extractLsb' 0 64 := by
  refine BitVec.eq_of_toNat_eq ?_
  simp only [lo64, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
  exact Nat.mod_mod_of_dvd _ (by norm_num)
theorem a_hi (a : BitVec 256) : hi64 (a.extractLsb' 0 128) = a.extractLsb' 64 64 := by
  refine BitVec.eq_of_toNat_eq ?_
  simp only [hi64, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod]

section loop
variable {im : Image} (hS : SrchAt im) {sk : BitVec 256} (index : Nat) (v sib pk : Digest) (s8 : MachineState)
include hS

omit hS in
theorem sOff_cases (index : Nat) : sOff index = 8 ∨ sOff index = 56 := by unfold sOff; split <;> simp

theorem search_loop : ∀ fuel c t, c + fuel = 65536 → SInv index v sib pk s8 c t →
    TBSim im sk t (fuel * 30) (WCT9.searchTop index v sib pk fuel c) (SQ index sib s8) := by
  intro fuel
  induction fuel with
  | zero => intro c t hcf hI; have := hI.hc2; omega
  | succ fuel ih =>
    intro c t hcf hI
    have hcs : c < 2 ^ 16 := by have := hI.hc2; omega
    have hso := sOff_cases index
    obtain ⟨t1, st1, p1, x7', mB, r1, f1⟩ := l1_spec hS t hI.pc (NODE + sOff index) (wn sib (c - 1)) (2 ^ 48)
      (by rcases hso with h | h <;> rw [h] <;> decide) (by rcases hso with h | h <;> rw [h] <;> decide)
      hI.x28 hI.x7 hI.x15
    rw [show wn sib (c - 1) + 2 ^ 48 = wn sib c by rw [wn_succ]; congr 1; have := hI.hc1; omega] at x7' mB
    have hblk1 : ∀ i < 8, t1.getMem (BitVec.ofNat 64 (NODE + 8 * i)) =
        (blkW index v (WCT9.setTop sib c)).getD i 0 := by
      intro i hi
      by_cases hib : i = bwi index
      · subst hib
        rw [← sOff_bwi, mB, blkW_hi, hi64_setTop _ _ hcs]
      · rw [f1.get (by simp only [NODE]; omega) (by rw [sOff_bwi]; omega), hI.blk i hi,
          blkW_other index v _ _ ((lo64_setTop _ _).trans (lo64_setTop _ _).symm) i hib]
    have g1 : ∀ r, r ≠ .x7 → t1.getReg r = t.getReg r := fun r hr => r1.get (by simpa using hr)
    have hq : hashInput t1 = toQ (pad64 (topIn index v (WCT9.setTop sib c))) := by
      rw [pad64_of_aligned _ (by rw [topIn_length])]
      refine hashInput_toQ t1 _ 0 NODE (topIn_length _ _ _) (by rw [g1 _ (by decide)]; exact hI.x10) (by decide)
        (by decide) (by rw [g1 _ (by decide)]; exact hI.x11) (by decide) ?_
      have hr := readWords_ext t1 (blkW index v (WCT9.setTop sib c)) NODE
        (fun i hi => by rw [blkW_length] at hi; exact hblk1 i hi)
      rw [blkW_length] at hr
      rw [wordsOf_topIn]
      exact hr
    have hv : hashArgumentsValid t1 = true :=
      hashArgs_const t1 NODE 64 NOUT (by rw [g1 _ (by decide)]; exact hI.x10) (by rw [g1 _ (by decide)]; exact hI.x11)
        (by rw [g1 _ (by decide)]; exact hI.x12) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hf1 : fetch im t1 = some (.base .ECALL) := by
      have hc := codeAt_srch hS 36 1 (by decide)
      exact (hc.fetch t1 p1).trans rfl
    unfold WCT9.searchTop
    rw [topNode_eq]
    refine (TBSim.steps st1 (tb_shortHash_bind' (W := fuel * 30 + 7) hf1 (by rw [g1 _ (by decide)]; exact hI.x5) hv hq
      (fun a => ?_))).mono ?_ (fun _ _ h => h)
    rotate_left
    · rw [pad64_of_aligned _ (by rw [topIn_length]), blocks_toQ ⟨by rw [topIn_length]; omega,
        by rw [topIn_length]⟩, topIn_length]; omega
    set t2 := writeHash t1 a with ht2
    have p2 : t2.pc = pcOf 42832 := by rw [ht2, pc_writeHash, p1]; rfl
    have g2 : ∀ r, r ≠ .x7 → t2.getReg r = t.getReg r := fun r hr => by rw [ht2, getReg_writeHash]; exact g1 r hr
    have fw := Frame.writeHash t1 a NOUT (by rw [g1 _ (by decide)]; exact hI.x12) (by decide)
    have hlo : t2.getMem (BitVec.ofNat 64 NOUT) = a.extractLsb' 0 64 := by
      have := (DigAt.writeHash_lo t1 a NOUT (by rw [g1 _ (by decide)]; exact hI.x12) (by decide)).1
      rw [this, ← a_lo]; rfl
    have hhi : t2.getMem (BitVec.ofNat 64 (NOUT + 8)) = a.extractLsb' 64 64 := by
      have := (DigAt.writeHash_lo t1 a NOUT (by rw [g1 _ (by decide)]; exact hI.x12) (by decide)).2
      rw [this, ← a_hi]; rfl
    obtain ⟨t3, st3, p3, r3, f3⟩ := l2_spec hS t2 p2 (by rw [g2 _ (by decide)]; exact hI.x12)
    rw [hlo, g2 _ (by decide), hI.x13] at p3
    have hsplit := pk_split (a.extractLsb' 0 128) pk
    rw [a_lo, a_hi] at hsplit
    have F3 : Frame s8 t3 (fun A => (NODE ≤ A ∧ A < NODE + 64) ∨ (NOUT ≤ A ∧ A < NOUT + 32)) := by
      refine (((hI.frame.trans f1).trans fw).trans f3).mono (fun A _ h => ?_)
      rcases h with ((h | h) | h) | h
      · exact h
      · left; subst h; rcases hso with e | e <;> rw [e] <;> simp only [NODE] <;> omega
      · right; exact h
      · exact h.elim
    have g3 : ∀ r, r ≠ .x7 → r ≠ .x6 → t3.getReg r = t.getReg r := fun r h7 h6 => by
      rw [r3.get (by simpa using h6)]; exact g2 r h7
    have next : ∀ (u : MachineState), u.pc = pcOf 42836 →
        (∀ r, r ≠ .x7 → r ≠ .x6 → u.getReg r = t.getReg r) → u.getReg .x7 = BitVec.ofNat 64 (wn sib c) →
        (∀ i < 8, u.getMem (BitVec.ofNat 64 (NODE + 8 * i)) = (blkW index v (WCT9.setTop sib c)).getD i 0) →
        Frame s8 u (fun A => (NODE ≤ A ∧ A < NODE + 64) ∨ (NOUT ≤ A ∧ A < NOUT + 32)) →
        TBSim im sk u (fuel * 30 + 3) (WCT9.searchTop index v sib pk fuel (c + 1)) (SQ index sib s8) := by
      intro u pu gu x7u blku Fu
      obtain ⟨t4, st4, p4, x30', r4, f4⟩ := l4_spec hS u pu c hI.hc2
        (by rw [gu _ (by decide) (by decide)]; exact hI.x30) (by rw [gu _ (by decide) (by decide)]; exact hI.x17)
      by_cases hlast : c + 1 < 65536
      · rw [if_pos hlast] at p4
        have g4 : ∀ r, r ≠ .x30 → t4.getReg r = u.getReg r := fun r hr => r4.get (by simpa using hr)
        have hI' : SInv index v sib pk s8 (c + 1) t4 := by
          refine ⟨p4, ?_, x30', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hlast, ?_, ?_⟩
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x5
          · rw [g4 _ (by decide), x7u]; rfl
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x28
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x31
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x10
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x11
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x12
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x13
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x14
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x15
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x17
          · intro i hi; rw [f4.get (by simp only [NODE]; omega) (fun h => h), blku i hi, Nat.add_sub_cancel]
          · exact (Fu.trans f4).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)
        exact (TBSim.steps st4 (ih (c + 1) t4 (by omega) hI')).mono (by omega) (fun _ _ h => h)
      · rw [if_neg hlast] at p4
        have hfuel : fuel = 0 := by omega
        subst hfuel
        have st5 := jal_at hS t4 42838 354 (by decide) (by decide) 2199740527 rfl (by decide) p4
        unfold WCT9.searchTop
        exact (TBSim.steps (st4.trans st5) (TBSim.pure (show (t4.setPC (pcOf 354)).pc = pcOf 354 from rfl))).mono
          (by omega) (fun _ _ h => h)
    by_cases hl : a.extractLsb' 0 64 = lo64 pk
    · rw [if_pos hl] at p3
      obtain ⟨t4, st4, p4, r4, f4⟩ := l3_spec hS t3 p3 (by rw [g3 _ (by decide) (by decide)]; exact hI.x12)
      rw [f3.get (by decide) (by simp), hhi, r3.get (by decide), g2 _ (by decide), hI.x14] at p4
      by_cases hh : a.extractLsb' 64 64 = hi64 pk
      · rw [if_pos hh] at p4
        have hroot : a.extractLsb' 0 128 = pk := hsplit.mpr ⟨hl, hh⟩
        rw [if_pos hroot]
        obtain ⟨t5, st5, p5, m5, r5, f5⟩ := f1_spec hS t4 p4 (0x2c48 + sOff index)
          (by rcases hso with e | e <;> rw [e] <;> decide) (by rcases hso with e | e <;> rw [e] <;> decide)
          (by rw [r4.get (by decide), g3 _ (by decide) (by decide)]; exact hI.x31)
        have st6 := jal_at hS t5 42840 351 (by decide) (by decide) 2178769007 rfl (by decide) p5
        refine (TBSim.steps (st3.trans (st4.trans (st5.trans st6))) (TBSim.pure ⟨rfl,
          fun h => absurd h (by have := hI.hc1; omega), fun _ => ⟨hI.hc2, ?_, ?_⟩⟩)).mono (by omega)
          (fun _ _ h => h)
        · show t5.getMem _ = _
          rw [m5, r4.get (by decide), r3.get (by decide), ht2, getReg_writeHash, x7', hi64_setTop _ _ hcs]
        · show Frame s8 (t5.setPC (pcOf 351)) _
          refine ((F3.trans f4).trans f5).mono (fun A _ h => ?_)
          rcases h with (h | h) | h
          · rcases h with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · exact h.elim
          · exact Or.inr (Or.inr h)
      · rw [if_neg hh] at p4
        have hroot : a.extractLsb' 0 128 ≠ pk := fun h => hh (hsplit.mp h).2
        rw [if_neg hroot]
        refine (TBSim.steps (st3.trans st4) (next t4 p4 ?_ ?_ ?_ ?_)).mono (by omega) (fun _ _ h => h)
        · intro r h7 h6; rw [r4.get (by simpa using h6)]; exact g3 r h7 h6
        · rw [r4.get (by decide), r3.get (by decide), ht2, getReg_writeHash, x7']
        · intro i hi
          rw [f4.get (by simp only [NODE]; omega) (fun h => h), f3.get (by simp only [NODE]; omega) (fun h => h),
            ht2, fw.get (by simp only [NODE]; omega) (by simp only [NODE, NOUT]; omega), hblk1 i hi]
        · exact (F3.trans f4).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)
    · rw [if_neg hl] at p3
      have hroot : a.extractLsb' 0 128 ≠ pk := fun h => hl (hsplit.mp h).1
      rw [if_neg hroot]
      refine (TBSim.steps st3 (next t3 p3 (fun r h7 h6 => g3 r h7 h6) ?_ ?_ F3)).mono (by omega)
        (fun _ _ h => h)
      · rw [r3.get (by decide), ht2, getReg_writeHash, x7']
      · intro i hi
        rw [f3.get (by simp only [NODE]; omega) (fun h => h), ht2,
          fw.get (by simp only [NODE]; omega) (by simp only [NODE, NOUT]; omega), hblk1 i hi]
end loop


theorem shr_and (x : Nat) (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x >>> 30 &&& 1) = BitVec.ofNat 64 (x / 2 ^ 30 % 2) := by
  show (BitVec.ofNat 64 x >>> 30 &&& 1#64) = _
  refine BitVec.eq_of_toNat_eq ?_
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega)]
  rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, pow_one,
    Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num) : x / 2 ^ 30 % 2 < 2 ^ 64)]

/-- The search after the layers, from word 342 to a halt address: candidate 0 is the old comparison. -/
theorem search_entry {im : Image} (hS : SrchAt im) {sk : BitVec 256} (index : Nat) (hidx : index < 2 ^ 31)
    (v sib root0 pk : Digest) (hsib : WCT9.setTop sib 0 = sib) (s8 : MachineState) (hpc : s8.pc = pcOf 342)
    (hx5 : s8.getReg .x5 = 0) (henc : DigAt s8 ENC root0)
    (hpk0 : s8.getMem (BitVec.ofNat 64 0xA0) = lo64 pk) (hpk1 : s8.getMem (BitVec.ofNat 64 0xA8) = hi64 pk)
    (hix : s8.getMem (BitVec.ofNat 64 0x20550) = BitVec.ofNat 64 index)
    (hblk : ∀ i < 8, s8.getMem (BitVec.ofNat 64 (NODE + 8 * i)) = (blkW index v sib).getD i 0) :
    TBSim im sk s8 (65535 * 30 + 100)
      (if root0 = pk then pure (some 0) else WCT9.searchTop index v sib pk WCT9.searchFuel 1) (SQ index sib s8) := by
  have st0 := w342_step hS s8 hpc
  set u0 := s8.setPC (pcOf 42795) with hu0
  have gu0 : ∀ A, u0.getMem A = s8.getMem A := fun _ => rfl
  have ru0 : ∀ r, u0.getReg r = s8.getReg r := fun _ => rfl
  obtain ⟨u1, st1, p1, x28, x13, x14, r1, f1⟩ := s1_spec hS u0 rfl
  rw [gu0, gu0, henc.1, hpk0] at p1
  rw [gu0, hpk0] at x13
  rw [gu0, hpk1] at x14
  have hsplit := pk_split root0 pk
  have miss : root0 ≠ pk → ∀ (u : MachineState) (k : Nat), Steps im s8 k k u → k ≤ 12 → u.pc = pcOf 42805 →
      (∀ r, r ≠ .x6 → r ≠ .x13 → r ≠ .x14 → r ≠ .x28 → r ≠ .x29 → u.getReg r = s8.getReg r) →
      u.getReg .x13 = lo64 pk → u.getReg .x14 = hi64 pk → Frame s8 u (fun _ => False) →
      TBSim im sk s8 (65535 * 30 + 100)
        (if root0 = pk then pure (some 0) else WCT9.searchTop index v sib pk WCT9.searchFuel 1) (SQ index sib s8) := by
    intro hne u k stu hk pu gu u13 u14 fu
    rw [if_neg hne]
    obtain ⟨u2, st2, p2, x7a, r2, f2⟩ := m1_spec hS u pu
    rw [fu.get (by decide) (fun h => h), hix, shr_and index (by omega)] at p2
    have hbit : (BitVec.ofNat 64 (index / 2 ^ 30 % 2) = 0) ↔ bitc index := by
      rw [bitc_iff]
      constructor
      · intro h; have := congrArg BitVec.toNat h; simp at this; omega
      · intro h; rw [h]; rfl
    -- reach the setup block with x7 = sOff index
    obtain ⟨u3, k3, st3, hk3, p3, x7b, r3, f3⟩ : ∃ u3 k3, Steps im u2 k3 k3 u3 ∧ k3 ≤ 1 ∧ u3.pc = pcOf 42813 ∧
        u3.getReg .x7 = BitVec.ofNat 64 (sOff index) ∧ RegsExcept u2 u3 [.x7] ∧ Frame u2 u3 (fun _ => False) := by
      by_cases hb : bitc index
      · rw [if_pos (hbit.mpr hb)] at p2
        obtain ⟨u3, st3, p3, x7b, r3, f3⟩ := m2_spec hS u2 p2
        refine ⟨u3, 1, st3, le_rfl, p3, ?_, r3, f3⟩
        rw [x7b]; unfold sOff; rw [if_pos hb]
      · rw [if_neg (fun h => hb (hbit.mp h))] at p2
        refine ⟨u2, 0, Steps.refl u2, by omega, p2, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
        rw [x7a]; unfold sOff; rw [if_neg hb]
    obtain ⟨u4, st4, p4, x28', x31', x7', x15', x10', x11', x12', x30', x17', r4, f4⟩ :=
      sd_spec hS u3 p3 (sOff index) (sOff_cases index) x7b
    have F4 : Frame s8 u4 (fun _ => False) :=
      (((fu.trans f2).trans f3).trans f4).mono (fun A _ h => by
        rcases h with ((h | h) | h) | h <;> exact h)
    have g4 : ∀ r, r ∉ [Reg.x6, .x7, .x10, .x11, .x12, .x13, .x14, .x15, .x17, .x28, .x29, .x30, .x31] →
        u4.getReg r = s8.getReg r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [r4.get (by simp [hr]),
        r3.get (by simp [hr]), r2.get (by simp [hr]),
        gu r hr.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2.2.2.1]
    have F3 : Frame s8 u3 (fun _ => False) :=
      ((fu.trans f2).trans f3).mono (fun A _ h => by rcases h with (h | h) | h <;> exact h)
    have hI : SInv index v sib pk s8 1 u4 := by
      refine ⟨p4, ?_, x30', ?_, x28', x31', x10', x11', x12', ?_, ?_, x15', x17', le_rfl, by decide, ?_, ?_⟩
      · rw [g4 _ (by decide)]; exact hx5
      · rw [x7', F3.get (show NODE + sOff index < 2 ^ 64 by unfold sOff; split <;> simp only [NODE] <;> omega)
          (fun h => h),
          sOff_bwi, hblk _ (by unfold bwi; split <;> omega), blkW_hi, show 1 - 1 = 0 from rfl]
        have e := hi64_setTop sib 0 (by decide)
        rw [hsib] at e
        exact e
      · rw [r4.get (by decide), r3.get (by decide), r2.get (by decide)]; exact u13
      · rw [r4.get (by decide), r3.get (by decide), r2.get (by decide)]; exact u14
      · intro i hi; rw [F4.get (by simp only [NODE]; omega) (fun h => h), hblk i hi, show 1 - 1 = 0 from rfl, hsib]
      · exact F4.mono (fun A _ h => h.elim)
    have hloop := search_loop hS (sk := sk) index v sib pk s8 65535 1 u4 (by decide) hI
    refine (TBSim.steps (stu.trans (st2.trans (st3.trans st4))) hloop).mono ?_ (fun _ _ h => h)
    omega
  by_cases hl : root0.extractLsb' 0 64 = lo64 pk
  · rw [if_pos hl] at p1
    obtain ⟨u2, st2, p2, r2, f2⟩ := s2_spec hS u1 p1 x28
    rw [f1.get (by decide) (fun h => h), gu0, henc.2] at p2
    rw [x14] at p2
    by_cases hh : root0.extractLsb' 64 64 = hi64 pk
    · rw [if_pos hh] at p2
      have hroot : root0 = pk := hsplit.mpr ⟨hl, hh⟩
      rw [if_pos hroot]
      have st3 := jal_at hS u2 42804 351 (by decide) (by decide) 2329763951 rfl (by decide) p2
      refine (TBSim.steps (st0.trans (st1.trans (st2.trans st3))) (TBSim.pure ⟨rfl, fun _ => ?_,
        fun h => absurd rfl h⟩)).mono (by omega) (fun _ _ h => h)
      intro A hA hn
      show u2.getMem _ = s8.getMem _
      exact (f1.trans f2) A hA (fun h => by rcases h with h | h <;> exact h)
    · rw [if_neg hh] at p2
      exact miss (fun h => hh (hsplit.mp h).2) u2 _ (st0.trans (st1.trans st2)) (by omega) p2
        (fun r h6 h13 h14 h28 h29 => by rw [r2.get (by simpa using h6), r1.get (by simp [h6, h13, h14, h28, h29]), ru0])
        (by rw [r2.get (by decide)]; exact x13) (by rw [r2.get (by decide)]; exact x14)
        ((f1.trans f2).mono (fun A _ h => by rcases h with h | h <;> exact h))
  · rw [if_neg hl] at p1
    exact miss (fun h => hl (hsplit.mp h).1) u1 _ (st0.trans st1) (by omega) p1
      (fun r h6 h13 h14 h28 h29 => by rw [r1.get (by simp [h6, h13, h14, h28, h29]), ru0]) x13 x14 f1


/-! ### The top layer's last block, as the search reads it -/

theorem topBlk_words (sig : WCT9.Signature) (index : Nat) (v : Digest) (t : MachineState)
    (h : SigGolfCandidate.T3M.Expand.TopBlkG (WCT9.toT3Signature sig) index 0 v t) :
    t.readWords (BitVec.ofNat 64 NODE) 8 = blkW index v (WCT9.topSib sig) := by
  rw [← wordsOf_topIn]
  unfold SigGolfCandidate.T3M.Expand.TopBlkG at h
  have hl : SigGolfCandidate.T3M.Expand.lpath (WCT9.toT3Signature sig) 0 11 = WCT9.topSib sig := by
    unfold SigGolfCandidate.T3M.Expand.lpath; rw [dif_pos (by decide)]; rfl
  rw [h, hl]
  unfold topIn topHdr
  have h11 : WCT9.topJ.val = 11 := rfl
  simp only [h11]
  by_cases hc : (route index 0).1 / 2 ^ 11 % 2 = 0
  · simp only [hc, ↓reduceIte]
  · simp only [hc, ↓reduceIte]

theorem topBlk_get (sig : WCT9.Signature) (index : Nat) (v : Digest) (t : MachineState)
    (h : SigGolfCandidate.T3M.Expand.TopBlkG (WCT9.toT3Signature sig) index 0 v t) :
    ∀ i < 8, t.getMem (BitVec.ofNat 64 (NODE + 8 * i)) = (blkW index v (WCT9.topSib sig)).getD i 0 := by
  intro i hi
  have e := topBlk_words sig index v t h
  rw [readWords_eight] at e
  rw [← e]
  interval_cases i <;> rfl

/-! ### The reference expander split at the old front -/

/-- After the front: the layers (with the top sibling read as given), then candidate 0 or the search. -/
def tailProgS (pk : PublicKey) (sig : WCT9.Signature) :
    Option (BitVec 32 × HashOutput × Digest) → M (Option (HashOutput × WCT9.Witness))
  | none => pure none
  | some (counter, N, root) => do
    let some (v, root', counters) ← WCT9.expandLayersT sig (WCT9.digestIndex N) (WCT9.topSib sig) 4 (.forest root)
      | pure none
    let oc ← if root' = pk then pure (some 0) else
      WCT9.searchTop (WCT9.digestIndex N) v (WCT9.topSib sig) pk WCT9.searchFuel 1
    match oc with
    | none => pure none
    | some c => pure (some (N, ⟨WCT9.fillTop sig c, counter, fun lay => counters.getD lay.val 0⟩))

theorem expandN_splitS (m : Message) (pk : PublicKey) (sig : WCT9.Signature) (hp : WCT9.proj sig = sig) :
    ClaudeWCT.W9.T3M.expandN m pk sig = newProg m sig >>= tailProgS pk sig := by
  unfold ClaudeWCT.W9.T3M.expandN WCT9.expandS newProg
  rw [hp, bind_assoc]
  dsimp only
  refine bind_congr (fun r => ?_)
  rcases r with _ | ⟨counter, N⟩
  · first | rfl | (simp only [pure_bind]; done) | (simp only [pure_bind]; rfl)
  · simp only [bind_assoc, pure_bind]
    refine bind_congr (fun root => ?_)
    simp only [pure_bind, tailProgS]
    refine bind_congr (fun x => ?_)
    rcases x with _ | ⟨v, root', counters⟩
    · rfl
    · by_cases h : root' = pk
      · simp only [h, ↓reduceIte, pure_bind]
        show _ = pure (some (N, (⟨WCT9.proj sig, counter, _⟩ : WCT9.Witness)))
        rw [hp]
      · simp only [h, ↓reduceIte]
        refine bind_congr (fun oc => ?_)
        rcases oc with _ | c <;> rfl

end ClaudeWCT.W9.Machine.Expand
end
