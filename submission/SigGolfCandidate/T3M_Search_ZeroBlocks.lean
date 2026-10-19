import SigGolfCandidate.T3M_Search_CounterSearch
import SigGolfCandidate.T3_Nonbinary_LowerLayout

namespace SigGolfCandidate.T3M.Search.Zero
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def lanes0 (x : BitVec 64) : BitVec 64 :=
  ((x >>> 1 ||| x ||| x >>> 2) ^^^ 18446744073709551615#64) &&& 1317624576693539401#64

def clear (x : BitVec 64) : BitVec 64 := x &&& (x - 1#64)

sym_block z354_0 := symRun {noAlias := true} z_0 (pcOf 42841) 200
sym_block z543_0 := symRun {noAlias := true} z_0 (pcOf 20832) 200
sym_block z354_2 := symRun {noAlias := true} z_2 (pcOf 42843) 200
sym_block z543_2 := symRun {noAlias := true} z_2 (pcOf 20834) 200
sym_block z354_5 := symRun {noAlias := true} z_5 (pcOf 42846) 200
sym_block z543_5 := symRun {noAlias := true} z_5 (pcOf 20837) 200
sym_block z354_22 := symRun {noAlias := true} z_22 (pcOf 42863) 200
sym_block z543_22 := symRun {noAlias := true} z_22 (pcOf 20854) 200
sym_block z354_23 := symRun {noAlias := true} z_23 (pcOf 42864) 200
sym_block z543_23 := symRun {noAlias := true} z_23 (pcOf 20855) 200
sym_block z354_27 := symRun {noAlias := true} z_27 (pcOf 42868) 200
sym_block z543_27 := symRun {noAlias := true} z_27 (pcOf 20859) 200
sym_block z354_28 := symRun {noAlias := true} z_28 (pcOf 42869) 200
sym_block z543_28 := symRun {noAlias := true} z_28 (pcOf 20860) 200
sym_block z354_32 := symRun {noAlias := true} z_32 (pcOf 42873) 200
sym_block z543_32 := symRun {noAlias := true} z_32 (pcOf 20864) 200
sym_block z354_33 := symRun {noAlias := true} z_33 (pcOf 42874) 200
sym_block z543_33 := symRun {noAlias := true} z_33 (pcOf 20865) 200
sym_block z354_34 := symRun {noAlias := true} z_34 (pcOf 42875) 200
sym_block z543_34 := symRun {noAlias := true} z_34 (pcOf 20866) 200
sym_block z354_36 := symRun {noAlias := true} (z_36 354) (pcOf 42877) 200
sym_block z543_36 := symRun {noAlias := true} (z_36 543) (pcOf 20868) 200
sym_block z354_37 := symRun {noAlias := true} (z_37 354) (pcOf 42878) 200
sym_block z543_37 := symRun {noAlias := true} (z_37 543) (pcOf 20869) 200

def end0 (b : Nat) : E := rebase z354_0.res.pc (pcOf (zBase b + 5)) (pcOf (zBase b + 2))
def end2 (b : Nat) : E := rebase z354_2.res.pc (pcOf (zBase b + 37)) (pcOf (zBase b + 5))
def end22 (b : Nat) : E := rebase z354_22.res.pc (pcOf (zBase b + 27)) (pcOf (zBase b + 23))
def end27 (b : Nat) : E := rebase z354_27.res.pc (pcOf (zBase b + 32)) (pcOf (zBase b + 28))
def end32 (b : Nat) : E := rebase z354_32.res.pc (pcOf (zBase b + 34)) (pcOf (zBase b + 33))
def end34 (b : Nat) : E := rebase z354_34.res.pc (pcOf (zBase b + 37)) (pcOf (zBase b + 36))

theorem run0 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun {noAlias := true} z_0 (pcOf (zBase b)) 200 =
      some ⟨z354_0.res.st, end0 b, z354_0.res.stop, z354_0.res.steps, z354_0.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact z354_0.trans (congrArg some (by kernel_rfl))
  · exact z543_0.trans (congrArg some (by kernel_rfl))

theorem run2 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun {noAlias := true} z_2 (pcOf (zBase b + 2)) 200 =
      some ⟨z354_2.res.st, end2 b, z354_2.res.stop, z354_2.res.steps, z354_2.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact z354_2.trans (congrArg some (by kernel_rfl))
  · exact z543_2.trans (congrArg some (by kernel_rfl))

theorem run5 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun {noAlias := true} z_5 (pcOf (zBase b + 5)) 200 =
      some ⟨z354_5.res.st, .c (pcOf (zBase b + 22)), .endOfCode, 17, 20⟩ := by
  rcases hb with rfl | rfl
  · exact z354_5.trans (congrArg some (by kernel_rfl))
  · exact z543_5.trans (congrArg some (by kernel_rfl))

theorem run22 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun {noAlias := true} z_22 (pcOf (zBase b + 22)) 200 =
      some ⟨z354_22.res.st, end22 b, z354_22.res.stop, z354_22.res.steps, z354_22.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact z354_22.trans (congrArg some (by kernel_rfl))
  · exact z543_22.trans (congrArg some (by kernel_rfl))

theorem run23 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun {noAlias := true} z_23 (pcOf (zBase b + 23)) 200 =
      some ⟨z354_23.res.st, .c (pcOf (zBase b + 22)), z354_23.res.stop, 4, 4⟩ := by
  rcases hb with rfl | rfl
  · exact z354_23.trans (congrArg some (by kernel_rfl))
  · exact z543_23.trans (congrArg some (by kernel_rfl))

theorem run27 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun {noAlias := true} z_27 (pcOf (zBase b + 27)) 200 =
      some ⟨z354_27.res.st, end27 b, z354_27.res.stop, z354_27.res.steps, z354_27.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact z354_27.trans (congrArg some (by kernel_rfl))
  · exact z543_27.trans (congrArg some (by kernel_rfl))

theorem run28 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun {noAlias := true} z_28 (pcOf (zBase b + 28)) 200 =
      some ⟨z354_28.res.st, .c (pcOf (zBase b + 27)), z354_28.res.stop, 4, 4⟩ := by
  rcases hb with rfl | rfl
  · exact z354_28.trans (congrArg some (by kernel_rfl))
  · exact z543_28.trans (congrArg some (by kernel_rfl))

theorem run32 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun {noAlias := true} z_32 (pcOf (zBase b + 32)) 200 =
      some ⟨z354_32.res.st, end32 b, z354_32.res.stop, z354_32.res.steps, z354_32.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact z354_32.trans (congrArg some (by kernel_rfl))
  · exact z543_32.trans (congrArg some (by kernel_rfl))

theorem run33 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun {noAlias := true} z_33 (pcOf (zBase b + 33)) 200 =
      some ⟨z354_33.res.st, .c (pcOf (zBase b + 34)), .endOfCode, 1, 1⟩ := by
  rcases hb with rfl | rfl
  · exact z354_33.trans (congrArg some (by kernel_rfl))
  · exact z543_33.trans (congrArg some (by kernel_rfl))

theorem run34 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun {noAlias := true} z_34 (pcOf (zBase b + 34)) 200 =
      some ⟨z354_34.res.st, end34 b, z354_34.res.stop, z354_34.res.steps, z354_34.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact z354_34.trans (congrArg some (by kernel_rfl))
  · exact z543_34.trans (congrArg some (by kernel_rfl))

theorem run36 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun {noAlias := true} (z_36 b) (pcOf (zBase b + 36)) 200 =
      some ⟨z354_36.res.st, .c (pcOf (zBase b + 38)), z354_36.res.stop, 1, 1⟩ := by
  rcases hb with rfl | rfl
  · exact z354_36.trans (congrArg some (by kernel_rfl))
  · exact z543_36.trans (congrArg some (by kernel_rfl))

theorem run37 {b : Nat} (hb : b = 354 ∨ b = 543) :
    symRun {noAlias := true} (z_37 b) (pcOf (zBase b + 37)) 200 =
      some ⟨z354_37.res.st, .c (pcOf (b + 468)), z354_37.res.stop, 1, 1⟩ := by
  rcases hb with rfl | rfl
  · exact z354_37.trans (congrArg some (by kernel_rfl))
  · exact z543_37.trans (congrArg some (by kernel_rfl))

variable {image : Image} {b : Nat}

theorem setup_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (zBase b + 5)) :
    ∃ t, Steps image s 17 20 t ∧ t.pc = pcOf (zBase b + 22) ∧
      t.getReg .x29 = lanes0 (s.getReg .x6) ∧ t.getReg .x28 = lanes0 (s.getReg .x7) ∧
      t.getReg .x21 = 0 ∧ RegsExcept s t [.x20, .x21, .x28, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run5 hK.2.1) (codeAt_zero hK 2 5 z_5 (by rfl)) s hpc
    (by simp [z354_5.res, rv_simp]), rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [z354_5.res, rv_simp, lanes0]
  · simp [z354_5.res, rv_simp, lanes0]
  · simp [z354_5.res, rv_simp]
  · intro r hr; cases r <;> simp_all [z354_5.res, rv_simp] <;> rfl
  · intro A _ _; simp [z354_5.res, rv_simp]

theorem clear_lo_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (zBase b + 23)) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (zBase b + 22) ∧
      t.getReg .x29 = clear (s.getReg .x29) ∧ t.getReg .x21 = s.getReg .x21 + 1#64 ∧
      RegsExcept s t [.x21, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run23 hK.2.1) (codeAt_zero hK 4 23 z_23 (by rfl)) s hpc
    (by simp [z354_23.res, rv_simp]), rfl, ?_, ?_, ?_, ?_⟩
  · simp only [z354_23.res, rv_simp, clear, BitVec.sub_eq_add_neg]
  · simp [z354_23.res, rv_simp]
  · intro r hr; cases r <;> simp_all [z354_23.res, rv_simp] <;> rfl
  · intro A _ _; simp [z354_23.res, rv_simp]

theorem clear_hi_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (zBase b + 28)) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (zBase b + 27) ∧
      t.getReg .x28 = clear (s.getReg .x28) ∧ t.getReg .x21 = s.getReg .x21 + 1#64 ∧
      RegsExcept s t [.x21, .x28, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run28 hK.2.1) (codeAt_zero hK 6 28 z_28 (by rfl)) s hpc
    (by simp [z354_28.res, rv_simp]), rfl, ?_, ?_, ?_, ?_⟩
  · simp only [z354_28.res, rv_simp, clear, BitVec.sub_eq_add_neg]
  · simp [z354_28.res, rv_simp]
  · intro r hr; cases r <;> simp_all [z354_28.res, rv_simp] <;> rfl
  · intro A _ _; simp [z354_28.res, rv_simp]

theorem entry_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (zBase b))
    (lay : Nat) (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (zBase b + (if lay ≠ 3 then 2 else 5)) ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run0 hK.2.1) (codeAt_zero hK 0 0 z_0 (by rfl)) s hpc
    (by simp [z354_0.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, end0, rebase, z354_0.res, E.eval, CmpOp.eval, BinOp.eval, h8]
    interval_cases lay <;> simp
  · intro r hr; cases r <;> simp_all [z354_0.res, rv_simp] <;> rfl
  · intro A _ _; simp [z354_0.res, rv_simp]

theorem extra_credit_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (zBase b + 2)) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc = pcOf (zBase b + (if clear (s.getReg .x28) = 0#64 then 37 else 5)) ∧
      RegsExcept s t [.x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run2 hK.2.1) (codeAt_zero hK 1 2 z_2 (by rfl)) s hpc
    (by simp [z354_2.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, end2, rebase, z354_2.res, E.eval, CmpOp.eval, BinOp.eval]
    have hm : ∀ y : BitVec 64, y + 18446744073709551615#64 = y - 1#64 := fun y => by
      rw [BitVec.sub_eq_add_neg]; rfl
    simp only [clear, hm]
    split_ifs <;> simp_all
  · intro r hr; cases r <;> simp_all [z354_2.res, rv_simp] <;> rfl
  · intro A _ _; simp [z354_2.res, rv_simp]

theorem test_lo_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (zBase b + 22)) :
    ∃ t, Steps image s 1 1 t ∧
      t.pc = pcOf (zBase b + (if s.getReg .x29 = 0#64 then 27 else 23)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run22 hK.2.1) (codeAt_zero hK 3 22 z_22 (by rfl)) s hpc
    (by simp [z354_22.res, rv_simp]), ?_, ?_, ?_⟩
  · by_cases h : s.getReg .x29 = 0#64 <;> simp [end22, rebase, z354_22.res, rv_simp, h]
  · intro r hr; cases r <;> simp_all [z354_22.res, rv_simp] <;> rfl
  · intro A _ _; simp [z354_22.res, rv_simp]

theorem test_hi_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (zBase b + 27)) :
    ∃ t, Steps image s 1 1 t ∧
      t.pc = pcOf (zBase b + (if s.getReg .x28 = 0#64 then 32 else 28)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run27 hK.2.1) (codeAt_zero hK 5 27 z_27 (by rfl)) s hpc
    (by simp [z354_27.res, rv_simp]), ?_, ?_, ?_⟩
  · by_cases h : s.getReg .x28 = 0#64 <;> simp [end27, rebase, z354_27.res, rv_simp, h]
  · intro r hr; cases r <;> simp_all [z354_27.res, rv_simp] <;> rfl
  · intro A _ _; simp [z354_27.res, rv_simp]

theorem checksum_test_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (zBase b + 32)) :
    ∃ t, Steps image s 1 1 t ∧
      t.pc = pcOf (zBase b + (if s.getReg .x17 = s.getReg .x25 then 33 else 34)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run32 hK.2.1) (codeAt_zero hK 7 32 z_32 (by rfl)) s hpc
    (by simp [z354_32.res, rv_simp]), ?_, ?_, ?_⟩
  · by_cases h : s.getReg .x17 = s.getReg .x25 <;> simp [end32, rebase, z354_32.res, rv_simp, h]
  · intro r hr; cases r <;> simp_all [z354_32.res, rv_simp] <;> rfl
  · intro A _ _; simp [z354_32.res, rv_simp]

theorem checksum_inc_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (zBase b + 33)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (zBase b + 34) ∧
      t.getReg .x21 = s.getReg .x21 + 1#64 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run33 hK.2.1) (codeAt_zero hK 8 33 z_33 (by rfl)) s hpc
    (by simp [z354_33.res, rv_simp]), rfl, ?_, ?_, ?_⟩
  · simp [z354_33.res, rv_simp]
  · intro r hr; cases r <;> simp_all [z354_33.res, rv_simp] <;> rfl
  · intro A _ _; simp [z354_33.res, rv_simp]

theorem limit_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (zBase b + 34)) (n : Nat)
    (hn : n < 2 ^ 64) (h21 : s.getReg .x21 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (zBase b + (if n ≤ 5 then 36 else 37)) ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run34 hK.2.1) (codeAt_zero hK 9 34 z_34 (by rfl)) s hpc
    (by simp [z354_34.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, end34, rebase, z354_34.res, E.eval, CmpOp.eval, BinOp.eval, h21]
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    by_cases h : n ≤ 5
    · simp [show n < 6 by omega, h]
    · simp [show ¬ n < 6 by omega, h]
  · intro r hr; cases r <;> simp_all [z354_34.res, rv_simp] <;> rfl
  · intro A _ _; simp [z354_34.res, rv_simp]

theorem exit_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (o : Nat) (ho : o = 36 ∨ o = 37)
    (hpc : s.pc = pcOf (zBase b + o)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if o = 36 then pcOf (zBase b + 38) else pcOf (b + 468)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  rcases ho with rfl | rfl
  · refine ⟨_, symRun_sound (run36 hK.2.1) (codeAt_zero hK 10 36 (z_36 b) (by rfl)) s hpc
      (by simp [z354_36.res, rv_simp]), rfl, ?_, ?_⟩
    · intro r hr; cases r <;> simp_all [z354_36.res, rv_simp] <;> rfl
    · intro A _ _; simp [z354_36.res, rv_simp]
  · refine ⟨_, symRun_sound (run37 hK.2.1) (codeAt_zero hK 11 37 (z_37 b) (by rfl)) s hpc
      (by simp [z354_37.res, rv_simp]), rfl, ?_, ?_⟩
    · intro r hr; cases r <;> simp_all [z354_37.res, rv_simp] <;> rfl
    · intro A _ _; simp [z354_37.res, rv_simp]

end SigGolfCandidate.T3M.Search.Zero

section
namespace SigGolfCandidate.T3M.Search.Rank
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest lowerWord)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def bad (x : BitVec 64) (i limit : Nat) : BitVec 64 :=
  if ((x >>> (9*i)) &&& 511#64).ult (BitVec.ofNat 64 limit) then 1#64 else 0#64

def flags (lo hi : BitVec 64) : BitVec 64 :=
  0#64 ||| bad lo 0 3 ||| bad lo 1 5 ||| bad lo 2 3 ||| bad lo 3 3 ||| bad lo 4 3 ||| bad lo 5 3 ||| bad lo 6 3 |||
    bad hi 0 3 ||| bad hi 1 5 ||| bad hi 2 3 ||| bad hi 3 3 ||| bad hi 4 3 ||| bad hi 5 3 ||| bad hi 6 3

def rankFloor (i : Nat) : Nat := if i=1 ∨ i=8 then 5 else 3
def rankOK (v : Digest) : Prop := ∀ i : Fin 14, rankFloor i.val ≤ lowerWord v / 2^(9*i.val) % 512
instance (v : Digest) : Decidable (rankOK v) := by unfold rankOK; infer_instance

theorem rank_field (v : Digest) (i : Fin 14) :
    v.toNat / 2 ^ (if i.val < 7 then 9*i.val else 64+9*(i.val-7)) % 512 =
      lowerWord v / 2 ^ (9*i.val) % 512 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [show (512 : Nat) = 2^9 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, T3.testBit_lowerWord]
  by_cases hj : j < 9
  · simp only [hj, decide_true, Bool.true_and]
    by_cases hi : i.val < 7
    · rw [if_pos hi, if_pos (by omega)]
    · rw [if_neg hi, if_neg (by omega)]
      simp only [show j+9*i.val < 126 by omega, decide_true, Bool.true_and]
      congr 1
      omega
  · simp [hj]

theorem bad_zero (x : BitVec 64) (i limit : Nat) (hl : limit < 2^64) :
    bad x i limit = 0#64 ↔ limit ≤ x.toNat / 2^(9*i) % 512 := by
  unfold bad
  have hmask : ((x >>> (9*i)) &&& 511#64).toNat = x.toNat / 2^(9*i) % 512 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    change (x.toNat / 2^(9*i)) &&& (2^9-1) = _
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  simp only [BitVec.ult, hmask, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]
  by_cases h : x.toNat / 2^(9*i) % 512 < limit
  · simp [h] <;> omega
  · simp [h] <;> omega

theorem flags_zero (v : Digest) :
    flags (v.extractLsb' 0 64) (v.extractLsb' 64 64) = 0#64 ↔ rankOK v := by
  have field (i : Fin 14) :
      (if i.val < 7 then v.extractLsb' 0 64 else v.extractLsb' 64 64).toNat /
        2^(9*(i.val%7)) % 512 = lowerWord v / 2^(9*i.val) % 512 := by
    rw [← rank_field v i]
    fin_cases i <;>
      simp only [Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceLT, Nat.reduceMod,
        Nat.reduceMul, Nat.reduceSub, if_true, if_false, BitVec.extractLsb'_toNat,
        Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.div_one] <;> omega
  have hb (i : Fin 14) :
      bad (if i.val < 7 then v.extractLsb' 0 64 else v.extractLsb' 64 64) (i.val%7) (rankFloor i.val) = 0#64 ↔
        rankFloor i.val ≤ lowerWord v / 2^(9*i.val) % 512 := by
    rw [bad_zero _ _ _ (by unfold rankFloor; split <;> decide), field]
  have h := forall_congr' hb
  simpa [flags, rankOK, rankFloor, BitVec.or_eq_zero_iff, Fin.forall_fin_succ, and_assoc] using h

sym_block r354 := symRun {noAlias := true} (rankCode 354) (pcOf 42879) 200
sym_block r543 := symRun {noAlias := true} (rankCode 543) (pcOf 20870) 200

def rankEnd (b : Nat) : E :=
  rebase r354.res.pc (pcOf (zBase b+97)) (pcOf (zBase b+96))

theorem run_rank {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias := true} (rankCode b) (pcOf (zBase b+38)) 200 =
      some ⟨r354.res.st, rankEnd b, r354.res.stop, r354.res.steps, r354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact r354.trans (congrArg some (by kernel_rfl))
  · exact r543.trans (congrArg some (by kernel_rfl))

def exitCode (b o : Nat) : List (BitVec 32) := ((rankCode b).drop o).take 1
def rankLayout (b : Nat) : Rv.Layout :=
  [(0,(rankCode b).take 58),(58,exitCode b 58),(59,exitCode b 59)]
theorem rankLayout_ok {b : Nat} (hb : b=354 ∨ b=543) : layoutOk 0 (rankLayout b) = true := by
  rcases hb with rfl | rfl <;> decide +kernel
theorem rankLayout_code {b : Nat} (hb : b=354 ∨ b=543) : layoutCode (rankLayout b) = rankCode b := by
  rcases hb with rfl | rfl <;> decide +kernel

sym_block re354_58 := symRun {noAlias := true} (exitCode 354 58) (pcOf (42841+96)) 200
sym_block re543_58 := symRun {noAlias := true} (exitCode 543 58) (pcOf (20832+96)) 200
sym_block re354_59 := symRun {noAlias := true} (exitCode 354 59) (pcOf (42841+97)) 200
sym_block re543_59 := symRun {noAlias := true} (exitCode 543 59) (pcOf (20832+97)) 200

theorem code_rank {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) :
    CodeAt image (pcOf (zBase b+38)) (rankCode b) :=
  codeAt_zero hK 12 38 (rankCode b) (by rfl)

theorem run_exit {b o : Nat} (hb : b=354 ∨ b=543) (ho : o=58 ∨ o=59) :
    symRun {noAlias := true} (exitCode b o) (pcOf (zBase b+38+o)) 200 =
      some ⟨re354_58.res.st, .c ((if o=58 then pcOf (Reward.base b false) else pcOf (b+468))), .jump, 1, 1⟩ := by
  rcases hb with rfl | rfl <;> rcases ho with rfl | rfl
  · exact re354_58.trans (congrArg some (by kernel_rfl))
  · exact re354_59.trans (congrArg some (by kernel_rfl))
  · exact re543_58.trans (congrArg some (by kernel_rfl))
  · exact re543_59.trans (congrArg some (by kernel_rfl))

theorem exit_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState)
    (o : Nat) (ho : o=58 ∨ o=59) (hp : s.pc=pcOf (zBase b+38+o)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=(if o=58 then pcOf (Reward.base b false) else pcOf (b+468)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hc : CodeAt image (pcOf (zBase b+38+o)) (exitCode b o) := by
    have h := code_rank hK
    rw [← rankLayout_code hK.2.1] at h
    rcases ho with rfl | rfl
    · exact codeAt_sublayout h (rankLayout_ok hK.2.1) (i:=1) (o:=58) (by rfl)
    · exact codeAt_sublayout h (rankLayout_ok hK.2.1) (i:=2) (o:=59) (by rfl)
  refine ⟨_,symRun_sound (run_exit hK.2.1 ho) hc s hp (by simp [re354_58.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> simp [re354_58.res,rv_simp] <;> rfl
  · intro A _ _; simp [re354_58.res,rv_simp]

theorem spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState)
    (hp : s.pc=pcOf (zBase b+38)) (v : Digest)
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64) :
    ∃ t, Steps image s 59 59 t ∧ t.pc=(if rankOK v then pcOf (Reward.base b false) else pcOf (b+468)) ∧
      RegsExcept s t [.x21,.x28] ∧ Frame s t (fun _ => False) := by
  have first := symRun_sound (run_rank hK.2.1) (code_rank hK) s hp (by simp [r354.res,rv_simp])
  have pp : (Result.toState ⟨r354.res.st,rankEnd b,r354.res.stop,r354.res.steps,r354.res.cycles⟩ s).pc =
      pcOf (zBase b+38+(if rankOK v then 58 else 59)) := by
    simp only [Result.toState_pc,rankEnd,rebase,r354.res,rv_simp,h6,h7]
    change (if (flags (v.extractLsb' 0 64) (v.extractLsb' 64 64) != 0#64) = true then _ else _) = _
    simp only [bne_iff_ne, ne_eq, flags_zero]
    by_cases h : rankOK v <;> simp [h, Nat.add_assoc]
  obtain ⟨t,st,pt,rt,ft⟩ := exit_spec hK _ (if rankOK v then 58 else 59) (by split <;> simp) pp
  refine ⟨t,first.trans st,?_,?_,?_⟩
  · by_cases h : rankOK v <;> simpa [h] using pt
  · have rfirst : RegsExcept s
        (Result.toState ⟨r354.res.st,rankEnd b,r354.res.stop,r354.res.steps,r354.res.cycles⟩ s) [.x21,.x28] := by
      intro r hr; cases r <;> simp_all [r354.res,rv_simp] <;> rfl
    exact (rfirst.trans rt).mono (by simp)
  · have ffirst : Frame s
        (Result.toState ⟨r354.res.st,rankEnd b,r354.res.stop,r354.res.steps,r354.res.cycles⟩ s) (fun _ => False) := by
      intro A _ _; simp [r354.res,rv_simp]
    exact (ffirst.trans ft).mono (fun _ _ h => by simp at h)

end SigGolfCandidate.T3M.Search.Rank
end
