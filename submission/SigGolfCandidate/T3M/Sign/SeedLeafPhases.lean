import SigGolfCandidate.T3M.Sign.TopLeaf
import SigGolfCandidate.T3M.Sign.SeedChain

section


namespace SigGolfCandidate.T3M.Sign.Seed
open SigGolfCandidate.T3M.Sign.SeedIndependent
open SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def sub43 : List (BitVec 32) := Keygen.sub_42.drop 1
sym_block blk117_43 := symRun { noAlias := true } sub43 (pcOf (117 + 43)) 100
sym_block blk1013_43 := symRun { noAlias := true } sub43 (pcOf (1013 + 43)) 100
def st_43 : SymState := blk117_43.res.st
def pcE_43 (b : Nat) : E := rebase blk117_43.res.pc (pcOf (b + 60)) (pcOf (b + 44))
theorem run_43 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub43 (pcOf (b + 43)) 100 =
      some ⟨st_43, pcE_43 b, blk117_43.res.stop, blk117_43.res.steps,
        blk117_43.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_43.trans (congrArg some (by kernel_rfl))
  · exact blk1013_43.trans (congrArg some (by kernel_rfl))
theorem sub43_spec {image : Image} {b : Nat} (hb : b = 117 ∨ b = 1013)
    (hc : CodeAt image (pcOf (b + 43)) sub43) (s : MachineState)
    (hpc : s.pc = pcOf (b + 43)) :
    ∃ t, Steps image s 1 1 t ∧
      t.pc = (if s.getReg .x6 = 0 then pcOf (b + 44) else pcOf (b + 60)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_43 hb) hc s hpc (by simp [st_43, blk117_43.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, pcE_43, rebase, blk117_43.res, rv_simp]
  · intro r hr; cases r <;> simp_all [st_43, blk117_43.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_43, blk117_43.res, rv_simp]
def sub61 : List (BitVec 32) := Keygen.sub_60.drop 1
sym_block blk117_61 := symRun { noAlias := true } sub61 (pcOf (117 + 61)) 100
sym_block blk1013_61 := symRun { noAlias := true } sub61 (pcOf (1013 + 61)) 100
def st_61 : SymState := blk117_61.res.st
def pcE_61 (b : Nat) : E := .c (pcOf (b + 72))
theorem run_61 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub61 (pcOf (b + 61)) 100 =
      some ⟨st_61, pcE_61 b, blk117_61.res.stop, blk117_61.res.steps,
        blk117_61.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_61.trans (congrArg some (by kernel_rfl))
  · exact blk1013_61.trans (congrArg some (by kernel_rfl))
set_option maxRecDepth 100000 in
theorem sub61_spec {image : Image} {b : Nat} (hb : b = 117 ∨ b = 1013)
    (hc : CodeAt image (pcOf (b + 61)) sub61) (s : MachineState)
    (hpc : s.pc = pcOf (b + 61)) (i digp half : Nat) (hh : half < 2)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 digp)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 half) :
    ∃ t, Steps image s 11 11 t ∧ t.pc = pcOf (b + 72) ∧
      t.getReg .x28 = BitVec.ofNat 64 (digp + i) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 48)) =
        s.getMem (BitVec.ofNat 64 (SEEDS + 16 * half)) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 56)) =
        s.getMem (BitVec.ofNat 64 (SEEDS + 16 * half + 8)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  have hobl : Oblig.all s st_61.obl := by
    simp only [st_61, blk117_61.res]
    t3n [h28]
    omega
  refine ⟨_, symRun_sound (run_61 hb) hc s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_61, Result.toState_pc, E.eval]
  · t3n [st_61, blk117_61.res, h19, h22]
  · simp only [Result.toState_getMem, st_61, blk117_61.res, CHAIN, SEEDS]
    t3n [h28]
    congr 2 <;> omega
  · simp only [Result.toState_getMem, st_61, blk117_61.res, CHAIN, SEEDS]
    t3n [h28]
    congr 2 <;> omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_61, blk117_61.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [CHAIN] at hn
    simp only [Result.toState_getMem, st_61, blk117_61.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
theorem sub27_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 27)) (lay : T3.Layer) (tree leaf : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 32)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h15 : tree = 0 ∨ s.getReg .x15 = BitVec.ofNat 64 (T3.height lay)) :
    ∃ t, Steps image s 17 17 t ∧ t.pc = pcOf (b + 41) ∧ t.getReg .x3 = s.getReg .x1 ∧
      t.getReg .x19 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧
      RegsExcept s t [.x3, .x6, .x7, .x19, .x28, .x30] ∧
      Frame s t (fun A => A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
  obtain rfl := SeedIndependent.b_eq h
  obtain ⟨t1, s1, p1, x3, r1, f1⟩ : ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 1528 ∧
      t.getReg .x3 = s.getReg .x1 ∧ RegsExcept s t [.x3] ∧ Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_27 (SeedIndependent.codeAt_sub27S h) s hpc
      (by simp [SeedIndependent.blkS_27.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_27.res, E.eval]
    · simp [SeedIndependent.blkS_27.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_27.res, rv_simp] <;> rfl
    · intro A _ _; simp [SeedIndependent.blkS_27.res, rv_simp]
  have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [r1.get (by decide), h8]
  have g9 : t1.getReg .x9 = BitVec.ofNat 64 tree := by rw [r1.get (by decide), h9]
  have g18 : t1.getReg .x18 = BitVec.ofNat 64 leaf := by rw [r1.get (by decide), h18]
  obtain ⟨t2, s2, p2, m16, m24, r2, f2⟩ : ∃ t, Steps image t1 14 14 t ∧ t.pc = pcOf (1013 + 40) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧
      RegsExcept t1 t [.x6, .x28, .x30] ∧ Frame t1 t (fun A => A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_hp (SeedIndependent.codeAt_hpS h) t1 p1
      (by simp [SeedIndependent.blkS_hp.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_hp.res, E.eval]
    · simp only [Result.toState_getMem, SeedIndependent.blkS_hp.res]
      t3n [g8, g9, g18, LEAFPK]
      have hh : T3.height lay < 64 := by fin_cases lay <;> decide
      have hsh : tree * 2 ^ ((t1.getReg .x15).toNat % 64) = tree * 2 ^ T3.height lay := by
        rcases h15 with h | h
        · simp [h]
        · rw [r1.get (by decide), h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : T3.height lay < 2 ^ 64),
            Nat.mod_eq_of_lt hh]
      have hl := lay.isLt
      rw [hsh, show (513#64) = BitVec.ofNat 64 513 from rfl,
        ofNat_or_disjoint 513 ((tree * 2 ^ T3.height lay + leaf) * 65536) 16 (by decide) (by omega),
        ofNat_or_disjoint' _ (↑lay * 281474976710656) 48 (by omega) (by omega),
        show (13907115649320091648#64) = BitVec.ofNat 64 (193 * 2 ^ 56) from rfl,
        ofNat_or_disjoint' _ (193 * 2 ^ 56) 56 (by omega) (by omega)]
      unfold T3.hyperWord
      congr 1
      rw [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt (by omega : lay.val < 256)]
      omega
    · simp only [Result.toState_getMem, SeedIndependent.blkS_hp.res]
      t3n [LEAFPK]
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_hp.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, SeedIndependent.blkS_hp.res]
      t3n []
      simp only [LEAFPK] at hn
      rw [if_neg (by omega), if_neg (by omega)]
  obtain ⟨t3, s3, p3, x19, r3, f3⟩ : ∃ t, Steps image t2 1 1 t ∧ t.pc = pcOf (1013 + 41) ∧
      t.getReg .x19 = BitVec.ofNat 64 0 ∧ RegsExcept t2 t [.x19] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_40 (SeedIndependent.codeAt_sub40S h) t2 p2
      (by simp [SeedIndependent.blkS_40.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_40.res, E.eval]
    · simp [SeedIndependent.blkS_40.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_40.res, rv_simp] <;> rfl
    · intro A _ _; simp [SeedIndependent.blkS_40.res, rv_simp]
  refine ⟨t3, (s1.trans s2).trans s3, p3, ?_, x19, ?_, ?_, ((r1.trans r2).trans r3).mono (by decide),
    ((f1.trans f2).trans f3).mono (fun A _ h => by simp_all)⟩
  · rw [r3.get (by decide), r2.get (by decide), x3]
  · rw [f3.get (by simp only [LEAFPK]; omega) (by simp), m16]
  · rw [f3.get (by simp only [LEAFPK]; omega) (by simp), m24]
theorem sub41_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 41)) (i n : Nat) (hi : i < 2 ^ 63) (hn : n < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if i < n then pcOf (b + 42) else pcOf (b + 95)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_41 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_41 h) s hpc (by simp [st_41, blk117_41.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_41, rebase, blk117_41.res, E.eval, CmpOp.eval, h19, h26,
      ofNat_slt i n hi hn]
    by_cases hin : i < n <;> simp [hin]
  · intro r hr; cases r <;> simp_all [st_41, blk117_41.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_41, blk117_41.res, rv_simp]
theorem sub44_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 44)) (lay tree leaf i : Nat) (hlay : lay < 256) (htree : tree < 2 ^ 32)
    (hleaf : leaf < 2 ^ 32) (hi : i < 2 ^ 32) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 15 15 t ∧ t.pc = pcOf (b + 59) ∧
      t.getReg .x10 = BitVec.ofNat 64 PRIV ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 SEEDS ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 16)) = BitVec.ofNat 64 (hdr0 0 lay tree (i / 2)) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 24)) = BitVec.ofNat 64 (hdr1 tree leaf) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun A => A = PRIV + 16 ∨ A = PRIV + 24) := by
  have hrun := run_44 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_44 h) s hpc (by simp [st_44, blk117_44.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_44, Result.toState_pc, E.eval]
  · simp [st_44, blk117_44.res, rv_simp]
  · simp [st_44, blk117_44.res, rv_simp]
  · simp [st_44, blk117_44.res, rv_simp]
  · simp only [Result.toState_getMem, st_44, blk117_44.res, PRIV]
    t3n [h8, h19]
    rw [ofNat_shr i 1 (by omega), ofNat_shl, Nat.pow_one,
      ofNat_or_disjoint' (lay * 65536) (i / 2 * 2 ^ 32) 32 (by omega) (by omega),
      ofNat_or_disjoint 1 _ 16 (by omega) (by omega), hdr0_eq 0 lay tree (i / 2) (by omega) hlay htree
        (by omega)]
    congr 1; omega
  · simp only [Result.toState_getMem, st_44, blk117_44.res, PRIV]
    t3n [h9, h18]
    rw [BitVec.or_comm, ofNat_or_disjoint tree (leaf * 4294967296) 32 htree (by omega),
      hdr1_eq tree leaf htree hleaf]
    congr 1; ring
  · intro r hr; simp at hr; cases r <;> simp_all [st_44, blk117_44.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem, st_44, blk117_44.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
theorem fetch_sub59 {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 59)) : fetch image s = some (.base .ECALL) :=
  ((SeedIndependent.codeAt_sub_59 h).fetch s hpc).trans rfl
set_option maxRecDepth 100000 in
theorem sub60_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 60)) (i digp : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 digp) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf (b + 72) ∧ t.getReg .x28 = BitVec.ofNat 64 (digp + i) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 48)) = s.getMem (BitVec.ofNat 64 (SEEDS + 16 * (i % 2))) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 56)) = s.getMem (BitVec.ofNat 64 (SEEDS + 16 * (i % 2) + 8)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  have hrun := run_60 h.2.1
  have hm : i % 2 < 2 := Nat.mod_lt _ (by decide)
  have hobl : Oblig.all s st_60.obl := by
    simp only [st_60, blk117_60.res]
    t3n [h19, ofNat_and1]
    omega
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_60 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_60, Result.toState_pc, E.eval]
  · t3n [st_60, blk117_60.res, h19, h22]
  · simp only [Result.toState_getMem, st_60, blk117_60.res, CHAIN, SEEDS]
    t3n [h19, ofNat_and1]
    congr 2; omega
  · simp only [Result.toState_getMem, st_60, blk117_60.res, CHAIN, SEEDS]
    t3n [h19, ofNat_and1]
    congr 2; omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_60, blk117_60.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [CHAIN] at hn
    simp only [Result.toState_getMem, st_60, blk117_60.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
theorem sub72_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 72)) (a : Nat) (ha : a + 1 ≤ 2 ^ 24) (d : Nat) (hd : d < 256)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 a) (hbyte : s.getByte (BitVec.ofNat 64 a) = BitVec.ofNat 8 d) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 73) ∧ t.getReg .x17 = BitVec.ofNat 64 d ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun _ => False) := by
  have hoff : s.getReg .x28 + signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 a := by
    rw [h28]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
  have st := steps_lbu (rd := .x17) (rs := .x28) (off := 0) (SeedIndependent.codeAt_sub_72 h) hpc rfl
    (by rw [hoff, accessValid_iff, toNat_ofNat_lt (by omega)]; simp [MEMORY_BYTES]; omega)
  refine ⟨_, st, ?_, ?_, ?_, ?_⟩
  · show s.pc + 4 = pcOf (b + 73)
    rw [hpc, pcOf_add4]
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide), hoff, hbyte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · intro A _ _; simp
theorem sub73_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 73)) (lay : Nat) (hlay : lay < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if lay = 0 then pcOf (b + 75) else pcOf (b + 76)) ∧
      t.getReg .x21 = BitVec.ofNat 64 7 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hrun := run_73 h.2.1
  have hz : (BitVec.ofNat 64 lay = 0#64) ↔ lay = 0 := by
    constructor
    · intro e
      have q := congrArg BitVec.toNat e
      simpa [toNat_ofNat_lt (show lay < 2 ^ 64 by omega)] using q
    · intro e; subst lay; rfl
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_73 h) s hpc (by simp [st_73, blk117_73.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, pcE_73, rebase, blk117_73.res, E.eval, CmpOp.eval, h8, hz]
  · simp [st_73, blk117_73.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_73, blk117_73.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_73, blk117_73.res, rv_simp]
theorem sub75_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 75)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 1000) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_75 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_75 h) s hpc (by simp [st_75, blk117_75.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp [pcE_75, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [st_75, blk117_75.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_75, blk117_75.res, rv_simp]
theorem maxLow_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1000)) (i n4 : Nat) (hi : i < 2 ^ 63) (hn : n4 < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h27 : s.getReg .x27 = BitVec.ofNat 64 n4) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i < n4 then pcOf (b + 1002) else pcOf (b + 76)) ∧
      t.getReg .x21 = BitVec.ofNat 64 3 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hrun := run_maxLow h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_maxLow h) s hpc (by simp [maxLowState, max117Low.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, maxLowPC, rebase, max117Low.res, E.eval, CmpOp.eval, h19, h27,
      ofNat_slt i n4 hi hn]
    by_cases hin : i < n4 <;> simp [hin]
  · simp [maxLowState, max117Low.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [maxLowState, max117Low.res, rv_simp] <;> rfl
  · intro A _ _; simp [maxLowState, max117Low.res, rv_simp]
theorem maxHigh_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1002)) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 76) ∧ t.getReg .x21 = BitVec.ofNat 64 4 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hrun := run_maxHigh h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_maxHigh h) s hpc (by simp [maxHighState, max117High.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [maxHighPC, Result.toState_pc, E.eval]
  · simp [maxHighState, max117High.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [maxHighState, max117High.res, rv_simp] <;> rfl
  · intro A _ _; simp [maxHighState, max117High.res, rv_simp]
theorem sub76_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 76)) (so : Bool) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if so then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if so then pcOf (b + 77) else pcOf (b + 78)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_76 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_76 h) s hpc (by simp [st_76, blk117_76.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_76, rebase, blk117_76.res, E.eval, CmpOp.eval, h31]
    cases so <;> simp
  · intro r hr; cases r <;> simp_all [st_76, blk117_76.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_76, blk117_76.res, rv_simp]
theorem sub77_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 77)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 78) ∧ t.getReg .x21 = s.getReg .x17 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hrun := run_77 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_77 h) s hpc (by simp [st_77, blk117_77.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_77, Result.toState_pc, E.eval]
  · simp [st_77, blk117_77.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_77, blk117_77.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_77, blk117_77.res, rv_simp]
theorem sub78_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 78)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf b ∧ t.getReg .x1 = pcOf (b + 79) ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) := by
  have hrun := run_78 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_78 h) s hpc (by simp [st_78, blk117_78.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_78, Result.toState_pc, E.eval]
  · simp [st_78, blk117_78.res, rv_simp, RegFile.set]
  · intro r hr; simp at hr; cases r <;> simp_all [st_78, blk117_78.res, rv_simp, RegFile.set] <;> rfl
  · intro A _ _; simp [st_78, blk117_78.res, rv_simp]
theorem sub79_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 79)) (so : Bool) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if so then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if so then pcOf (b + 92) else pcOf (b + 80)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_79 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_79 h) s hpc (by simp [st_79, blk117_79.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_79, rebase, blk117_79.res, E.eval, CmpOp.eval, h31]
    cases so <;> simp
  · intro r hr; cases r <;> simp_all [st_79, blk117_79.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_79, blk117_79.res, rv_simp]
theorem sub80_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 80)) (i : Nat) (hi : i < 2 ^ 32) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i = 0 then pcOf (b + 83) else pcOf (b + 82)) ∧
      t.getReg .x28 = BitVec.ofNat 64 (16 * i) ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  obtain rfl := SeedIndependent.b_eq h
  refine ⟨_, symRun_sound SeedIndependent.blkS_80 (SeedIndependent.codeAt_sub80S h) s hpc
    (by simp [SeedIndependent.blkS_80.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, SeedIndependent.blkS_80.res, E.eval, CmpOp.eval, h19]
    by_cases hi0 : i = 0
    · subst hi0; simp
    · have : BitVec.ofNat 64 i ≠ 0#64 := fun he => hi0 (by
        have := congrArg BitVec.toNat he; rwa [toNat_ofNat_lt (by omega)] at this)
      simp [hi0, this]
  · t3n [SeedIndependent.blkS_80.res, h19]; congr 1; omega
  · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_80.res, rv_simp] <;> rfl
  · intro A _ _; simp [SeedIndependent.blkS_80.res, rv_simp]
theorem sub82_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 82)) (o : Nat) (h28 : s.getReg .x28 = BitVec.ofNat 64 o) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 83) ∧ t.getReg .x28 = BitVec.ofNat 64 (o + 16) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have hrun := run_82 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_82 h) s hpc (by simp [st_82, blk117_82.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_82, Result.toState_pc, E.eval]
  · t3n [st_82, blk117_82.res, h28]
  · intro r hr; simp at hr; cases r <;> simp_all [st_82, blk117_82.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_82, blk117_82.res, rv_simp]
theorem sub83_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 83)) (o : Nat) (ho : o % 8 = 0) (ho' : LEAFPK + o + 16 ≤ 2 ^ 24)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 o) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf (b + 92) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + o)) = s.getMem (BitVec.ofNat 64 (CHAIN + 48)) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + o + 8)) = s.getMem (BitVec.ofNat 64 (CHAIN + 56)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = LEAFPK + o ∨ A = LEAFPK + o + 8) := by
  have hrun := run_83 h.2.1
  have hobl : Oblig.all s st_83.obl := by
    simp only [st_83, blk117_83.res]
    t3n [h28]
    simp only [LEAFPK] at ho'
    omega
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_83 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_83, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, st_83, blk117_83.res]
    t3n [h28]
    simp only [LEAFPK] at ho' ⊢
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, st_83, blk117_83.res]
    t3n [h28]
    simp only [LEAFPK] at ho' ⊢
    rw [if_pos (by omega)]
  · intro r hr; simp at hr; cases r <;> simp_all [st_83, blk117_83.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [LEAFPK] at hn ho'
    simp only [Result.toState_getMem, st_83, blk117_83.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]
theorem sub92_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 92)) (i v : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 v) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 41) ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      t.getReg .x23 = BitVec.ofNat 64 (v + 16) ∧ RegsExcept s t [.x19, .x23] ∧
      Frame s t (fun _ => False) := by
  have hrun := run_92 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_92 h) s hpc (by simp [st_92, blk117_92.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_92, Result.toState_pc, E.eval]
  · t3n [st_92, blk117_92.res, h19]
  · t3n [st_92, blk117_92.res, h23]
  · intro r hr; simp at hr; cases r <;> simp_all [st_92, blk117_92.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_92, blk117_92.res, rv_simp]
theorem sub95_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 95)) (so : Bool) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if so then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if so then pcOf (b + 112) else pcOf (b + 96)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_95 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_95 h) s hpc (by simp [st_95, blk117_95.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_95, rebase, blk117_95.res, E.eval, CmpOp.eval, h31]
    cases so <;> simp
  · intro r hr; cases r <;> simp_all [st_95, blk117_95.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_95, blk117_95.res, rv_simp]
theorem sub96_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 96)) (n : Nat) (hn : n = 54 ∨ n = 43)
    (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf (b + 105) ∧ t.getReg .x10 = BitVec.ofNat 64 LEAFPK ∧
      t.getReg .x11 = BitVec.ofNat 64 ((16 * (n + 1) + 63) / 64 * 64) ∧
      t.getReg .x12 = BitVec.ofNat 64 LOUT ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      Frame s t (fun _ => False) := by
  have hrun := run_96 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_96 h) s hpc (by simp [st_96, blk117_96.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_96, Result.toState_pc, E.eval]
  · simp [st_96, blk117_96.res, rv_simp]
  · simp only [Result.toState_getReg, st_96, blk117_96.res, rv_simp, h26]
    rcases hn with rfl | rfl <;> decide
  · simp [st_96, blk117_96.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_96, blk117_96.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_96, blk117_96.res, rv_simp]
theorem fetch_sub105 {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 105)) : fetch image s = some (.base .ECALL) :=
  ((SeedIndependent.codeAt_sub_105 h).fetch s hpc).trans rfl
theorem sub106_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 106)) (dest : Nat) (hd : dest % 8 = 0) (hd' : dest + 16 ≤ 2 ^ 24)
    (hdl : dest + 16 ≤ LOUT ∨ LOUT + 16 ≤ dest) (h25 : s.getReg .x25 = BitVec.ofNat 64 dest) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (b + 112) ∧
      t.getMem (BitVec.ofNat 64 dest) = s.getMem (BitVec.ofNat 64 LOUT) ∧
      t.getMem (BitVec.ofNat 64 (dest + 8)) = s.getMem (BitVec.ofNat 64 (LOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29] ∧ Frame s t (fun A => A = dest ∨ A = dest + 8) := by
  have hrun := run_106 h.2.1
  have hobl : Oblig.all s st_106.obl := by
    simp only [st_106, blk117_106.res]
    t3n [h25]
    omega
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_106 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_106, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, st_106, blk117_106.res]
    t3n [h25]
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, st_106, blk117_106.res]
    t3n [h25]
  · intro r hr; simp at hr; cases r <;> simp_all [st_106, blk117_106.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, st_106, blk117_106.res]
    t3n [h25]
    rw [if_neg (by omega), if_neg (by omega)]
theorem sub112_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 112)) (k : Nat) (h3 : s.getReg .x3 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_112 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_112 h) s hpc (by simp [st_112, blk117_112.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_112, blk117_112.res, rv_simp, h3, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_112, blk117_112.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_112, blk117_112.res, rv_simp]
end SigGolfCandidate.T3M.Sign.Seed
end

section



namespace SigGolfCandidate.T3M.Sign.Seed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3M.Sign.SeedIndependent
open SigGolfCandidate.T3 (Layer Digest chainCount width maxDigit chain chainInput buildLeaf leafHash privatePair
  shortHash header pad64 zero16 privateInput)
open SphincsSecurity (bytesLE bytesLE_length)
theorem slot_low {lay : Layer} (h : lay ≠ 0) (c : Nat) :
    slot lay c = if c = 0 then LEAFPK else LEAFPK + 16 * (c + 1) := by
  simp [slot, h]
theorem slotK_low {lay : Layer} (h : lay ≠ 0) (c : Nat) : slotK lay c = if c = 0 then 0 else 1 := by
  simp [slotK, h]
section leaf
variable {image : Image} {b : Nat} (hsub : SeedIndependentAt image b) (sk : BitVec 256) {s0 : MachineState}
  {A : LeafArgs} (hpre : LeafPreS sk s0 A)
include hsub hpre
theorem leaf_prechainS {j : Nat} (hj : j < A.n) {st : List Digest × List Digest} {t : MachineState}
    (ht : LeafInv s0 A j st t) (hpc : t.pc = pcOf (b + 60)) (seed : Digest)
    (hseed : DigAt t (SEEDS + 16 * (j % 2)) seed) :
    ∃ u, Steps image t (17 + selectorExtra A.lay j + (if A.so then 1 else 0))
        (17 + selectorExtra A.lay j + (if A.so then 1 else 0)) u ∧ u.pc = pcOf b ∧
      ChainPre u A.lay A.tree A.leaf j (A.d j) (A.e j) (A.valp + 16 * j) (b + 79) ∧
      DigAt u (CHAIN + 48) seed ∧ RegsExcept t u [.x1, .x6, .x7, .x17, .x21, .x28, .x29, .x30] ∧
      Frame t u (fun X => X = CHAIN + 48 ∨ X = CHAIN + 56) := by
  have hn := chainCount_cases A.lay
  have hn4 := n4_le A.lay
  have hdb := hpre.hdigb j hj
  have hvs := hpre.hvs
  have hv := hpre.hv
  have hv8 := hpre.hv8
  have g : ∀ r, r ∉ leafRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r22 : t.getReg .x22 = BitVec.ofNat 64 A.digp := by rw [g _ (by simp [leafRegs]), hpre.x22]
  have r27 : t.getReg .x27 = BitVec.ofNat 64 (n4 A.lay) := by rw [g _ (by simp [leafRegs]), hpre.x27]
  have r31 : t.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0) := by
    rw [g _ (by simp [leafRegs]), hpre.x31]
  obtain ⟨t1, st1, t1pc, t1x28, t1c48, t1c56, t1r, t1f⟩ := sub60_spec hsub t hpc j A.digp ht.x19 r22
  have hw := hpre.hdigW j hj
  have hbyte : t1.getByte (BitVec.ofNat 64 (A.digp + j)) = BitVec.ofNat 8 (A.d j) := by
    rw [t1f.getByte (by have := hpre.hdigp; omega) (fun h => hw (by
        simp only [LeafW, CHAIN, PRIV, SEEDS, LEAFPK, LOUT] at h ⊢; omega)),
      ht.frame.getByte (by have := hpre.hdigp; omega) hw, hpre.hdig j hj]
  obtain ⟨t2, st2, t2pc, t2x17, t2r, t2f⟩ := sub72_spec hsub t1 t1pc (A.digp + j)
    (by have := hpre.hdigp; omega) (A.d j) hdb.1 t1x28 hbyte
  have e12 : RegsExcept t t2 [.x6, .x7, .x17, .x28, .x29, .x30] := (t1r.trans t2r).mono (by simp)
  have r8 : t.getReg .x8 = BitVec.ofNat 64 A.lay.val := by rw [g _ (by simp [leafRegs]), hpre.x8]
  obtain ⟨t3, st3, t3pc, t3x21, t3r, t3f⟩ := sub73_spec hsub t2 t2pc A.lay.val
    (by have := A.lay.isLt; omega) (by rw [e12.get (by simp)]; exact r8)
  have hseedv : DigAt t1 (CHAIN + 48) seed := ⟨t1c48.trans hseed.1, by
    rw [t1c56, show SEEDS + 16 * (j % 2) + 8 = SEEDS + 16 * (j % 2) + 8 from rfl]; exact hseed.2⟩
  obtain ⟨t4, st4, t4pc, t4x21, t4r, t4f⟩ : ∃ t4, Steps image t3 (selectorExtra A.lay j)
      (selectorExtra A.lay j) t4 ∧ t4.pc = pcOf (b + 76) ∧
      t4.getReg .x21 = BitVec.ofNat 64 (maxDigit A.lay j) ∧ RegsExcept t3 t4 [.x21] ∧
      Frame t3 t4 (fun _ => False) := by
    have hlay0 : A.lay.val = 0 ↔ A.lay = 0 := by simp
    by_cases hl : A.lay = 0
    · rw [if_pos (hlay0.mpr hl)] at t3pc
      obtain ⟨ta, sta, tapc, tar, taf⟩ := sub75_spec hsub t3 t3pc
      have e1a := ((e12.trans t3r).trans tar)
      obtain ⟨tb, stb, tbpc, tbx21, tbr, tbf⟩ := maxLow_spec hsub ta tapc j (n4 A.lay)
        (by omega) (by omega) (by rw [e1a.get (by simp)]; exact ht.x19)
        (by rw [e1a.get (by simp)]; exact r27)
      by_cases hjn : j < n4 A.lay
      · rw [if_pos hjn] at tbpc
        obtain ⟨tc, stc, tcpc, tcx21, tcr, tcf⟩ := maxHigh_spec hsub tb tbpc
        refine ⟨tc, ?_, tcpc, ?_, ?_, ?_⟩
        · simpa only [selectorExtra, if_pos hl, if_pos hjn] using (sta.trans stb).trans stc
        · simpa only [maxDigit_shape, if_pos hl, if_pos hjn] using tcx21
        · exact ((tar.trans tbr).trans tcr).mono (by simp)
        · exact ((taf.trans tbf).trans tcf).mono (by simp)
      · rw [if_neg hjn] at tbpc
        refine ⟨tb, ?_, tbpc, ?_, ?_, ?_⟩
        · simpa only [selectorExtra, if_pos hl, if_neg hjn] using sta.trans stb
        · simpa only [maxDigit_shape, if_pos hl, if_neg hjn] using tbx21
        · exact (tar.trans tbr).mono (by simp)
        · exact (taf.trans tbf).mono (by simp)
    · rw [if_neg (fun hv => hl (hlay0.mp hv))] at t3pc
      exact ⟨t3, by simpa [selectorExtra, hl] using Steps.refl t3, t3pc,
        by simpa [maxDigit_shape, hl] using t3x21, RegsExcept.refl _ _, Frame.refl _ _⟩
  have e14 : RegsExcept t t4 [.x6, .x7, .x17, .x21, .x28, .x29, .x30] :=
    ((e12.trans t3r).trans t4r).mono (by simp)
  obtain ⟨t5, st5, t5pc, t5r, t5f⟩ := sub76_spec hsub t4 t4pc A.so (by rw [e14.get (by simp)]; exact r31)
  obtain ⟨t6, st6, t6pc, t6x21, t6r, t6f⟩ : ∃ t6, Steps image t5 (if A.so then 1 else 0)
      (if A.so then 1 else 0) t6 ∧ t6.pc = pcOf (b + 78) ∧
      t6.getReg .x21 = BitVec.ofNat 64 (A.e j) ∧ RegsExcept t5 t6 [.x21] ∧
      Frame t5 t6 (fun _ => False) := by
    cases hso : A.so
    · rw [hso, if_neg (by simp)] at t5pc
      refine ⟨t5, by simpa using Steps.refl t5, t5pc, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
      rw [t5r.get (by simp), t4x21, LeafArgs.e, hso]; rfl
    · rw [hso, if_pos rfl] at t5pc
      obtain ⟨t6, st6, t6pc, t6x21, t6r, t6f⟩ := sub77_spec hsub t5 t5pc
      refine ⟨t6, by simpa using st6, t6pc, ?_, t6r, t6f⟩
      rw [t6x21, t5r.get (by simp), t4r.get (by simp), t3r.get (by simp), t2x17, LeafArgs.e, hso]; rfl
  obtain ⟨u, st7, upc, ux1, ur, uf⟩ := sub78_spec hsub t6 t6pc
  have e1u : RegsExcept t u [.x1, .x6, .x7, .x17, .x21, .x28, .x29, .x30] :=
    (((e14.trans t5r).trans t6r).trans ur).mono (by simp)
  have f1u : Frame t u (fun X => X = CHAIN + 48 ∨ X = CHAIN + 56) :=
    (((((t1f.trans t2f).trans t3f).trans t4f).trans t5f).trans (t6f.trans uf)).mono (fun X _ h => by
      simp only [or_false] at h; exact h)
  have f2u : Frame t2 u (fun _ => False) :=
    ((((t3f.trans t4f).trans t5f).trans t6f).trans uf).mono (fun X _ h => by simp_all)
  have gu : ∀ r, r ∉ leafRegs → r ∉ [.x1, .x6, .x7, .x17, .x21, .x28, .x29, .x30] →
      u.getReg r = s0.getReg r := fun r h1 h2 => (e1u.get h2).trans (g r h1)
  have fr : ∀ X, X < 2 ^ 64 → ¬ LeafW A X → X ≠ CHAIN + 48 → X ≠ CHAIN + 56 →
      u.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX h1 h2 h3 =>
    (f1u.get hX (by simp [h2, h3])).trans (ht.frame.get hX h1)
  have hL : ∀ X, (X = CHAIN ∨ X = CHAIN + 8 ∨ X = CHAIN + 32 ∨ X = CHAIN + 40) → ¬ LeafW A X := by
    intro X hX hw'
    simp only [LeafW, CHAIN, PRIV, SEEDS, LEAFPK, LOUT] at hX hw' hvs
    have := hpre.hds
    have := hpre.hdv
    simp only [CHAIN, PRIV, SEEDS, LEAFPK, LOUT] at *
    split_ifs at hw' <;> omega
  refine ⟨u, ?_, upc, {
      x5 := ?_, x1 := ux1, x8 := ?_, x9 := ?_, x18 := ?_
      x17 := ?_, x19 := ?_, x21 := ?_, x23 := ?_, htree := hpre.htree
      hi := by change j < 64; change A.n = 54 ∨ A.n = 43 at hn; omega
      hroute := hpre.hroute, hleaf := hpre.hleafHeight
      hcap := ?_, he := hpre.hsteps j hj, hv8 := ?_, hv := ?_, hvc := ?_
      z0 := ?_, z8 := ?_, z32 := ?_, z40 := ?_ },
    hseedv.frame (((t2f.trans t3f).trans t4f).trans (t5f.trans (t6f.trans uf))) (by decide)
      (by simp) (by simp), e1u, f1u⟩
  · have := (st1.trans st2).trans ((st3.trans st4).trans ((st5.trans st6).trans st7))
    refine Steps.of_eq this ?_ ?_ <;> split_ifs <;> simp_all <;> omega
  · rw [gu _ (by simp [leafRegs]) (by simp), hpre.x5]
  · rw [gu _ (by simp [leafRegs]) (by simp), hpre.x8]
  · rw [gu _ (by simp [leafRegs]) (by simp), hpre.x9]
  · rw [gu _ (by simp [leafRegs]) (by simp), hpre.x18]
  · rw [ur.get (by simp), t6r.get (by simp), t5r.get (by simp), t4r.get (by simp), t3r.get (by simp),
      t2x17]
  · rw [e1u.get (by simp)]; exact ht.x19
  · rw [ur.get (by simp)]; exact t6x21
  · rw [e1u.get (by simp)]; exact ht.x23
  · unfold LeafArgs.e; split_ifs with hso
    · exact le_refl _
    · exact hdb.2 (by simpa using hso)
  · omega
  · omega
  · simp only [CHAIN, PRIV, LEAFPK] at hvs ⊢; omega
  · rw [fr CHAIN (by decide) (hL _ (by simp)) (by decide) (by decide), hpre.z0]
  · rw [fr (CHAIN + 8) (by decide) (hL _ (by simp)) (by decide) (by decide), hpre.z8]
  · rw [fr (CHAIN + 32) (by decide) (hL _ (by simp)) (by decide) (by decide), hpre.z32]
  · rw [fr (CHAIN + 40) (by decide) (hL _ (by simp)) (by decide) (by decide), hpre.z40]
set_option maxHeartbeats 1000000 in
theorem leaf_prechainFrom61S {j : Nat} (hj : j < A.n) {st : List Digest × List Digest} {t : MachineState}
    (ht : LeafInv s0 A j st t) (hpc : t.pc = pcOf (b + 61)) (seed : Digest) (half : Nat) (hhalf : half < 2)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 half)
    (hcopy : CodeAt image (pcOf (b + 61)) sub61)
    (hseed : DigAt t (SEEDS + 16 * half) seed) :
    ∃ u, Steps image t (16 + selectorExtra A.lay j + (if A.so then 1 else 0))
        (16 + selectorExtra A.lay j + (if A.so then 1 else 0)) u ∧ u.pc = pcOf b ∧
      ChainPre u A.lay A.tree A.leaf j (A.d j) (A.e j) (A.valp + 16 * j) (b + 79) ∧
      DigAt u (CHAIN + 48) seed ∧ RegsExcept t u [.x1, .x6, .x7, .x17, .x21, .x28, .x29, .x30] ∧
      Frame t u (fun X => X = CHAIN + 48 ∨ X = CHAIN + 56) := by
  have hn := chainCount_cases A.lay
  have hn4 := n4_le A.lay
  have hdb := hpre.hdigb j hj
  have hvs := hpre.hvs
  have hv := hpre.hv
  have hv8 := hpre.hv8
  have g : ∀ r, r ∉ leafRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r22 : t.getReg .x22 = BitVec.ofNat 64 A.digp := by rw [g _ (by simp [leafRegs]), hpre.x22]
  have r27 : t.getReg .x27 = BitVec.ofNat 64 (n4 A.lay) := by rw [g _ (by simp [leafRegs]), hpre.x27]
  have r31 : t.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0) := by
    rw [g _ (by simp [leafRegs]), hpre.x31]
  obtain ⟨t1, st1, t1pc, t1x28, t1c48, t1c56, t1r, t1f⟩ := sub61_spec hsub.2.1 hcopy t hpc j A.digp half hhalf ht.x19 r22 h28
  have hw := hpre.hdigW j hj
  have hbyte : t1.getByte (BitVec.ofNat 64 (A.digp + j)) = BitVec.ofNat 8 (A.d j) := by
    rw [t1f.getByte (by have := hpre.hdigp; omega) (fun h => hw (by
        simp only [LeafW, CHAIN, PRIV, SEEDS, LEAFPK, LOUT] at h ⊢; omega)),
      ht.frame.getByte (by have := hpre.hdigp; omega) hw, hpre.hdig j hj]
  obtain ⟨t2, st2, t2pc, t2x17, t2r, t2f⟩ := sub72_spec hsub t1 t1pc (A.digp + j)
    (by have := hpre.hdigp; omega) (A.d j) hdb.1 t1x28 hbyte
  have e12 : RegsExcept t t2 [.x6, .x7, .x17, .x28, .x29, .x30] := (t1r.trans t2r).mono (by simp)
  have r8 : t.getReg .x8 = BitVec.ofNat 64 A.lay.val := by rw [g _ (by simp [leafRegs]), hpre.x8]
  obtain ⟨t3, st3, t3pc, t3x21, t3r, t3f⟩ := sub73_spec hsub t2 t2pc A.lay.val
    (by have := A.lay.isLt; omega) (by rw [e12.get (by simp)]; exact r8)
  have hseedv : DigAt t1 (CHAIN + 48) seed := ⟨t1c48.trans hseed.1, by
    rw [t1c56, show SEEDS + 16 * half + 8 = SEEDS + 16 * half + 8 from rfl]; exact hseed.2⟩
  obtain ⟨t4, st4, t4pc, t4x21, t4r, t4f⟩ : ∃ t4, Steps image t3 (selectorExtra A.lay j)
      (selectorExtra A.lay j) t4 ∧ t4.pc = pcOf (b + 76) ∧
      t4.getReg .x21 = BitVec.ofNat 64 (maxDigit A.lay j) ∧ RegsExcept t3 t4 [.x21] ∧
      Frame t3 t4 (fun _ => False) := by
    have hlay0 : A.lay.val = 0 ↔ A.lay = 0 := by simp
    by_cases hl : A.lay = 0
    · rw [if_pos (hlay0.mpr hl)] at t3pc
      obtain ⟨ta, sta, tapc, tar, taf⟩ := sub75_spec hsub t3 t3pc
      have e1a := ((e12.trans t3r).trans tar)
      obtain ⟨tb, stb, tbpc, tbx21, tbr, tbf⟩ := maxLow_spec hsub ta tapc j (n4 A.lay)
        (by omega) (by omega) (by rw [e1a.get (by simp)]; exact ht.x19)
        (by rw [e1a.get (by simp)]; exact r27)
      by_cases hjn : j < n4 A.lay
      · rw [if_pos hjn] at tbpc
        obtain ⟨tc, stc, tcpc, tcx21, tcr, tcf⟩ := maxHigh_spec hsub tb tbpc
        refine ⟨tc, ?_, tcpc, ?_, ?_, ?_⟩
        · simpa only [selectorExtra, if_pos hl, if_pos hjn] using (sta.trans stb).trans stc
        · simpa only [maxDigit_shape, if_pos hl, if_pos hjn] using tcx21
        · exact ((tar.trans tbr).trans tcr).mono (by simp)
        · exact ((taf.trans tbf).trans tcf).mono (by simp)
      · rw [if_neg hjn] at tbpc
        refine ⟨tb, ?_, tbpc, ?_, ?_, ?_⟩
        · simpa only [selectorExtra, if_pos hl, if_neg hjn] using sta.trans stb
        · simpa only [maxDigit_shape, if_pos hl, if_neg hjn] using tbx21
        · exact (tar.trans tbr).mono (by simp)
        · exact (taf.trans tbf).mono (by simp)
    · rw [if_neg (fun hv => hl (hlay0.mp hv))] at t3pc
      exact ⟨t3, by simpa [selectorExtra, hl] using Steps.refl t3, t3pc,
        by simpa [maxDigit_shape, hl] using t3x21, RegsExcept.refl _ _, Frame.refl _ _⟩
  have e14 : RegsExcept t t4 [.x6, .x7, .x17, .x21, .x28, .x29, .x30] :=
    ((e12.trans t3r).trans t4r).mono (by simp)
  obtain ⟨t5, st5, t5pc, t5r, t5f⟩ := sub76_spec hsub t4 t4pc A.so (by rw [e14.get (by simp)]; exact r31)
  obtain ⟨t6, st6, t6pc, t6x21, t6r, t6f⟩ : ∃ t6, Steps image t5 (if A.so then 1 else 0)
      (if A.so then 1 else 0) t6 ∧ t6.pc = pcOf (b + 78) ∧
      t6.getReg .x21 = BitVec.ofNat 64 (A.e j) ∧ RegsExcept t5 t6 [.x21] ∧
      Frame t5 t6 (fun _ => False) := by
    cases hso : A.so
    · rw [hso, if_neg (by simp)] at t5pc
      refine ⟨t5, by simpa using Steps.refl t5, t5pc, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
      rw [t5r.get (by simp), t4x21, LeafArgs.e, hso]; rfl
    · rw [hso, if_pos rfl] at t5pc
      obtain ⟨t6, st6, t6pc, t6x21, t6r, t6f⟩ := sub77_spec hsub t5 t5pc
      refine ⟨t6, by simpa using st6, t6pc, ?_, t6r, t6f⟩
      rw [t6x21, t5r.get (by simp), t4r.get (by simp), t3r.get (by simp), t2x17, LeafArgs.e, hso]; rfl
  obtain ⟨u, st7, upc, ux1, ur, uf⟩ := sub78_spec hsub t6 t6pc
  have e1u : RegsExcept t u [.x1, .x6, .x7, .x17, .x21, .x28, .x29, .x30] :=
    (((e14.trans t5r).trans t6r).trans ur).mono (by simp)
  have f1u : Frame t u (fun X => X = CHAIN + 48 ∨ X = CHAIN + 56) :=
    (((((t1f.trans t2f).trans t3f).trans t4f).trans t5f).trans (t6f.trans uf)).mono (fun X _ h => by
      simp only [or_false] at h; exact h)
  have f2u : Frame t2 u (fun _ => False) :=
    ((((t3f.trans t4f).trans t5f).trans t6f).trans uf).mono (fun X _ h => by simp_all)
  have gu : ∀ r, r ∉ leafRegs → r ∉ [.x1, .x6, .x7, .x17, .x21, .x28, .x29, .x30] →
      u.getReg r = s0.getReg r := fun r h1 h2 => (e1u.get h2).trans (g r h1)
  have fr : ∀ X, X < 2 ^ 64 → ¬ LeafW A X → X ≠ CHAIN + 48 → X ≠ CHAIN + 56 →
      u.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX h1 h2 h3 =>
    (f1u.get hX (by simp [h2, h3])).trans (ht.frame.get hX h1)
  have hL : ∀ X, (X = CHAIN ∨ X = CHAIN + 8 ∨ X = CHAIN + 32 ∨ X = CHAIN + 40) → ¬ LeafW A X := by
    intro X hX hw'
    simp only [LeafW, CHAIN, PRIV, SEEDS, LEAFPK, LOUT] at hX hw' hvs
    have := hpre.hds
    have := hpre.hdv
    simp only [CHAIN, PRIV, SEEDS, LEAFPK, LOUT] at *
    split_ifs at hw' <;> omega
  refine ⟨u, ?_, upc, {
      x5 := ?_, x1 := ux1, x8 := ?_, x9 := ?_, x18 := ?_
      x17 := ?_, x19 := ?_, x21 := ?_, x23 := ?_, htree := hpre.htree
      hi := by change j < 64; change A.n = 54 ∨ A.n = 43 at hn; omega
      hroute := hpre.hroute, hleaf := hpre.hleafHeight
      hcap := ?_, he := hpre.hsteps j hj, hv8 := ?_, hv := ?_, hvc := ?_
      z0 := ?_, z8 := ?_, z32 := ?_, z40 := ?_ },
    hseedv.frame (((t2f.trans t3f).trans t4f).trans (t5f.trans (t6f.trans uf))) (by decide)
      (by simp) (by simp), e1u, f1u⟩
  · have := (st1.trans st2).trans ((st3.trans st4).trans ((st5.trans st6).trans st7))
    refine Steps.of_eq this ?_ ?_ <;> split_ifs <;> simp_all <;> omega
  · rw [gu _ (by simp [leafRegs]) (by simp), hpre.x5]
  · rw [gu _ (by simp [leafRegs]) (by simp), hpre.x8]
  · rw [gu _ (by simp [leafRegs]) (by simp), hpre.x9]
  · rw [gu _ (by simp [leafRegs]) (by simp), hpre.x18]
  · rw [ur.get (by simp), t6r.get (by simp), t5r.get (by simp), t4r.get (by simp), t3r.get (by simp),
      t2x17]
  · rw [e1u.get (by simp)]; exact ht.x19
  · rw [ur.get (by simp)]; exact t6x21
  · rw [e1u.get (by simp)]; exact ht.x23
  · unfold LeafArgs.e; split_ifs with hso
    · exact le_refl _
    · exact hdb.2 (by simpa using hso)
  · omega
  · omega
  · simp only [CHAIN, PRIV, LEAFPK] at hvs ⊢; omega
  · rw [fr CHAIN (by decide) (hL _ (by simp)) (by decide) (by decide), hpre.z0]
  · rw [fr (CHAIN + 8) (by decide) (hL _ (by simp)) (by decide) (by decide), hpre.z8]
  · rw [fr (CHAIN + 32) (by decide) (hL _ (by simp)) (by decide) (by decide), hpre.z32]
  · rw [fr (CHAIN + 40) (by decide) (hL _ (by simp)) (by decide) (by decide), hpre.z40]
set_option maxHeartbeats 1000000 in
theorem leaf_postchainS {j : Nat} (hj : j < A.n) {st : List Digest × List Digest} {t u : MachineState}
    (ht : LeafInv s0 A j st t) (hupc : u.pc = pcOf (b + 79))
    (hur : RegsExcept t u ([.x1, .x6, .x7, .x17, .x21, .x28, .x29, .x30] ++ chainRegs))
    (huf : Frame t u (fun X => (X = CHAIN + 48 ∨ X = CHAIN + 56) ∨ ChainW (A.valp + 16 * j) X))
    (v last : Digest) (hv : DigAt u (A.valp + 16 * j) v) (hl : DigAt u (CHAIN + 48) last) :
    ∃ w, Steps image u (4 + (if A.so then 0 else 11 + slotK A.lay j))
        (4 + (if A.so then 0 else 11 + slotK A.lay j)) w ∧ w.pc = pcOf (b + 41) ∧
      LeafInv s0 A (j + 1) (if A.so then (st.1, st.2 ++ [v]) else (st.1 ++ [last], st.2 ++ [v])) w ∧
      Frame u w (fun X => slot A.lay j ≤ X ∧ X < slot A.lay j + 16) := by
  have hn : A.n = 54 ∨ A.n = 43 := chainCount_cases A.lay
  have hvs := hpre.hvs
  have hvb := hpre.hv
  have hv8 := hpre.hv8
  have g : ∀ r, r ∉ leafRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r31 : u.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0) := by
    rw [hur.get (by simp [chainRegs]), g _ (by simp [leafRegs]), hpre.x31]
  obtain ⟨u1, st1, u1pc, u1r, u1f⟩ := sub79_spec hsub u hupc A.so r31
  obtain ⟨u2, st2, u2pc, u2r, u2f, u2s⟩ : ∃ u2, Steps image u1 (if A.so then 0 else 11 + slotK A.lay j)
      (if A.so then 0 else 11 + slotK A.lay j) u2 ∧ u2.pc = pcOf (b + 92) ∧
      RegsExcept u1 u2 [.x6, .x7, .x28, .x29] ∧
      Frame u1 u2 (fun X => slot A.lay j ≤ X ∧ X < slot A.lay j + 16) ∧
      (A.so = false → DigAt u2 (slot A.lay j) last) := by
    cases hso : A.so
    · rw [hso, if_neg (by simp)] at u1pc
      have r19 : u1.getReg .x19 = BitVec.ofNat 64 j := by
        rw [u1r.get (by simp), hur.get (by simp [chainRegs])]; exact ht.x19
      obtain ⟨u3, st3, u3pc, u3x28, u3r, u3f⟩ := sub80_spec hsub u1 u1pc j (by omega) r19
      have hl1 : DigAt u1 (CHAIN + 48) last := hl.frame u1f (by decide) (by simp) (by simp)
      have hl0 := hpre.hsl hso
      rw [slotK_low hl0]
      by_cases hj0 : j = 0
      · subst hj0
        rw [if_pos rfl] at u3pc
        obtain ⟨u4, st4, u4pc, u4a, u4b, u4r, u4f⟩ := sub83_spec hsub u3 u3pc (16 * 0) (by omega)
          (by decide) u3x28
        refine ⟨u4, by simpa using st3.trans st4, u4pc, (u3r.trans u4r).mono (by simp),
          (u3f.trans u4f).mono (fun X _ h => by simp [slot_low hl0] at h ⊢; omega), fun _ => ?_⟩
        have hl3 := hl1.frame u3f (by decide) (by simp) (by simp)
        exact ⟨by rw [slot_low hl0, if_pos rfl, show LEAFPK = LEAFPK + 16 * 0 from rfl, u4a]; exact hl3.1,
          by rw [slot_low hl0, if_pos rfl, show LEAFPK + 8 = LEAFPK + 16 * 0 + 8 from rfl, u4b]; exact hl3.2⟩
      · rw [if_neg hj0] at u3pc
        obtain ⟨u4, st4, u4pc, u4x28, u4r, u4f⟩ := sub82_spec hsub u3 u3pc (16 * j) u3x28
        obtain ⟨u5, st5, u5pc, u5a, u5b, u5r, u5f⟩ := sub83_spec hsub u4 u4pc (16 * j + 16) (by omega)
          (by sc_omega) u4x28
        have hs : slot A.lay j = LEAFPK + (16 * j + 16) := by rw [slot_low hl0, if_neg hj0]; ring
        refine ⟨u5, by simpa [hj0] using st3.trans (st4.trans st5), u5pc,
          ((u3r.trans u4r).trans u5r).mono (by simp),
          ((u3f.trans u4f).trans u5f).mono (fun X _ h => by rw [hs]; simp at h ⊢; omega), fun _ => ?_⟩
        have hl4 := hl1.frame (u3f.trans u4f) (by decide) (by simp) (by simp)
        exact ⟨by rw [hs, u5a]; exact hl4.1, by rw [hs, u5b]; exact hl4.2⟩
    · rw [hso, if_pos rfl] at u1pc
      exact ⟨u1, by simpa using Steps.refl u1, u1pc, RegsExcept.refl _ _, Frame.refl _ _,
        fun h => by simp at h⟩
  have r19' : u2.getReg .x19 = BitVec.ofNat 64 j := by
    rw [u2r.get (by simp), u1r.get (by simp), hur.get (by simp [chainRegs])]; exact ht.x19
  have r23' : u2.getReg .x23 = BitVec.ofNat 64 (A.valp + 16 * j) := by
    rw [u2r.get (by simp), u1r.get (by simp), hur.get (by simp [chainRegs])]; exact ht.x23
  obtain ⟨w, st6, wpc, wx19, wx23, wr, wf⟩ := sub92_spec hsub u2 u2pc j (A.valp + 16 * j) r19' r23'
  have hslot : ∀ c, c < A.n → LEAFPK ≤ slot A.lay c ∧ slot A.lay c + 16 ≤ LEAFPK + 16 * (A.n + 2) := by
    intro c hc; unfold slot; split_ifs <;> constructor <;> omega
  have hsj := hslot j hj
  have ftw : Frame t w (fun X => ((X = CHAIN + 48 ∨ X = CHAIN + 56) ∨ ChainW (A.valp + 16 * j) X) ∨
      (slot A.lay j ≤ X ∧ X < slot A.lay j + 16)) :=
    (((huf.trans u1f).trans u2f).trans wf).mono (fun X _ h => by
      rcases h with ((h | h) | h) | h
      · exact Or.inl h
      · exact h.elim
      · exact Or.inr h
      · exact h.elim)
  have fuw : Frame u w (fun X => slot A.lay j ≤ X ∧ X < slot A.lay j + 16) :=
    ((u1f.trans u2f).trans wf).mono (fun X _ h => by
      rcases h with (h | h) | h
      · exact h.elim
      · exact h
      · exact h.elim)
  refine ⟨w, ?_, wpc, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fuw⟩
  · have := st1.trans (st2.trans st6)
    refine Steps.of_eq this ?_ ?_ <;> split_ifs <;> simp_all <;> omega <;> omega
  · rw [wx19]
  · rw [wx23, show A.valp + 16 * j + 16 = A.valp + 16 * (j + 1) by ring]
  · rw [wr.get (by simp), u2r.get (by simp), u1r.get (by simp), hur.get (by simp [chainRegs])]; exact ht.x3
  · exact ((ht.regs.trans hur).trans ((u1r.trans u2r).trans wr)).mono (by decide)
  · refine (ht.frame.trans ftw).mono (fun X _ h => ?_)
    rcases h with h | ((h | h) | h)
    · exact h
    · exact LeafW_of_c48 h
    · exact LeafW_of_chainW hj h
    · exact LeafW_of_slot hj h
  · have := slot_hdr A.lay j
    rw [ftw.get (by decide) (by unfold ChainW; sc_omega), ht.lh16]
  · have := slot_hdr A.lay j
    rw [ftw.get (by decide) (by unfold ChainW; sc_omega), ht.lh24]
  · have := ht.elen; split_ifs at this ⊢ with hso <;> simp_all
  · have := ht.vlen; split_ifs <;> simp_all
  · intro hso c hc
    rw [if_neg (by simp [hso])]
    simp only
    have hlen : st.1.length = j := by have := ht.elen; simpa [hso] using this
    by_cases hcj : c = j
    · subst hcj
      have hl5 : DigAt w (slot A.lay c) last :=
        (u2s hso).frame wf (by have := hsj; simp only [LEAFPK] at this; omega) (by simp) (by simp)
      simpa [List.getD_eq_getElem?_getD, hlen] using hl5
    · have hc' : c < j := by omega
      have hsc := slot_lt A.lay (show c < A.n by omega)
      have hsc0 := slot_ge A.lay c
      have hd := slot_disj A.lay hcj
      have hnot : ∀ X, slot A.lay c ≤ X → X < slot A.lay c + 16 →
          ¬ (((X = CHAIN + 48 ∨ X = CHAIN + 56) ∨ ChainW (A.valp + 16 * j) X) ∨
            (slot A.lay j ≤ X ∧ X < slot A.lay j + 16)) := by
        intro X h1 h2 h
        unfold ChainW at h
        sc_omega
      have hb64 : slot A.lay c + 8 < 2 ^ 64 := by
        have := hsc; simp only [LEAFPK] at this; omega
      have h2 : DigAt w (slot A.lay c) (st.1.getD c 0) :=
        (ht.ends hso c hc').frame ftw hb64 (hnot _ le_rfl (by omega)) (hnot _ (by omega) (by omega))
      simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : c < st.1.length)] using h2
  · have hsj0 := slot_ge A.lay j
    have hvw : DigAt w (A.valp + 16 * j) v :=
      hv.frame fuw (by omega) (by sc_omega) (by sc_omega)
    have hvals : DigsAt w A.valp st.2 :=
      ht.vals.frame ftw (by rw [ht.vlen]; omega) (fun X h1 h2 h => by
        rw [ht.vlen] at h2
        unfold ChainW at h
        sc_omega)
    have := hvals.snoc (d := v) (by rw [ht.vlen]; exact hvw)
    split_ifs <;> exact this
theorem leaf_exitS {st : List Digest × List Digest} {t : MachineState} (ht : LeafInv s0 A A.n st t)
    (hpc : t.pc = pcOf (b + 41)) :
    TSim image sk t (if A.so then 3 else 19) (if A.so then 3 else 18 + 8 * leafBlocks A.lay)
      (if A.so then 0 else 1) (if A.so then 0 else leafBlocks A.lay)
      (if A.so then pure (0, st.2) else (leafHash A.lay A.tree A.leaf st.1 >>= fun root => pure (root, st.2)))
      (fun r u => u.pc = pcOf A.ret ∧ (A.so = false → DigAt u A.dest r.1) ∧ DigsAt u A.valp r.2 ∧
        r.2.length = A.n ∧ u.getReg .x23 = BitVec.ofNat 64 (A.valp + 16 * A.n) ∧ RegsExcept s0 u leafRegs ∧
        Frame s0 u (LeafW A) ∧
        Frame t u (fun X => (LOUT ≤ X ∧ X < LOUT + 32) ∨ (X = A.dest ∨ X = A.dest + 8))) := by
  have hn : A.n = 54 ∨ A.n = 43 := chainCount_cases A.lay
  have g : ∀ r, r ∉ leafRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r26 : t.getReg .x26 = BitVec.ofNat 64 A.n := by rw [g _ (by simp [leafRegs]), hpre.x26]
  have r31 : t.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0) := by
    rw [g _ (by simp [leafRegs]), hpre.x31]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub41_spec hsub t hpc A.n A.n (by omega) (by omega) ht.x19 r26
  rw [if_neg (lt_irrefl _)] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := sub95_spec hsub t1 t1pc A.so (by rw [t1r.get (by simp)]; exact r31)
  have e12 : RegsExcept t t2 [] := (t1r.trans t2r).mono (by simp)
  have f12 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp_all)
  cases hso : A.so
  ·
    rw [hso, if_neg (by simp)] at t2pc
    simp only [Bool.false_eq_true, if_false]
    obtain ⟨t3, st3, t3pc, t3x10, t3x11, t3x12, t3r, t3f⟩ := sub96_spec hsub t2 t2pc A.n hn
      (by rw [e12.get (by simp)]; exact r26)
    have r13 : RegsExcept t t3 [.x6, .x10, .x11, .x12] := (e12.trans t3r).mono (by simp)
    have f13 : Frame t t3 (fun _ => False) := (f12.trans t3f).mono (fun X _ h => by simp_all)
    have hlen : st.1.length = A.n := by have := ht.elen; simpa [hso] using this
    have hends := ht.ends hso
    have hl0 := hpre.hsl hso
    have hn43 : A.n = 43 := chainCount_low hl0
    have hw : t3.readWords (BitVec.ofNat 64 LEAFPK) (8 * leafBlocks A.lay) =
        wordsOf (pad64 (T3.leafInput A.lay A.tree A.leaf st.1)) := by
      rw [leafInput_wordsS A hl0 st.1 hlen]
      have h0 : DigAt t3 LEAFPK (st.1.getD 0 0) := by
        have := (hends 0 (by omega)).frame f13 (by rw [slot_low hl0, if_pos rfl]; decide) (by simp) (by simp)
        rwa [slot_low hl0, if_pos rfl] at this
      have hrest : DigsAt t3 (LEAFPK + 32) (st.1.drop 1) := by
        intro c hc
        simp only [List.length_drop] at hc
        have hsl := slot_lt A.lay (show c + 1 < A.n by omega)
        rw [slot_low hl0, if_neg (show c + 1 ≠ 0 by omega)] at hsl
        simp only [LEAFPK] at hsl
        have := (hends (c + 1) (by omega)).frame f13
          (by rw [slot_low hl0, if_neg (show c + 1 ≠ 0 by omega)]; simp only [LEAFPK]; omega) (by simp) (by simp)
        rw [slot_low hl0, if_neg (show c + 1 ≠ 0 by omega)] at this
        rw [show LEAFPK + 32 + 16 * c = LEAFPK + 16 * (c + 1 + 1) by ring]
        simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using this
      have hhd : t3.readWords (BitVec.ofNat 64 (LEAFPK + 16)) 2 =
          [T3.hyperWord A.lay.val (A.tree * 2 ^ T3.height A.lay + A.leaf), 0] := by
        rw [readWords_two, f13.get (by decide) (by simp), f13.get (by decide) (by simp), ht.lh16,
          show LEAFPK + 16 + 8 = LEAFPK + 24 from rfl, ht.lh24]
      have hb : 8 * leafBlocks A.lay = 2 + (2 + 2 * (st.1.drop 1).length) := by
        simp only [List.length_drop, hlen, leafBlocks, show chainCount A.lay = A.n from rfl, hn43]
      rw [hb, readWords_add, readWords_add, h0.words, hhd, hrest.words]
      simp only [List.append_assoc]
    have hl := leafInput_lengthS A hl0 st.1 hlen
    have hnb : leafBlocks A.lay = 14 ∨ leafBlocks A.lay = 11 := by
      unfold leafBlocks; rcases hn with h | h <;> rw [show chainCount A.lay = A.n from rfl, h] <;> simp
    have hq : hashInput t3 = toQ (pad64 (T3.leafInput A.lay A.tree A.leaf st.1)) := by
      refine hashInput_toQ t3 _ (leafBlocks A.lay - 1) LEAFPK (by rw [hl]; omega) t3x10 (by decide)
        (by decide) ?_ (by omega) (by rw [show 8 * (leafBlocks A.lay - 1 + 1) = 8 * leafBlocks A.lay by omega]; exact hw)
      rw [t3x11]; congr 1
      unfold leafBlocks; rcases hn with h | h <;> rw [show chainCount A.lay = A.n from rfl, h]
    have hblk : (toQ (pad64 (T3.leafInput A.lay A.tree A.leaf st.1))).blocks =
        leafBlocks A.lay := by
      rw [blocks_toQ ⟨by rw [hl]; omega, by rw [hl]; omega⟩, hl]; omega
    have hv : hashArgumentsValid t3 = true := by
      refine hashArgs_const t3 LEAFPK (64 * leafBlocks A.lay) LOUT t3x10 ?_ t3x12 (by decide) (by omega)
        (by simp only [LEAFPK]; omega) (by decide) (by decide)
      rw [t3x11]; congr 1
      unfold leafBlocks; rcases hn with h | h <;> rw [show chainCount A.lay = A.n from rfl, h]
    have h5 : t3.getReg .x5 = 0 := by rw [r13.get (by simp), g _ (by simp [leafRegs]), hpre.x5]
    unfold leafHash
    refine (TSim.steps (st1.trans (st2.trans st3)) (TSim.shortHash_bind (k := 7) (c := 7) (n := 0) (b := 0)
      (f := fun root => pure (root, st.2)) (fetch_sub105 hsub t3 t3pc) h5 hv hq (fun a => ?_))).of_eq rfl
      (by omega) (by rw [hblk]; omega) (by omega) (by rw [hblk]; omega)
    have hds := hpre.hds
    have hdv := hpre.hdv
    have hvs := hpre.hvs
    have hdb := hpre.hd
    have hd8 := (hpre.hd8 hso)
    have hwf := Frame.writeHash t3 a LOUT t3x12 (by decide)
    obtain ⟨u2, st5, u2pc, u2a, u2b, u2r, u2f⟩ := sub106_spec hsub (writeHash t3 a)
      (by rw [pc_writeHash, t3pc, pcOf_add4]) A.dest hd8 hdb (by sc_omega)
      (by rw [getReg_writeHash, r13.get (by simp), g _ (by simp [leafRegs]), hpre.x25])
    have hlo := DigAt.writeHash_lo t3 a LOUT t3x12 (by decide)
    obtain ⟨u3, st6, u3pc, u3r, u3f⟩ := sub112_spec hsub u2 u2pc A.ret
      (by rw [u2r.get (by simp), getReg_writeHash, r13.get (by simp)]; exact ht.x3)
    have fall : Frame t u3 (fun X => (LOUT ≤ X ∧ X < LOUT + 32) ∨ (X = A.dest ∨ X = A.dest + 8)) :=
      ((f13.trans hwf).trans (u2f.trans u3f)).mono (fun X _ h => by
        rcases h with (h | h) | (h | h)
        · exact h.elim
        · left; exact h
        · right; exact h
        · exact h.elim)
    refine TSim.pure_steps (st5.trans st6) ⟨u3pc, fun _ => ?_, ?_, ht.vlen, ?_, ?_, ?_, fall⟩
    · have hd2 : DigAt u2 A.dest (a.extractLsb' 0 128) := ⟨u2a.trans hlo.1, by rw [u2b]; exact hlo.2⟩
      exact hd2.frame u3f (by omega) (by simp) (by simp)
    · have hvl := ht.vlen
      exact ht.vals.frame fall (by rw [hvl]; have := hpre.hv; omega) (fun X h1 h2 => by
        rw [hvl] at h2; sc_omega)
    · rw [u3r.get (by simp), u2r.get (by simp), getReg_writeHash, r13.get (by simp)]; exact ht.x23
    · have hw0 : RegsExcept t3 (writeHash t3 a) [] := fun r _ => getReg_writeHash t3 a r
      exact ((ht.regs.trans r13).trans ((hw0.trans u2r).trans u3r)).mono (by decide)
    · refine (ht.frame.trans fall).mono (fun X _ h => ?_)
      rcases h with h | h | h
      · exact h
      · unfold LeafW; right; right; right; right; right; right; right; left; exact h
      · unfold LeafW; right; right; right; right; right; right; right; right; right
        rcases h with h | h <;> omega
  ·
    rw [hso, if_pos rfl] at t2pc
    simp only [if_true]
    obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := sub112_spec hsub t2 t2pc A.ret (by rw [e12.get (by simp)]; exact ht.x3)
    refine TSim.pure_steps (st1.trans (st2.trans st3)) ⟨t3pc, fun h => by simp at h, ?_, ht.vlen, ?_, ?_, ?_, ?_⟩
    · have hvl := ht.vlen
      exact ht.vals.frame (f12.trans t3f) (by rw [hvl]; have := hpre.hv; omega) (fun X _ _ h => by simp_all)
    · rw [t3r.get (by simp), e12.get (by simp)]; exact ht.x23
    · exact (ht.regs.trans (e12.trans t3r)).mono (by decide)
    · exact (ht.frame.trans (f12.trans t3f)).mono (fun X _ h => by
        rcases h with h | h | h; exact h; exact h.elim; exact h.elim)
    · exact (f12.trans t3f).mono (fun _ _ h => by rcases h with h | h <;> exact h.elim)
end leaf
end SigGolfCandidate.T3M.Sign.Seed
end
