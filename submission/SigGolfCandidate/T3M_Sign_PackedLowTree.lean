import SigGolfCandidate.T3M_Sign_TopBlocks
import SigGolfCandidate.T3M_Sign_BaseInv
import SigGolfCandidate.T3M_Sign_TopLeaf
import SigGolfCandidate.T3M_Sign_SeedTree
import SigGolfCandidate.T3M_Witness_Dfs

section
namespace SigGolfCandidate.T3M.Sign.Packed
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
/-- Stage B (campaign X1): the scratch region the lower-leaf seed code writes (FTS scratch `PRIVW .. SCREND`, dead
after the forest: the 17 family coefficients at `COEF = 0x50800`, the x13..x16 spill at `COEF + 288`, the Horner
result at `CHAINW + 48`). -/
def BScr (X : Nat) : Prop := 0x50000 ≤ X ∧ X < 0x52010
macro "packed_sgo" : tactic =>
  `(tactic| ((try simp only [BScr, PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK, MOUT, ZDIG, DUMMY, TOP, MACBLK,
    REGION, MSG, SK, SIG, CACHE, NONCE, RHOOUT, DIG, NBUF, ENC, EOUT, FLEAF, LFOUT, FOREST, FOUT, MACOUT, TAG,
    DIGITS, SEL, IDXV, LOW, FTS, SEC, false_or, or_false] at *) <;> omega))
theorem ofNat_xor1 (v : Nat) (hv : v < 2 ^ 64) : BitVec.ofNat 64 v ^^^ 1#64 = BitVec.ofNat 64 (v ^^^ 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, toNat_ofNat_lt hv, toNat_ofNat_lt (Nat.xor_lt_two_pow hv (by norm_num))]
  rfl
theorem toNat_mod64 (l : Nat) (hl : l < 64) : (BitVec.ofNat 64 l).toNat % 64 = l := by
  rw [toNat_ofNat_lt (by omega)]; omega
theorem blk1173_spec (s : MachineState) (hpc : s.pc = pcOf 1173) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 1175 ∧ t.getReg .x4 = s.getReg .x1 ∧
      t.getReg .x13 = BitVec.ofNat 64 0 ∧ RegsExcept s t [.x4, .x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1173 codeAt_1173 s hpc (by simp [blk_1173.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1173.res, E.eval]
  · simp [blk_1173.res, rv_simp]
  · simp [blk_1173.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1173.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1173.res, rv_simp]
theorem blk1175_spec (s : MachineState) (hpc : s.pc = pcOf 1175) (l h : Nat) (hl : l < 2 ^ 63) (hh : h ≤ 12)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h15 : s.getReg .x15 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = (if l < 2 ^ h then pcOf 1178 else pcOf 1193) ∧
      t.getReg .x6 = BitVec.ofNat 64 (2 ^ h) ∧ RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hp : 2 ^ h ≤ 4096 := by
    calc 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
      _ = 4096 := by norm_num
  have e : (1#64 : Word) <<< ((BitVec.ofNat 64 h).toNat % 64) = BitVec.ofNat 64 (2 ^ h) := by
    rw [toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega), show (1#64 : Word) = BitVec.ofNat 64 1 from rfl,
      ofNat_shl, Nat.one_mul]
  refine ⟨_, symRun_sound blk_1175 codeAt_1175 s hpc (by simp [blk_1175.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_1175.res, E.eval, CmpOp.eval, BinOp.eval, h13, h15, e,
      ofNat_slt l (2 ^ h) hl (by omega)]
    by_cases hc : l < 2 ^ h <;> simp [hc]
  · simp only [Result.toState_getReg, blk_1175.res, rv_simp, BinOp.eval, h15, e]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1175.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1175.res, rv_simp]
theorem blk1178_spec (s : MachineState) (hpc : s.pc = pcOf 1178) (l sel : Nat) (hl : l < 2 ^ 64)
    (hsel : sel < 2 ^ 64) (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h14 : s.getReg .x14 = BitVec.ofNat 64 sel) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = (if l = sel then pcOf 1184 else pcOf 1187) ∧
      t.getReg .x18 = BitVec.ofNat 64 l ∧ t.getReg .x22 = BitVec.ofNat 64 ZDIG ∧
      t.getReg .x23 = BitVec.ofNat 64 DUMMY ∧ RegsExcept s t [.x18, .x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1178 codeAt_1178 s hpc (by simp [blk_1178.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_1178.res, E.eval, CmpOp.eval, h13, h14]
    by_cases hc : l = sel
    · subst hc; simp
    · rw [if_neg hc]
      have : BitVec.ofNat 64 l ≠ BitVec.ofNat 64 sel := fun he => hc ((ofNat_inj hl hsel).mp he)
      simp [this]
  · simp only [Result.toState_getReg, blk_1178.res]; t3n [h13]
  · simp [blk_1178.res, rv_simp]
  · simp [blk_1178.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1178.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1178.res, rv_simp]
theorem blk1184_spec (s : MachineState) (hpc : s.pc = pcOf 1184) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 1187 ∧ t.getReg .x22 = BitVec.ofNat 64 DIGITS ∧
      t.getReg .x23 = s.getReg .x16 ∧ RegsExcept s t [.x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1184 codeAt_1184 s hpc (by simp [blk_1184.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1184.res, E.eval]
  · simp [blk_1184.res, rv_simp]
  · simp [blk_1184.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1184.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1184.res, rv_simp]
theorem blk1187_spec (s : MachineState) (hpc : s.pc = pcOf 1187) (l h ar : Nat) (hl : l < 2 ^ h)
    (hh : h ≤ 12) (har : ar + 16 * 8192 < 2 ^ 64)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h6 : s.getReg .x6 = BitVec.ofNat 64 (2 ^ h))
    (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (1013 + 27) ∧ t.getReg .x1 = pcOf 1191 ∧
      t.getReg .x25 = BitVec.ofNat 64 (ar + 16 * (2 ^ h + l)) ∧
      RegsExcept s t [.x1, .x7, .x25] ∧ Frame s t (fun _ => False) := by
  have hp : 2 ^ h ≤ 4096 := by
    calc 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
      _ = 4096 := by norm_num
  refine ⟨_, symRun_sound blk_1187 codeAt_1187 s hpc (by simp [blk_1187.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1187.res, E.eval]
  · simp [blk_1187.res, rv_simp]
  · simp only [Result.toState_getReg, blk_1187.res]; t3n [h13, h6, h2]; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1187.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1187.res, rv_simp]
theorem blk1191_spec (s : MachineState) (hpc : s.pc = pcOf 1191) (l : Nat)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 1175 ∧ t.getReg .x13 = BitVec.ofNat 64 (l + 1) ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1191 codeAt_1191 s hpc (by simp [blk_1191.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [blk_1191.res, E.eval]
  · simp only [Result.toState_getReg, blk_1191.res]; t3n [h13]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1191.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1191.res, rv_simp]
def w1195 : List (BitVec 32) := [0xeedff0ef]
theorem codeAt_w1195 : CodeAt image (pcOf 1195) w1195 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
sym_block blk_w1195 := symRun { noAlias := true } w1195 (pcOf 1195) 100
theorem blk1193_spec (s : MachineState) (hpc : s.pc = pcOf 1193) (lay tree : Nat) (hlay1 : 1 ≤ lay)
    (hlay : lay < 256) (htree : tree < 2 ^ 32)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) :
    ∃ t, Steps image s 11 11 t ∧ t.pc = pcOf (1013 + 113) ∧ t.getReg .x1 = pcOf 1196 ∧
      t.getReg .x21 = BitVec.ofNat 64 (Keygen.nodeLo lay tree) ∧
      RegsExcept s t [.x1, .x6, .x21] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1542 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound blk_1193 codeAt_1193 s hpc (by simp [blk_1193.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [blk_1193.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have hS := SeedIndependent.seedIndependentAt_sign
  obtain ⟨t2, s2, p2, x21, r2, f2⟩ : ∃ t, Steps image t1 9 9 t ∧ t.pc = pcOf 1195 ∧
      t.getReg .x21 = BitVec.ofNat 64 (Keygen.nodeLo lay tree) ∧ RegsExcept t1 t [.x6, .x21] ∧
      Frame t1 t (fun _ => False) := by
    have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay := by rw [r1.get (by decide), h8]
    have g9 : t1.getReg .x9 = BitVec.ofNat 64 tree := by rw [r1.get (by decide), h9]
    refine ⟨_, symRun_sound SeedIndependent.blkS_hpm (SeedIndependent.codeAt_hpmS hS) t1 p1
      (by simp [SeedIndependent.blkS_hpm.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_hpm.res, E.eval]
    · simp only [Result.toState_getReg, SeedIndependent.blkS_hpm.res]
      t3n [g8, g9]
      unfold Keygen.nodeLo
      rw [if_neg (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      have hl : BitVec.ofNat 64 ((lay + 18446744073709551615) * 281474976710656) =
          BitVec.ofNat 64 ((lay - 1) * 281474976710656) := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
      rw [hl, show (513#64) = BitVec.ofNat 64 513 from rfl,
        ofNat_or_disjoint 513 (tree * 65536) 16 (by decide) (by omega),
        ofNat_or_disjoint' _ ((lay - 1) * 281474976710656) 48 (by omega) (by omega),
        show (13907115649320091648#64) = BitVec.ofNat 64 (193 * 2 ^ 56) from rfl,
        ofNat_or_disjoint' _ (193 * 2 ^ 56) 56 (by omega) (by omega)]
      unfold T3.hyperWord
      congr 1
      rw [Nat.mod_eq_of_lt htree, Nat.mod_eq_of_lt (by omega : lay - 1 < 256)]
      omega
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_hpm.res, rv_simp] <;> rfl
    · intro A _ _; simp [SeedIndependent.blkS_hpm.res, rv_simp]
  obtain ⟨t3, s3, p3, x1, r3, f3⟩ : ∃ t, Steps image t2 1 1 t ∧ t.pc = pcOf (1013 + 113) ∧
      t.getReg .x1 = pcOf 1196 ∧ RegsExcept t2 t [.x1] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound blk_w1195 codeAt_w1195 t2 p2 (by simp [blk_w1195.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [blk_w1195.res, E.eval]
    · simp [blk_w1195.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [blk_w1195.res, rv_simp] <;> rfl
    · intro A _ _; simp [blk_w1195.res, rv_simp]
  refine ⟨t3, (s1.trans s2).trans s3, p3, x1, by rw [r3.get (by decide), x21],
    ((r1.trans r2).trans r3).mono (by decide), ((f1.trans f2).trans f3).mono (fun A _ h => by simp_all)⟩
theorem blk1196_spec (s : MachineState) (hpc : s.pc = pcOf 1196) (h sel sb n : Nat) (hh : h ≤ 12)
    (hsel : sel < 4096) (hsb : sb + 16 * n < 2 ^ 64)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 h) (h14 : s.getReg .x14 = BitVec.ofNat 64 sel)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 sb) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf 1202 ∧ t.getReg .x13 = BitVec.ofNat 64 0 ∧
      t.getReg .x19 = BitVec.ofNat 64 (2 ^ h + sel) ∧ t.getReg .x24 = BitVec.ofNat 64 (sb + 16 * n) ∧
      RegsExcept s t [.x6, .x7, .x13, .x19, .x24] ∧ Frame s t (fun _ => False) := by
  have hp : 2 ^ h ≤ 4096 := by
    calc 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
      _ = 4096 := by norm_num
  have e : (1#64 : Word) <<< ((BitVec.ofNat 64 h).toNat % 64) = BitVec.ofNat 64 (2 ^ h) := by
    rw [toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega), show (1#64 : Word) = BitVec.ofNat 64 1 from rfl,
      ofNat_shl, Nat.one_mul]
  refine ⟨_, symRun_sound blk_1196 codeAt_1196 s hpc (by simp [blk_1196.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1196.res, E.eval]
  · simp [blk_1196.res, rv_simp]
  · simp only [Result.toState_getReg, blk_1196.res, rv_simp, BinOp.eval, h15, h14, e, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, blk_1196.res]; t3n [h16, h26]; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1196.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1196.res, rv_simp]
theorem blk1202_spec (s : MachineState) (hpc : s.pc = pcOf 1202) (l h : Nat) (hl : l < 2 ^ 63) (hh : h < 2 ^ 63)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h15 : s.getReg .x15 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if l < h then pcOf 1203 else pcOf 1214) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1202 codeAt_1202 s hpc (by simp [blk_1202.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_1202.res, E.eval, CmpOp.eval, h13, h15, ofNat_slt l h hl hh]
    by_cases hc : l < h <;> simp [hc]
  · intro r hr; cases r <;> simp_all [blk_1202.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1202.res, rv_simp]
theorem blk1203_spec (s : MachineState) (hpc : s.pc = pcOf 1203) (l hi ar ep : Nat) (hl : l < 64)
    (hhi : hi < 8192) (har : ar + 16 * 8192 ≤ 2 ^ 24) (har8 : ar % 8 = 0) (hep : ep + 16 ≤ 2 ^ 24)
    (hep8 : ep % 8 = 0)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h19 : s.getReg .x19 = BitVec.ofNat 64 hi)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) (h24 : s.getReg .x24 = BitVec.ofNat 64 ep) :
    ∃ t, Steps image s 11 11 t ∧ t.pc = pcOf 1202 ∧ t.getReg .x13 = BitVec.ofNat 64 (l + 1) ∧
      t.getReg .x24 = BitVec.ofNat 64 (ep + 16) ∧
      t.getMem (BitVec.ofNat 64 ep) = s.getMem (BitVec.ofNat 64 (ar + 16 * (hi / 2 ^ l ^^^ 1))) ∧
      t.getMem (BitVec.ofNat 64 (ep + 8)) = s.getMem (BitVec.ofNat 64 (ar + 16 * (hi / 2 ^ l ^^^ 1) + 8)) ∧
      RegsExcept s t [.x6, .x7, .x13, .x24, .x28] ∧ Frame s t (fun A => A = ep ∨ A = ep + 8) := by
  have hd : hi / 2 ^ l < 8192 := lt_of_le_of_lt (Nat.div_le_self _ _) hhi
  have hx : hi / 2 ^ l ^^^ 1 < 8192 := Nat.xor_lt_two_pow (n := 13) hd (by norm_num)
  have e1 : BitVec.ofNat 64 hi >>> ((BitVec.ofNat 64 l).toNat % 64) ^^^ 1#64 =
      BitVec.ofNat 64 (hi / 2 ^ l ^^^ 1) := by
    rw [toNat_mod64 l hl, ofNat_shr hi l (by omega), ofNat_xor1 _ (by omega)]
  have hobl : Oblig.all s blk_1203.res.st.obl := by
    simp only [blk_1203.res]
    simp only [rv_simp, h13, h19, h2, h24, e1]
    t3n []
    omega
  refine ⟨_, symRun_sound blk_1203 codeAt_1203 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1203.res, E.eval]
  · simp only [Result.toState_getReg, blk_1203.res]; t3n [h13]
  · simp only [Result.toState_getReg, blk_1203.res]; t3n [h24]
  · simp only [Result.toState_getMem, blk_1203.res]
    simp only [rv_simp, h13, h19, h2, h24, e1]
    t3n []
    repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])
    congr 2; omega
  · simp only [Result.toState_getMem, blk_1203.res]
    simp only [rv_simp, h13, h19, h2, h24, e1]
    t3n []
    repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])
    congr 2; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1203.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, blk_1203.res]
    t3n [h24]
    rw [if_neg (by omega), if_neg (by omega)]
end SigGolfCandidate.T3M.Sign.Packed
end
section
namespace SigGolfCandidate.T3M.Sign.Packed.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def entryCode : List (BitVec 32) := [134967,638521107,0xc90906f]
def pairCode : List (BitVec 32) := [33633027,42021763,7286819,8336419,50410243,58798979,40843299,41892899,131175]
theorem entry_at : CodeAt image (pcOf 1214) entryCode :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem pair_at : CodeAt image (pcOf 10994) pairCode :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
sym_block entryBlock := symRun { noAlias := true } entryCode (pcOf 1214) 20
sym_block pairBlock := symRun { noAlias := true } pairCode (pcOf 10994) 20
theorem pair_spec (s : MachineState) (hpc : s.pc = pcOf 10994) (ar ret : Nat)
    (har : ar + 64 ≤ 2 ^ 24) (har8 : ar % 8 = 0)
    (hsep : ENC + 64 ≤ ar ∨ ar + 64 ≤ ENC)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) (h4 : s.getReg .x4 = pcOf ret)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 ENC) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 (ar + 32)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (ar + 40)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 48)) = s.getMem (BitVec.ofNat 64 (ar + 48)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 56)) = s.getMem (BitVec.ofNat 64 (ar + 56)) ∧
      RegsExcept s t [.x6, .x7] ∧
      Frame s t (fun A => A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
  have hobl : Oblig.all s pairBlock.res.st.obl := by
    simp only [pairBlock.res]
    t3n [h2, h30, ENC]
    simp only [ENC] at hsep
    simp only [and_true]
    omega
  refine ⟨_, symRun_sound pairBlock pair_at s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pairBlock.res, rv_simp, h4, pcOf_and_max]
  · simp only [Result.toState_getMem, pairBlock.res, ENC]
    t3n [h2, h30, ENC]
  · simp only [Result.toState_getMem, pairBlock.res, ENC]
    t3n [h2, h30, ENC]
  · simp only [Result.toState_getMem, pairBlock.res, ENC]
    t3n [h2, h30, ENC]
  · simp only [Result.toState_getMem, pairBlock.res, ENC]
    t3n [h2, h30, ENC]
  · intro r hr; simp at hr; cases r <;> simp_all [pairBlock.res, rv_simp]; rfl
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, pairBlock.res]
    t3n [h30, ENC]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem entry_spec (s : MachineState) (hpc : s.pc = pcOf 1214) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 10994 ∧
      t.getReg .x30 = BitVec.ofNat 64 ENC ∧ RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound entryBlock entry_at s hpc (by simp [entryBlock.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, entryBlock.res, rv_simp, pcOf]
  · simp [Result.toState_getReg, entryBlock.res, rv_simp, ENC]
  · intro r hr; simp at hr; cases r <;> simp_all [entryBlock.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, entryBlock.res, rv_simp]
theorem blk1214_pair_spec (s : MachineState) (hpc : s.pc = pcOf 1214) (ar ret : Nat)
    (har : ar + 64 ≤ 2 ^ 24) (har8 : ar % 8 = 0)
    (hsep : ENC + 64 ≤ ar ∨ ar + 64 ≤ ENC)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) (h4 : s.getReg .x4 = pcOf ret) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 (ar + 32)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (ar + 40)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 48)) = s.getMem (BitVec.ofNat 64 (ar + 48)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 56)) = s.getMem (BitVec.ofNat 64 (ar + 56)) ∧
      RegsExcept s t [.x6, .x7, .x30] ∧
      Frame s t (fun A => A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
  obtain ⟨u, su, upc, u30, ur, uf⟩ := entry_spec s hpc
  obtain ⟨t, ut, tpc, m0, m8, m48, m56, tr, tf⟩ := pair_spec u upc ar ret har har8 hsep
    (by rw [ur.get (by simp), h2]) (by rw [ur.get (by simp), h4]) u30
  refine ⟨t, su.trans ut, tpc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m0, uf.get (by omega) (by simp)]
  · rw [m8, uf.get (by omega) (by simp)]
  · rw [m48, uf.get (by omega) (by simp)]
  · rw [m56, uf.get (by omega) (by simp)]
  · exact (ur.trans tr).mono (by decide)
  · exact (uf.trans tf).mono (by intro A hA h; simpa using h)
#print axioms blk1214_pair_spec
end SigGolfCandidate.T3M.Sign.Packed.BCBlocks
end
section
namespace SigGolfCandidate.T3M.Sign.Packed
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest buildLeaf buildLevels buildTree height chainCount width)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION
  LeafArgs LeafPre LeafW leafRegs LevArgs LevPre HeapAt LevW levRegs n4 buildLeaf_tsim)
def memDig (t : MachineState) (A : Nat) : Digest := t.getMem (BitVec.ofNat 64 (A + 8)) ++ t.getMem (BitVec.ofNat 64 A)
theorem memDig_toNat (t : MachineState) (A : Nat) :
    (memDig t A).toNat = (t.getMem (BitVec.ofNat 64 (A + 8))).toNat * 2 ^ 64 + (t.getMem (BitVec.ofNat 64 A)).toNat := by
  rw [memDig, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (t.getMem (BitVec.ofNat 64 A)).isLt,
    Nat.shiftLeft_eq]
theorem memDig_digAt (t : MachineState) (A : Nat) : DigAt t A (memDig t A) := by
  have h1 := (t.getMem (BitVec.ofNat 64 A)).isLt
  have h2 := (t.getMem (BitVec.ofNat 64 (A + 8))).isLt
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, memDig_toNat, Nat.shiftRight_zero]
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, memDig_toNat, Nat.shiftRight_eq_div_pow]
    omega
theorem memDig_eq {t : MachineState} {A : Nat} {d : Digest} (h : DigAt t A d) : memDig t A = d := by
  apply BitVec.eq_of_toNat_eq
  rw [memDig_toNat, h.1, h.2, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Nat.shiftRight_eq_div_pow]
  have := d.isLt
  omega
abbrev LeafFn := Layer → Nat → Nat → List Nat → Digest → T3.M ((Digest × List Digest) × Digest)
def topPair (lay : Layer) (levels : List (List Digest)) : Digest × Digest :=
  ((levels.getD (height lay - 1) []).getD 0 0, (levels.getD (height lay - 1) []).getD 1 0)
/-- Cycle bound of one lower leaf (v6: the family prologue (≤ 19 pairs), 43 Horner seeds over ≤ 38 coefficients,
43 chains). -/
def lowLeafC : Nat := 292000
def PackedLeafSpec (leafFn : LeafFn) : Prop :=
  ∀ (sk : SecretKey) (A : LeafArgs) (s : MachineState) (carry : Digest),
    A.lay ≠ 0 → A.so = false → LeafPreS sk s A → s.pc = pcOf (1013 + 27) →
    s.getReg .x15 = BitVec.ofNat 64 (T3.height A.lay) →
    A.valp + 16 * A.n ≤ 0x50000 → A.digp + A.n ≤ 0x50000 → A.dest + 16 ≤ 0x50000 →
    (A.leaf % 2 = 1 → DigAt s (SEEDS + 16) carry) →
    TBSim image sk s lowLeafC
      (leafFn A.lay A.tree A.leaf A.digits carry)
      (fun r t => t.pc = pcOf A.ret ∧
        (A.so = false → DigAt t A.dest r.1.1) ∧ DigsAt t A.valp r.1.2 ∧
        r.1.2.length = A.n ∧ DigAt t (SEEDS + 16) r.2 ∧
        RegsExcept s t leafRegs ∧ Frame s t (fun X => LeafW A X ∨ BScr X))
def btLeaf (lay : Layer) (tree sel : Nat) (ds : List Nat) (sb l : Nat) : LeafArgs :=
  ⟨lay, tree, l, if l = sel then ds else [], false, if l = sel then DIGITS else ZDIG,
    if l = sel then sb else DUMMY, LOW + 16 * (2 ^ height lay + l), 1191⟩
theorem btLeaf_costs (lay : Layer) (hlay : lay ≠ 0) (tree sel : Nat) (ds : List Nat) (sb l : Nat) :
    (btLeaf lay tree sel ds sb l).leafK = (if lay = 1 then 13800 else 14101) ∧
    (btLeaf lay tree sel ds sb l).leafC = (if lay = 1 then 16148 else 16449) ∧
    (btLeaf lay tree sel ds sb l).leafN = 324 ∧ (btLeaf lay tree sel ds sb l).leafB = 334 := by
  have e : (btLeaf lay tree sel ds sb l).leafK = (btLeaf lay 0 0 [] 0 1).leafK ∧
      (btLeaf lay tree sel ds sb l).leafC = (btLeaf lay 0 0 [] 0 1).leafC ∧
      (btLeaf lay tree sel ds sb l).leafN = (btLeaf lay 0 0 [] 0 1).leafN ∧
      (btLeaf lay tree sel ds sb l).leafB = (btLeaf lay 0 0 [] 0 1).leafB := ⟨rfl, rfl, rfl, rfl⟩
  rw [e.1, e.2.1, e.2.2.1, e.2.2.2]
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
theorem chainCount_low {lay : Layer} (h : lay ≠ 0) : chainCount lay = 43 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals rfl
theorem n4_low {lay : Layer} (h : lay ≠ 0) : n4 lay = 0 := by simp [n4, h]
theorem height_low {lay : Layer} (h : lay ≠ 0) : height lay = 6 ∨ height lay = 7 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals simp [height]
structure BtPre (sk : SecretKey) (cache : Bytes 131072) (lay : Layer) (tree sel : Nat) (ds : List Nat)
    (sb : Nat) (s : MachineState) (cfFlag : Nat := 1) : Prop where
  x2 : s.getReg .x2 = BitVec.ofNat 64 LOW
  x8 : s.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 tree
  x14 : s.getReg .x14 = BitVec.ofNat 64 sel
  x15 : s.getReg .x15 = BitVec.ofNat 64 (height lay)
  x16 : s.getReg .x16 = BitVec.ofNat 64 sb
  x26 : s.getReg .x26 = BitVec.ofNat 64 43
  x27 : s.getReg .x27 = BitVec.ofNat 64 0
  x31 : s.getReg .x31 = BitVec.ofNat 64 0
  base : Base (cfFlag := cfFlag) sk cache s
  hlay : lay ≠ 0
  htree : tree < 2 ^ 32
  hroute : ∀ l < 2 ^ height lay, tree * 2 ^ height lay + l < 2 ^ 31
  hsel : sel < 2 ^ height lay
  hdb : ∀ i < 43, ds.getD i 0 ≤ 7
  digits : ∀ i < 43, s.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 (ds.getD i 0)
  hsb : SIG ≤ sb ∧ sb + 16 * (43 + height lay) ≤ SIG + 5616
  hsb8 : sb % 8 = 0
def BtW (sb H : Nat) (X : Nat) : Prop :=
  X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ X = CHAIN + 16 ∨ X = CHAIN + 24 ∨
    (CHAIN + 32 ≤ X ∧ X < CHAIN + 112) ∨ (LEAFPK ≤ X ∧ X < LEAFPK + 16 * 45) ∨ (LOUT ≤ X ∧ X < LOUT + 32) ∨
    (DUMMY ≤ X ∧ X < DUMMY + 16 * 43) ∨ (sb ≤ X ∧ X < sb + 16 * 43) ∨
    (LOW + 16 * 2 ^ H ≤ X ∧ X < LOW + 16 * 2 ^ (H + 1)) ∨ BScr X
def btRegs : List Reg := leafRegs ++ [.x6, .x13, .x18, .x22, .x23, .x25]
structure BtInv (s1 : MachineState) (sb sel H l : Nat) (st : List Digest × List Digest) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf 1175
  x13 : t.getReg .x13 = BitVec.ofNat 64 l
  regs : RegsExcept s1 t btRegs
  frame : Frame s1 t (BtW sb H)
  len : st.1.length = l
  roots : DigsAt t (LOW + 16 * 2 ^ H) st.1
  vals : sel < l → st.2.length = 43 ∧ DigsAt t sb st.2
theorem extractByte_zero' (k : Nat) : extractByte (0 : Word) k = 0 := by
  simp [extractByte]
structure BtInvP (s1 : MachineState) (sb sel H l : Nat)
    (st : List Digest × List Digest × Digest) (t : MachineState) : Prop where
  old : BtInv s1 sb sel H l (st.1, st.2.1) t
  carry : l % 2 = 1 → DigAt t (SEEDS + 16) st.2.2
def btBodyP (leafFn : LeafFn) (lay : Layer) (tree sel : Nat) (ds : List Nat)
    (state : List Digest × List Digest × Digest) (leaf : Nat) : T3.M (List Digest × List Digest × Digest) := do
  let ((root, values), carry) ← leafFn lay tree leaf (if leaf = sel then ds else []) state.2.2
  pure (state.1 ++ [root], (if leaf = sel then values else state.2.1), carry)
def buildTreeP (leafFn : LeafFn) (lay : Layer) (tree sel : Nat) (ds : List Nat) :
    T3.M (List (List Digest) × List Digest) := do
  let state ← (List.range (2 ^ height lay)).foldlM (btBodyP leafFn lay tree sel ds) ([], [], 0)
  let levels ← Seed.levelsBelowW lay.val tree (height lay) state.1
  pure (levels, state.2.1)
section loop
variable {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} {tree sel : Nat} {ds : List Nat} {sb : Nat}
  {s1 : MachineState} (hs : BtPre (cfFlag := cfFlag) sk cache lay tree sel ds sb s1)
include hs
-- (witness stack) removed: legacy reference-image lower tree (LeafW now covers CHAIN+32..112; no users).
end loop
theorem bt_path_loop (t0 : MachineState) (H hi : Nat) (hH : H ≤ 7) (hhi : hi < 2 ^ (H + 1)) :
    ∀ (n j : Nat), j + n = H → ∀ (t : MachineState) (ep : Nat), t.pc = pcOf 1202 →
      t.getReg .x13 = BitVec.ofNat 64 j → t.getReg .x15 = BitVec.ofNat 64 H →
      t.getReg .x19 = BitVec.ofNat 64 hi → t.getReg .x2 = BitVec.ofNat 64 LOW →
      t.getReg .x24 = BitVec.ofNat 64 ep → ep % 8 = 0 → ep + 16 * n ≤ LOW →
      (∀ A, LOW ≤ A → A < LOW + 4096 → t.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A)) →
      ∃ u k, Steps image t k k u ∧ k ≤ 12 * n + 1 ∧ u.pc = pcOf 1214 ∧
        (∀ i < n, DigAt u (ep + 16 * i) (memDig t0 (LOW + 16 * (hi / 2 ^ (j + i) ^^^ 1)))) ∧
        RegsExcept t u [.x6, .x7, .x13, .x24, .x28] ∧ Frame t u (fun A => ep ≤ A ∧ A < ep + 16 * n)
  | 0, j, hjn, t, ep, hpc, h13, h15, _, _, _, _, _, _ => by
    obtain ⟨u, st, upc, ur, uf⟩ := blk1202_spec t hpc j H (by omega) (by omega) h13 h15
    rw [if_neg (by omega)] at upc
    exact ⟨u, 1, st, by omega, upc, fun i hi => absurd hi (by omega), ur.mono (by simp),
      uf.mono (fun _ _ h => h.elim)⟩
  | n + 1, j, hjn, t, ep, hpc, h13, h15, h19, h2, h24, hep8, hepl, hheap => by
    obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk1202_spec t hpc j H (by omega) (by omega) h13 h15
    rw [if_pos (by omega)] at t1pc
    have hhi' : hi < 8192 := lt_of_lt_of_le hhi (by
      calc 2 ^ (H + 1) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ 8192 := by norm_num)
    obtain ⟨t2, st2, t2pc, t2x13, t2x24, m0, m8, t2r, t2f⟩ := blk1203_spec t1 t1pc j hi LOW ep (by omega)
      hhi' (by packed_sgo) (by packed_sgo) (by packed_sgo) hep8 (by rw [t1r.get (by simp)]; exact h13)
      (by rw [t1r.get (by simp)]; exact h19) (by rw [t1r.get (by simp)]; exact h2)
      (by rw [t1r.get (by simp)]; exact h24)
    have hx : hi / 2 ^ j ^^^ 1 < 8192 :=
      Nat.xor_lt_two_pow (n := 13) (lt_of_le_of_lt (Nat.div_le_self _ _) hhi') (by norm_num)
    have hx' : hi / 2 ^ j ^^^ 1 < 256 := by
      have h1 : hi / 2 ^ j < 2 ^ 8 := lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_lt_of_le hhi
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
      exact Nat.xor_lt_two_pow h1 (by norm_num)
    have f12 : Frame t t2 (fun A => A = ep ∨ A = ep + 8) := (t1f.trans t2f).mono (fun _ _ h => by
      rcases h with h | h; exact h.elim; exact h)
    obtain ⟨u, k, st, hk, upc, uem, ur, uf⟩ := bt_path_loop t0 H hi hH hhi n (j + 1) (by omega) t2 (ep + 16) t2pc
      t2x13 (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h15)
      (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h19) (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h2)
      t2x24 (by omega) (by omega) (fun A h1 h2' => (f12.get (by packed_sgo) (by packed_sgo)).trans (hheap A h1 h2'))
    refine ⟨u, 1 + (11 + k), st1.trans (st2.trans st), by omega, upc, fun i hi' => ?_,
      ((t1r.trans t2r).trans ur).mono (by simp), (f12.trans uf).mono (fun A _ h => by rcases h with h | h <;> omega)⟩
    rcases i with _ | i
    · simp only [Nat.mul_zero, Nat.add_zero]
      refine ⟨?_, ?_⟩
      · rw [uf.get (by packed_sgo) (by omega), m0, t1f.get (by packed_sgo) (fun h => h), hheap _ (by packed_sgo) (by packed_sgo)]
        exact (memDig_digAt t0 (LOW + 16 * (hi / 2 ^ j ^^^ 1))).1
      · rw [uf.get (by packed_sgo) (by omega), m8, t1f.get (by packed_sgo) (fun h => h), hheap _ (by packed_sgo) (by packed_sgo)]
        exact (memDig_digAt t0 (LOW + 16 * (hi / 2 ^ j ^^^ 1))).2
    · have := uem i (by omega)
      rw [show ep + 16 + 16 * i = ep + 16 * (i + 1) by ring, show j + 1 + i = j + (i + 1) by ring] at this
      exact this
def btLev (lay : Layer) (tree : Nat) : LevArgs := ⟨3, lay.val, tree, height lay, LOW, 1196⟩
def btAllRegs : List Reg :=
  [.x4, .x13] ++ btRegs ++ [.x6] ++ [.x1, .x6, .x21] ++ levRegs ++ [.x6, .x7, .x13, .x19, .x24] ++
    [.x6, .x7, .x13, .x24, .x28] ++ [.x6, .x7, .x30]
def BtAllW (lay : Layer) (tree sb : Nat) (A : Nat) : Prop :=
  BtW sb (height lay) A ∨ LevW (btLev lay tree) A ∨ (sb + 16 * 43 ≤ A ∧ A < sb + 16 * (43 + height lay)) ∨
    A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56
structure BtPost (sk : SecretKey) (cache : Bytes 131072) (lay : Layer) (tree sel sb ret : Nat) (s : MachineState)
    (r : List (List Digest) × List Digest) (u : MachineState) (cfFlag : Nat := 1) : Prop where
  pc : u.pc = pcOf ret
  vlen : r.2.length = 43
  vals : DigsAt u sb r.2
  path : DigsAt u (sb + 16 * 43) ((List.range (height lay)).map fun j => (r.1.getD j []).getD (sel / 2 ^ j ^^^ 1) 0)
  left : DigAt u ENC (topPair lay r.1).1
  right : DigAt u (ENC + 48) (topPair lay r.1).2
  base : Base (cfFlag := cfFlag) sk cache u
  regs : RegsExcept s u btAllRegs
  frame : Frame s u (BtAllW lay tree sb)
def btCost : Nat := 37400000
theorem sumTo_le_mul (f : Nat → Nat) (b : Nat) : ∀ n, (∀ j < n, f j ≤ b) → sumTo f n ≤ n * b
  | 0, _ => by simp [sumTo]
  | n + 1, h => by
    have := sumTo_le_mul f b n (fun j hj => h j (by omega))
    have := h n (by omega)
    simp only [sumTo]; rw [Nat.succ_mul]; omega
theorem sumTo_le_sumTo (f g : Nat → Nat) : ∀ n, (∀ j < n, f j ≤ g j) → sumTo f n ≤ sumTo g n
  | 0, _ => le_rfl
  | n + 1, h => by
    have := sumTo_le_sumTo f g n (fun j hj => h j (by omega))
    have := h n (by omega)
    simp only [sumTo]; omega
theorem heapH_sib {H sel i : Nat} (hi : i < H) :
    (2 ^ H + sel) / 2 ^ i ^^^ 1 = 2 ^ (H - i) + (sel / 2 ^ i ^^^ 1) := by
  have h2 : 2 ^ H = 2 ^ (H - i) * 2 ^ i := by rw [← pow_add, Nat.sub_add_cancel hi.le]
  rw [h2, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i), Nat.add_comm,
    two_pow_add_xor_one (by omega)]
theorem btLev_costs (lay : Layer) (hlay : lay ≠ 0) (tree : Nat) :
    Seed.levKB (btLev lay tree) ≤ Seed.levCB (btLev lay tree) ∧ Seed.levCB (btLev lay tree) ≤ 6609 := by
  rcases height_low hlay with h | h <;> simp only [Seed.levKB, Seed.levCB, btLev, h] <;> decide
-- (witness stack) removed: legacy reference-image lower tree (LeafW now covers CHAIN+32..112; no users).
end SigGolfCandidate.T3M.Sign.Packed
end

namespace SigGolfCandidate.T3M.Sign.SharedLowCode
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Sign
structure Code (im : Image) : Prop where
  at1173 : CodeAt im (pcOf 1173) seg_1173
  at1175 : CodeAt im (pcOf 1175) seg_1175
  at1178 : CodeAt im (pcOf 1178) seg_1178
  at1184 : CodeAt im (pcOf 1184) seg_1184
  at1187 : CodeAt im (pcOf 1187) seg_1187
  at1191 : CodeAt im (pcOf 1191) seg_1191
  at1193 : CodeAt im (pcOf 1193) seg_1193
  at1196 : CodeAt im (pcOf 1196) seg_1196
  at1202 : CodeAt im (pcOf 1202) seg_1202
  at1203 : CodeAt im (pcOf 1203) seg_1203
  at1195 : CodeAt im (pcOf 1195) Packed.w1195
  hpm : CodeAt im (pcOf 1542) SeedIndependent.hpmS
  entry : CodeAt im (pcOf 1214) Packed.BCBlocks.entryCode
  pair : CodeAt im (pcOf 10994) Packed.BCBlocks.pairCode
end SigGolfCandidate.T3M.Sign.SharedLowCode

namespace SigGolfCandidate.T3M.Sign.SharedLowTree
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
variable {im : Image} (hc : SharedLowCode.Code im)
include hc
theorem blk1173_spec (s : MachineState) (hpc : s.pc = pcOf 1173) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 1175 ∧ t.getReg .x4 = s.getReg .x1 ∧
      t.getReg .x13 = BitVec.ofNat 64 0 ∧ RegsExcept s t [.x4, .x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1173 hc.at1173 s hpc (by simp [blk_1173.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1173.res, E.eval]
  · simp [blk_1173.res, rv_simp]
  · simp [blk_1173.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1173.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1173.res, rv_simp]
theorem blk1175_spec (s : MachineState) (hpc : s.pc = pcOf 1175) (l h : Nat) (hl : l < 2 ^ 63) (hh : h ≤ 12)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h15 : s.getReg .x15 = BitVec.ofNat 64 h) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if l < 2 ^ h then pcOf 1178 else pcOf 1193) ∧
      t.getReg .x6 = BitVec.ofNat 64 (2 ^ h) ∧ RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hp : 2 ^ h ≤ 4096 := by
    calc 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
      _ = 4096 := by norm_num
  have e : (1#64 : Word) <<< ((BitVec.ofNat 64 h).toNat % 64) = BitVec.ofNat 64 (2 ^ h) := by
    rw [toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega), show (1#64 : Word) = BitVec.ofNat 64 1 from rfl,
      ofNat_shl, Nat.one_mul]
  refine ⟨_, symRun_sound blk_1175 hc.at1175 s hpc (by simp [blk_1175.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_1175.res, E.eval, CmpOp.eval, BinOp.eval, h13, h15, e,
      ofNat_slt l (2 ^ h) hl (by omega)]
    by_cases hc : l < 2 ^ h <;> simp [hc]
  · simp only [Result.toState_getReg, blk_1175.res, rv_simp, BinOp.eval, h15, e]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1175.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1175.res, rv_simp]
theorem blk1178_spec (s : MachineState) (hpc : s.pc = pcOf 1178) (l sel : Nat) (hl : l < 2 ^ 64)
    (hsel : sel < 2 ^ 64) (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h14 : s.getReg .x14 = BitVec.ofNat 64 sel) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = (if l = sel then pcOf 1184 else pcOf 1187) ∧
      t.getReg .x18 = BitVec.ofNat 64 l ∧ t.getReg .x22 = BitVec.ofNat 64 ZDIG ∧
      t.getReg .x23 = BitVec.ofNat 64 DUMMY ∧ RegsExcept s t [.x18, .x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1178 hc.at1178 s hpc (by simp [blk_1178.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_1178.res, E.eval, CmpOp.eval, h13, h14]
    by_cases hc : l = sel
    · subst hc; simp
    · rw [if_neg hc]
      have : BitVec.ofNat 64 l ≠ BitVec.ofNat 64 sel := fun he => hc ((ofNat_inj hl hsel).mp he)
      simp [this]
  · simp only [Result.toState_getReg, blk_1178.res]; t3n [h13]
  · simp [blk_1178.res, rv_simp]
  · simp [blk_1178.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1178.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1178.res, rv_simp]
theorem blk1184_spec (s : MachineState) (hpc : s.pc = pcOf 1184) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 1187 ∧ t.getReg .x22 = BitVec.ofNat 64 DIGITS ∧
      t.getReg .x23 = s.getReg .x16 ∧ RegsExcept s t [.x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1184 hc.at1184 s hpc (by simp [blk_1184.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1184.res, E.eval]
  · simp [blk_1184.res, rv_simp]
  · simp [blk_1184.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1184.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1184.res, rv_simp]
theorem blk1187_spec (s : MachineState) (hpc : s.pc = pcOf 1187) (l h ar : Nat) (hl : l < 2 ^ h)
    (hh : h ≤ 12) (har : ar + 16 * 8192 < 2 ^ 64)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h6 : s.getReg .x6 = BitVec.ofNat 64 (2 ^ h))
    (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf (1013 + 27) ∧ t.getReg .x1 = pcOf 1191 ∧
      t.getReg .x25 = BitVec.ofNat 64 (ar + 16 * (2 ^ h + l)) ∧
      RegsExcept s t [.x1, .x7, .x25] ∧ Frame s t (fun _ => False) := by
  have hp : 2 ^ h ≤ 4096 := by
    calc 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
      _ = 4096 := by norm_num
  refine ⟨_, symRun_sound blk_1187 hc.at1187 s hpc (by simp [blk_1187.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1187.res, E.eval]
  · simp [blk_1187.res, rv_simp]
  · simp only [Result.toState_getReg, blk_1187.res]; t3n [h13, h6, h2]; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1187.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1187.res, rv_simp]
theorem blk1191_spec (s : MachineState) (hpc : s.pc = pcOf 1191) (l : Nat)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 1175 ∧ t.getReg .x13 = BitVec.ofNat 64 (l + 1) ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1191 hc.at1191 s hpc (by simp [blk_1191.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [blk_1191.res, E.eval]
  · simp only [Result.toState_getReg, blk_1191.res]; t3n [h13]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1191.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1191.res, rv_simp]
theorem blk1193_spec (s : MachineState) (hpc : s.pc = pcOf 1193) (lay tree : Nat) (hlay1 : 1 ≤ lay)
    (hlay : lay < 256) (htree : tree < 2 ^ 32)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf (1013 + 113) ∧ t.getReg .x1 = pcOf 1196 ∧
      t.getReg .x21 = BitVec.ofNat 64 (Keygen.nodeLo lay tree) ∧
      RegsExcept s t [.x1, .x6, .x21] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 1542 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound blk_1193 hc.at1193 s hpc (by simp [blk_1193.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [blk_1193.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  obtain ⟨t2, s2, p2, x21, r2, f2⟩ : ∃ t, Steps im t1 9 9 t ∧ t.pc = pcOf 1195 ∧
      t.getReg .x21 = BitVec.ofNat 64 (Keygen.nodeLo lay tree) ∧ RegsExcept t1 t [.x6, .x21] ∧
      Frame t1 t (fun _ => False) := by
    have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay := by rw [r1.get (by decide), h8]
    have g9 : t1.getReg .x9 = BitVec.ofNat 64 tree := by rw [r1.get (by decide), h9]
    refine ⟨_, symRun_sound SeedIndependent.blkS_hpm hc.hpm t1 p1
      (by simp [SeedIndependent.blkS_hpm.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_hpm.res, E.eval]
    · simp only [Result.toState_getReg, SeedIndependent.blkS_hpm.res]
      t3n [g8, g9]
      unfold Keygen.nodeLo
      rw [if_neg (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      have hl : BitVec.ofNat 64 ((lay + 18446744073709551615) * 281474976710656) =
          BitVec.ofNat 64 ((lay - 1) * 281474976710656) := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
      rw [hl, show (513#64) = BitVec.ofNat 64 513 from rfl,
        ofNat_or_disjoint 513 (tree * 65536) 16 (by decide) (by omega),
        ofNat_or_disjoint' _ ((lay - 1) * 281474976710656) 48 (by omega) (by omega),
        show (13907115649320091648#64) = BitVec.ofNat 64 (193 * 2 ^ 56) from rfl,
        ofNat_or_disjoint' _ (193 * 2 ^ 56) 56 (by omega) (by omega)]
      unfold T3.hyperWord
      congr 1
      rw [Nat.mod_eq_of_lt htree, Nat.mod_eq_of_lt (by omega : lay - 1 < 256)]
      omega
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_hpm.res, rv_simp] <;> rfl
    · intro A _ _; simp [SeedIndependent.blkS_hpm.res, rv_simp]
  obtain ⟨t3, s3, p3, x1, r3, f3⟩ : ∃ t, Steps im t2 1 1 t ∧ t.pc = pcOf (1013 + 113) ∧
      t.getReg .x1 = pcOf 1196 ∧ RegsExcept t2 t [.x1] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound blk_w1195 hc.at1195 t2 p2 (by simp [blk_w1195.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [blk_w1195.res, E.eval]
    · simp [blk_w1195.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [blk_w1195.res, rv_simp] <;> rfl
    · intro A _ _; simp [blk_w1195.res, rv_simp]
  refine ⟨t3, (s1.trans s2).trans s3, p3, x1, by rw [r3.get (by decide), x21],
    ((r1.trans r2).trans r3).mono (by decide), ((f1.trans f2).trans f3).mono (fun A _ h => by simp_all)⟩
theorem blk1196_spec (s : MachineState) (hpc : s.pc = pcOf 1196) (h sel sb n : Nat) (hh : h ≤ 12)
    (hsel : sel < 4096) (hsb : sb + 16 * n < 2 ^ 64)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 h) (h14 : s.getReg .x14 = BitVec.ofNat 64 sel)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 sb) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 1202 ∧ t.getReg .x13 = BitVec.ofNat 64 0 ∧
      t.getReg .x19 = BitVec.ofNat 64 (2 ^ h + sel) ∧ t.getReg .x24 = BitVec.ofNat 64 (sb + 16 * n) ∧
      RegsExcept s t [.x6, .x7, .x13, .x19, .x24] ∧ Frame s t (fun _ => False) := by
  have hp : 2 ^ h ≤ 4096 := by
    calc 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
      _ = 4096 := by norm_num
  have e : (1#64 : Word) <<< ((BitVec.ofNat 64 h).toNat % 64) = BitVec.ofNat 64 (2 ^ h) := by
    rw [toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega), show (1#64 : Word) = BitVec.ofNat 64 1 from rfl,
      ofNat_shl, Nat.one_mul]
  refine ⟨_, symRun_sound blk_1196 hc.at1196 s hpc (by simp [blk_1196.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1196.res, E.eval]
  · simp [blk_1196.res, rv_simp]
  · simp only [Result.toState_getReg, blk_1196.res, rv_simp, BinOp.eval, h15, h14, e, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, blk_1196.res]; t3n [h16, h26]; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1196.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1196.res, rv_simp]
theorem blk1202_spec (s : MachineState) (hpc : s.pc = pcOf 1202) (l h : Nat) (hl : l < 2 ^ 63) (hh : h < 2 ^ 63)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h15 : s.getReg .x15 = BitVec.ofNat 64 h) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = (if l < h then pcOf 1203 else pcOf 1214) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1202 hc.at1202 s hpc (by simp [blk_1202.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_1202.res, E.eval, CmpOp.eval, h13, h15, ofNat_slt l h hl hh]
    by_cases hc : l < h <;> simp [hc]
  · intro r hr; cases r <;> simp_all [blk_1202.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1202.res, rv_simp]
theorem blk1203_spec (s : MachineState) (hpc : s.pc = pcOf 1203) (l hi ar ep : Nat) (hl : l < 64)
    (hhi : hi < 8192) (har : ar + 16 * 8192 ≤ 2 ^ 24) (har8 : ar % 8 = 0) (hep : ep + 16 ≤ 2 ^ 24)
    (hep8 : ep % 8 = 0)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h19 : s.getReg .x19 = BitVec.ofNat 64 hi)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) (h24 : s.getReg .x24 = BitVec.ofNat 64 ep) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf 1202 ∧ t.getReg .x13 = BitVec.ofNat 64 (l + 1) ∧
      t.getReg .x24 = BitVec.ofNat 64 (ep + 16) ∧
      t.getMem (BitVec.ofNat 64 ep) = s.getMem (BitVec.ofNat 64 (ar + 16 * (hi / 2 ^ l ^^^ 1))) ∧
      t.getMem (BitVec.ofNat 64 (ep + 8)) = s.getMem (BitVec.ofNat 64 (ar + 16 * (hi / 2 ^ l ^^^ 1) + 8)) ∧
      RegsExcept s t [.x6, .x7, .x13, .x24, .x28] ∧ Frame s t (fun A => A = ep ∨ A = ep + 8) := by
  have hd : hi / 2 ^ l < 8192 := lt_of_le_of_lt (Nat.div_le_self _ _) hhi
  have hx : hi / 2 ^ l ^^^ 1 < 8192 := Nat.xor_lt_two_pow (n := 13) hd (by norm_num)
  have e1 : BitVec.ofNat 64 hi >>> ((BitVec.ofNat 64 l).toNat % 64) ^^^ 1#64 =
      BitVec.ofNat 64 (hi / 2 ^ l ^^^ 1) := by
    rw [toNat_mod64 l hl, ofNat_shr hi l (by omega), ofNat_xor1 _ (by omega)]
  have hobl : Oblig.all s blk_1203.res.st.obl := by
    simp only [blk_1203.res]
    simp only [rv_simp, h13, h19, h2, h24, e1]
    t3n []
    omega
  refine ⟨_, symRun_sound blk_1203 hc.at1203 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1203.res, E.eval]
  · simp only [Result.toState_getReg, blk_1203.res]; t3n [h13]
  · simp only [Result.toState_getReg, blk_1203.res]; t3n [h24]
  · simp only [Result.toState_getMem, blk_1203.res]
    simp only [rv_simp, h13, h19, h2, h24, e1]
    t3n []
    repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])
    congr 2; omega
  · simp only [Result.toState_getMem, blk_1203.res]
    simp only [rv_simp, h13, h19, h2, h24, e1]
    t3n []
    repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])
    congr 2; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1203.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, blk_1203.res]
    t3n [h24]
    rw [if_neg (by omega), if_neg (by omega)]
namespace BCBlocks
open Packed.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem pair_spec (s : MachineState) (hpc : s.pc = pcOf 10994) (ar ret : Nat)
    (har : ar + 64 ≤ 2 ^ 24) (har8 : ar % 8 = 0)
    (hsep : ENC + 64 ≤ ar ∨ ar + 64 ≤ ENC)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) (h4 : s.getReg .x4 = pcOf ret)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 ENC) :
    ∃ t, Steps im s 9 9 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 (ar + 32)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (ar + 40)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 48)) = s.getMem (BitVec.ofNat 64 (ar + 48)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 56)) = s.getMem (BitVec.ofNat 64 (ar + 56)) ∧
      RegsExcept s t [.x6, .x7] ∧
      Frame s t (fun A => A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
  have hobl : Oblig.all s pairBlock.res.st.obl := by
    simp only [pairBlock.res]
    t3n [h2, h30, ENC]
    simp only [ENC] at hsep
    simp only [and_true]
    omega
  refine ⟨_, symRun_sound pairBlock hc.pair s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pairBlock.res, rv_simp, h4, pcOf_and_max]
  · simp only [Result.toState_getMem, pairBlock.res, ENC]
    t3n [h2, h30, ENC]
  · simp only [Result.toState_getMem, pairBlock.res, ENC]
    t3n [h2, h30, ENC]
  · simp only [Result.toState_getMem, pairBlock.res, ENC]
    t3n [h2, h30, ENC]
  · simp only [Result.toState_getMem, pairBlock.res, ENC]
    t3n [h2, h30, ENC]
  · intro r hr; simp at hr; cases r <;> simp_all [pairBlock.res, rv_simp]; rfl
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, pairBlock.res]
    t3n [h30, ENC]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem entry_spec (s : MachineState) (hpc : s.pc = pcOf 1214) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 10994 ∧
      t.getReg .x30 = BitVec.ofNat 64 ENC ∧ RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound entryBlock hc.entry s hpc (by simp [entryBlock.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, entryBlock.res, rv_simp, pcOf]
  · simp [Result.toState_getReg, entryBlock.res, rv_simp, ENC]
  · intro r hr; simp at hr; cases r <;> simp_all [entryBlock.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, entryBlock.res, rv_simp]
theorem blk1214_pair_spec (s : MachineState) (hpc : s.pc = pcOf 1214) (ar ret : Nat)
    (har : ar + 64 ≤ 2 ^ 24) (har8 : ar % 8 = 0)
    (hsep : ENC + 64 ≤ ar ∨ ar + 64 ≤ ENC)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) (h4 : s.getReg .x4 = pcOf ret) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 (ar + 32)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (ar + 40)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 48)) = s.getMem (BitVec.ofNat 64 (ar + 48)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 56)) = s.getMem (BitVec.ofNat 64 (ar + 56)) ∧
      RegsExcept s t [.x6, .x7, .x30] ∧
      Frame s t (fun A => A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
  obtain ⟨u, su, upc, u30, ur, uf⟩ := entry_spec hc s hpc
  obtain ⟨t, ut, tpc, m0, m8, m48, m56, tr, tf⟩ := pair_spec hc u upc ar ret har har8 hsep
    (by rw [ur.get (by simp), h2]) (by rw [ur.get (by simp), h4]) u30
  refine ⟨t, su.trans ut, tpc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m0, uf.get (by omega) (by simp)]
  · rw [m8, uf.get (by omega) (by simp)]
  · rw [m48, uf.get (by omega) (by simp)]
  · rw [m56, uf.get (by omega) (by simp)]
  · exact (ur.trans tr).mono (by decide)
  · exact (uf.trans tf).mono (by intro A hA h; simpa using h)
end BCBlocks

end SigGolfCandidate.T3M.Sign.SharedLowTree

namespace SigGolfCandidate.T3M.Sign.SharedLowTree
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest height chainCount)
open Packed
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Pairing stage 1: also the chain scratch a G chain writes outside `LeafW` (`CHAIN+32 .. CHAIN+48`,
`CHAIN+80 .. CHAIN+112`; the F pads `CHAIN+32/40` are zero again after each lower leaf, `Inv.z`). -/
def BScr (X : Nat) : Prop := (0x50000≤X ∧ X<0x76000) ∨ (0x201C0≤X ∧ X<0x201D0) ∨ (0x201F0≤X ∧ X<0x20210)
macro "shared_tree_sgo" : tactic =>
  `(tactic| ((try simp only [BScr, PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK, MOUT, ZDIG, DUMMY, TOP, MACBLK,
    REGION, MSG, SK, SIG, CACHE, NONCE, RHOOUT, DIG, NBUF, ENC, EOUT, FLEAF, LFOUT, FOREST, FOUT, MACOUT, TAG,
    DIGITS, SEL, IDXV, LOW, FTS, SEC, false_or, or_false] at *) <;> omega))
def BtW (sb H : Nat) (X : Nat) : Prop :=
  X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ X = CHAIN + 16 ∨ X = CHAIN + 24 ∨
    (CHAIN + 32 ≤ X ∧ X < CHAIN + 112) ∨ (LEAFPK ≤ X ∧ X < LEAFPK + 16 * 45) ∨ (LOUT ≤ X ∧ X < LOUT + 32) ∨
    (DUMMY ≤ X ∧ X < DUMMY + 16 * 43) ∨ (sb ≤ X ∧ X < sb + 16 * 43) ∨
    (LOW + 16 * 2 ^ H ≤ X ∧ X < LOW + 16 * 2 ^ (H + 1)) ∨ BScr X

def TreeWrites (lay : Layer) (X : Nat) : Prop := X<0x66000 ∨
  (0x6e000+8192*lay.val≤X ∧ X<0x6e000+8192*(lay.val+1))

section leafPre
variable {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} {tree sel : Nat} {ds : List Nat} {sb : Nat}
  {s1 : MachineState} (hs : BtPre (cfFlag := cfFlag) sk cache lay tree sel ds sb s1)
include hs
theorem bt_leafPre {l : Nat} (hl : l < 2 ^ height lay) {t : MachineState}
    (hr : RegsExcept s1 t (btRegs ++ [.x1, .x4, .x6, .x7, .x18, .x22, .x23, .x25])) (hf : Frame s1 t (BtW sb (height lay)))
    (h1 : t.getReg .x1 = pcOf 1191) (h18 : t.getReg .x18 = BitVec.ofNat 64 l)
    (h22 : t.getReg .x22 = BitVec.ofNat 64 (if l = sel then DIGITS else ZDIG))
    (h23 : t.getReg .x23 = BitVec.ofNat 64 (if l = sel then sb else DUMMY))
    (h25 : t.getReg .x25 = BitVec.ofNat 64 (LOW + 16 * (2 ^ height lay + l))) :
    LeafPreS sk t (btLeaf lay tree sel ds sb l) := by
  have hlay := hs.hlay
  have hn : (btLeaf lay tree sel ds sb l).n = 43 := chainCount_low hlay
  have hH := height_low hlay
  have hHp : 2 ^ height lay ≤ 128 := by rcases hH with h | h <;> rw [h] <;> norm_num
  have hsb := hs.hsb
  have g : ∀ r, r ∉ btRegs ++ [.x1, .x4, .x6, .x7, .x18, .x22, .x23, .x25] → t.getReg r = s1.getReg r :=
    fun r hr' => hr.get hr'
  have m : ∀ X, X < 2 ^ 64 → ¬ BtW sb (height lay) X → t.getMem (BitVec.ofNat 64 X) = s1.getMem (BitVec.ofNat 64 X) :=
    fun X hX hn' => hf.get hX hn'
  have hz : ∀ X, X < 2 ^ 64 → NeverW X → (X < 0x201C0 ∨ 0x20210 ≤ X) → t.getMem (BitVec.ofNat 64 X) = 0 :=
    fun X hX hnw hc =>
    (m X hX (by unfold NeverW at hnw; unfold BtW; rcases hH with h | h <;> rw [h] <;> shared_tree_sgo)).trans
      (hs.base.zero X hX hnw)
  refine
    { x1 := h1
      x5 := by rw [g _ (by decide), hs.base.x5]
      x8 := by rw [g _ (by decide), hs.x8]; rfl
      x9 := by rw [g _ (by decide), hs.x9]; rfl
      x18 := h18
      x22 := h22
      x23 := h23
      x25 := h25
      x26 := by rw [g _ (by decide), hs.x26, hn]
      x27 := by rw [g _ (by decide), hs.x27]; show _ = BitVec.ofNat 64 (n4 lay); rw [n4_low hlay]
      x31 := by rw [g _ (by decide), hs.x31]; rfl
      htree := hs.htree
      hleaf := by show l < 2 ^ 32; omega
      hroute := hs.hroute l hl
      hleafHeight := hl
      hsteps := fun i _ => by change T3.maxDigit lay i ≤ 8; simp [T3.maxDigit, hlay]
      p0 := by rw [m _ (by decide) (by unfold BtW; shared_tree_sgo), hs.base.p0]
      p8 := by rw [m _ (by decide) (by unfold BtW; shared_tree_sgo), hs.base.p8]
      p32 := by rw [m _ (by decide) (by unfold BtW; shared_tree_sgo), hs.base.p32]
      p40 := by rw [m _ (by decide) (by unfold BtW; shared_tree_sgo), hs.base.p40]
      p48 := by rw [m _ (by decide) (by unfold BtW; shared_tree_sgo), hs.base.p48]
      p56 := by rw [m _ (by decide) (by unfold BtW; shared_tree_sgo), hs.base.p56]
      z0 := hz _ (by decide) (by unfold NeverW; simp) (by decide)
      z8 := hz _ (by decide) (by unfold NeverW; simp) (by decide)
      hsl := fun _ => hlay
      hdig := fun i hi => by
        rw [hn] at hi
        show t.getByte (BitVec.ofNat 64 ((if l = sel then DIGITS else ZDIG) + i)) =
          BitVec.ofNat 8 ((if l = sel then ds else []).getD i 0)
        by_cases hls : l = sel
        · simp only [hls, if_true]
          rw [hf.getByte (by shared_tree_sgo) (by unfold BtW; rcases hH with h | h <;> rw [h] <;> shared_tree_sgo)]
          exact hs.digits i hi
        · simp only [hls, if_false, List.getD_nil]
          rw [hf.getByte (by shared_tree_sgo) (by unfold BtW; rcases hH with h | h <;> rw [h] <;> shared_tree_sgo),
            getByte_eq_word s1 _ (by shared_tree_sgo), hs.base.zero _ (by shared_tree_sgo) (by unfold NeverW; shared_tree_sgo), extractByte_zero']
          rfl
      hdigb := fun i hi => by
        rw [hn] at hi
        show (if l = sel then ds else []).getD i 0 < 256 ∧
          (false = false → (if l = sel then ds else []).getD i 0 ≤ T3.maxDigit lay i)
        have hw : T3.maxDigit lay i = 7 := by simp [T3.maxDigit, hlay]
        rw [hw]
        by_cases hls : l = sel
        · simp only [hls, if_true]; have := hs.hdb i hi; omega
        · simp [hls]
      hdigp := by show (if l = sel then DIGITS else ZDIG) + (btLeaf lay tree sel ds sb l).n ≤ 2 ^ 24
                  rw [hn]; split_ifs <;> shared_tree_sgo
      hdigC := by
        show (if l = sel then DIGITS else ZDIG) + (btLeaf lay tree sel ds sb l).n ≤ 0x201C0 ∨
          0x20210 ≤ (if l = sel then DIGITS else ZDIG)
        right; split_ifs <;> decide
      hdigW := fun i hi => by
        rw [hn] at hi
        show ¬ LeafW (btLeaf lay tree sel ds sb l) (((if l = sel then DIGITS else ZDIG) + i) / 8 * 8)
        unfold LeafW
        show ¬ (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ ((if (btLeaf lay tree sel ds sb l).lay = 0 then LEAFPK + 16 else LEAFPK) ≤ _ ∧ _ < LEAFPK + 16 * ((btLeaf lay tree sel ds sb l).n + 2)) ∨ _ ∨
          ((if l = sel then sb else DUMMY) ≤ _ ∧ _ < (if l = sel then sb else DUMMY) + 16 * (btLeaf lay tree sel ds sb l).n) ∨
          (LOW + 16 * (2 ^ height lay + l) ≤ _ ∧ _ < LOW + 16 * (2 ^ height lay + l) + 16))
        rw [hn]
        split_ifs <;> shared_tree_sgo
      hv8 := by show (if l = sel then sb else DUMMY) % 8 = 0; split_ifs; exact hs.hsb8; decide
      hv := by
        show (if l = sel then sb else DUMMY) + 16 * (btLeaf lay tree sel ds sb l).n ≤ 2 ^ 24
        rw [hn]; split_ifs <;> shared_tree_sgo
      hvs := by
        show (if l = sel then sb else DUMMY) + 16 * (btLeaf lay tree sel ds sb l).n ≤ PRIV ∨
          LEAFPK + 960 ≤ (if l = sel then sb else DUMMY)
        rw [hn]; split_ifs
        · left; shared_tree_sgo
        · right; decide
      hd8 := fun _ => by show (LOW + 16 * (2 ^ height lay + l)) % 8 = 0; shared_tree_sgo
      hd := by show LOW + 16 * (2 ^ height lay + l) + 16 ≤ 2 ^ 24; shared_tree_sgo
      hds := Or.inr (Or.inl (by show LEAFPK + 960 ≤ LOW + 16 * (2 ^ height lay + l); shared_tree_sgo))
      hdv := by
        show LOW + 16 * (2 ^ height lay + l) + 16 ≤ (if l = sel then sb else DUMMY) ∨
          (if l = sel then sb else DUMMY) + 16 * (btLeaf lay tree sel ds sb l).n ≤ LOW + 16 * (2 ^ height lay + l)
        rw [hn]; right; split_ifs <;> shared_tree_sgo }
end leafPre
end SigGolfCandidate.T3M.Sign.SharedLowTree

namespace SigGolfCandidate.T3M.Sign.SharedLowCode
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : Code Images.signImage := by
  constructor
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
end SigGolfCandidate.T3M.Sign.SharedLowCode
