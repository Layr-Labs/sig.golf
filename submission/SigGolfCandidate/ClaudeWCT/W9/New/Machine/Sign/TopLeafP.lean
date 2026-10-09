import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.PackedHelper
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.GfMul
import SigGolfCandidate.T3M.Sign.SeedLeafPhases
import SigGolfCandidate.T3M.Sign.PackedBoundaryEntry

/-!
# Campaign T8D (TOP2 NF17): the top-leaf seed routines of the sign image

* PRE (1554): `bne s0,zero,1053; jal ra,COEFGEN; j 1053` (reached from the leaf prologue's `j 1554`).
* COEFGEN (1559..1595): the 12 `privatePair 0 0 0 (12 leaf + j) 0` queries of `SigGolfCandidate.T3.topCoefs leaf`, both halves copied
  to `TCOEF + 32 j` (coefficient `k` at `TCOEF + 16 k`); `tp/s8/a4` saved at `TSAVE`; `s3 := 0`; returns via `ra`.
* TOPSEED (1557): `jal ra,HORN; j 1084` (reached through `20746 beq s0 → 20769 j 1557` once per top chain).
* HORN (1597..1652): `familyEval coefs (s3 + 1)` over the 24 coefficients into `CHAIN + 48`, `a3..a6/s8/tp` saved at
  `TSAVE + 32`. Horner loop `HK` (1610): `a0` walks down the coefficients, `(a4, a5)` hold the accumulator; bit loop
  `HB` (1616..1629): `(a4, a5, a2)` hold `acc * 2^k`, `(a6, s8, tp)` hold `clmulSmall acc d k`, `t4 = d >> k`;
  `HF` (1630..1641) folds once with 0x87 and adds the coefficient.
-/

namespace ClaudeWCT.W9.Machine.Sign.TopSeed
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN)
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT.W9.Machine.Sign.Gf ClaudeWCT.Arith
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Top coefficient buffer (24 x 16 bytes). -/
abbrev TCOEF : Nat := 0x61000
/-- Register save area of COEFGEN (`+0..+24`) and HORN (`+32..+80`). -/
abbrev TSAVE : Nat := 0x60000
/-- The scratch the top seed routines write outside the leaf write set. -/
def TScr (A : Nat) : Prop := TSAVE ≤ A ∧ A < TCOEF + 384

/-! ### Code -/

def cgHead : List (BitVec 32) := [0x60f37,0x4f3023,0x18f3423,0xef3823,0x61c37,0xc00f13,0x3e90733,0x2071713,0x176713,0xe93]
def cgCall : List (BitVec 32) := [0x20537,0xe53823,0x53c23,0x4000593,0x4050613,0x73]
def cgCopy : List (BitVec 32) := [0x4053203,0x4c3023,0x4853203,0x4c3423,0x5053203,0x4c3823,0x5853203,0x4c3c23,0x20c0c13,0x100f13,0x20f1f13,0x1e70733,0x1e8e93,0xc00f13,0xfbee98e3]
def cgExit : List (BitVec 32) := [0x60f37,0xf3203,0x8f3c03,0x10f3703,0x993,0x8067]
def hnEntry : List (BitVec 32) := [0x60f37,0x2df3023,0x2ef3423,0x2ff3823,0x30f3c23,0x58f3023,0x44f3423,0x198693,0x713,0x793,0x61537,0x18050513,0x615b7]
def hnHK : List (BitVec 32) := [0xff050513,0x813,0xc13,0x213,0x613,0x68e93]
def hnHB : List (BitVec 32) := [0x1eff13,0xf0863]
def hnX : List (BitVec 32) := [0xe84833,0xfc4c33,0xc24233]
def hnHS : List (BitVec 32) := [0x3f7df13,0x161613,0x1e66633,0x3f75f13,0x179793,0x1e7e7b3,0x171713,0x1ede93,0xfc0e96e3]
def hnHF : List (BitVec 32) := [0x121f13,0x1e84833,0x221f13,0x1e84833,0x721f13,0x1e84833,0x484833,0x53f03,0x1e84733,0x853f03,0x1ec47b3,0xf8b512e3]
def hnExit : List (BitVec 32) := [0x20f37,0x1cef3823,0x1cff3c23,0x60f37,0x20f3683,0x28f3703,0x30f3783,0x38f3803,0x40f3c03,0x48f3203,0x8067]

theorem codeAt_1554 : CodeAt Sign.image (pcOf 1554) [0x820416e3] :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1555 : CodeAt Sign.image (pcOf 1555) [0x10000ef] := codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1556 : CodeAt Sign.image (pcOf 1556) [0x825ff06f] :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1557 : CodeAt Sign.image (pcOf 1557) [0xa0000ef] := codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1558 : CodeAt Sign.image (pcOf 1558) [0x899ff06f] :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_cgHead : CodeAt Sign.image (pcOf 1559) cgHead := codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_cgCall : CodeAt Sign.image (pcOf 1569) cgCall := codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_cgCopy : CodeAt Sign.image (pcOf 1575) cgCopy := codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_cgExit : CodeAt Sign.image (pcOf 1590) cgExit := codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_hnEntry : CodeAt Sign.image (pcOf 1597) hnEntry :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_hnHK : CodeAt Sign.image (pcOf 1610) hnHK := codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_hnHB : CodeAt Sign.image (pcOf 1616) hnHB := codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_hnX : CodeAt Sign.image (pcOf 1618) hnX := codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_hnHS : CodeAt Sign.image (pcOf 1621) hnHS := codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_hnHF : CodeAt Sign.image (pcOf 1630) hnHF := codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_hnExit : CodeAt Sign.image (pcOf 1642) hnExit :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)

sym_block bPre := symRun { noAlias := true } [0x820416e3] (pcOf 1554) 100
sym_block bJal := symRun { noAlias := true } [0x10000ef] (pcOf 1555) 100
sym_block bJ1053 := symRun { noAlias := true } [0x825ff06f] (pcOf 1556) 100
sym_block bTsJal := symRun { noAlias := true } [0xa0000ef] (pcOf 1557) 100
sym_block bTsJ := symRun { noAlias := true } [0x899ff06f] (pcOf 1558) 100
sym_block bCgHead := symRun { noAlias := true } cgHead (pcOf 1559) 100
sym_block bCgCall := symRun { noAlias := true } cgCall (pcOf 1569) 100
sym_block bCgCopy := symRun { noAlias := true } cgCopy (pcOf 1575) 100
sym_block bCgExit := symRun { noAlias := true } cgExit (pcOf 1590) 100
sym_block bEntry := symRun { noAlias := true } hnEntry (pcOf 1597) 100
sym_block bHK := symRun { noAlias := true } hnHK (pcOf 1610) 100
sym_block bHB := symRun { noAlias := true } hnHB (pcOf 1616) 100
sym_block bX := symRun { noAlias := true } hnX (pcOf 1618) 100
sym_block bHS := symRun { noAlias := true } hnHS (pcOf 1621) 100
sym_block bHF := symRun { noAlias := true } hnHF (pcOf 1630) 100
sym_block bExit := symRun { noAlias := true } hnExit (pcOf 1642) 100

/-! ### HORN pieces -/

/-- The registers HORN's entry changes (the saved ones are restored at the exit). -/
def entryRegs : List Reg := [.x10, .x11, .x13, .x14, .x15, .x30]
def SaveW (A : Nat) : Prop := TSAVE + 32 ≤ A ∧ A < TSAVE + 80

theorem entry_spec (s : MachineState) (hpc : s.pc = pcOf 1597) (i : Nat) (hi : i + 1 < 2 ^ 64)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps Sign.image s 13 13 t ∧ t.pc = pcOf 1610 ∧ t.getReg .x13 = BitVec.ofNat 64 (i + 1) ∧
      t.getReg .x14 = 0 ∧ t.getReg .x15 = 0 ∧ t.getReg .x10 = BitVec.ofNat 64 (TCOEF + 16 * 24) ∧
      t.getReg .x11 = BitVec.ofNat 64 TCOEF ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 32)) = s.getReg .x13 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 40)) = s.getReg .x14 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 48)) = s.getReg .x15 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 56)) = s.getReg .x16 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 64)) = s.getReg .x24 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 72)) = s.getReg .x4 ∧
      RegsExcept s t entryRegs ∧ Frame s t SaveW := by
  refine ⟨_, symRun_sound bEntry codeAt_hnEntry s hpc (by simp [bEntry.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bEntry.res, E.eval]
  · simp only [Result.toState_getReg, bEntry.res]; t3n [h19]
  · simp [bEntry.res, rv_simp]
  · simp [bEntry.res, rv_simp]
  · simp only [Result.toState_getReg, bEntry.res]; t3n []
  · simp only [Result.toState_getReg, bEntry.res]; t3n []
  · simp only [Result.toState_getMem, bEntry.res]; t3n [TSAVE]
  · simp only [Result.toState_getMem, bEntry.res]; t3n [TSAVE]
  · simp only [Result.toState_getMem, bEntry.res]; t3n [TSAVE]
  · simp only [Result.toState_getMem, bEntry.res]; t3n [TSAVE]
  · simp only [Result.toState_getMem, bEntry.res]; t3n [TSAVE]
  · simp only [Result.toState_getMem, bEntry.res]; t3n [TSAVE]
  · intro r hr; simp [entryRegs] at hr; cases r <;> simp_all [bEntry.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [SaveW, TSAVE] at hn
    simp only [Result.toState_getMem, bEntry.res]
    t3n []
    split_ifs <;> first | rfl | omega

/-- Registers the Horner loop changes. -/
def loopRegs : List Reg := [.x4, .x10, .x12, .x14, .x15, .x16, .x24, .x29, .x30]

theorem hk_spec (s : MachineState) (hpc : s.pc = pcOf 1610) :
    ∃ t, Steps Sign.image s 6 6 t ∧ t.pc = pcOf 1616 ∧
      t.getReg .x10 = s.getReg .x10 - 16#64 ∧ t.getReg .x16 = 0 ∧ t.getReg .x24 = 0 ∧
      t.getReg .x4 = 0 ∧ t.getReg .x12 = 0 ∧ t.getReg .x29 = s.getReg .x13 ∧
      RegsExcept s t [.x4, .x10, .x12, .x16, .x24, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bHK codeAt_hnHK s hpc (by simp [bHK.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bHK.res, E.eval]
  · simp only [Result.toState_getReg, bHK.res]; t3n []
  · simp [bHK.res, rv_simp]
  · simp [bHK.res, rv_simp]
  · simp [bHK.res, rv_simp]
  · simp [bHK.res, rv_simp]
  · simp [bHK.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bHK.res, rv_simp] <;> rfl
  · intro A _ _; simp [bHK.res, rv_simp]

theorem hb_spec (s : MachineState) (hpc : s.pc = pcOf 1616) :
    ∃ t, Steps Sign.image s 2 2 t ∧
      t.pc = (if s.getReg .x29 &&& 1#64 = 0#64 then pcOf 1621 else pcOf 1618) ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bHB codeAt_hnHB s hpc (by simp [bHB.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bHB.res, E.eval, CmpOp.eval, BinOp.eval]
    split_ifs <;> simp_all
  · intro r hr; simp at hr; cases r <;> simp_all [bHB.res, rv_simp] <;> rfl
  · intro A _ _; simp [bHB.res, rv_simp]

theorem x_spec (s : MachineState) (hpc : s.pc = pcOf 1618) :
    ∃ t, Steps Sign.image s 3 3 t ∧ t.pc = pcOf 1621 ∧ t.getReg .x16 = s.getReg .x16 ^^^ s.getReg .x14 ∧
      t.getReg .x24 = s.getReg .x24 ^^^ s.getReg .x15 ∧ t.getReg .x4 = s.getReg .x4 ^^^ s.getReg .x12 ∧
      RegsExcept s t [.x4, .x16, .x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bX codeAt_hnX s hpc (by simp [bX.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bX.res, E.eval]
  · simp [bX.res, rv_simp]
  · simp [bX.res, rv_simp]
  · simp [bX.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bX.res, rv_simp] <;> rfl
  · intro A _ _; simp [bX.res, rv_simp]

theorem hs_spec (s : MachineState) (hpc : s.pc = pcOf 1621) :
    ∃ t, Steps Sign.image s 9 9 t ∧
      t.pc = (if s.getReg .x29 >>> 1 = 0#64 then pcOf 1630 else pcOf 1616) ∧
      t.getReg .x14 = s.getReg .x14 <<< 1 ∧
      t.getReg .x15 = (s.getReg .x15 <<< 1) ||| (s.getReg .x14 >>> 63) ∧
      t.getReg .x12 = (s.getReg .x12 <<< 1) ||| (s.getReg .x15 >>> 63) ∧
      t.getReg .x29 = s.getReg .x29 >>> 1 ∧
      RegsExcept s t [.x12, .x14, .x15, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bHS codeAt_hnHS s hpc (by simp [bHS.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bHS.res, E.eval, CmpOp.eval, BinOp.eval]
    split_ifs <;> simp_all
  · simp [bHS.res, rv_simp]
  · simp [bHS.res, rv_simp]
  · simp [bHS.res, rv_simp]
  · simp [bHS.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bHS.res, rv_simp] <;> rfl
  · intro A _ _; simp [bHS.res, rv_simp]

theorem hf_spec (s : MachineState) (hpc : s.pc = pcOf 1630) {A : Nat}
    (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 16 ≤ 2 ^ 24) :
    ∃ t, Steps Sign.image s 12 12 t ∧
      t.pc = (if s.getReg .x10 = s.getReg .x11 then pcOf 1642 else pcOf 1610) ∧
      t.getReg .x14 = foldLo (s.getReg .x16) (s.getReg .x4) ^^^ s.getMem (BitVec.ofNat 64 A) ∧
      t.getReg .x15 = s.getReg .x24 ^^^ s.getMem (BitVec.ofNat 64 (A + 8)) ∧
      RegsExcept s t [.x14, .x15, .x16, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bHF codeAt_hnHF s hpc (by simp [bHF.res, rv_simp, h10]; t3n []; omega),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bHF.res, E.eval, CmpOp.eval, BinOp.eval]
    split_ifs <;> simp_all
  · simp only [Result.toState_getReg, bHF.res]; simp only [rv_simp, h10, foldLo]; t3n []
  · simp only [Result.toState_getReg, bHF.res]; simp only [rv_simp, h10]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [bHF.res, rv_simp] <;> rfl
  · intro A _ _; simp [bHF.res, rv_simp]

theorem exit_spec (s : MachineState) (hpc : s.pc = pcOf 1642) :
    ∃ t, Steps Sign.image s 11 11 t ∧ t.pc = s.getReg .x1 &&& ~~~1#64 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 48)) = s.getReg .x14 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 56)) = s.getReg .x15 ∧
      t.getReg .x13 = s.getMem (BitVec.ofNat 64 (TSAVE + 32)) ∧
      t.getReg .x14 = s.getMem (BitVec.ofNat 64 (TSAVE + 40)) ∧
      t.getReg .x15 = s.getMem (BitVec.ofNat 64 (TSAVE + 48)) ∧
      t.getReg .x16 = s.getMem (BitVec.ofNat 64 (TSAVE + 56)) ∧
      t.getReg .x24 = s.getMem (BitVec.ofNat 64 (TSAVE + 64)) ∧
      t.getReg .x4 = s.getMem (BitVec.ofNat 64 (TSAVE + 72)) ∧
      RegsExcept s t [.x4, .x13, .x14, .x15, .x16, .x24, .x30] ∧
      Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  refine ⟨_, symRun_sound bExit codeAt_hnExit s hpc (by simp [bExit.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simp [bExit.res, E.eval, BinOp.eval]
  · simp only [Result.toState_getMem, bExit.res]; t3n [CHAIN]
  · simp only [Result.toState_getMem, bExit.res]; t3n [CHAIN]
  · simp only [Result.toState_getReg, bExit.res]; t3n [TSAVE]
  · simp only [Result.toState_getReg, bExit.res]; t3n [TSAVE]
  · simp only [Result.toState_getReg, bExit.res]; t3n [TSAVE]
  · simp only [Result.toState_getReg, bExit.res]; t3n [TSAVE]
  · simp only [Result.toState_getReg, bExit.res]; t3n [TSAVE]
  · simp only [Result.toState_getReg, bExit.res]; t3n [TSAVE]
  · intro r hr; simp at hr; cases r <;> simp_all [bExit.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [CHAIN] at hn
    simp only [Result.toState_getMem, bExit.res]
    t3n []
    split_ifs <;> first | rfl | omega

/-! ### The Horner loop -/

def hbRegsT : List Reg := [.x4, .x12, .x14, .x15, .x16, .x24, .x29, .x30]

structure HbSt (t0 : MachineState) (d a k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 1616
  sh : lim3 (t.getReg .x14) (t.getReg .x15) (t.getReg .x12) = a * 2 ^ k
  pr : lim3 (t.getReg .x16) (t.getReg .x24) (t.getReg .x4) = clmulSmall a d k
  dd : t.getReg .x29 = BitVec.ofNat 64 (d / 2 ^ k)
  regs : RegsExcept t0 t hbRegsT
  frame : Frame t0 t (fun _ => False)

structure HfSt (t0 : MachineState) (d a : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 1630
  pr : lim3 (t.getReg .x16) (t.getReg .x24) (t.getReg .x4) = clmulSmall a d 10
  regs : RegsExcept t0 t hbRegsT
  frame : Frame t0 t (fun _ => False)

theorem and1_ofNat (x : Nat) (hx : x < 2 ^ 64) : BitVec.ofNat 64 x &&& 1#64 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat_lt hx, show (1#64).toNat = 1 from rfl, toNat_ofNat_lt (by omega),
    Nat.and_one_is_mod]

theorem lim3_ite' (b : Bool) (a0 a1 a2 x0 x1 x2 : BitVec 64) :
    lim3 (if b then a0 ^^^ x0 else a0) (if b then a1 ^^^ x1 else a1) (if b then a2 ^^^ x2 else a2) =
      if b then lim3 a0 a1 a2 ^^^ lim3 x0 x1 x2 else lim3 a0 a1 a2 := by
  cases b
  · rfl
  · simp only [if_true]; exact lim3_xor ..

/-- One bit iteration (`HB`, `X` if the bit is set, `HS`): at most 14 cycles. -/
theorem bit_step {t0 : MachineState} {d a : Nat} (ha : a < 2 ^ 128) (hd : d < 2 ^ 10) {k : Nat} (hk : k ≤ 9)
    {t : MachineState} (ht : HbSt t0 d a k t) :
    ∃ u m, Steps Sign.image t m m u ∧ m ≤ 14 ∧
      u.pc = (if d / 2 ^ (k + 1) = 0 then pcOf 1630 else pcOf 1616) ∧
      lim3 (u.getReg .x14) (u.getReg .x15) (u.getReg .x12) = a * 2 ^ (k + 1) ∧
      lim3 (u.getReg .x16) (u.getReg .x24) (u.getReg .x4) = clmulSmall a d (k + 1) ∧
      u.getReg .x29 = BitVec.ofNat 64 (d / 2 ^ (k + 1)) ∧
      RegsExcept t0 u hbRegsT ∧ Frame t0 u (fun _ => False) := by
  have hp9 : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hk
  have hdk : d / 2 ^ k < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hlt12 : (t.getReg .x12).toNat < 2 ^ 63 := by
    have := lim3_lt (t.getReg .x14) (t.getReg .x15) (t.getReg .x12) (n := 9) (by
      rw [ht.sh, Nat.pow_add]
      exact Nat.mul_lt_mul_of_lt_of_le ha hp9 (Nat.two_pow_pos _))
    omega
  have hshr : t.getReg .x29 >>> 1 = BitVec.ofNat 64 (d / 2 ^ (k + 1)) := by
    rw [ht.dd, ofNat_shr _ _ hdk, Nat.div_div_eq_div_mul, pow_one, ← Nat.pow_succ]
  have hz : (t.getReg .x29 >>> 1 = 0#64) ↔ d / 2 ^ (k + 1) = 0 := by
    rw [hshr, show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
      ofNat_inj (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)) (by norm_num)]
  -- the bit
  obtain ⟨t1, s1, p1, r1, f1⟩ := hb_spec t ht.pc
  have hand : t.getReg .x29 &&& 1#64 = BitVec.ofNat 64 (d / 2 ^ k % 2) := by rw [ht.dd]; exact and1_ofNat _ hdk
  -- `X` when the bit is set
  obtain ⟨t2, m2, s2, hm2, p2, x16, x24, x4, r2, f2⟩ : ∃ t2 m2, Steps Sign.image t1 m2 m2 t2 ∧ m2 ≤ 3 ∧
      t2.pc = pcOf 1621 ∧
      t2.getReg .x16 = (if d.testBit k then t.getReg .x16 ^^^ t.getReg .x14 else t.getReg .x16) ∧
      t2.getReg .x24 = (if d.testBit k then t.getReg .x24 ^^^ t.getReg .x15 else t.getReg .x24) ∧
      t2.getReg .x4 = (if d.testBit k then t.getReg .x4 ^^^ t.getReg .x12 else t.getReg .x4) ∧
      RegsExcept t t2 [.x30, .x4, .x16, .x24] ∧ Frame t t2 (fun _ => False) := by
    rw [hand] at p1
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (d / 2 ^ k) with h | h
    · rw [h] at p1
      rw [if_pos rfl] at p1
      simp only [h, show ¬ (0 = 1) by omega, decide_false, Bool.false_eq_true, if_false]
      exact ⟨t1, 0, Steps.refl _, by omega, p1, r1.get (by decide), r1.get (by decide), r1.get (by decide),
        r1.mono (by simp), f1⟩
    · rw [h] at p1
      rw [if_neg (by decide)] at p1
      simp only [h, decide_true, if_true]
      obtain ⟨t2, s2, p2, a16, a24, a4, r2, f2⟩ := x_spec t1 p1
      refine ⟨t2, 3, s2, le_rfl, p2, ?_, ?_, ?_, (r1.trans r2).mono (by simp), (f1.trans f2).mono (by simp)⟩
      · rw [a16, r1.get (by decide), r1.get (by decide)]
      · rw [a24, r1.get (by decide), r1.get (by decide)]
      · rw [a4, r1.get (by decide), r1.get (by decide)]
  have g : ∀ r, r ∉ [Reg.x30, .x4, .x16, .x24] → t2.getReg r = t.getReg r := fun r hr => r2.get hr
  obtain ⟨u, s3, p3, u14, u15, u12, u29, r3, f3⟩ := hs_spec t2 p2
  refine ⟨u, _, s1.trans (s2.trans s3), by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p3, g _ (by decide)]
    by_cases h0 : d / 2 ^ (k + 1) = 0
    · rw [if_pos (hz.mpr h0), if_pos h0]
    · rw [if_neg (fun h => h0 (hz.mp h)), if_neg h0]
  · rw [u14, u15, u12, g _ (by decide), g _ (by decide), g _ (by decide), lim3_shl1 _ _ _ hlt12, ht.sh,
      Nat.pow_succ]
    ring
  · rw [r3.get (by decide), r3.get (by decide), r3.get (by decide), x16, x24, x4, lim3_ite', ht.pr, ht.sh]
    rw [← clmul_step a d k _ rfl (d.testBit k) rfl]
  · rw [u29, g _ (by decide), hshr]
  · exact ((ht.regs.trans r2).trans r3).mono (by simp [hbRegsT])
  · exact ((ht.frame.trans f2).trans f3).mono (fun _ _ h => by simp_all)

theorem hb_loop {t0 : MachineState} {d a : Nat} (ha : a < 2 ^ 128) (hd : d < 2 ^ 10) :
    ∀ n k, k + n = 10 → (k = 0 ∨ 2 ^ k ≤ d) → ∀ t, HbSt t0 d a k t →
      ∃ u m, Steps Sign.image t m m u ∧ m ≤ 14 * n ∧ HfSt t0 d a u := by
  intro n
  induction n with
  | zero =>
    intro k hk hk0 t _
    exfalso
    rcases hk0 with h | h
    · omega
    · have : k = 10 := by omega
      subst this; omega
  | succ n ih =>
    intro k hk hk0 t ht
    obtain ⟨u, m, su, hm, upc, ush, upr, udd, ur, uf⟩ := bit_step ha hd (by omega) ht
    by_cases hz : d / 2 ^ (k + 1) = 0
    · have hdlt : d < 2 ^ (k + 1) := by
        by_contra hc
        have := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.two_pow_pos (k + 1))
        omega
      refine ⟨u, m, su, by omega, ⟨by rw [upc, if_pos hz], ?_, ur, uf⟩⟩
      rw [upr, clmulSmall_stable a hdlt 10 (by omega)]
    · have hge : 2 ^ (k + 1) ≤ d := by
        by_contra hc
        exact hz (Nat.div_eq_of_lt (Nat.lt_of_not_le hc))
      obtain ⟨v, m', sv, hm', hv⟩ := ih (k + 1) (by omega) (Or.inr hge) u
        ⟨by rw [upc, if_neg hz], ush, upr, udd, ur, uf⟩
      exact ⟨v, _, su.trans sv, by omega, hv⟩

/-- The first 24 coefficients of the buffer. -/
def CoefAtT (t : MachineState) (coefs : List Digest) : Prop :=
  ∀ k < 24, DigAt t (TCOEF + 16 * k) (coefs.getD k 0)

theorem CoefAtT.frame {s t : MachineState} {coefs : List Digest} {W : Nat → Prop} (h : CoefAtT s coefs)
    (hf : Frame s t W) (hW : ∀ A, TCOEF ≤ A → A < TCOEF + 384 → ¬ W A) : CoefAtT t coefs :=
  fun k hk => (h k hk).frame hf (by unfold TCOEF; omega) (hW _ (by omega) (by omega)) (hW _ (by omega) (by omega))

structure HkSt (s0 : MachineState) (d : Nat) (coefs : List Digest) (m : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 1610
  x13 : t.getReg .x13 = BitVec.ofNat 64 d
  x10 : t.getReg .x10 = BitVec.ofNat 64 (TCOEF + 16 * m)
  x11 : t.getReg .x11 = BitVec.ofNat 64 TCOEF
  acc : lim2 (t.getReg .x14) (t.getReg .x15) = (familyEval (coefs.drop m) d).toNat
  regs : RegsExcept s0 t loopRegs
  frame : Frame s0 t (fun _ => False)

/-- Cycle bound of one Horner step (HK, at most ten bit iterations, HF). -/
def hstepC : Nat := 6 + 14 * 10 + 12

theorem lim3_zero_hi' (a b : BitVec 64) : lim3 a b 0 = lim2 a b := by
  unfold lim3 lim2; simp

theorem familyEval_drop' (coefs : List Digest) (m : Nat) (hm : m < coefs.length) (d : Nat) :
    familyEval (coefs.drop m) d = gfMulPt (familyEval (coefs.drop (m + 1)) d) d ^^^ coefs.getD m 0 := by
  rw [List.drop_eq_getElem_cons hm, familyEval_cons, List.getD_eq_getElem _ _ hm]

theorem coef_limbsT {s0 u : MachineState} {coefs : List Digest} (hcoef : CoefAtT s0 coefs)
    (hf : Frame s0 u (fun _ => False)) {m : Nat} (hm : m < 24) :
    lim2 (u.getMem (BitVec.ofNat 64 (TCOEF + 16 * m))) (u.getMem (BitVec.ofNat 64 (TCOEF + 16 * m + 8))) =
      (coefs.getD m 0).toNat := by
  have h := hcoef m hm
  rw [hf.get (by unfold TCOEF; omega) id, hf.get (by unfold TCOEF; omega) id, h.1, h.2, lim2_toNat]

theorem horner_step {s0 : MachineState} {d : Nat} {coefs : List Digest} (hd : d < 2 ^ 10)
    (hcoef : CoefAtT s0 coefs) (hlen : coefs.length = 24)
    {m : Nat} (hm : m < 24) {t : MachineState} (ht : HkSt s0 d coefs (m + 1) t) :
    ∃ u n, Steps Sign.image t n n u ∧ n ≤ hstepC ∧
      u.pc = (if m = 0 then pcOf 1642 else pcOf 1610) ∧
      u.getReg .x13 = BitVec.ofNat 64 d ∧ u.getReg .x10 = BitVec.ofNat 64 (TCOEF + 16 * m) ∧
      u.getReg .x11 = BitVec.ofNat 64 TCOEF ∧
      lim2 (u.getReg .x14) (u.getReg .x15) = (familyEval (coefs.drop m) d).toNat ∧
      RegsExcept s0 u loopRegs ∧ Frame s0 u (fun _ => False) := by
  obtain ⟨t1, s1, p1, x10, x16, x24, x4, x12, x29, r1, f1⟩ := hk_spec t ht.pc
  have h10 : t1.getReg .x10 = BitVec.ofNat 64 (TCOEF + 16 * m) := by
    rw [x10, ht.x10]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    unfold TCOEF; omega
  have ha := (familyEval (coefs.drop (m + 1)) d).isLt
  have h0 : HbSt t1 d (familyEval (coefs.drop (m + 1)) d).toNat 0 t1 := by
    refine ⟨p1, ?_, ?_, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [x12, lim3_zero_hi', r1.get (by decide), r1.get (by decide), ht.acc]; simp
    · rw [x16, x24, x4]; unfold lim3; simp [clmulSmall]
    · rw [x29, ht.x13]; simp
  obtain ⟨u, n, su, hn, hu⟩ := hb_loop ha hd 10 0 (by norm_num) (Or.inl rfl) t1 h0
  have u10 : u.getReg .x10 = BitVec.ofNat 64 (TCOEF + 16 * m) := by rw [hu.regs.get (by decide), h10]
  have u11 : u.getReg .x11 = BitVec.ofNat 64 TCOEF := by
    rw [hu.regs.get (by decide), r1.get (by decide), ht.x11]
  obtain ⟨v, sv, vpc, v14, v15, vr, vf⟩ := hf_spec u hu.pc u10 (by unfold TCOEF; omega) (by unfold TCOEF; omega)
  have hf0 : Frame s0 u (fun _ => False) := ((ht.frame.trans f1).trans hu.frame).mono (fun _ _ h => by simp_all)
  have hl := horner_limbs hu.pr (coef_limbsT hcoef hf0 hm)
  rw [← familyEval_drop' coefs m (by omega)] at hl
  refine ⟨v, _, (s1.trans su).trans sv, by unfold hstepC; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vpc, u10, u11]
    by_cases hm0 : m = 0
    · subst hm0; simp
    · rw [if_neg hm0, if_neg]
      rw [ofNat_inj (by unfold TCOEF; omega) (by unfold TCOEF; omega)]; omega
  · rw [vr.get (by decide), hu.regs.get (by decide), r1.get (by decide), ht.x13]
  · rw [vr.get (by decide), u10]
  · rw [vr.get (by decide), u11]
  · rw [v14, v15]; exact hl
  · exact (((ht.regs.trans r1).trans hu.regs).trans vr).mono (by simp [loopRegs, hbRegsT])
  · exact (hf0.trans vf).mono (fun _ _ h => by simp_all)

theorem horner_loop {s0 : MachineState} {d : Nat} {coefs : List Digest} (hd : d < 2 ^ 10)
    (hcoef : CoefAtT s0 coefs) (hlen : coefs.length = 24) :
    ∀ m, m < 24 → ∀ t, HkSt s0 d coefs (m + 1) t →
      ∃ u n, Steps Sign.image t n n u ∧ n ≤ hstepC * (m + 1) ∧ u.pc = pcOf 1642 ∧
        lim2 (u.getReg .x14) (u.getReg .x15) = (familyEval coefs d).toNat ∧
        RegsExcept s0 u loopRegs ∧ Frame s0 u (fun _ => False) := by
  intro m
  induction m with
  | zero =>
    intro _ t ht
    obtain ⟨u, n, su, hn, upc, -, -, -, uacc, ur, uf⟩ := horner_step hd hcoef hlen (by norm_num) ht
    exact ⟨u, n, su, by omega, by rw [upc, if_pos rfl], by simpa using uacc, ur, uf⟩
  | succ m ih =>
    intro hm t ht
    obtain ⟨u, n, su, hn, upc, u13, u10, u11, uacc, ur, uf⟩ := horner_step hd hcoef hlen hm ht
    rw [if_neg (by omega)] at upc
    obtain ⟨v, n', sv, hn', vpc, vacc, vr, vf⟩ := ih (by omega) u ⟨upc, u13, u10, u11, uacc, ur, uf⟩
    exact ⟨v, _, su.trans sv, by unfold hstepC at *; omega, vpc, vacc, vr, vf⟩

/-- Cycle bound of HORN. -/
def hornCT : Nat := 13 + hstepC * 24 + 11

/-- HORN: `familyEval coefs (i + 1)` into `CHAIN + 48`; `a3..a6, s8, tp` restored. -/
theorem horn_run (s : MachineState) (hpc : s.pc = pcOf 1597) {i : Nat} (hi : i + 1 < 2 ^ 10)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) {coefs : List Digest} (hlen : coefs.length = 24)
    (hcoef : CoefAtT s coefs) :
    ∃ u n, Steps Sign.image s n n u ∧ n ≤ hornCT ∧ u.pc = s.getReg .x1 &&& ~~~1#64 ∧
      DigAt u (CHAIN + 48) (familyEval coefs (i + 1)) ∧ RegsExcept s u [.x10, .x11, .x12, .x29, .x30] ∧
      Frame s u (fun A => SaveW A ∨ A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  obtain ⟨t, st, tpc, t13, t14, t15, t10, t11, m32, m40, m48, m56, m64, m72, tr, tf⟩ :=
    entry_spec s hpc i (by omega) h19
  have hc : CoefAtT t coefs := hcoef.frame tf (fun A h1 h2 h => by unfold SaveW TSAVE at h; unfold TCOEF at h1; omega)
  have ht : HkSt t (i + 1) coefs (23 + 1) t := by
    refine ⟨tpc, t13, t10, t11, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    rw [t14, t15, List.drop_eq_nil_of_le (by omega)]
    rfl
  obtain ⟨u, n, su, hn, upc, uacc, ur, uf⟩ := horner_loop hi hc hlen 23 (by norm_num) t ht
  obtain ⟨v, sv, vpc, v48, v56, v13, v14, v15, v16, v24, v4, vr, vf⟩ := exit_spec u upc
  obtain ⟨l0, l1⟩ := limbs_of_lim2 uacc
  have keep : ∀ A, SaveW A → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA => uf.get (by unfold SaveW TSAVE at hA; omega) id
  refine ⟨v, _, (st.trans su).trans sv, by unfold hornCT; omega, ?_, ⟨by rw [v48, l0], by rw [v56, ← l1]⟩, ?_, ?_⟩
  · rw [vpc, ur.get (by decide), tr.get (by decide)]
  · intro r hr
    by_cases h13 : r = .x13
    · subst h13; rw [v13, keep _ (by unfold SaveW; omega), m32]
    by_cases h14 : r = .x14
    · subst h14; rw [v14, keep _ (by unfold SaveW; omega), m40]
    by_cases h15 : r = .x15
    · subst h15; rw [v15, keep _ (by unfold SaveW; omega), m48]
    by_cases h16 : r = .x16
    · subst h16; rw [v16, keep _ (by unfold SaveW; omega), m56]
    by_cases h24 : r = .x24
    · subst h24; rw [v24, keep _ (by unfold SaveW; omega), m64]
    by_cases h4 : r = .x4
    · subst h4; rw [v4, keep _ (by unfold SaveW; omega), m72]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [vr.get (by simp [*]), ur.get (by simp [loopRegs, *]), tr.get (by simp [entryRegs, *])]
  · exact ((tf.trans uf).trans vf).mono (fun A _ h => by
      rcases h with (h | h) | h
      · left; exact h
      · exact h.elim
      · right; exact h)

/-! ### COEFGEN pieces -/

def CgSaveW (A : Nat) : Prop := TSAVE ≤ A ∧ A < TSAVE + 24

theorem hdrTop_word (leaf j : Nat) (hl : leaf < 4096) (hj : j < 12) :
    ((BitVec.ofNat 64 leaf * 12#64) <<< 32 ||| 1#64) + BitVec.ofNat 64 (2 ^ 32 * j) =
      BitVec.ofNat 64 (1 + 2 ^ 32 * (12 * leaf + j)) := by
  have e1 : BitVec.ofNat 64 leaf * 12#64 = BitVec.ofNat 64 (12 * leaf) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  rw [e1, ofNat_shl, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_or_add 1 _ 32 (by norm_num),
    ofNat_add_ofNat]
  congr 1; ring

theorem cgHead_spec (s : MachineState) (hpc : s.pc = pcOf 1559) (leaf : Nat) (hl : leaf < 4096)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps Sign.image s 10 13 t ∧ t.pc = pcOf 1569 ∧ t.getReg .x24 = BitVec.ofNat 64 TCOEF ∧
      t.getReg .x14 = BitVec.ofNat 64 (1 + 2 ^ 32 * (12 * leaf + 0)) ∧ t.getReg .x29 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 TSAVE) = s.getReg .x4 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 8)) = s.getReg .x24 ∧
      t.getMem (BitVec.ofNat 64 (TSAVE + 16)) = s.getReg .x14 ∧
      RegsExcept s t [.x14, .x24, .x29, .x30] ∧ Frame s t CgSaveW := by
  refine ⟨_, symRun_sound bCgHead codeAt_cgHead s hpc (by simp [bCgHead.res, rv_simp]), ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simp [bCgHead.res, E.eval]
  · simp only [Result.toState_getReg, bCgHead.res]; t3n [TCOEF]
  · have := hdrTop_word leaf 0 hl (by norm_num)
    rw [show BitVec.ofNat 64 (2 ^ 32 * 0) = 0#64 from rfl, BitVec.add_zero] at this
    simp only [Result.toState_getReg, bCgHead.res]; simp only [rv_simp, h18]
    rw [show ((32#64 : BitVec 64).toNat % 64) = 32 from rfl, this]
  · simp [bCgHead.res, rv_simp]
  · simp only [Result.toState_getMem, bCgHead.res]; t3n [TSAVE]
  · simp only [Result.toState_getMem, bCgHead.res]; t3n [TSAVE]
  · simp only [Result.toState_getMem, bCgHead.res]; t3n [TSAVE]
  · intro r hr; simp at hr; cases r <;> simp_all [bCgHead.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [CgSaveW, TSAVE] at hn
    simp only [Result.toState_getMem, bCgHead.res]
    t3n []
    split_ifs <;> first | rfl | omega

theorem cgCall_spec (s : MachineState) (hpc : s.pc = pcOf 1569) (H : Nat)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 H) :
    ∃ t, Steps Sign.image s 5 5 t ∧ t.pc = pcOf 1574 ∧ fetch Sign.image t = some (.base .ECALL) ∧
      t.getReg .x10 = BitVec.ofNat 64 PRIV ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 SEEDS ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 16)) = BitVec.ofNat 64 H ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 24)) = 0 ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun A => A = PRIV + 16 ∨ A = PRIV + 24) := by
  have hobl : bCgCall.res.obligs s := by simp [bCgCall.res, rv_simp]
  refine ⟨_, symRun_sound bCgCall codeAt_cgCall s hpc hobl, ?_,
    symRun_ecall bCgCall codeAt_cgCall s hobl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bCgCall.res, E.eval]
  · simp only [Result.toState_getReg, bCgCall.res]; t3n [PRIV]
  · simp only [Result.toState_getReg, bCgCall.res]; t3n []
  · simp only [Result.toState_getReg, bCgCall.res]; t3n [SEEDS]
  · simp only [Result.toState_getMem, bCgCall.res]; t3n [PRIV, h14]
  · simp only [Result.toState_getMem, bCgCall.res]; t3n [PRIV]
  · intro r hr; simp at hr; cases r <;> simp_all [bCgCall.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem, bCgCall.res]
    t3n []
    split_ifs <;> first | rfl | omega

theorem cgCopy_spec (s : MachineState) (hpc : s.pc = pcOf 1575) {P H j : Nat}
    (h10 : s.getReg .x10 = BitVec.ofNat 64 PRIV) (h24 : s.getReg .x24 = BitVec.ofNat 64 P)
    (hP : P % 8 = 0) (hP' : TCOEF ≤ P ∧ P + 32 ≤ TCOEF + 384)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 j) (hj : j < 12)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 H) (hH : H + 2 ^ 32 < 2 ^ 64) :
    ∃ t, Steps Sign.image s 15 15 t ∧ t.pc = (if j + 1 = 12 then pcOf 1590 else pcOf 1569) ∧
      t.getMem (BitVec.ofNat 64 P) = s.getMem (BitVec.ofNat 64 SEEDS) ∧
      t.getMem (BitVec.ofNat 64 (P + 8)) = s.getMem (BitVec.ofNat 64 (SEEDS + 8)) ∧
      t.getMem (BitVec.ofNat 64 (P + 16)) = s.getMem (BitVec.ofNat 64 (SEEDS + 16)) ∧
      t.getMem (BitVec.ofNat 64 (P + 24)) = s.getMem (BitVec.ofNat 64 (SEEDS + 24)) ∧
      t.getReg .x24 = BitVec.ofNat 64 (P + 32) ∧ t.getReg .x14 = BitVec.ofNat 64 (H + 2 ^ 32) ∧
      t.getReg .x29 = BitVec.ofNat 64 (j + 1) ∧
      RegsExcept s t [.x4, .x14, .x24, .x29, .x30] ∧ Frame s t (fun A => P ≤ A ∧ A < P + 32) := by
  have hobl : bCgCopy.res.obligs s := by
    simp [bCgCopy.res, rv_simp, h10, h24]
    t3n [PRIV]
    unfold TCOEF at hP'
    simp only [and_true, true_and]
    omega
  refine ⟨_, symRun_sound bCgCopy codeAt_cgCopy s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bCgCopy.res, E.eval, CmpOp.eval, BinOp.eval, h29]
    t3n []
    split_ifs <;> first | rfl | omega
  · simp only [Result.toState_getMem, bCgCopy.res]; t3n [h24, h10, PRIV, SEEDS]
    all_goals (split_ifs <;> first | rfl | omega)
  · simp only [Result.toState_getMem, bCgCopy.res]; t3n [h24, h10, PRIV, SEEDS]
    all_goals (split_ifs <;> first | rfl | omega)
  · simp only [Result.toState_getMem, bCgCopy.res]; t3n [h24, h10, PRIV, SEEDS]
    all_goals (split_ifs <;> first | rfl | omega)
  · simp only [Result.toState_getMem, bCgCopy.res]; t3n [h24, h10, PRIV, SEEDS]
    all_goals (split_ifs <;> first | rfl | omega)
  · simp only [Result.toState_getReg, bCgCopy.res]; t3n [h24]
  · simp only [Result.toState_getReg, bCgCopy.res]; t3n [h14]
  · simp only [Result.toState_getReg, bCgCopy.res]; t3n [h29]
  · intro r hr; simp at hr; cases r <;> simp_all [bCgCopy.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [TCOEF] at hP'
    simp only [Result.toState_getMem, bCgCopy.res]
    t3n [h24]
    all_goals (split_ifs <;> first | rfl | omega)

theorem cgExit_spec (s : MachineState) (hpc : s.pc = pcOf 1590) :
    ∃ t, Steps Sign.image s 6 6 t ∧ t.pc = s.getReg .x1 &&& ~~~1#64 ∧
      t.getReg .x4 = s.getMem (BitVec.ofNat 64 TSAVE) ∧
      t.getReg .x24 = s.getMem (BitVec.ofNat 64 (TSAVE + 8)) ∧
      t.getReg .x14 = s.getMem (BitVec.ofNat 64 (TSAVE + 16)) ∧ t.getReg .x19 = 0 ∧
      RegsExcept s t [.x4, .x14, .x19, .x24, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bCgExit codeAt_cgExit s hpc (by simp [bCgExit.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bCgExit.res, E.eval, BinOp.eval]
  · simp only [Result.toState_getReg, bCgExit.res]; t3n [TSAVE]
  · simp only [Result.toState_getReg, bCgExit.res]; t3n [TSAVE]
  · simp only [Result.toState_getReg, bCgExit.res]; t3n [TSAVE]
  · simp [bCgExit.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bCgExit.res, rv_simp] <;> rfl
  · intro A _ _; simp [bCgExit.res, rv_simp]

/-! ### COEFGEN as a refinement of `SigGolfCandidate.T3.topCoefs` -/

/-- Writes of COEFGEN. -/
def CgW (A : Nat) : Prop :=
  A = PRIV + 16 ∨ A = PRIV + 24 ∨ (SEEDS ≤ A ∧ A < SEEDS + 32) ∨ CgSaveW A ∨ (TCOEF ≤ A ∧ A < TCOEF + 384)
def cgRegs : List Reg := [.x4, .x10, .x11, .x12, .x14, .x24, .x29, .x30]

/-- The secret-key words of the private input block. -/
structure SkAt (sk : BitVec 256) (s : MachineState) : Prop where
  p0 : s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : s.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : s.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : s.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : s.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : s.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0

theorem SkAt.frame {sk : BitVec 256} {s t : MachineState} {W : Nat → Prop} (h : SkAt sk s) (hf : Frame s t W)
    (hW : ∀ A, A = PRIV ∨ A = PRIV + 8 ∨ A = PRIV + 32 ∨ A = PRIV + 40 ∨ A = PRIV + 48 ∨ A = PRIV + 56 → ¬ W A) :
    SkAt sk t :=
  ⟨(hf.get (by decide) (hW _ (by simp))).trans h.p0, (hf.get (by decide) (hW _ (by simp))).trans h.p8,
    (hf.get (by decide) (hW _ (by simp))).trans h.p32, (hf.get (by decide) (hW _ (by simp))).trans h.p40,
    (hf.get (by decide) (hW _ (by simp))).trans h.p48, (hf.get (by decide) (hW _ (by simp))).trans h.p56⟩

structure CgSt (s0 : MachineState) (leaf j : Nat) (acc : List Digest) (u : MachineState) : Prop where
  pc : u.pc = pcOf (if j < 12 then 1569 else 1590)
  x29 : u.getReg .x29 = BitVec.ofNat 64 j
  x24 : u.getReg .x24 = BitVec.ofNat 64 (TCOEF + 32 * j)
  x14 : u.getReg .x14 = BitVec.ofNat 64 (1 + 2 ^ 32 * (12 * leaf + j))
  len : acc.length = 2 * j
  coefs : ∀ k < 2 * j, DigAt u (TCOEF + 16 * k) (acc.getD k 0)
  m0 : u.getMem (BitVec.ofNat 64 TSAVE) = s0.getReg .x4
  m8 : u.getMem (BitVec.ofNat 64 (TSAVE + 8)) = s0.getReg .x24
  m16 : u.getMem (BitVec.ofNat 64 (TSAVE + 16)) = s0.getReg .x14
  regs : RegsExcept s0 u cgRegs
  frame : Frame s0 u CgW

theorem getD_append2_lt {l : List Digest} {a b : Digest} {k : Nat} (hk : k < l.length) :
    (l ++ [a, b]).getD k 0 = l.getD k 0 := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hk, List.getElem_append_left hk]
theorem getD_append2_0 {l : List Digest} {a b : Digest} : (l ++ [a, b]).getD l.length 0 = a := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by omega)]; simp
theorem getD_append2_1 {l : List Digest} {a b : Digest} : (l ++ [a, b]).getD (l.length + 1) 0 = b := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by omega)]; simp

/-- Cycles of one COEFGEN iteration (5 + the hash + 15). -/
def cgStepC : Nat := 5 + 8 + 15

theorem cg_step (sk : BitVec 256) {s0 : MachineState} (hsk : SkAt sk s0) (h5 : s0.getReg .x5 = 0)
    {leaf : Nat} (hl : leaf < 4096) {j : Nat} (hj : j < 12) {acc : List Digest} {u : MachineState}
    (hu : CgSt s0 leaf j acc u) :
    TBSim Sign.image sk u cgStepC
      (SigGolfCandidate.T3.topSeedPair (SigGolfCandidate.T3.topCoefPairs * leaf + j) >>= fun p => pure (acc ++ [p.1, p.2]))
      (CgSt s0 leaf (j + 1)) := by
  have hP : PRIV = 131072 := rfl
  have hS : SEEDS = 131136 := rfl
  obtain ⟨u1, su1, u1pc, e1, u1x10, u1x11, u1x12, m16, m24, u1r, u1f⟩ :=
    cgCall_spec u (by rw [hu.pc, if_pos hj]) _ hu.x14
  have hcgw : ∀ A, A = PRIV ∨ A = PRIV + 8 ∨ A = PRIV + 32 ∨ A = PRIV + 40 ∨ A = PRIV + 48 ∨ A = PRIV + 56 →
      ¬ CgW A := by
    intro A hA hw; unfold CgW CgSaveW TSAVE TCOEF at hw; simp only [PRIV, SEEDS] at hA hw; omega
  have hsk1 : SkAt sk u1 := (hsk.frame hu.frame hcgw).frame u1f (fun A hA hw => by
    simp only [PRIV] at hA hw; omega)
  have hqin : hashInput u1 = toQ (SigGolfCandidate.T3.privateInput sk
      (.inl (SigGolfCandidate.T3.header 0 0 0 (SigGolfCandidate.T3.topCoefPairs * leaf + j) 0))) := by
    refine hashInput_toQ u1 _ 0 PRIV (privateInput_tweak_length _ _) u1x10 (by decide) (by decide) u1x11
      (by decide) ?_
    have m16' : u1.getMem (BitVec.ofNat 64 (PRIV + 16)) =
        BitVec.ofNat 64 (hdr0 0 0 0 (SigGolfCandidate.T3.topCoefPairs * leaf + j)) := by
      rw [m16, hdr0_eq 0 0 0 _ (by norm_num) (by norm_num) (by norm_num)
        (by unfold SigGolfCandidate.T3.topCoefPairs; omega)]
      unfold SigGolfCandidate.T3.topCoefPairs; congr 1
    have m24' : u1.getMem (BitVec.ofNat 64 (PRIV + 24)) = BitVec.ofNat 64 (hdr1 0 0) := by
      rw [m24, hdr1_eq 0 0 (by norm_num) (by norm_num)]; rfl
    rw [wordsOf_privateInput_tweak, header_lo, header_hi, readWords_eight, hsk1.p0, hsk1.p8, m16', m24',
      hsk1.p32, hsk1.p40, hsk1.p48, hsk1.p56]
    rfl
  have hva : hashArgumentsValid u1 = true :=
    hashArgs_const u1 PRIV 64 SEEDS u1x10 u1x11 u1x12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5' : u1.getReg .x5 = 0 := by rw [u1r.get (by decide), hu.regs.get (by decide), h5]
  unfold SigGolfCandidate.T3.topSeedPair
  refine TBSim.mono (TBSim.steps su1 (TBSim.privatePair_bind' (W := 15) e1 h5' hva hqin (fun a => ?_)))
    (by unfold cgStepC; omega) (fun _ _ h => h)
  have hwf := Frame.writeHash u1 a SEEDS u1x12 (by decide)
  have lo := DigAt.writeHash_lo u1 a SEEDS u1x12 (by decide)
  have hi := DigAt.writeHash_hi u1 a SEEDS u1x12 (by decide)
  have hP' : TCOEF ≤ TCOEF + 32 * j ∧ TCOEF + 32 * j + 32 ≤ TCOEF + 384 := by omega
  obtain ⟨u3, su3, u3pc, c0, c8, c16, c24, u3x24, u3x14, u3x29, u3r, u3f⟩ := cgCopy_spec (writeHash u1 a)
    (by rw [pc_writeHash, u1pc, pcOf_add4]) (by rw [getReg_writeHash]; exact u1x10)
    (by rw [getReg_writeHash, u1r.get (by decide)]; exact hu.x24) (by unfold TCOEF; omega) hP'
    (by rw [getReg_writeHash, u1r.get (by decide)]; exact hu.x29) hj
    (by rw [getReg_writeHash, u1r.get (by decide)]; exact hu.x14) (by omega)
  have f13 : Frame u u3 (fun A => ((A = PRIV + 16 ∨ A = PRIV + 24) ∨ (SEEDS ≤ A ∧ A < SEEDS + 32)) ∨
      (TCOEF + 32 * j ≤ A ∧ A < TCOEF + 32 * j + 32)) := (u1f.trans hwf).trans u3f
  refine TBSim.pure_steps' su3 ⟨?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u3pc]
    by_cases h : j + 1 = 12
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg h, if_pos (by omega)]
  · exact u3x29
  · rw [u3x24, show TCOEF + 32 * j + 32 = TCOEF + 32 * (j + 1) by ring]
  · rw [u3x14, show 1 + 2 ^ 32 * (12 * leaf + j) + 2 ^ 32 = 1 + 2 ^ 32 * (12 * leaf + (j + 1)) by ring]
  · simp [hu.len]; ring
  · by_cases hkj : k < 2 * j
    · rw [getD_append2_lt (by rw [hu.len]; exact hkj)]
      exact (hu.coefs k hkj).frame f13 (by unfold TCOEF; omega) (by unfold TCOEF; simp only [PRIV, SEEDS]; omega)
        (by unfold TCOEF; simp only [PRIV, SEEDS]; omega)
    · by_cases hk0 : k = 2 * j
      · subst hk0
        rw [← hu.len, getD_append2_0]
        refine ⟨?_, ?_⟩
        · rw [show TCOEF + 16 * acc.length = TCOEF + 32 * j by rw [hu.len]; ring, c0, lo.1]
        · rw [show TCOEF + 16 * acc.length + 8 = TCOEF + 32 * j + 8 by rw [hu.len]; ring, c8, lo.2]
      · have hk1 : k = 2 * j + 1 := by omega
        subst hk1
        rw [← hu.len, getD_append2_1]
        refine ⟨?_, ?_⟩
        · rw [show TCOEF + 16 * (acc.length + 1) = TCOEF + 32 * j + 16 by rw [hu.len]; ring, c16, hi.1]
        · rw [show TCOEF + 16 * (acc.length + 1) + 8 = TCOEF + 32 * j + 24 by rw [hu.len]; ring, c24]
          rw [show SEEDS + 24 = SEEDS + 16 + 8 from rfl]; exact hi.2
  · rw [f13.get (by decide) (by unfold TSAVE TCOEF; simp only [PRIV, SEEDS]; omega), hu.m0]
  · rw [f13.get (by decide) (by unfold TSAVE TCOEF; simp only [PRIV, SEEDS]; omega), hu.m8]
  · rw [f13.get (by decide) (by unfold TSAVE TCOEF; simp only [PRIV, SEEDS]; omega), hu.m16]
  · exact ((hu.regs.trans u1r).trans ((show RegsExcept u1 (writeHash u1 a) [] from
      fun r _ => getReg_writeHash u1 a r).trans u3r)).mono (by simp [cgRegs])
  · exact (hu.frame.trans f13).mono (fun A _ h => by
      unfold CgW at *
      rcases h with h | ((h | h) | h) | h
      · exact h
      · left; exact h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; right; unfold TCOEF at *; omega)

/-- Cycle bound of COEFGEN (entry to return). -/
def cgC : Nat := 13 + (12 * cgStepC + 6)

theorem coefgen_tbsim (sk : BitVec 256) (s : MachineState) (hpc : s.pc = pcOf 1559)
    (h1 : s.getReg .x1 = pcOf 1556) {leaf : Nat} (hl : leaf < 4096) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h5 : s.getReg .x5 = 0) (hsk : SkAt sk s) :
    TBSim Sign.image sk s cgC (SigGolfCandidate.T3.topCoefs leaf)
      (fun r u => u.pc = pcOf 1556 ∧ r.length = 24 ∧ CoefAtT u r ∧ u.getReg .x19 = 0 ∧
        RegsExcept s u [.x10, .x11, .x12, .x19, .x29, .x30] ∧ Frame s u CgW) := by
  obtain ⟨t0, s0, p0, x24, x14, x29, m0, m8, m16, r0, f0⟩ := cgHead_spec s hpc leaf hl h18
  have h0 : CgSt s leaf 0 [] t0 :=
    ⟨by rw [p0]; rfl, x29, by rw [x24], x14, rfl, fun k hk => absurd hk (by omega), m0, m8, m16,
      r0.mono (by simp [cgRegs]), f0.mono (fun A _ h => by unfold CgW; right; right; right; left; exact h)⟩
  have hloop := TBSim.foldlM_range' (image := Sign.image) (sk := sk) 0 12
    (fun (acc : List Digest) j => SigGolfCandidate.T3.topSeedPair (SigGolfCandidate.T3.topCoefPairs * leaf + j) >>=
      fun p => pure (acc ++ [p.1, p.2])) [] (fun j acc u => CgSt s leaf j acc u) cgStepC
    (fun j hj acc u hu => by simpa using cg_step sk hsk h5 hl hj hu) h0
  have hprog : SigGolfCandidate.T3.topCoefs leaf =
      (List.range' 0 12).foldlM (fun (acc : List Digest) j =>
        SigGolfCandidate.T3.topSeedPair (SigGolfCandidate.T3.topCoefPairs * leaf + j) >>=
          fun p => pure (acc ++ [p.1, p.2])) [] >>= pure := by
    rw [bind_pure, ← List.range_eq_range']; rfl
  rw [hprog]
  refine TBSim.mono (TBSim.steps s0 (TBSim.bind (W₂ := 6) hloop (fun r u hu => ?_))) (by unfold cgC; omega)
    (fun _ _ h => h)
  obtain ⟨v, sv, vpc, v4, v24, v14, v19, vr, vf⟩ := cgExit_spec u (by rw [hu.pc]; rfl)
  refine TBSim.pure_steps' sv ⟨?_, by rw [hu.len], fun k hk => ?_, v19, fun r hr => ?_, ?_⟩
  · rw [vpc, hu.regs.get (by decide), h1, pcOf_and_not1]
  · exact (hu.coefs k (by omega)).frame vf (by unfold TCOEF; omega) id id
  · by_cases h4 : r = .x4
    · subst h4; rw [v4, hu.m0]
    by_cases h14 : r = .x14
    · subst h14; rw [v14, hu.m16]
    by_cases h24 : r = .x24
    · subst h24; rw [v24, hu.m8]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [vr.get (by simp [*]), hu.regs.get (by simp [cgRegs, *])]
  · exact (hu.frame.trans vf).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)

end ClaudeWCT.W9.Machine.Sign.TopSeed

/-!
# Campaign T8D (TOP2 NF17): the signature-only top leaf of the sign image refines `T3.buildLeafTop`

The prologue (`1040 → 1528..1541 → 1554`) falls through PRE into COEFGEN (`T3.topCoefs leaf`, coefficients at
`TCOEF`), then `j 1053; li s3,0`. Each of the 54 chains reaches `b + 42 → 20746 → 20769 j TOPSEED`, runs HORN
(`familyEval coefs (i + 1)` into `CHAIN + 48`) and re-enters the unchanged leaf code at `b + 71`. The seed routines
write the scratch `TScr` (outside `LeafW`); the keygen-shared leaf invariants are used relative to the hybrid base
`hybT s0 t` (the leaf entry `s0` with the scratch of `t`), as for the stage-B lower leaves.
-/

namespace ClaudeWCT.W9.Machine.Sign.TopLeafP
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3M.Sign (LeafPreS)
open SigGolfCandidate.T3M.Sign.SeedIndependent (SeedIndependentAt)
open SigGolfCandidate.T3 (Layer Digest chainCount maxDigit chain)
open ClaudeWCT.W9.Machine.Sign.TopSeed
open ClaudeWCT.Arith
set_option maxRecDepth 10000

/-! ### Hybrid base states (scratch `TScr = [0x60000, 0x61180)`) -/

theorem tscr_iff (A : Nat) : TScr A ↔ SigGolfCandidate.T3M.Sign.Packed.TopScr A := by
  unfold TScr TSAVE TCOEF SigGolfCandidate.T3M.Sign.Packed.TopScr; omega

def hybT (s0 t : MachineState) : MachineState :=
  { s0 with mem := fun a => if 0x60000 ≤ a.toNat ∧ a.toNat < 0x61180 then t.mem a else s0.mem a }
structure HybOfT (s0 s t : MachineState) : Prop where
  regs : ∀ r, s.getReg r = s0.getReg r
  base : Frame s0 s TScr
  scr : ∀ A, A < 2 ^ 64 → TScr A → s.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A)
theorem hybT_of (s0 t : MachineState) : HybOfT s0 (hybT s0 t) t := by
  refine ⟨fun r => rfl, fun A hA hn => ?_, fun A hA h => ?_⟩
  · show (if 0x60000 ≤ (BitVec.ofNat 64 A).toNat ∧ (BitVec.ofNat 64 A).toNat < 0x61180 then t.mem _ else s0.mem _) =
      s0.mem _
    rw [toNat_ofNat_lt hA, if_neg (show ¬ (0x60000 ≤ A ∧ A < 0x61180) by unfold TScr TSAVE TCOEF at hn; omega)]
  · show (if 0x60000 ≤ (BitVec.ofNat 64 A).toNat ∧ (BitVec.ofNat 64 A).toNat < 0x61180 then t.mem _ else s0.mem _) =
      t.mem _
    rw [toNat_ofNat_lt hA, if_pos (show 0x60000 ≤ A ∧ A < 0x61180 by unfold TScr TSAVE TCOEF at h; omega)]
theorem HybOfT.refl_of {s0 t : MachineState} (hf : Frame s0 t (fun A => ¬ TScr A)) : HybOfT s0 s0 t :=
  ⟨fun _ => rfl, Frame.refl _ _, fun A hA hb => (hf.get hA (fun h => h hb)).symm⟩

theorem not_tscr {X : Nat} (h : X < 0x60000) : ¬ TScr X := fun hb => by unfold TScr TSAVE at hb; omega

theorem LeafPreS.transferT {sk : BitVec 256} {s0 s : MachineState} {A : LeafArgs} (h : LeafPreS sk s0 A)
    (hr : ∀ r, s.getReg r = s0.getReg r) (hf : Frame s0 s TScr) (hd : A.digp + A.n ≤ 0x60000) :
    LeafPreS sk s A := by
  have g : ∀ X, X < 0x60000 → s.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) :=
    fun X hX => hf.get (by omega) (not_tscr hX)
  refine
    { x1 := by rw [hr]; exact h.x1
      x5 := by rw [hr]; exact h.x5
      x8 := by rw [hr]; exact h.x8
      x9 := by rw [hr]; exact h.x9
      x18 := by rw [hr]; exact h.x18
      x22 := by rw [hr]; exact h.x22
      x23 := by rw [hr]; exact h.x23
      x25 := by rw [hr]; exact h.x25
      x26 := by rw [hr]; exact h.x26
      x27 := by rw [hr]; exact h.x27
      x31 := by rw [hr]; exact h.x31
      htree := h.htree
      hleaf := h.hleaf
      hroute := h.hroute
      hleafHeight := h.hleafHeight
      hsteps := h.hsteps
      p0 := by rw [g _ (by decide)]; exact h.p0
      p8 := by rw [g _ (by decide)]; exact h.p8
      p32 := by rw [g _ (by decide)]; exact h.p32
      p40 := by rw [g _ (by decide)]; exact h.p40
      p48 := by rw [g _ (by decide)]; exact h.p48
      p56 := by rw [g _ (by decide)]; exact h.p56
      z0 := by rw [g _ (by decide)]; exact h.z0
      z8 := by rw [g _ (by decide)]; exact h.z8
      z32 := by rw [g _ (by decide)]; exact h.z32
      z40 := by rw [g _ (by decide)]; exact h.z40
      hsl := h.hsl
      hdig := fun i hi => by
        rw [hf.getByte (by omega) (not_tscr (by omega))]; exact h.hdig i hi
      hdigb := h.hdigb
      hdigp := h.hdigp
      hdigW := h.hdigW
      hv8 := h.hv8
      hv := h.hv
      hvs := h.hvs
      hd8 := h.hd8
      hd := h.hd
      hds := h.hds
      hdv := h.hdv }

/-- Writes of the top seed routines: the scratch, the private-pair header/answer and the chain seed slot. -/
def SeedWT (X : Nat) : Prop :=
  TScr X ∨ X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ (CHAIN + 48 ≤ X ∧ X < CHAIN + 64)

theorem LeafInv.rebaseT {s0 s t s' u : MachineState} {A : LeafArgs} {j : Nat} {st : List Digest × List Digest}
    (ht : LeafInv s A j st t) (hs : HybOfT s0 s t) (hs' : HybOfT s0 s' u) {R : List Reg}
    (hr : RegsExcept t u R) (hR : ∀ r ∈ R, r ∈ leafRegs ∧ r ≠ .x19 ∧ r ≠ .x23 ∧ r ≠ .x3)
    {W : Nat → Prop} (hf : Frame t u W) (hW : ∀ X, W X → SeedWT X)
    (hvs : A.valp + 16 * A.n ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp) (hv : A.valp + 16 * A.n ≤ 0x60000)
    (hj : j ≤ A.n) : LeafInv s' A j st u := by
  have hn : A.n = 54 ∨ A.n = 43 := chainCount_cases A.lay
  have hP : PRIV = 131072 := rfl
  have hS : SEEDS = 131136 := rfl
  have hL : LEAFPK = 132608 := rfl
  have hC : CHAIN = 131488 := rfl
  have hLW : ∀ X, (X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ (CHAIN + 48 ≤ X ∧ X < CHAIN + 64)) →
      LeafW A X := by
    intro X h
    unfold LeafW
    rcases h with h | h | h | h
    · left; exact h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; right; right; left; omega
  have nW : ∀ X, X < 0x60000 → ¬ (X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨
      (CHAIN + 48 ≤ X ∧ X < CHAIN + 64)) → ¬ W X := by
    intro X h1 h2 hw
    rcases hW X hw with h | h
    · exact not_tscr h1 h
    · exact h2 h
  have gr : ∀ r, r = .x19 ∨ r = .x23 ∨ r = .x3 → u.getReg r = t.getReg r := fun r h =>
    hr.get (fun hm => by
      obtain ⟨-, h1, h2, h3⟩ := hR r hm
      rcases h with rfl | rfl | rfl <;> simp_all)
  have hlv : ∀ X, LEAFPK ≤ X → X < LEAFPK + 16 * (A.n + 2) → ¬ W X := fun X h1 h2 =>
    nW X (by omega) (by omega)
  refine ⟨by rw [gr _ (by simp)]; exact ht.x19, by rw [gr _ (by simp)]; exact ht.x23,
    by rw [gr _ (by simp)]; exact ht.x3, fun r hr' => ?_, fun X hX hn' => ?_, ?_, ?_, ht.elen, ht.vlen,
    fun hso c hc => ?_, ?_⟩
  · rw [hr.get (fun h => hr' (hR r h).1), ht.regs.get hr', hs.regs, hs'.regs]
  · by_cases hb : TScr X
    · rw [hs'.scr X hX hb]
    · have hnw : ¬ W X := fun hw => by
        rcases hW X hw with h | h
        · exact hb h
        · exact hn' (hLW X h)
      rw [hf.get hX hnw, ht.frame.get hX hn', hs.base.get hX hb, hs'.base.get hX hb]
  · rw [hf.get (by decide) (hlv _ (by omega) (by omega))]; exact ht.lh16
  · rw [hf.get (by decide) (hlv _ (by omega) (by omega))]; exact ht.lh24
  · have h1 := slot_ge A.lay c; have h2 := slot_lt A.lay (show c < A.n by omega)
    exact (ht.ends hso c hc).frame hf (by omega) (hlv _ (by omega) (by omega)) (hlv _ (by omega) (by omega))
  · exact ht.vals.frame hf (by rw [ht.vlen]; omega) (fun X h1 h2 => by
      rw [ht.vlen] at h2
      exact nW X (by omega) (by omega))

theorem LeafW_not_tscr {A : LeafArgs} (hv : A.valp + 16 * A.n ≤ 0x60000) (hd : A.dest + 16 ≤ 0x60000) {X : Nat}
    (h : LeafW A X) : ¬ TScr X := by
  have hn : A.n = 54 ∨ A.n = 43 := chainCount_cases A.lay
  unfold LeafW at h
  intro hb; unfold TScr TSAVE TCOEF at hb
  simp only [PRIV, SEEDS, CHAIN, LEAFPK, LOUT] at h
  split_ifs at h <;> omega

/-! ### Single-word blocks around COEFGEN and TOPSEED -/

theorem pre0_spec (s : MachineState) (hpc : s.pc = pcOf 1554) (h8 : s.getReg .x8 = BitVec.ofNat 64 0) :
    ∃ t, Steps Sign.image s 1 1 t ∧ t.pc = pcOf 1555 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bPre codeAt_1554 s hpc (by simp [bPre.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bPre.res, E.eval, CmpOp.eval, h8]
  · intro r hr; cases r <;> simp_all [bPre.res, rv_simp] <;> rfl
  · intro A _ _; simp [bPre.res, rv_simp]
theorem jal_spec (s : MachineState) (hpc : s.pc = pcOf 1555) :
    ∃ t, Steps Sign.image s 1 1 t ∧ t.pc = pcOf 1559 ∧ t.getReg .x1 = pcOf 1556 ∧ RegsExcept s t [.x1] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bJal codeAt_1555 s hpc (by simp [bJal.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [bJal.res, E.eval]
  · simp [bJal.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bJal.res, rv_simp] <;> rfl
  · intro A _ _; simp [bJal.res, rv_simp]
theorem j1053_spec (s : MachineState) (hpc : s.pc = pcOf 1556) :
    ∃ t, Steps Sign.image s 1 1 t ∧ t.pc = pcOf (1013 + 40) ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bJ1053 codeAt_1556 s hpc (by simp [bJ1053.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bJ1053.res, E.eval]
  · intro r hr; cases r <;> simp_all [bJ1053.res, rv_simp] <;> rfl
  · intro A _ _; simp [bJ1053.res, rv_simp]
theorem li19_spec (s : MachineState) (hpc : s.pc = pcOf (1013 + 40)) :
    ∃ t, Steps Sign.image s 1 1 t ∧ t.pc = pcOf (1013 + 41) ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  have hsub := Sign.SeedIndependent.seedIndependentAt_sign
  refine ⟨_, symRun_sound Sign.SeedIndependent.blkS_40 (Sign.SeedIndependent.codeAt_sub40S hsub) s hpc
    (by simp [Sign.SeedIndependent.blkS_40.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Sign.SeedIndependent.blkS_40.res, E.eval]
  · simp [Sign.SeedIndependent.blkS_40.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [Sign.SeedIndependent.blkS_40.res, rv_simp] <;> rfl
  · intro A _ _; simp [Sign.SeedIndependent.blkS_40.res, rv_simp]
theorem tsJal_spec (s : MachineState) (hpc : s.pc = pcOf 1557) :
    ∃ t, Steps Sign.image s 1 1 t ∧ t.pc = pcOf 1597 ∧ t.getReg .x1 = pcOf 1558 ∧ RegsExcept s t [.x1] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bTsJal codeAt_1557 s hpc (by simp [bTsJal.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [bTsJal.res, E.eval]
  · simp [bTsJal.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [bTsJal.res, rv_simp] <;> rfl
  · intro A _ _; simp [bTsJal.res, rv_simp]
theorem tsJ_spec (s : MachineState) (hpc : s.pc = pcOf 1558) :
    ∃ t, Steps Sign.image s 1 1 t ∧ t.pc = pcOf (1013 + 71) ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bTsJ codeAt_1558 s hpc (by simp [bTsJ.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [bTsJ.res, E.eval]
  · intro r hr; cases r <;> simp_all [bTsJ.res, rv_simp] <;> rfl
  · intro A _ _; simp [bTsJ.res, rv_simp]

/-! ### One top chain -/

section chain
variable (sk : BitVec 256) {s0 : MachineState} {A : LeafArgs} (hpre : LeafPreS sk s0 A)
include hpre

/-- One signature-only chain from `b + 71` (seed already at `CHAIN + 48`). -/
theorem leaf_iter71 (hso : A.so = true) {j : Nat} (hj : j < A.n) {st : List Digest × List Digest}
    {t : MachineState} (ht : LeafInv s0 A j st t) (hpc : t.pc = pcOf (1013 + 71)) (seed : Digest)
    (hseed : DigAt t (CHAIN + 48) seed) :
    TSim Sign.image sk t (11 + selectorExtra A.lay j + (rungK A.lay * A.e j + 10))
      (11 + selectorExtra A.lay j + (rungC A.lay * A.e j + 10)) (A.e j) (A.e j)
      (halfUpd A st <$> chainProg A j seed)
      (fun st' u => u.pc = pcOf (1013 + 41) ∧ LeafInv s0 A (j + 1) st' u ∧
        Frame t u (fun X => (X = CHAIN + 16 ∨ X = CHAIN + 24) ∨ (CHAIN + 48 ≤ X ∧ X < CHAIN + 80) ∨
          (slot A.lay j ≤ X ∧ X < slot A.lay j + 16) ∨ (A.valp + 16 * j ≤ X ∧ X < A.valp + 16 * j + 16))) := by
  have hsub := Sign.SeedIndependent.seedIndependentAt_sign
  obtain ⟨u0, st0, u0pc, hcp, hcs, u0r, u0f⟩ := Sign.Seed.leaf_prechainFrom71S hsub sk hpre hj ht hpc seed hseed
  have hch := Sign.Seed.chainRun_tsim hsub sk hcp u0pc seed hcs
  rw [map_eq_bind_pure_comp]
  refine (TSim.steps st0 (TSim.bind (k₂ := 4 + (if A.so then 0 else 11 + slotK A.lay j))
    (c₂ := 4 + (if A.so then 0 else 11 + slotK A.lay j)) (n₂ := 0) (b₂ := 0) hch
    (fun r u hu => ?_))).of_eq (by unfold chainProg; rfl) ?_ ?_ ?_ ?_
  · obtain ⟨hupc, hv, hl, hur, huf⟩ := hu
    obtain ⟨w, stw, wpc, hw, hfw⟩ := Sign.Seed.leaf_postchainS hsub sk hpre hj ht hupc (u0r.trans hur)
      (u0f.trans huf) r.1 r.2 hv hl
    refine TSim.pure_steps stw ⟨wpc, by simpa [halfUpd] using hw, ?_⟩
    refine ((u0f.trans huf).trans hfw).mono (fun X _ h => ?_)
    unfold ChainW at h
    rcases h with ((h | h) | h | h | h) | h
    · right; left; simp only [CHAIN] at h ⊢; omega
    · right; left; simp only [CHAIN] at h ⊢; omega
    · left; exact h
    · right; left; exact h
    · right; right; right; exact h
    · right; right; left; exact h
  all_goals (try simp only [hso, if_true])
  all_goals omega

/-- Cycles of one top chain: `b+41`, hook, `20746`, `jal`, HORN, `j`, then the chain from `b + 71`. -/
def topChainC : Nat := 5 + hornCT + 1 + 320

structure FStT (s0 : MachineState) (A : LeafArgs) (coefs : List Digest) (j : Nat)
    (st : List Digest × List Digest) (u : MachineState) : Prop where
  pc : u.pc = pcOf (1013 + 41)
  coef : CoefAtT u coefs
  inv : ∃ s, HybOfT s0 s u ∧ LeafInv s A j st u

/-- The chain body of the signature-only `T3.buildLeafTop`. -/
def topStepT (leaf : Nat) (digits : List Nat) (coefs : List Digest) (state : List Digest × List Digest) (i : Nat) :
    SigGolfCandidate.T3.M (List Digest × List Digest) := do
  let value ← chain 0 0 leaf i 0 (digits.getD i 0) (SigGolfCandidate.T3.topSeed coefs i)
  pure (state.1, state.2 ++ [value])

omit hpre in
theorem topStep_eq (hlay : A.lay = 0) (hso : A.so = true) (htree : A.tree = 0) (coefs : List Digest)
    (st : List Digest × List Digest) (j : Nat) :
    topStepT A.leaf A.digits coefs st j = halfUpd A st <$> chainProg A j (familyEval coefs (j + 1)) := by
  unfold topStepT chainProg halfUpd
  simp only [hso, if_true, LeafArgs.e, Nat.sub_self, chain_zero, map_bind, pure_bind, map_pure, hlay, htree]
  rfl

theorem top_chain_step (hlay : A.lay = 0) (hso : A.so = true) (htree : A.tree = 0)
    (hd7 : ∀ i < A.n, A.d i ≤ 7) (hvS : A.valp + 16 * A.n ≤ 0x60000) (hdS : A.digp + A.n ≤ 0x60000)
    (hdestS : A.dest + 16 ≤ 0x60000) {coefs : List Digest} (hlen : coefs.length = 24) {j : Nat} (hj : j < 54)
    {st : List Digest × List Digest} {u : MachineState} (hu : FStT s0 A coefs j st u) :
    TBSim Sign.image sk u topChainC (topStepT A.leaf A.digits coefs st j) (FStT s0 A coefs (j + 1)) := by
  have hsub := Sign.SeedIndependent.seedIndependentAt_sign
  have hn : A.n = 54 := by show chainCount A.lay = 54; rw [hlay]; rfl
  obtain ⟨s, hs, hinv⟩ := hu.inv
  have g : ∀ r, r ∉ leafRegs → u.getReg r = s0.getReg r := fun r hr => by rw [hinv.regs.get hr, hs.regs]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := Sign.Seed.sub41_spec hsub u hu.pc j A.n (by omega) (by omega) hinv.x19
    (by rw [g _ (by simp [leafRegs]), hpre.x26])
  rw [if_pos (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := ClaudeWCT.W9.Machine.Sign.PackedLeaf.hook_spec t1 (by rw [t1pc])
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := ClaudeWCT.W9.Machine.Sign.PackedLeaf.top_spec t2 t2pc
    (by rw [t2r.get (by simp), t1r.get (by simp), g _ (by simp [leafRegs]), hpre.x8, hlay]; rfl)
  obtain ⟨t4, st4, t4pc, t4x1, t4r, t4f⟩ := tsJal_spec t3 t3pc
  have e14 : RegsExcept u t4 [.x1] := (((t1r.trans t2r).trans t3r).trans t4r).mono (by simp)
  have f14 : Frame u t4 (fun _ => False) := (((t1f.trans t2f).trans t3f).trans t4f).mono (fun _ _ h => by simp_all)
  obtain ⟨w, n, sw, hnw, wpc, wseed, wr, wf⟩ := horn_run t4 t4pc (i := j) (by omega)
    (by rw [e14.get (by simp)]; exact hinv.x19) hlen (hu.coef.frame f14 (fun _ _ _ h => h))
  obtain ⟨w2, sw2, w2pc, w2r, w2f⟩ := tsJ_spec w (by rw [wpc, t4x1, pcOf_and_not1])
  have hs' : HybOfT s0 (hybT s0 w2) w2 := hybT_of s0 w2
  have hinvw : LeafInv (hybT s0 w2) A j st w2 := LeafInv.rebaseT hinv hs hs' ((e14.trans wr).trans w2r) (by
      intro r hr
      simp only [List.nil_append, List.cons_append, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    ((f14.trans wf).trans w2f) (fun X h => by
      unfold SeedWT TScr SaveW TSAVE TCOEF at *
      simp only [CHAIN, PRIV, SEEDS, false_or, or_false] at *
      omega)
    hpre.hvs hvS (by omega)
  have hpre' : LeafPreS sk (hybT s0 w2) A := LeafPreS.transferT hpre hs'.regs hs'.base hdS
  have hseed : DigAt w2 (CHAIN + 48) (familyEval coefs (j + 1)) := wseed.frame w2f (by decide) (by simp) (by simp)
  have hit := leaf_iter71 sk hpre' hso (j := j) (by omega) hinvw (by rw [w2pc]) _ hseed
  have hk : 11 + selectorExtra A.lay j + (rungK A.lay * A.e j + 10) ≤
      11 + selectorExtra A.lay j + (rungC A.lay * A.e j + 10) := by
    have h1 : rungK A.lay ≤ rungC A.lay := by unfold rungK rungC; omega
    have := Nat.mul_le_mul_right (A.e j) h1
    omega
  have hc : 11 + selectorExtra A.lay j + (rungC A.lay * A.e j + 10) ≤ 320 := by
    have he : A.e j ≤ 7 := by unfold LeafArgs.e; rw [hso, if_pos rfl]; exact hd7 j (by omega)
    have hsel : selectorExtra A.lay j ≤ 5 := by unfold selectorExtra; split_ifs <;> omega
    have hr : rungC A.lay = 42 := by rw [hlay]; rfl
    rw [hr]
    have := Nat.mul_le_mul_left 42 he
    omega
  rw [topStep_eq hlay hso htree]
  refine TBSim.mono (TBSim.steps (((((st1.trans st2).trans st3).trans st4).trans sw).trans sw2)
    ((hit.toTBSim hk).mono hc (fun st' x hx => ?_))) (by unfold topChainC; omega) (fun _ _ h => h)
  obtain ⟨xpc, hxinv, hxf⟩ := hx
  have hxs : ∀ X, X < 2 ^ 64 → TScr X → x.getMem (BitVec.ofNat 64 X) = w2.getMem (BitVec.ofNat 64 X) :=
    fun X hX hb => (hxinv.frame.get hX (fun hl => LeafW_not_tscr hvS hdestS hl hb)).trans (hs'.scr X hX hb)
  refine ⟨xpc, fun k hk => ?_, ⟨hybT s0 w2, ⟨hs'.regs, hs'.base,
    fun X hX hb => (hs'.scr X hX hb).trans (hxs X hX hb).symm⟩, hxinv⟩⟩
  have hwk : DigAt w2 (TCOEF + 16 * k) (coefs.getD k 0) :=
    ((hu.coef k hk).frame (f14.trans wf) (by unfold TCOEF; omega)
      (by simp only [SaveW, TSAVE, TCOEF, CHAIN, false_or, not_or]; omega)
      (by simp only [SaveW, TSAVE, TCOEF, CHAIN, false_or, not_or]; omega)).frame w2f (by unfold TCOEF; omega)
      (by simp) (by simp)
  exact ⟨by rw [hxs _ (by unfold TCOEF; omega) (by unfold TScr TSAVE TCOEF; omega)]; exact hwk.1,
    by rw [hxs _ (by unfold TCOEF; omega) (by unfold TScr TSAVE TCOEF; omega)]; exact hwk.2⟩

end chain

/-! ### The top leaf -/

theorem buildLeafTop_so (leaf : Nat) (digits : List Nat) :
    SigGolfCandidate.T3.buildLeafTop leaf digits true = (SigGolfCandidate.T3.topCoefs leaf >>= fun coefs =>
      (List.range' 0 54).foldlM (topStepT leaf digits coefs) ([], []) >>= fun st => pure (0, st.2)) := by
  rw [← List.range_eq_range']
  rfl

theorem topLeafSpec : SigGolfCandidate.T3M.Sign.Packed.TopLeafSpec := by
  intro sk A s0 hlay hso htree hd7 hvS hdS hdestS hpre hpc
  have hsub := Sign.SeedIndependent.seedIndependentAt_sign
  have hn : A.n = 54 := by show chainCount A.lay = 54; rw [hlay]; rfl
  have hP : PRIV = 131072 := rfl
  have hS : SEEDS = 131136 := rfl
  have hL : LEAFPK = 132608 := rfl
  have hC : CHAIN = 131488 := rfl
  have hleaf : A.leaf < 4096 := by have := hpre.hleafHeight; rw [hlay] at this; exact this
  obtain ⟨t1, st1, t1pc, t1x3, t1l16, t1l24, t1r, t1f⟩ :=
    Sign.Seed.sub27_pre_spec hsub s0 hpc A.lay A.tree A.leaf (by have := hpre.hroute; omega) hpre.x8 hpre.x9
      hpre.x18 (Or.inl htree)
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := pre0_spec t1 t1pc (by rw [t1r.get (by decide), hpre.x8, hlay]; rfl)
  obtain ⟨t3, st3, t3pc, t3x1, t3r, t3f⟩ := jal_spec t2 t2pc
  have e13 : RegsExcept s0 t3 [.x3, .x6, .x28, .x30, .x1] := ((t1r.trans t2r).trans t3r).mono (by simp)
  have f13 : Frame s0 t3 (fun A => A = LEAFPK + 16 ∨ A = LEAFPK + 24) :=
    ((t1f.trans t2f).trans t3f).mono (fun X _ h => by simp_all)
  have hsk : SkAt sk t3 := ⟨by rw [f13.get (by decide) (by simp only [LEAFPK, PRIV]; omega)]; exact hpre.p0,
    by rw [f13.get (by decide) (by simp only [LEAFPK, PRIV]; omega)]; exact hpre.p8,
    by rw [f13.get (by decide) (by simp only [LEAFPK, PRIV]; omega)]; exact hpre.p32,
    by rw [f13.get (by decide) (by simp only [LEAFPK, PRIV]; omega)]; exact hpre.p40,
    by rw [f13.get (by decide) (by simp only [LEAFPK, PRIV]; omega)]; exact hpre.p48,
    by rw [f13.get (by decide) (by simp only [LEAFPK, PRIV]; omega)]; exact hpre.p56⟩
  have hcg := coefgen_tbsim sk t3 t3pc t3x1 hleaf (by rw [e13.get (by decide), hpre.x18])
    (by rw [e13.get (by decide), hpre.x5]) hsk
  rw [hso, buildLeafTop_so]
  refine TBSim.mono (TBSim.steps ((st1.trans st2).trans st3) (TBSim.bind
    (W₂ := 2 + (54 * topChainC + 3)) hcg (fun coefs u hu => ?_))) (by
      unfold SigGolfCandidate.T3M.Sign.Packed.topLeafC cgC cgStepC topChainC hornCT hstepC; omega) (fun _ _ h => h)
  obtain ⟨upc, ulen, ucoef, u19, ur, uf⟩ := hu
  obtain ⟨v1, sv1, v1pc, v1r, v1f⟩ := j1053_spec u upc
  obtain ⟨v, sv, vpc, v19, vr, vf⟩ := li19_spec v1 v1pc
  have euv : RegsExcept s0 v ([.x3, .x6, .x28, .x30, .x1] ++ [.x10, .x11, .x12, .x19, .x29, .x30] ++ [] ++ [.x19]) :=
    ((e13.trans ur).trans v1r).trans vr
  have fuv : Frame s0 v (fun X => (((X = LEAFPK + 16 ∨ X = LEAFPK + 24) ∨ CgW X) ∨ False) ∨ False) :=
    ((f13.trans uf).trans v1f).trans vf
  have hs1 : HybOfT s0 (hybT s0 v) v := hybT_of s0 v
  have h0 : LeafInv (hybT s0 v) A 0 ([], []) v := by
    refine ⟨v19, ?_, ?_, fun r hr => ?_, fun X hX hn' => ?_, ?_, ?_, by simp [hso], rfl,
      fun h => absurd h (by rw [hso]; decide), DigsAt.nil _ _⟩
    · rw [euv.get (by simp), hpre.x23]; simp
    · rw [vr.get (by decide), v1r.get (by decide), ur.get (by decide), t3r.get (by decide), t2r.get (by decide),
        t1x3, hpre.x1]
    · rw [euv.get (fun h => hr (by simp [leafRegs] at h ⊢; rcases h with h | h | h | h | h | h | h | h | h | h | h | h <;>
        simp [h])), hs1.regs]
    · by_cases hb : TScr X
      · rw [hs1.scr X hX hb]
      · have hW : ¬ ((((X = LEAFPK + 16 ∨ X = LEAFPK + 24) ∨ CgW X) ∨ False) ∨ False) := by
          intro h
          apply hn'
          unfold LeafW; rw [if_pos hlay, hn]
          rcases h with (((h | h) | h) | h) | h
          · right; right; right; right; right; right; left; omega
          · right; right; right; right; right; right; left; omega
          · unfold CgW at h
            rcases h with h | h | h | h | h
            · left; exact h
            · right; left; exact h
            · right; right; left; exact h
            · exact absurd (by unfold TScr TSAVE TCOEF; unfold CgSaveW TSAVE at h; omega) hb
            · exact absurd (by unfold TScr TSAVE TCOEF; unfold TCOEF at h; omega) hb
          · exact h.elim
          · exact h.elim
        rw [fuv.get hX hW, hs1.base.get hX hb]
    · rw [vf.get (by decide) (by simp), v1f.get (by decide) (by simp),
        uf.get (by decide) (by unfold CgW CgSaveW TSAVE TCOEF; simp only [PRIV, SEEDS, LEAFPK]; omega),
        t3f.get (by decide) (by simp), t2f.get (by decide) (by simp), t1l16]
    · rw [vf.get (by decide) (by simp), v1f.get (by decide) (by simp),
        uf.get (by decide) (by unfold CgW CgSaveW TSAVE TCOEF; simp only [PRIV, SEEDS, LEAFPK]; omega),
        t3f.get (by decide) (by simp), t2f.get (by decide) (by simp), t1l24]
  have hF0 : FStT s0 A coefs 0 ([], []) v := ⟨vpc, (ucoef.frame v1f (fun _ _ _ h => h)).frame vf (fun _ _ _ h => h),
    ⟨_, hs1, h0⟩⟩
  have hfold := TBSim.foldlM_range' (image := Sign.image) (sk := sk) 0 54
    (topStepT A.leaf A.digits coefs) ([], []) (FStT s0 A coefs) topChainC
    (fun j hj st x hx => by simpa using top_chain_step sk hpre hlay hso htree hd7 hvS hdS hdestS ulen hj hx) hF0
  refine TBSim.steps (sv1.trans sv) (TBSim.bind (W₁ := 54 * topChainC) (W₂ := 3) hfold (fun rows x hx => ?_))
  obtain ⟨xpc, -, ⟨s3, hs3, hinv3⟩⟩ := hx
  have hpre3 := LeafPreS.transferT hpre hs3.regs hs3.base hdS
  rw [show (54 : Nat) = A.n from hn.symm] at hinv3
  have hex := Sign.Seed.leaf_exitS hsub sk hpre3 hinv3 xpc
  simp only [hso, if_true] at hex
  refine TBSim.mono ((hex.toTBSim (by norm_num)).mono le_rfl (fun r y hy => ?_)) le_rfl (fun _ _ h => h)
  obtain ⟨ypc, -, yvals, ylen, -, yregs, yframe, -⟩ := hy
  refine ⟨ypc, yvals, ylen, fun r hr => by rw [yregs.get hr, hs3.regs], fun X hX hn' => ?_⟩
  have hl : ¬ LeafW A X := fun h => hn' (Or.inl h)
  have ht : ¬ TScr X := fun h => hn' (Or.inr ((tscr_iff X).mp h))
  rw [yframe.get hX hl, hs3.base.get hX ht]

end ClaudeWCT.W9.Machine.Sign.TopLeafP