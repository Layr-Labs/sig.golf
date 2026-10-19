import SigGolfCandidate.T3M_Sign_Basic
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_HornRun
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_PackedHelper
set_option Elab.async false

/-!
# Stage B (campaign X1): the lower-leaf seed code of the sign image

Lower leaves (`lay ≠ 0`) reach the hook `1055 → 20746` once per chain (`x19 = j`):
* `20746 beq s0` (top layer, unchanged), `20747 beq s3,zero` — chain `j ≥ 1` jumps to `SEED` (`D1`);
* chain 0 runs the coefficient prologue `20749..20767` (`D0`: `p = COEF`; the B4 parity mask is zero,
  so no initial carry is copied; `x6` = header word of pair `8 L / 2`), the head
  `CQ0 = 11513` (T8: dead tail of FTS segment (0,2), coordinate-0 code; `C0`: `x17 = 2^32`, `x30 = COEF + 128`) and
  the query loop `CQ` (`CQ`: `PRIV + 16 = x6`, `PRIV + 24 = tree`,
  ecall `64 B @ PRIV → SEEDS`; `CP`: copy `SEEDS[0,32)` to `p`, `p += 32`, `x6 += 2^32`, loop while
  `p < COEF + 128`, else `j SEED`);
* `SEED = 12272` (T8: dead tail of FTS segment (1,0), coordinate-1 code; `SP`): spill `x13..x16` to `COEF + 288`,
  `x6 = j + 1`, `x7 = COEF + 128`, `x10 = x11 = 0`, `jal ra,HK` (T8's Horner loop `hkI = 11220` over 8 coefficients);
  `RET = 12283` (`SR`): restore `x13..x16`, copy `CHAINW + 48` to `SEEDS`, `x28 = 0`, `j 1074` (the unchanged chain
  code).
-/

section
set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
open Gf ClaudeWCT.Arith
macro "aoc" : tactic => `(tactic| ((try simp only [COEF, CHAINW, PRIVW, SCREND] at *) <;> omega))

def presKC (regs : List (Reg × E)) (mem : SymMem) (obl : List Oblig) (pc : Nat) (ec : Bool) (k c : Nat)
    (brs : List Br) : PRes :=
  ⟨⟨regsOf regs, mem, obl⟩, pcOf pc, ec, k, c, brs, none⟩
def seedI : Nat := 12272
def retI : Nat := 12283
def cq0I : Nat := 11513
def cqI : Nat := 11517
def cqeI : Nat := 11523
def x28A (off : Nat) : Addr := ⟨some (.reg .x28), BitVec.ofNat 64 off⟩
def ld28 (off : Nat) : E := .ld (.bin .add (.reg .x28) (cE off))
def par18 : E := .bin .and (.reg .x18) (cE 0)
def hdrBE : E :=
  .bin .or (.bin .or (.bin .sll (.bin .srl (.bin .add (.bin .mul (.reg .x18) (cE 8)) par18) (cE 1)) (cE 32))
    (.bin .sll (.reg .x8) (cE 16))) (cE 1)
def expD1 : PRes := pres [] [] [] seedI false 3 [⟨.eq, .reg .x19, cE 0, false⟩, ⟨.eq, .reg .x8, cE 0, false⟩]
def expD0 (even : Bool) : PRes :=
  if even then
    presKC [(.x6, hdrBE), (.x7, par18), (.x10, .bin .sll (.reg .x8) (cE 16)), (.x29, cE COEF)] [] [] cq0I false 15 18
      [⟨.eq, par18, cE 0, true⟩, ⟨.eq, .reg .x19, cE 0, true⟩, ⟨.eq, .reg .x8, cE 0, false⟩]
  else
    presKC [(.x6, hdrBE), (.x7, par18), (.x10, .bin .sll (.reg .x8) (cE 16)), (.x11, ldc (0x20040 + 24)),
      (.x28, cE 0x20000), (.x29, cE (COEF + 16))] [mwc (COEF + 8) (ldc (0x20040 + 24)), mwc COEF (ldc (0x20040 + 16))]
      [] cq0I false 21 24 [⟨.eq, par18, cE 0, false⟩, ⟨.eq, .reg .x19, cE 0, true⟩, ⟨.eq, .reg .x8, cE 0, false⟩]
def expC0 : PRes := pres [(.x17, cE (2 ^ 32)), (.x30, cE (COEF + 128))] [] [] cqI false 4 []
def expCQ : PRes :=
  pres [(.x10, cE 0x20000), (.x11, cE 64), (.x12, cE 0x20040), (.x28, cE 0x20000)]
    [mwc 0x20018 (.reg .x9), mwc 0x20010 (.reg .x6)] [] cqeI true 6 []
def expCP (back : Bool) : PRes :=
  pres [(.x6, .bin .add (.reg .x6) (.reg .x17)), (.x7, ld28 88), (.x10, ld28 64), (.x11, ld28 72), (.x12, ld28 80),
      (.x29, .bin .add (.reg .x29) (cE 32))]
    [(x29A 24, ld28 88), (x29A 16, ld28 80), (x29A 8, ld28 72), (x29A 0, ld28 64)]
    [.valid (x29A 24) 8, .valid (x29A 16) 8, .valid (x29A 8) 8, .valid (x29A 0) 8, .valid (x28A 88) 8,
      .valid (x28A 80) 8, .valid (x28A 72) 8, .valid (x28A 64) 8]
    (if back then cqI else seedI) false (if back then 11 else 12)
    [⟨.ltu, .bin .add (.reg .x29) (cE 32), .reg .x30, back⟩]
def expSP : PRes :=
  pres [(.x1, cE (0x1000 + 4 * retI)), (.x6, .bin .add (.reg .x19) (cE 1)), (.x7, cE (COEF + 128)), (.x10, cE 0),
      (.x11, cE 0), (.x28, cE COEF)]
    [mwc (COEF + 312) (.reg .x16), mwc (COEF + 304) (.reg .x15), mwc (COEF + 296) (.reg .x14),
      mwc (COEF + 288) (.reg .x13)] [] hkI false 11 []
def expSR : PRes :=
  pres [(.x6, ldc (CHAINW + 48)), (.x7, ldc (CHAINW + 56)), (.x13, ldc (COEF + 288)), (.x14, ldc (COEF + 296)),
      (.x15, ldc (COEF + 304)), (.x16, ldc (COEF + 312)), (.x28, cE 0)]
    [mwc 0x20048 (ldc (CHAINW + 56)), mwc 0x20040 (ldc (CHAINW + 48))] [] 1074 false 13 []
def runD1 : Option PRes := run tailLook [seedI] 20746 [.br false, .br false]
def runD0 (even : Bool) : Option PRes := run tailLook [cq0I] 20746 [.br false, .br true, .br even]
def runC0 : Option PRes := run (coordLook 0) [cqI] cq0I []
def runCQ : Option PRes := run (coordLook 0) [] cqI []
def runCP (back : Bool) : Option PRes := run (coordLook 0) [cqI, seedI] (cqeI + 1) [.br back]
def runSP : Option PRes := run (coordLook 1) [hkI] seedI []
def runSR : Option PRes := run (coordLook 1) [1074] retI []
def okLower : Bool :=
  optBeq runD1 expD1 && optBeq (runD0 true) (expD0 true) && optBeq (runD0 false) (expD0 false) &&
    optBeq runC0 expC0 && optBeq runCQ expCQ && optBeq (runCP true) (expCP true) &&
    optBeq (runCP false) (expCP false) && optBeq runSP expSP && optBeq runSR expSR
/-! The legacy (pre-v6, per-leaf 8-coefficient) reference-image lower-seed run was removed: the reference chunks now
carry the v6 seed words; the live lower-seed proofs are in `SharedSeed` below. -/

/-- The header word of lower seed pair `pair` (tag 0, index 0) for `tree < 2^32`. -/
def hdrB (lay pair : Nat) : Nat := 1 + 65536 * lay + 2 ^ 32 * pair

/-- Cycle bound of one v6 lower seed (SEED spills + `qp` + `jal HK`: 19 steps, 25 cycles; at most 38 Horner steps; RET). -/
def lowerSeedC : Nat := 25 + (hornStepC * 38 + 5) + 13

theorem familyEval_nil (d : Nat) : familyEval [] d = 0 := rfl


end ClaudeWCT.W9.Machine.Sign
end

namespace ClaudeWCT.W9.Machine.Sign.SharedSeed
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
open Gf ClaudeWCT.Arith
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def block0 : List (BitVec 32) := (coordCodeW0.drop 1).take 887
def block1 : List (BitVec 32) := (coordCodeW1.drop 1).take 893
/-- v6 sign words `20746..20770` (literal: the reference chunk still holds the pre-v6 prologue `20749..`). -/
def blockTail : List (BitVec 32) := [0x04040e63,0x00098463,0xb91f706f,0x7690306f,0x800e8e93,0x00097393,0x00038e63,
  0x00020e37,0x050e3503,0x058e3583,0x00aeb023,0x00beb423,0x010e8e93,0x00800313,0x02690333,0x00730333,0x00135313,
  0x02031313,0x01041513,0x00a36333,0x00136313,0xf69f606f,0x00000013,0xbd0ed06f,0xbf9ec06f]
/-- v6 sign words `24807..24850`: the lower family prologue `qd` (`24807..24842`) and the seed point `qp`
(`24843..24850`). -/
def blockQ : List (BitVec 32) := [0x00700313,0x026973b3,0x08039263,0x02695533,0x026503b3,0x04000e93,0x00100f13,
  0x01e41463,0x08000e93,0x407e8eb3,0x006ee463,0x00700e93,0x002e9f13,0x01df0f33,0x003f0f13,0x00051e37,0x800e0e13,
  0x004f1393,0x01c383b3,0x36038393,0x5c7e3823,0x001f0f13,0x001f5f13,0x005f1f13,0x360e0e93,0x01df0f33,0x01300313,
  0x02650333,0x02031313,0x01041513,0x00a36333,0x00136313,0x00100893,0x02089893,0xfd1f206f,0xb99f306f,0x00700313,
  0x026976b3,0x02b00713,0x02e686b3,0x01368333,0x00130313,0x360e0e13,0xb99f306f]
def piece (base : Nat) (code : List (BitVec 32)) (n : Nat) := if base ≤ n then code[n-base]? else none
def coordLook (c : Nat) := if c=0 then piece 11187 block0 else piece 12239 block1
def tailLook := piece 20746 blockTail
def qLook := piece 24807 blockQ
/-- SEED (`12272..`, coordinate-1 code) with the appended `qp` (`24843..`). -/
def seedLook (n : Nat) : Option (BitVec 32) := if 24807 ≤ n then piece 24807 blockQ n else piece 12239 block1 n
structure Code (im : Image) : Prop where
  c0 : CodeAt im (pcOf 11187) block0
  c1 : CodeAt im (pcOf 12239) block1
  tail : CodeAt im (pcOf 20746) blockTail
  q : CodeAt im (pcOf 24807) blockQ

theorem coordLook_ok {im : Image} (h : Code im) {c : Nat} (_hc : c<9) : LookOK im (coordLook c) := by
  unfold coordLook
  split
  · exact PackedLeaf.lookOK_of_codeAt h.c0 (by decide +kernel)
  · exact PackedLeaf.lookOK_of_codeAt h.c1 (by decide +kernel)
theorem tailLook_ok {im : Image} (h : Code im) : LookOK im tailLook :=
  PackedLeaf.lookOK_of_codeAt h.tail (by decide +kernel)
theorem qLook_ok {im : Image} (h : Code im) : LookOK im qLook :=
  PackedLeaf.lookOK_of_codeAt h.q (by decide +kernel)
theorem seedLook_ok {im : Image} (h : Code im) : LookOK im seedLook := by
  intro n w hw
  unfold seedLook at hw
  split at hw
  · exact qLook_ok h n w hw
  · exact PackedLeaf.lookOK_of_codeAt h.c1 (by decide +kernel) n w hw

def runH0 : Option PRes := run (coordLook 0) [hkI] hornI []
def runHK : Option PRes := run (coordLook 0) [hbI] hkI []
def runHB (b1 b2 : Bool) : Option PRes := run (coordLook 0) [hbI, hfI] hbI [.br b1, .br b2]
def runHF (b : Bool) : Option PRes := run (coordLook 0) [hkI] hfI (if b then [.br true] else [.br false, .jmp])
theorem runH0_eq : runH0 = some expH0 := by apply optBeq_eq; decide +kernel
theorem runHK_eq : runHK = some expHK := by apply optBeq_eq; decide +kernel
theorem runHB_eq (b1 b2 : Bool) : runHB b1 b2 = some (expHB b1 b2) := by cases b1 <;> cases b2 <;> apply optBeq_eq <;> decide +kernel
theorem runHF_eq (b : Bool) : runHF b = some (expHF b) := by cases b <;> apply optBeq_eq <;> decide +kernel
/-- Registers HORN may change. -/
def hornRegs : List Reg := [.x7, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x28, .x29]
/-- The coefficient buffer. -/
def CoefAt (t : MachineState) (coefs : List Digest) : Prop :=
  ∀ k < 54, DigAt t (COEF + 16 * k) (coefs.getD k 0)

theorem CoefAt.frame {s t : MachineState} {coefs : List Digest} {W : Nat → Prop} (h : CoefAt s coefs)
    (hf : Frame s t W) (hW : ∀ A, COEF ≤ A → A < COEF + 864 → ¬ W A) : CoefAt t coefs :=
  fun k hk => (h k hk).frame hf (by unfold COEF; omega) (hW _ (by omega) (by omega)) (hW _ (by omega) (by omega))

section steps
variable {im : Image}

theorem horn_look (hcode : Code im) : LookOK im (coordLook 0) := coordLook_ok hcode (c := 0) (by norm_num)

theorem step_H0 (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf hornI) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf hkI ∧ t.getReg .x7 = BitVec.ofNat 64 (COEF + 16 * 54) ∧
      t.getReg .x10 = BitVec.ofNat 64 0 ∧ t.getReg .x11 = BitVec.ofNat 64 0 ∧
      t.getReg .x28 = BitVec.ofNat 64 COEF ∧ RegsExcept s t [.x7, .x10, .x11, .x28] ∧
      Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (horn_look hcode) runH0_eq s hpc (no_obl s) (no_br s)
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩

theorem step_HK (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf hkI) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf hbI ∧
      t.getReg .x7 = s.getReg .x7 + BitVec.ofNat 64 (2 ^ 64 - 16) ∧ t.getReg .x12 = BitVec.ofNat 64 0 ∧
      t.getReg .x13 = BitVec.ofNat 64 0 ∧ t.getReg .x14 = BitVec.ofNat 64 0 ∧ t.getReg .x15 = BitVec.ofNat 64 0 ∧
      t.getReg .x16 = s.getReg .x6 ∧ RegsExcept s t [.x7, .x12, .x13, .x14, .x15, .x16] ∧
      Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (horn_look hcode) runHK_eq s hpc (no_obl s) (no_br s)
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩

/-- Cycles of one bit iteration (`b1`: the bit is zero, `b2`: more bits follow). -/
def hbRegs : List Reg := [.x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]
def hbK (b1 b2 : Bool) : Nat := (if b1 then 11 else 14) + (if b2 then 0 else 1)

theorem step_HB (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf hbI) (b1 b2 : Bool)
    (h1 : (s.getReg .x16 &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0) = b1)
    (h2 : (s.getReg .x16 >>> 1 != BitVec.ofNat 64 0) = b2) :
    ∃ t, Steps im s (hbK b1 b2) (hbK b1 b2) t ∧ t.pc = pcOf (if b2 then hbI else hfI) ∧
      t.getReg .x10 = s.getReg .x10 <<< 1 ∧
      t.getReg .x11 = (s.getReg .x11 <<< 1) ||| (s.getReg .x10 >>> 63) ∧
      t.getReg .x12 = (s.getReg .x12 <<< 1) ||| (s.getReg .x11 >>> 63) ∧
      t.getReg .x13 = (if b1 then s.getReg .x13 else s.getReg .x13 ^^^ s.getReg .x10) ∧
      t.getReg .x14 = (if b1 then s.getReg .x14 else s.getReg .x14 ^^^ s.getReg .x11) ∧
      t.getReg .x15 = (if b1 then s.getReg .x15 else s.getReg .x15 ^^^ s.getReg .x12) ∧
      t.getReg .x16 = s.getReg .x16 >>> 1 ∧ RegsExcept s t hbRegs ∧ Frame s t (fun _ => False) := by
  have hbr : ∀ b ∈ (expHB b1 b2).brs, b.holds s := by
    intro b hb
    simp only [expHB, pres, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · show (BinOp.eval .srl (s.getReg .x16) (BitVec.ofNat 64 1) != BitVec.ofNat 64 0) = b2
      rw [binop_srl _ _ (by norm_num)]; exact h2
    · exact h1
  obtain ⟨hst, -⟩ := run_pres (horn_look hcode) (runHB_eq b1 b2) s hpc (no_obl s) hbr
  have e10 : ((expHB b1 b2).toState s).getReg .x10 = s.getReg .x10 <<< 1 := by
    rw [PRes.toState_getReg']; cases b1 <;> exact binop_sll _ 1 (by norm_num)
  have e11 : ((expHB b1 b2).toState s).getReg .x11 = (s.getReg .x11 <<< 1) ||| (s.getReg .x10 >>> 63) := by
    rw [PRes.toState_getReg']
    cases b1 <;>
    · show BinOp.eval .or (BinOp.eval .sll (s.getReg .x11) (BitVec.ofNat 64 1))
        (BinOp.eval .srl (s.getReg .x10) (BitVec.ofNat 64 63)) = _
      rw [binop_sll _ _ (by norm_num), binop_srl _ _ (by norm_num)]; rfl
  have e12 : ((expHB b1 b2).toState s).getReg .x12 = (s.getReg .x12 <<< 1) ||| (s.getReg .x11 >>> 63) := by
    rw [PRes.toState_getReg']
    cases b1 <;>
    · show BinOp.eval .or (BinOp.eval .sll (s.getReg .x12) (BitVec.ofNat 64 1))
        (BinOp.eval .srl (s.getReg .x11) (BitVec.ofNat 64 63)) = _
      rw [binop_sll _ _ (by norm_num), binop_srl _ _ (by norm_num)]; rfl
  have e16 : ((expHB b1 b2).toState s).getReg .x16 = s.getReg .x16 >>> 1 := by
    rw [PRes.toState_getReg']; cases b1 <;> exact binop_srl _ 1 (by norm_num)
  refine ⟨_, hst, ?_, e10, e11, e12, ?_, ?_, ?_, e16, (pres_regsExcept _ _ _ _ _ _ _ s).mono ?_, fun A _ _ => rfl⟩
  · cases b2 <;> rfl
  · rw [PRes.toState_getReg']; cases b1 <;> rfl
  · rw [PRes.toState_getReg']; cases b1 <;> rfl
  · rw [PRes.toState_getReg']; cases b1 <;> rfl
  · cases b1 <;> simp [hbShift, hbRegs]

theorem eval_foldE (s : MachineState) : foldE.eval s = foldLo (s.getReg .x13) (s.getReg .x15) := by
  show BinOp.eval .xor (BinOp.eval .xor (BinOp.eval .xor (BinOp.eval .xor (s.getReg .x13)
    (BinOp.eval .sll (s.getReg .x15) (BitVec.ofNat 64 1))) (BinOp.eval .sll (s.getReg .x15) (BitVec.ofNat 64 2)))
    (BinOp.eval .sll (s.getReg .x15) (BitVec.ofNat 64 7))) (s.getReg .x15) = _
  rw [binop_sll _ _ (by norm_num), binop_sll _ _ (by norm_num), binop_sll _ _ (by norm_num)]
  rfl

theorem eval_c0E (s : MachineState) {A : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 A) :
    c0E.eval s = s.getMem (BitVec.ofNat 64 A) := by
  show s.getMem (s.getReg .x7) = _; rw [h7]

theorem eval_c1E (s : MachineState) {A : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 A) :
    c1E.eval s = s.getMem (BitVec.ofNat 64 (A + 8)) := by
  show s.getMem (s.getReg .x7 + BitVec.ofNat 64 8) = _; rw [h7, ofNat_add_ofNat]

theorem hfObl_holds (s : MachineState) {A : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA' : A + 16 ≤ MEMORY_BYTES) : ∀ o ∈ hfObl, o.holds s := by
  intro o ho
  simp only [hfObl, List.mem_cons, List.not_mem_nil, or_false] at ho
  have hb : (E.reg .x7).eval s = BitVec.ofNat 64 A := h7
  rcases ho with rfl | rfl
  · exact valid_ofNat hb (by omega) (by omega)
  · exact valid_ofNat (off := 0) hb (by omega) (by omega)

theorem step_HF_cont (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf hfI) {A : Nat}
    (h7 : s.getReg .x7 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 16 ≤ MEMORY_BYTES)
    (hne : s.getReg .x7 ≠ s.getReg .x28) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf hkI ∧
      t.getReg .x10 = foldLo (s.getReg .x13) (s.getReg .x15) ^^^ s.getMem (BitVec.ofNat 64 A) ∧
      t.getReg .x11 = s.getReg .x14 ^^^ s.getMem (BitVec.ofNat 64 (A + 8)) ∧
      RegsExcept s t hfRegs.unzip.1 ∧ Frame s t (fun _ => False) := by
  have hbr : ∀ b ∈ (expHF true).brs, b.holds s := by
    intro b hb
    simp only [expHF, if_true, pres, List.mem_singleton] at hb
    subst hb
    show (s.getReg .x7 != s.getReg .x28) = true
    simpa using hne
  have hobl : ∀ o ∈ (expHF true).st.obl, o.holds s := hfObl_holds s h7 hA hA'
  obtain ⟨hst, -⟩ := run_pres (horn_look hcode) (runHF_eq true) s hpc hobl hbr
  refine ⟨_, hst, rfl, ?_, ?_, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [hfRegs]), fun A _ _ => rfl⟩
  · rw [pres_getReg]
    show BinOp.eval .xor (foldE.eval s) (c0E.eval s) = _
    rw [eval_foldE, eval_c0E s h7]; rfl
  · rw [pres_getReg]
    show BinOp.eval .xor (s.getReg .x14) (c1E.eval s) = _
    rw [eval_c1E s h7]; rfl

theorem step_HF_exit (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf hfI) {A : Nat}
    (h7 : s.getReg .x7 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 16 ≤ MEMORY_BYTES)
    (heq : s.getReg .x7 = s.getReg .x28) :
    ∃ t, Steps im s 17 17 t ∧ t.pc = s.getReg .x1 &&& BitVec.ofNat 64 (2 ^ 64 - 2) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 48)) =
        foldLo (s.getReg .x13) (s.getReg .x15) ^^^ s.getMem (BitVec.ofNat 64 A) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 56)) = s.getReg .x14 ^^^ s.getMem (BitVec.ofNat 64 (A + 8)) ∧
      RegsExcept s t (.x29 :: hfRegs.unzip.1) ∧ Frame s t (fun B => B = CHAINW + 48 ∨ B = CHAINW + 56) := by
  have hbr : ∀ b ∈ (expHF false).brs, b.holds s := by
    intro b hb
    simp only [expHF, Bool.false_eq_true, if_false, List.mem_singleton] at hb
    subst hb
    show (s.getReg .x7 != s.getReg .x28) = false
    simp [heq]
  have hobl : ∀ o ∈ (expHF false).st.obl, o.holds s := hfObl_holds s h7 hA hA'
  obtain ⟨hst, -⟩ := run_sound (horn_look hcode) (runHF_eq false) s hpc hobl hbr
  have hm : ∀ a, ((expHF false).toState s).getMem a =
      memEval s [mwc (CHAINW + 56) (.bin .xor (.reg .x14) c1E), mwc (CHAINW + 48) (.bin .xor foldE c0E)] a :=
    fun a => rfl
  refine ⟨_, hst, rfl, ?_, ?_, fun x hx => ?_, frame_of_memEval hm _ (fun p hp => ?_)⟩
  · rw [hm, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
    show BinOp.eval .xor (foldE.eval s) (c0E.eval s) = _
    rw [eval_foldE, eval_c0E s h7]; rfl
  · rw [hm, memEval_mwc_self _ _ _ _ (by ao)]
    show BinOp.eval .xor (s.getReg .x14) (c1E.eval s) = _
    rw [eval_c1E s h7]; rfl
  · rw [PRes.toState_getReg']
    show ((regsOf (hfRegs ++ [(.x29, cE CHAINW)])).get x).eval s = _
    rw [regsOf_get_ne _ _ (fun p hp he => hx (by
      simp only [hfRegs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> (subst he; simp [hfRegs]))), RegFile.init_get_eval]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> simp
end steps

section loops
variable {im : Image}

structure HbSt (t0 : MachineState) (d a k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf hbI
  sh : lim3 (t.getReg .x10) (t.getReg .x11) (t.getReg .x12) = a * 2 ^ k
  pr : lim3 (t.getReg .x13) (t.getReg .x14) (t.getReg .x15) = clmulSmall a d k
  dd : t.getReg .x16 = BitVec.ofNat 64 (d / 2 ^ k)
  regs : RegsExcept t0 t hbRegs
  frame : Frame t0 t (fun _ => False)

structure HfSt (t0 : MachineState) (d a : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf hfI
  pr : lim3 (t.getReg .x13) (t.getReg .x14) (t.getReg .x15) = clmulSmall a d 10
  regs : RegsExcept t0 t hbRegs
  frame : Frame t0 t (fun _ => False)

theorem lim3_ite (b : Bool) (a0 a1 a2 x0 x1 x2 : BitVec 64) :
    lim3 (if b then a0 else a0 ^^^ x0) (if b then a1 else a1 ^^^ x1) (if b then a2 else a2 ^^^ x2) =
      if b then lim3 a0 a1 a2 else lim3 a0 a1 a2 ^^^ lim3 x0 x1 x2 := by
  cases b
  · simp only [Bool.false_eq_true, if_false]; exact lim3_xor ..
  · rfl

theorem hbK_le (b1 b2 : Bool) : hbK b1 b2 ≤ 15 := by unfold hbK; cases b1 <;> cases b2 <;> simp

theorem hb_loop (hcode : Code im) {t0 : MachineState} {d a : Nat} (ha : a < 2 ^ 128) (hd : d < 2 ^ 10) :
    ∀ n k, k + n = 10 → (k = 0 ∨ 2 ^ k ≤ d) → ∀ t, HbSt t0 d a k t →
      ∃ u m, Steps im t m m u ∧ m ≤ 14 * n + 1 ∧ HfSt t0 d a u := by
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
    have hk9 : k ≤ 9 := by omega
    have hp9 : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hk9
    have hdk : d / 2 ^ k < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    obtain ⟨u, su, upc, u10, u11, u12, u13, u14, u15, u16, uregs, uframe⟩ :=
      step_HB hcode t ht.pc _ _ rfl rfl
    have hand : t.getReg .x16 &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (d / 2 ^ k % 2) := by
      rw [ht.dd]; exact ofNat_and_one _ hdk
    have hshr : t.getReg .x16 >>> 1 = BitVec.ofNat 64 (d / 2 ^ (k + 1)) := by
      rw [ht.dd, ofNat_shr _ _ hdk, Nat.div_div_eq_div_mul, pow_one, ← Nat.pow_succ]
    have hb1 : (t.getReg .x16 &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0) = !(d.testBit k) := by
      rw [hand, Nat.testBit_eq_decide_div_mod_eq]
      have h2 : d / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by norm_num)
      rcases Nat.mod_two_eq_zero_or_one (d / 2 ^ k) with h | h <;> simp [h]
    have hlt12 : (t.getReg .x12).toNat < 2 ^ 63 := by
      have := lim3_lt (t.getReg .x10) (t.getReg .x11) (t.getReg .x12) (n := 9) (by
        rw [ht.sh, Nat.pow_add]
        exact Nat.mul_lt_mul_of_lt_of_le ha hp9 (Nat.two_pow_pos _))
      omega
    have hsh : lim3 (u.getReg .x10) (u.getReg .x11) (u.getReg .x12) = a * 2 ^ (k + 1) := by
      rw [u10, u11, u12, lim3_shl1 _ _ _ hlt12, ht.sh, Nat.pow_succ]; ring
    have hpr : lim3 (u.getReg .x13) (u.getReg .x14) (u.getReg .x15) = clmulSmall a d (k + 1) := by
      rw [u13, u14, u15, lim3_ite, hb1, ht.pr, ht.sh]
      rw [← clmul_step a d k _ rfl (d.testBit k) rfl]
      cases d.testBit k <;> rfl
    have hdd : u.getReg .x16 = BitVec.ofNat 64 (d / 2 ^ (k + 1)) := by rw [u16, hshr]
    have hregs : RegsExcept t0 u hbRegs := (ht.regs.trans uregs).mono (by simp [hbRegs])
    have hframe : Frame t0 u (fun _ => False) := (ht.frame.trans uframe).mono (fun _ _ h => by simpa using h)
    by_cases hz : d / 2 ^ (k + 1) = 0
    · have hb2 : (t.getReg .x16 >>> 1 != BitVec.ofNat 64 0) = false := by rw [hshr, hz]; rfl
      have hdlt : d < 2 ^ (k + 1) := by
        by_contra hc
        have := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.two_pow_pos (k + 1))
        omega
      refine ⟨u, _, su, le_trans (hbK_le _ _) (by omega), ⟨?_, ?_, hregs, hframe⟩⟩
      · rw [upc, hb2]; rfl
      · rw [hpr, clmulSmall_stable a hdlt 10 (by omega)]
    · have hb2 : (t.getReg .x16 >>> 1 != BitVec.ofNat 64 0) = true := by
        rw [hshr, ofNat_bne (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)) (by norm_num)]; simpa using hz
      have hge : 2 ^ (k + 1) ≤ d := by
        by_contra hc
        exact hz (Nat.div_eq_of_lt (Nat.lt_of_not_le hc))
      obtain ⟨v, m, sv, hm, hv⟩ := ih (k + 1) (by omega) (Or.inr hge) u
        ⟨by rw [upc, hb2]; rfl, hsh, hpr, hdd, hregs, hframe⟩
      refine ⟨v, _, su.trans sv, ?_, hv⟩
      have hk14 : hbK (t.getReg .x16 &&& BitVec.ofNat 64 1 == BitVec.ofNat 64 0)
          (t.getReg .x16 >>> 1 != BitVec.ofNat 64 0) ≤ 14 := by
        rw [hb2]; unfold hbK; split <;> simp
      omega

/-- Horner state over the coefficient buffer at base `B` (`B = COEF`: HORN; `B = COEF + 864`: the v6 lower family
buffer `FB`). -/
structure HkSt (s0 : MachineState) (B d : Nat) (coefs : List Digest) (m : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf hkI
  x6 : t.getReg .x6 = BitVec.ofNat 64 d
  x7 : t.getReg .x7 = BitVec.ofNat 64 (B + 16 * m)
  x28 : t.getReg .x28 = BitVec.ofNat 64 B
  acc : lim2 (t.getReg .x10) (t.getReg .x11) = (familyEval (coefs.drop m) d).toNat
  regs : RegsExcept s0 t hornRegs
  frame : Frame s0 t (fun _ => False)

/-- Cycle bound of one Horner step (HK, at most ten bit iterations, HF). -/
def hornStepC : Nat := 6 + (14 * 10 + 1) + 12

theorem lim3_zero_hi (a b : BitVec 64) : lim3 a b (BitVec.ofNat 64 0) = lim2 a b := by
  unfold lim3 lim2; simp

theorem familyEval_drop (coefs : List Digest) (m : Nat) (hm : m < coefs.length) (d : Nat) :
    familyEval (coefs.drop m) d = gfMulPt (familyEval (coefs.drop (m + 1)) d) d ^^^ coefs.getD m 0 := by
  rw [List.drop_eq_getElem_cons hm, familyEval_cons, List.getD_eq_getElem _ _ hm]

theorem coefAddrB (B m : Nat) (hB : B + 16 * (m + 1) < 2 ^ 64) :
    BitVec.ofNat 64 (B + 16 * (m + 1)) + BitVec.ofNat 64 (2 ^ 64 - 16) = BitVec.ofNat 64 (B + 16 * m) := by
  rw [ofNat_add_ofNat, ofNat_eq_iff]; omega

theorem horner_mul (hcode : Code im) {s0 : MachineState} {B d : Nat} {coefs : List Digest} (hd : d < 2 ^ 10)
    {m : Nat} (hB : B + 16 * (m + 1) < 2 ^ 64) {t : MachineState} (ht : HkSt s0 B d coefs (m + 1) t) :
    ∃ u n, Steps im t n n u ∧ n ≤ 6 + (14 * 10 + 1) ∧ u.pc = pcOf hfI ∧
      u.getReg .x7 = BitVec.ofNat 64 (B + 16 * m) ∧ u.getReg .x28 = BitVec.ofNat 64 B ∧
      u.getReg .x6 = BitVec.ofNat 64 d ∧
      lim3 (u.getReg .x13) (u.getReg .x14) (u.getReg .x15) =
        clmulSmall (familyEval (coefs.drop (m + 1)) d).toNat d 10 ∧
      RegsExcept s0 u hornRegs ∧ Frame s0 u (fun _ => False) := by
  obtain ⟨t1, s1, p1, x7, x12, x13, x14, x15, x16, r1, f1⟩ := step_HK hcode t ht.pc
  have h0 : HbSt t1 d (familyEval (coefs.drop (m + 1)) d).toNat 0 t1 := by
    refine ⟨p1, ?_, ?_, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [x12, lim3_zero_hi, r1.get (by simp), r1.get (by simp), ht.acc]; simp
    · rw [x13, x14, x15]; unfold lim3; simp [clmulSmall]
    · rw [x16, ht.x6]; simp
  obtain ⟨u, n, su, hn, hu⟩ := hb_loop hcode (BitVec.isLt _) hd 10 0 (by norm_num) (Or.inl rfl) t1 h0
  refine ⟨u, 6 + n, s1.trans su, by omega, hu.pc, ?_, ?_, ?_, hu.pr, ?_, ?_⟩
  · rw [hu.regs.get (by simp [hbRegs]), x7, ht.x7, coefAddrB B m hB]
  · rw [hu.regs.get (by simp [hbRegs]), r1.get (by simp), ht.x28]
  · rw [hu.regs.get (by simp [hbRegs]), r1.get (by simp), ht.x6]
  · exact ((ht.regs.trans r1).trans hu.regs).mono (by simp [hornRegs, hbRegs])
  · exact ((ht.frame.trans f1).trans hu.frame).mono (fun _ _ h => by simpa using h)

/-- The first `n` coefficients of the buffer at base `B`. -/
def CoefAtB (B n : Nat) (t : MachineState) (coefs : List Digest) : Prop :=
  ∀ k < n, DigAt t (B + 16 * k) (coefs.getD k 0)
/-- The first `n` coefficients of the buffer at `COEF`. -/
def CoefAtN (n : Nat) (t : MachineState) (coefs : List Digest) : Prop :=
  ∀ k < n, DigAt t (COEF + 16 * k) (coefs.getD k 0)

theorem coef_limbs {B N : Nat} (hBN : B + 16 * N < 2 ^ 64) {s0 u : MachineState} {coefs : List Digest}
    (hcoef : CoefAtB B N s0 coefs) (hf : Frame s0 u (fun _ => False)) {m : Nat} (hm : m < N) :
    lim2 (u.getMem (BitVec.ofNat 64 (B + 16 * m))) (u.getMem (BitVec.ofNat 64 (B + 16 * m + 8))) =
      (coefs.getD m 0).toNat := by
  have h := hcoef m hm
  rw [hf.get (by omega) id, hf.get (by omega) id, h.1, h.2, lim2_toNat]

/-- The Horner loop over the first `N` coefficients of the buffer at base `B` (`B = COEF`, `N = 54`: HORN of
stage A; `B = COEF + 864`, `N ≤ 38`: the v6 lower family seeds, entered at `HK` with `x7 = B + 16 N`). -/
theorem horner_loopB (hcode : Code im) {s0 : MachineState} {B d : Nat} {coefs : List Digest} {N : Nat}
    (hB8 : B % 8 = 0) (hBN : B + 16 * N + 16 ≤ MEMORY_BYTES) (hd : d < 2 ^ 10) (hlen : coefs.length = N)
    (hcoef : CoefAtB B N s0 coefs) :
    ∀ m, m < N → ∀ t, HkSt s0 B d coefs (m + 1) t →
      ∃ u n c, Steps im t n c u ∧ c ≤ hornStepC * (m + 1) + 5 ∧
        u.pc = s0.getReg .x1 &&& BitVec.ofNat 64 (2 ^ 64 - 2) ∧ DigAt u (CHAINW + 48) (familyEval coefs d) ∧
        RegsExcept s0 u hornRegs ∧ Frame s0 u (fun A => A = CHAINW + 48 ∨ A = CHAINW + 56) := by
  unfold MEMORY_BYTES at hBN
  intro m
  induction m with
  | zero =>
    intro _ t ht
    obtain ⟨u, n, su, hn, upc, u7, u28, -, upr, uregs, uframe⟩ := horner_mul hcode hd (by omega) ht
    obtain ⟨v, sv, vpc, v48, v56, vregs, vframe⟩ := step_HF_exit hcode u upc (A := B + 16 * 0) u7
      (by omega) (by unfold MEMORY_BYTES; omega) (by rw [u7, u28, Nat.mul_zero, Nat.add_zero])
    have hl := horner_limbs upr (coef_limbs (by omega) hcoef uframe (m := 0) (by omega))
    rw [← familyEval_drop coefs 0 (by omega), List.drop_zero] at hl
    obtain ⟨l0, l1⟩ := limbs_of_lim2 hl
    refine ⟨v, _, _, su.trans sv, by unfold hornStepC; omega, ?_, ⟨by rw [v48, l0], by rw [v56, ← l1]⟩, ?_, ?_⟩
    · rw [vpc, uregs.get (by simp [hornRegs])]
    · exact (uregs.trans vregs).mono (by simp [hornRegs, hfRegs])
    · exact (uframe.trans vframe).mono (fun _ _ h => by simpa using h)
  | succ m ih =>
    intro hm t ht
    obtain ⟨u, n, su, hn, upc, u7, u28, u6, upr, uregs, uframe⟩ := horner_mul hcode hd (by omega) ht
    have hne : u.getReg .x7 ≠ u.getReg .x28 := by
      rw [u7, u28]; intro h; rw [ofNat_inj (by omega) (by omega)] at h; omega
    obtain ⟨v, sv, vpc, v10, v11, vregs, vframe⟩ := step_HF_cont hcode u upc u7
      (by omega) (by unfold MEMORY_BYTES; omega) hne
    have hl := horner_limbs upr (coef_limbs (by omega) hcoef uframe (m := m + 1) (by omega))
    rw [← familyEval_drop coefs (m + 1) (by omega)] at hl
    have hv : HkSt s0 B d coefs (m + 1) v := by
      refine ⟨vpc, ?_, ?_, ?_, ?_, (uregs.trans vregs).mono (by simp [hornRegs, hfRegs]),
        (uframe.trans vframe).mono (fun _ _ h => by simpa using h)⟩
      · rw [vregs.get (by simp [hfRegs]), u6]
      · rw [vregs.get (by simp [hfRegs]), u7]
      · rw [vregs.get (by simp [hfRegs]), u28]
      · rw [v10, v11]; exact hl
    obtain ⟨w, n', c', sw, hc', wpc, wd, wregs, wframe⟩ := ih (by omega) v hv
    refine ⟨w, _, _, (su.trans sv).trans sw, ?_, wpc, wd, wregs, wframe⟩
    unfold hornStepC at *
    omega

theorem horner_loop (hcode : Code im) {s0 : MachineState} {d : Nat} {coefs : List Digest} {N : Nat}
    (hN : N ≤ 54) (hd : d < 2 ^ 10) (hlen : coefs.length = N) (hcoef : CoefAtN N s0 coefs) :
    ∀ m, m < N → ∀ t, HkSt s0 COEF d coefs (m + 1) t →
      ∃ u n c, Steps im t n c u ∧ c ≤ hornStepC * (m + 1) + 5 ∧
        u.pc = s0.getReg .x1 &&& BitVec.ofNat 64 (2 ^ 64 - 2) ∧ DigAt u (CHAINW + 48) (familyEval coefs d) ∧
        RegsExcept s0 u hornRegs ∧ Frame s0 u (fun A => A = CHAINW + 48 ∨ A = CHAINW + 56) :=
  horner_loopB hcode (by unfold COEF; omega) (by unfold COEF MEMORY_BYTES; omega) hd hlen hcoef
/-- Cycle bound of HORN. -/
def hornC : Nat := 6 + (hornStepC * 54 + 5)

theorem horn_run (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf hornI) {d : Nat} (hd : d < 2 ^ 10)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 d) {coefs : List Digest} (hlen : coefs.length = 54)
    (hcoef : CoefAt s coefs) :
    ∃ u n c, Steps im s n c u ∧ c ≤ hornC ∧ u.pc = s.getReg .x1 &&& BitVec.ofNat 64 (2 ^ 64 - 2) ∧
      DigAt u (CHAINW + 48) (familyEval coefs d) ∧ RegsExcept s u hornRegs ∧
      Frame s u (fun A => A = CHAINW + 48 ∨ A = CHAINW + 56) := by
  obtain ⟨t, st, tpc, t7, t10, t11, t28, tregs, tframe⟩ := step_H0 hcode s hpc
  have ht : HkSt s COEF d coefs (53 + 1) t := by
    refine ⟨tpc, by rw [tregs.get (by simp)]; exact h6, t7, t28, ?_, tregs.mono (by simp [hornRegs]), tframe⟩
    rw [t10, t11, List.drop_eq_nil_of_le (by omega)]
    rfl
  obtain ⟨u, n, c, su, hc, upc, ud, uregs, uframe⟩ := horner_loop hcode (le_refl 54) hd hlen hcoef 53 (by norm_num) t ht
  exact ⟨u, _, _, st.trans su, by unfold hornC; omega, upc, ud, uregs, uframe⟩

end loops

def presKC (regs : List (Reg × E)) (mem : SymMem) (obl : List Oblig) (pc : Nat) (ec : Bool) (k c : Nat)
    (brs : List Br) : PRes :=
  ⟨⟨regsOf regs, mem, obl⟩, pcOf pc, ec, k, c, brs, none⟩
abbrev seedI : Nat := ClaudeWCT.W9.Machine.Sign.seedI
abbrev retI : Nat := ClaudeWCT.W9.Machine.Sign.retI
abbrev cq0I : Nat := ClaudeWCT.W9.Machine.Sign.cq0I
abbrev cqI : Nat := ClaudeWCT.W9.Machine.Sign.cqI
abbrev cqeI : Nat := ClaudeWCT.W9.Machine.Sign.cqeI
def x28A (off : Nat) : Addr := ⟨some (.reg .x28), BitVec.ofNat 64 off⟩
def ld28 (off : Nat) : E := .ld (.bin .add (.reg .x28) (cE off))

/-! ### v6 lower families: the family buffer and the new code words -/

/-- The v6 lower family buffer `FB = COEF + 864` (at most 38 coefficients) and its end pointer `[COEF + 1488]`. -/
def FB : Nat := COEF + 864
def FEND : Nat := COEF + 1488
/-- The family prologue `qd` (`20749 → 24807`). -/
def qdI : Nat := 24807
/-- `2^height` as computed by `qd` (`t4 = 64`, `128` for layer 1). -/
def Pb (b1 : Bool) : Nat := if b1 then 64 else 128
/-- The family size `5 · min 7 (2^h − 7 f) + 3` computed by `qd` for leaf `L` of layer `lay`. -/
def famN (lay L : Nat) : Nat := 5 * min 7 ((if lay = 1 then 128 else 64) - 7 * (L / 7)) + 3

/-- The coefficient buffer state carried across the leaves of a family. -/
structure FamBuf (t : MachineState) (coefs : List Digest) : Prop where
  pos : 0 < coefs.length
  le : coefs.length ≤ 38
  coef : CoefAtB FB coefs.length t coefs
  fend : t.getMem (BitVec.ofNat 64 FEND) = BitVec.ofNat 64 (FB + 16 * coefs.length)

theorem FamBuf.frame {s t : MachineState} {coefs : List Digest} {W : Nat → Prop} (h : FamBuf s coefs)
    (hf : Frame s t W) (hW : ∀ X, FB ≤ X → X < FEND + 8 → ¬ W X) : FamBuf t coefs := by
  have hle := h.le
  refine ⟨h.pos, hle, fun k hk => ?_, ?_⟩
  · exact (h.coef k hk).frame hf (by unfold FB COEF; omega) (hW _ (by omega) (by unfold FB FEND COEF at *; omega))
      (hW _ (by omega) (by unfold FB FEND COEF at *; omega))
  · rw [hf.get (by unfold FEND COEF; omega) (hW _ (by unfold FB FEND; omega) (by omega)), h.fend]

def remE : E := .bin .remu (.reg .x18) (cE 7)
def divE : E := .bin .divu (.reg .x18) (cE 7)
def dE (b1 : Bool) : E := .bin .sub (cE (Pb b1)) (.bin .mul divE (cE 7))
def nE (b1 : Bool) : E := .bin .add (.bin .add (.bin .sll (dE b1) (cE 2)) (dE b1)) (cE 3)
def endE (b1 b2 : Bool) : E := if b2 then .bin .add (.bin .sll (nE b1) (cE 4)) (cE FB) else cE (FB + 16 * 38)
def topE (b1 b2 : Bool) : E :=
  if b2 then .bin .add (.bin .sll (.bin .srl (.bin .add (.bin .add (.bin .sll (dE b1) (cE 2)) (dE b1)) (cE 4)) (cE 1))
    (cE 5)) (cE FB) else cE (FB + 32 * 19)
def hdrQE : E :=
  .bin .or (.bin .or (.bin .sll (.bin .mul divE (cE 19)) (cE 32)) (.bin .sll (.reg .x8) (cE 16))) (cE 1)
def ptE : E := .bin .add (.bin .add (.bin .mul remE (cE 43)) (.reg .x19)) (cE 1)

def expD1 : PRes := pres [] [] [] seedI false 3 [⟨.eq, .reg .x19, cE 0, false⟩, ⟨.eq, .reg .x8, cE 0, false⟩]
def expD0 : PRes := pres [] [] [] qdI false 3 [⟨.eq, .reg .x19, cE 0, true⟩, ⟨.eq, .reg .x8, cE 0, false⟩]
def expQS : PRes := pres2 [(.x6, cE 7), (.x7, remE)] [] [] seedI false 4 7 [⟨.ne, remE, cE 0, true⟩]
def expQL (b1 b2 : Bool) : PRes :=
  pres2 [(.x6, hdrQE), (.x7, endE b1 b2), (.x10, .bin .sll (.reg .x8) (cE 16)), (.x17, cE (2 ^ 32)),
      (.x28, cE COEF), (.x29, cE FB), (.x30, topE b1 b2)] [mwc FEND (endE b1 b2)] [] cqI false
    (33 + (if b1 then 0 else 1) + (if b2 then 0 else 1)) (45 + (if b1 then 0 else 1) + (if b2 then 0 else 1))
    [⟨.ltu, dE b1, cE 7, b2⟩, ⟨.ne, .reg .x8, cE 1, b1⟩, ⟨.ne, remE, cE 0, false⟩]
def expCQ : PRes :=
  pres [(.x10, cE 0x20000), (.x11, cE 64), (.x12, cE 0x20040), (.x28, cE 0x20000)]
    [mwc 0x20018 (.reg .x9), mwc 0x20010 (.reg .x6)] [] cqeI true 6 []
def expCP (back : Bool) : PRes :=
  pres [(.x6, .bin .add (.reg .x6) (.reg .x17)), (.x7, ld28 88), (.x10, ld28 64), (.x11, ld28 72), (.x12, ld28 80),
      (.x29, .bin .add (.reg .x29) (cE 32))]
    [(x29A 24, ld28 88), (x29A 16, ld28 80), (x29A 8, ld28 72), (x29A 0, ld28 64)]
    [.valid (x29A 24) 8, .valid (x29A 16) 8, .valid (x29A 8) 8, .valid (x29A 0) 8, .valid (x28A 88) 8,
      .valid (x28A 80) 8, .valid (x28A 72) 8, .valid (x28A 64) 8]
    (if back then cqI else seedI) false (if back then 11 else 12)
    [⟨.ltu, .bin .add (.reg .x29) (cE 32), .reg .x30, back⟩]
def expSP : PRes :=
  pres2 [(.x1, cE (0x1000 + 4 * retI)), (.x6, ptE), (.x7, ldc FEND), (.x10, cE 0), (.x11, cE 0),
      (.x13, .bin .mul remE (cE 43)), (.x14, cE 43), (.x28, cE FB)]
    [mwc (COEF + 1528) (.reg .x16), mwc (COEF + 1520) (.reg .x15), mwc (COEF + 1512) (.reg .x14),
      mwc (COEF + 1504) (.reg .x13)] [] hkI false 19 25 []
def expSR : PRes :=
  pres [(.x6, ldc (CHAINW + 48)), (.x7, ldc (CHAINW + 56)), (.x13, ldc (COEF + 1504)), (.x14, ldc (COEF + 1512)),
      (.x15, ldc (COEF + 1520)), (.x16, ldc (COEF + 1528)), (.x28, cE 0)]
    [mwc 0x20048 (ldc (CHAINW + 56)), mwc 0x20040 (ldc (CHAINW + 48))] [] 1074 false 13 []
def runD1 : Option PRes := run tailLook [seedI] 20746 [.br false, .br false]
def runD0 : Option PRes := run tailLook [qdI] 20746 [.br false, .br true]
def runQS : Option PRes := run qLook [seedI] qdI [.br true]
def runQL (b1 b2 : Bool) : Option PRes := run qLook [cqI] qdI [.br false, .br b1, .br b2]
def runCQ : Option PRes := run (coordLook 0) [] cqI []
def runCP (back : Bool) : Option PRes := run (coordLook 0) [cqI, seedI] (cqeI + 1) [.br back]
def runSP : Option PRes := run seedLook [hkI] seedI []
def runSR : Option PRes := run (coordLook 1) [1074] retI []
theorem runD1_eq : runD1 = some expD1 := by apply optBeq_eq; decide +kernel
theorem runD0_eq : runD0 = some expD0 := by apply optBeq_eq; decide +kernel
theorem runQS_eq : runQS = some expQS := by apply optBeq_eq; decide +kernel
theorem runQL_eq (b1 b2 : Bool) : runQL b1 b2 = some (expQL b1 b2) := by
  cases b1 <;> cases b2 <;> apply optBeq_eq <;> decide +kernel
theorem runCQ_eq : runCQ = some expCQ := by apply optBeq_eq; decide +kernel
theorem runCP_eq (back : Bool) : runCP back = some (expCP back) := by
  cases back <;> apply optBeq_eq <;> decide +kernel
theorem runSP_eq : runSP = some expSP := by apply optBeq_eq; decide +kernel
theorem runSR_eq : runSR = some expSR := by apply optBeq_eq; decide +kernel

theorem eq_br_false (s : MachineState) (x : E) {v : Nat} (hx : x.eval s = BitVec.ofNat 64 v) (hv : v < 2 ^ 64)
    (h0 : v ≠ 0) : Br.holds s ⟨.eq, x, cE 0, false⟩ := by
  show ((x.eval s == BitVec.ofNat 64 0) = false)
  rw [hx, beq_eq_false_iff_ne]
  intro he; exact h0 ((ofNat_inj hv (by norm_num)).mp he)
theorem eq_br_true (s : MachineState) (x : E) (hx : x.eval s = BitVec.ofNat 64 0) :
    Br.holds s ⟨.eq, x, cE 0, true⟩ := by
  show ((x.eval s == BitVec.ofNat 64 0) = true)
  rw [hx]; simp

/-! ### Arithmetic of the family prologue -/

theorem remu_ofNat (n k : Nat) (hn : n < 2 ^ 64) (hk : 0 < k) (hk' : k < 2 ^ 64) :
    rv64_remu (BitVec.ofNat 64 n) (BitVec.ofNat 64 k) = BitVec.ofNat 64 (n % k) := by
  have hne : (BitVec.ofNat 64 k == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h
    have := congrArg BitVec.toNat h
    rw [toNat_ofNat_lt hk'] at this; simp at this; omega
  unfold rv64_remu; rw [hne]; simp only [Bool.false_eq_true, if_false]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, toNat_ofNat_lt hn, toNat_ofNat_lt hk',
    toNat_ofNat_lt (by have := Nat.mod_lt n hk; omega)]
theorem divu_ofNat (n k : Nat) (hn : n < 2 ^ 64) (hk : 0 < k) (hk' : k < 2 ^ 64) :
    rv64_divu (BitVec.ofNat 64 n) (BitVec.ofNat 64 k) = BitVec.ofNat 64 (n / k) := by
  have hne : (BitVec.ofNat 64 k == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h
    have := congrArg BitVec.toNat h
    rw [toNat_ofNat_lt hk'] at this; simp at this; omega
  unfold rv64_divu; rw [hne]; simp only [Bool.false_eq_true, if_false]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, toNat_ofNat_lt hn, toNat_ofNat_lt hk',
    toNat_ofNat_lt (by have := Nat.div_le_self n k; omega)]
theorem ofNat_sub_ofNat' (a b : Nat) (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat_lt ha, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]; omega

section evals
variable (s : MachineState) {L : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 L)
include h18
theorem eval_remE (hL : L < 2 ^ 64) : remE.eval s = BitVec.ofNat 64 (L % 7) := by
  show rv64_remu (s.getReg .x18) (BitVec.ofNat 64 7) = _
  rw [h18]; exact remu_ofNat L 7 hL (by norm_num) (by norm_num)
theorem eval_divE (hL : L < 2 ^ 64) : divE.eval s = BitVec.ofNat 64 (L / 7) := by
  show rv64_divu (s.getReg .x18) (BitVec.ofNat 64 7) = _
  rw [h18]; exact divu_ofNat L 7 hL (by norm_num) (by norm_num)
theorem eval_dE (b1 : Bool) (hL : L < Pb b1) : (dE b1).eval s = BitVec.ofNat 64 (Pb b1 - 7 * (L / 7)) := by
  have hP : Pb b1 ≤ 128 := by unfold Pb; split <;> omega
  show BinOp.eval .sub (BitVec.ofNat 64 (Pb b1)) (BinOp.eval .mul (divE.eval s) (BitVec.ofNat 64 7)) = _
  rw [eval_divE s h18 (by omega)]
  simp only [BinOp.eval]
  rw [BitVec.ofNat_mul_ofNat, ofNat_sub_ofNat' _ _ (by omega) (by omega)]
  congr 1; omega
theorem eval_nE (b1 : Bool) (hL : L < Pb b1) :
    (nE b1).eval s = BitVec.ofNat 64 (5 * (Pb b1 - 7 * (L / 7)) + 3) := by
  show BinOp.eval .add (BinOp.eval .add (BinOp.eval .sll ((dE b1).eval s) (BitVec.ofNat 64 2)) ((dE b1).eval s))
    (BitVec.ofNat 64 3) = _
  rw [eval_dE s h18 b1 hL, binop_sll _ _ (by norm_num), ofNat_shl]
  simp only [BinOp.eval]
  rw [ofNat_add_ofNat, ofNat_add_ofNat]
  congr 1; simp only [show (2 : Nat) ^ 2 = 4 from rfl]; omega
theorem eval_endE (b1 b2 : Bool) (hL : L < Pb b1) (hb2 : decide (Pb b1 - 7 * (L / 7) < 7) = b2) :
    (endE b1 b2).eval s = BitVec.ofNat 64 (FB + 16 * (5 * min 7 (Pb b1 - 7 * (L / 7)) + 3)) := by
  have hP : Pb b1 ≤ 128 := by unfold Pb; split <;> omega
  cases b2
  · have h7 : ¬ (Pb b1 - 7 * (L / 7) < 7) := by simpa using hb2
    show BitVec.ofNat 64 (FB + 16 * 38) = _
    congr 1; omega
  · have h7 : Pb b1 - 7 * (L / 7) < 7 := by simpa using hb2
    show BinOp.eval .add (BinOp.eval .sll ((nE b1).eval s) (BitVec.ofNat 64 4)) (BitVec.ofNat 64 FB) = _
    rw [eval_nE s h18 b1 hL, binop_sll _ _ (by norm_num), ofNat_shl]
    simp only [BinOp.eval]
    rw [ofNat_add_ofNat]
    congr 1; simp only [show (2 : Nat) ^ 4 = 16 from rfl]; omega
theorem eval_topE (b1 b2 : Bool) (hL : L < Pb b1) (hb2 : decide (Pb b1 - 7 * (L / 7) < 7) = b2) :
    (topE b1 b2).eval s = BitVec.ofNat 64 (FB + 32 * ((5 * min 7 (Pb b1 - 7 * (L / 7)) + 3 + 1) / 2)) := by
  have hP : Pb b1 ≤ 128 := by unfold Pb; split <;> omega
  cases b2
  · have h7 : ¬ (Pb b1 - 7 * (L / 7) < 7) := by simpa using hb2
    show BitVec.ofNat 64 (FB + 32 * 19) = _
    congr 1; omega
  · have h7 : Pb b1 - 7 * (L / 7) < 7 := by simpa using hb2
    show BinOp.eval .add (BinOp.eval .sll (BinOp.eval .srl (BinOp.eval .add (BinOp.eval .add
      (BinOp.eval .sll ((dE b1).eval s) (BitVec.ofNat 64 2)) ((dE b1).eval s)) (BitVec.ofNat 64 4))
      (BitVec.ofNat 64 1)) (BitVec.ofNat 64 5)) (BitVec.ofNat 64 FB) = _
    rw [eval_dE s h18 b1 hL, binop_sll _ 5 (by norm_num), binop_srl _ _ (by norm_num), binop_sll _ 2 (by norm_num),
      ofNat_shl]
    simp only [BinOp.eval]
    rw [ofNat_add_ofNat, ofNat_add_ofNat, ofNat_shr _ _ (by omega), ofNat_shl, ofNat_add_ofNat]
    congr 1; simp only [show (2 : Nat) ^ 5 = 32 from rfl, show (2 : Nat) ^ 2 = 4 from rfl, pow_one]; omega
theorem eval_hdrQE {lay : Nat} (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (hlay : lay < 256) (hL : L < 2 ^ 20) :
    hdrQE.eval s = BitVec.ofNat 64 (hdrB lay (19 * (L / 7))) := by
  show BinOp.eval .or (BinOp.eval .or (BinOp.eval .sll (BinOp.eval .mul (divE.eval s) (BitVec.ofNat 64 19))
    (BitVec.ofNat 64 32)) (BinOp.eval .sll (s.getReg .x8) (BitVec.ofNat 64 16))) (BitVec.ofNat 64 1) = _
  rw [binop_sll _ 32 (by norm_num), binop_sll _ 16 (by norm_num), eval_divE s h18 (by omega), h8]
  simp only [BinOp.eval]
  rw [BitVec.ofNat_mul_ofNat, ofNat_shl, ofNat_shl, BitVec.or_comm (BitVec.ofNat 64 (L / 7 * 19 * 2 ^ 32)),
    PackedLeaf.hdr_or lay _ hlay (by omega)]
  simp only [hdrB, ClaudeWCT.W9.Machine.Sign.hdrB]
  congr 1; ring
theorem eval_ptE {j : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 j) (hL : L < 2 ^ 32) (hj : j < 2 ^ 32) :
    ptE.eval s = BitVec.ofNat 64 (L % 7 * 43 + j + 1) := by
  show BinOp.eval .add (BinOp.eval .add (BinOp.eval .mul (remE.eval s) (BitVec.ofNat 64 43)) (s.getReg .x19))
    (BitVec.ofNat 64 1) = _
  rw [eval_remE s h18 (by omega), h19]
  simp only [BinOp.eval]
  rw [BitVec.ofNat_mul_ofNat, ofNat_add_ofNat, ofNat_add_ofNat]
end evals

section steps
variable {im : Image}

theorem step_D1 (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 20746) {lay j : Nat}
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (hlay : lay ≠ 0) (hlay' : lay < 256)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 j) (hj : j ≠ 0) (hj' : j < 2 ^ 32) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf seedI ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (tailLook_ok hcode) runD1_eq s hpc (no_obl s) (by
    intro b hb
    simp only [expD1, pres, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact eq_br_false s (.reg .x19) h19 (by omega) hj
    · exact eq_br_false s (.reg .x8) h8 (by omega) hlay)
  exact ⟨_, hst, rfl, pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩

/-- Chain 0 of a lower leaf: `20746 → 20749 → qd`. -/
theorem step_D0 (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf 20746) {lay : Nat}
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (hlay : lay ≠ 0) (hlay' : lay < 256)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 0) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf qdI ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (tailLook_ok hcode) runD0_eq s hpc (no_obl s) (by
    intro b hb
    simp only [expD0, pres, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact eq_br_true s (.reg .x19) h19
    · exact eq_br_false s (.reg .x8) h8 (by omega) hlay)
  exact ⟨_, hst, rfl, pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩

/-- `qd` for a non-first leaf of a family (`L % 7 ≠ 0`): straight to `SEED`. -/
theorem step_QS (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf qdI) {L : Nat}
    (h18 : s.getReg .x18 = BitVec.ofNat 64 L) (hL : L < 2 ^ 32) (hL7 : L % 7 ≠ 0) :
    ∃ t, Steps im s 4 7 t ∧ t.pc = pcOf seedI ∧ RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_sound (qLook_ok hcode) runQS_eq s hpc (no_obl s) (by
    intro b hb
    simp only [expQS, pres2, List.mem_singleton] at hb
    subst hb
    rw [br_ne_holds, eval_remE s h18 (by omega)]
    show (BitVec.ofNat 64 (L % 7) != BitVec.ofNat 64 0) = true
    rw [ofNat_bne (by omega) (by norm_num)]; simpa using hL7)
  exact ⟨_, hst, rfl, pres2_regsExcept _ _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩

/-- `qd` for the first leaf of a family (`L % 7 = 0`): the family size `N`, the end pointer, the pair loop bounds
`x29 = FB`, `x30 = FB + 32 ⌈N/2⌉`, the header of pair `19 f`, then `CQ`. -/
theorem step_QL (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf qdI) {lay L : Nat}
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (hlay : lay < 256) (h18 : s.getReg .x18 = BitVec.ofNat 64 L)
    (hL : L < (if lay = 1 then 128 else 64)) (hL7 : L % 7 = 0) :
    ∃ t k c, Steps im s k c t ∧ c ≤ 47 ∧ t.pc = pcOf cqI ∧
      t.getReg .x6 = BitVec.ofNat 64 (hdrB lay (19 * (L / 7))) ∧ t.getReg .x17 = BitVec.ofNat 64 (2 ^ 32) ∧
      t.getReg .x29 = BitVec.ofNat 64 FB ∧ t.getReg .x30 = BitVec.ofNat 64 (FB + 32 * ((famN lay L + 1) / 2)) ∧
      t.getMem (BitVec.ofNat 64 FEND) = BitVec.ofNat 64 (FB + 16 * famN lay L) ∧
      RegsExcept s t [.x6, .x7, .x10, .x17, .x28, .x29, .x30] ∧ Frame s t (fun A => A = FEND) := by
  have key : ∀ b1 b2 : Bool, decide (lay ≠ 1) = b1 → decide (Pb b1 - 7 * (L / 7) < 7) = b2 →
      ∃ t k c, Steps im s k c t ∧ c ≤ 47 ∧ t.pc = pcOf cqI ∧
        t.getReg .x6 = BitVec.ofNat 64 (hdrB lay (19 * (L / 7))) ∧ t.getReg .x17 = BitVec.ofNat 64 (2 ^ 32) ∧
        t.getReg .x29 = BitVec.ofNat 64 FB ∧ t.getReg .x30 = BitVec.ofNat 64 (FB + 32 * ((famN lay L + 1) / 2)) ∧
        t.getMem (BitVec.ofNat 64 FEND) = BitVec.ofNat 64 (FB + 16 * famN lay L) ∧
        RegsExcept s t [.x6, .x7, .x10, .x17, .x28, .x29, .x30] ∧ Frame s t (fun A => A = FEND) := by
    intro b1 b2 hb1 hb2
    have hP : Pb b1 = (if lay = 1 then 128 else 64) := by
      subst hb1; by_cases h : lay = 1 <;> simp [Pb, h]
    have hLb : L < Pb b1 := by rw [hP]; exact hL
    have hN : famN lay L = 5 * min 7 (Pb b1 - 7 * (L / 7)) + 3 := by unfold famN; rw [hP]
    have hL128 : L < 128 := by rw [hP] at hLb; split at hLb <;> omega
    obtain ⟨hst, -⟩ := run_sound (qLook_ok hcode) (runQL_eq b1 b2) s hpc (by
      intro o ho; simp [expQL, pres2] at ho) (by
      intro b hb
      simp only [expQL, pres2, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · rw [br_ltu_holds, eval_dE s h18 b1 hLb, eval_cE, ofNat_ult (by unfold Pb at *; split <;> omega)
          (by norm_num)]
        exact hb2
      · rw [br_ne_holds]
        show (s.getReg .x8 != BitVec.ofNat 64 1) = b1
        rw [h8, ofNat_bne (by omega) (by norm_num)]; exact hb1
      · rw [br_ne_holds, eval_remE s h18 (by omega)]
        show (BitVec.ofNat 64 (L % 7) != BitVec.ofNat 64 0) = false
        rw [ofNat_bne (by omega) (by norm_num)]; simpa using hL7)
    refine ⟨_, _, _, hst, by cases b1 <;> cases b2 <;> simp [expQL, pres2], rfl, ?_, ?_, ?_, ?_, ?_,
      pres2_regsExcept _ _ _ _ _ _ _ _ s, ?_⟩
    · rw [PRes.toState_getReg']; exact eval_hdrQE s h18 h8 hlay (by omega)
    · rw [PRes.toState_getReg']; rfl
    · rw [PRes.toState_getReg']; rfl
    · rw [PRes.toState_getReg', hN]; exact eval_topE s h18 b1 b2 hLb hb2
    · rw [PRes.toState_getMem']
      show memEval s [mwc FEND (endE b1 b2)] (BitVec.ofNat 64 FEND) = _
      rw [memEval_mwc_self s FEND _ _ (by unfold FEND COEF; norm_num), hN]
      exact eval_endE s h18 b1 b2 hLb hb2
    · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
      simp only [expQL, pres2, List.mem_singleton] at hq
      subst hq
      exact ⟨rfl, off_mwc _ _ (by unfold FEND COEF; norm_num)⟩
  exact key _ _ rfl rfl

theorem step_CQ (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf cqI) :
    ∃ t, Steps im s 6 6 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf cqeI ∧
      t.getReg .x10 = BitVec.ofNat 64 0x20000 ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 0x20040 ∧ t.getReg .x28 = BitVec.ofNat 64 0x20000 ∧
      t.getMem (BitVec.ofNat 64 0x20010) = s.getReg .x6 ∧ t.getMem (BitVec.ofNat 64 0x20018) = s.getReg .x9 ∧
      RegsExcept s t [.x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = 0x20018 ∨ A = 0x20010) := by
  obtain ⟨hst, hec⟩ := run_pres (coordLook_ok hcode (c := 0) (by norm_num)) runCQ_eq s hpc (no_obl s)
    (no_br s)
  refine ⟨_, hst, hec rfl, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by norm_num) (by norm_num) (by norm_num),
      memEval_mwc_self _ _ _ _ (by norm_num)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by norm_num)]; rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expCQ, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by norm_num)] <;> simp

theorem memEval_x29 (s : MachineState) {P : Nat} (h29 : s.getReg .x29 = BitVec.ofNat 64 P) (off : Nat) (e : E)
    (ws : SymMem) (A : Nat) (hA : A < 2 ^ 64) (hP : P + off < 2 ^ 64) :
    memEval s ((x29A off, e) :: ws) (BitVec.ofNat 64 A) =
      if A = P + off then e.eval s else memEval s ws (BitVec.ofNat 64 A) := by
  have hk : (x29A off).eval s = BitVec.ofNat 64 (P + off) := by
    show s.getReg .x29 + BitVec.ofNat 64 off = _
    rw [h29, ofNat_add_ofNat]
  simp only [memEval, hk, ofNat_inj hA hP]

/-- One copy step of the query loop: `SEEDS[0,32)` to `p`, `p += 32`, back to `CQ` while `p + 32 < x30`, else on
to `SEED`. -/
theorem step_CP (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf (cqeI + 1)) {P Q : Nat}
    (h28 : s.getReg .x28 = BitVec.ofNat 64 0x20000) (h29 : s.getReg .x29 = BitVec.ofNat 64 P)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 Q) (hP8 : P % 8 = 0) (hP : P + 32 ≤ 0x60000) (hQ : Q ≤ 0x60000) :
    ∃ t k, Steps im s k k t ∧ k ≤ 12 ∧ t.pc = pcOf (if P + 32 < Q then cqI else seedI) ∧
      t.getReg .x29 = BitVec.ofNat 64 (P + 32) ∧ t.getReg .x6 = s.getReg .x6 + s.getReg .x17 ∧
      (∀ d, DigAt s 0x20040 d → DigAt t P d) ∧ (∀ d, DigAt s (0x20040 + 16) d → DigAt t (P + 16) d) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => P ≤ A ∧ A < P + 32) := by
  have v29 : (E.reg .x29).eval s = BitVec.ofNat 64 P := h29
  have v28 : (E.reg .x28).eval s = BitVec.ofNat 64 0x20000 := h28
  have hobl : ∀ o ∈ (expCP true).st.obl, o.holds s := by
    intro o ho
    simp only [expCP, pres, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact valid_ofNat v29 (by omega) (by unfold MEMORY_BYTES; omega)
      | exact valid_ofNat v28 (by norm_num) (by unfold MEMORY_BYTES; norm_num)
  have hld : ∀ off, (ld28 off).eval s = s.getMem (BitVec.ofNat 64 (0x20000 + off)) := by
    intro off; show s.getMem (s.getReg .x28 + BitVec.ofNat 64 off) = _; rw [h28, ofNat_add_ofNat]
  have hbr : BitVec.ult ((E.bin .add (.reg .x29) (cE 32)).eval s) ((E.reg .x30).eval s) =
      decide (P + 32 < Q) := by
    show BitVec.ult (s.getReg .x29 + BitVec.ofNat 64 32) (s.getReg .x30) = _
    rw [h29, h30, ofNat_add_ofNat, ofNat_ult (by omega) (by omega)]
  have key : ∀ back : Bool, back = decide (P + 32 < Q) → ∃ t k, Steps im s k k t ∧ k ≤ 12 ∧
      t.pc = pcOf (if back then cqI else seedI) ∧ (∀ x, t.getReg x = (((expCP back).st.regs).get x).eval s) ∧
      (∀ a, t.getMem a = memEval s (expCP back).st.mem a) := by
    intro back hback
    have hst := (run_sound (coordLook_ok hcode (c := 0) (by norm_num)) (runCP_eq back) s hpc
      (by cases back <;> exact hobl) (by
        intro b hb
        cases back <;>
        · simp only [expCP, pres, List.mem_singleton] at hb
          subst hb
          rw [br_ltu_holds, hbr, hback])).1
    refine ⟨_, _, hst, by cases back <;> simp [expCP, pres], by cases back <;> rfl,
      fun x => PRes.toState_getReg' _ s x, fun a => rfl⟩
  obtain ⟨t, k, hst, hk, hpc', hr, hm⟩ := key _ rfl
  have hmem : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = P + 24 then s.getMem (BitVec.ofNat 64 (0x20000 + 88)) else
      if A = P + 16 then s.getMem (BitVec.ofNat 64 (0x20000 + 80)) else
      if A = P + 8 then s.getMem (BitVec.ofNat 64 (0x20000 + 72)) else
      if A = P + 0 then s.getMem (BitVec.ofNat 64 (0x20000 + 64)) else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [hm]
    simp only [expCP, pres]
    rw [memEval_x29 s h29 _ _ _ A hA (by omega), memEval_x29 s h29 _ _ _ A hA (by omega),
      memEval_x29 s h29 _ _ _ A hA (by omega), memEval_x29 s h29 _ _ _ A hA (by omega), hld, hld, hld, hld]
    rfl
  refine ⟨t, k, hst, hk, ?_, ?_, ?_, fun d hd => ⟨?_, ?_⟩, fun d hd => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hpc']; congr 1; simp only [decide_eq_true_eq]
  · rw [hr]; show s.getReg .x29 + BitVec.ofNat 64 32 = _; rw [h29, ofNat_add_ofNat]
  · rw [hr]; rfl
  · rw [hmem P (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]; exact hd.1
  · rw [hmem (P + 8) (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]; exact hd.2
  · rw [hmem (P + 16) (by omega), if_neg (by omega), if_pos rfl]; exact hd.1
  · rw [show P + 16 + 8 = P + 24 by ring, hmem (P + 24) (by omega), if_pos rfl]; exact hd.2
  · intro x hx
    rw [hr]
    cases back_eq : decide (P + 32 < Q)
    all_goals
      simp only [expCP, pres]
      rw [regsOf_get_ne _ _ (fun p hp he => hx (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> subst he <;> simp)), RegFile.init_get_eval]
  · intro A hA hn
    rw [hmem A hA, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- `SEED` + `qp`: spill `x13..x16` to `COEF + 1504`, `x7 = [FEND]`, `x6 = (L % 7) · 43 + j + 1`, `x28 = FB`,
`x10 = x11 = 0`, `jal ra,HK`. -/
theorem step_SP (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf seedI) {L j : Nat}
    (h18 : s.getReg .x18 = BitVec.ofNat 64 L) (hL : L < 2 ^ 32)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 j) (hj : j < 2 ^ 32) :
    ∃ t, Steps im s 19 25 t ∧ t.pc = pcOf hkI ∧ t.getReg .x1 = pcOf retI ∧
      t.getReg .x6 = BitVec.ofNat 64 (L % 7 * 43 + j + 1) ∧ t.getReg .x7 = s.getMem (BitVec.ofNat 64 FEND) ∧
      t.getReg .x10 = BitVec.ofNat 64 0 ∧ t.getReg .x11 = BitVec.ofNat 64 0 ∧ t.getReg .x28 = BitVec.ofNat 64 FB ∧
      t.getMem (BitVec.ofNat 64 (COEF + 1504)) = s.getReg .x13 ∧
      t.getMem (BitVec.ofNat 64 (COEF + 1512)) = s.getReg .x14 ∧
      t.getMem (BitVec.ofNat 64 (COEF + 1520)) = s.getReg .x15 ∧
      t.getMem (BitVec.ofNat 64 (COEF + 1528)) = s.getReg .x16 ∧
      RegsExcept s t [.x1, .x6, .x7, .x10, .x11, .x13, .x14, .x28] ∧
      Frame s t (fun A => COEF + 1504 ≤ A ∧ A < COEF + 1536) := by
  obtain ⟨hst, -⟩ := run_sound (seedLook_ok hcode) runSP_eq s hpc (no_obl s) (no_br s)
  refine ⟨_, hst, rfl, by rw [PRes.toState_getReg']; rfl, ?_, by rw [PRes.toState_getReg']; rfl, by rw [PRes.toState_getReg']; rfl,
    by rw [PRes.toState_getReg']; rfl, by rw [PRes.toState_getReg']; rfl, ?_, ?_, ?_, ?_, pres2_regsExcept _ _ _ _ _ _ _ _ s, ?_⟩
  · rw [PRes.toState_getReg']; exact eval_ptE s h18 h19 hL hj
  · rw [PRes.toState_getMem']; simp only [expSP, pres2]
    rw [memEval_mwc_ne _ _ _ (by aoc) (by aoc) (by aoc), memEval_mwc_ne _ _ _ (by aoc) (by aoc) (by aoc),
      memEval_mwc_ne _ _ _ (by aoc) (by aoc) (by aoc), memEval_mwc_self _ _ _ _ (by aoc)]; rfl
  · rw [PRes.toState_getMem']; simp only [expSP, pres2]
    rw [memEval_mwc_ne _ _ _ (by aoc) (by aoc) (by aoc), memEval_mwc_ne _ _ _ (by aoc) (by aoc) (by aoc),
      memEval_mwc_self _ _ _ _ (by aoc)]; rfl
  · rw [PRes.toState_getMem']; simp only [expSP, pres2]
    rw [memEval_mwc_ne _ _ _ (by aoc) (by aoc) (by aoc), memEval_mwc_self _ _ _ _ (by aoc)]; rfl
  · rw [PRes.toState_getMem']; simp only [expSP, pres2]
    rw [memEval_mwc_self _ _ _ _ (by aoc)]; rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expSP, pres2, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by aoc)] <;> aoc

theorem step_SR (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf retI) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf 1074 ∧ t.getReg .x28 = BitVec.ofNat 64 0 ∧
      t.getReg .x13 = s.getMem (BitVec.ofNat 64 (COEF + 1504)) ∧
      t.getReg .x14 = s.getMem (BitVec.ofNat 64 (COEF + 1512)) ∧
      t.getReg .x15 = s.getMem (BitVec.ofNat 64 (COEF + 1520)) ∧
      t.getReg .x16 = s.getMem (BitVec.ofNat 64 (COEF + 1528)) ∧
      (∀ d, DigAt s (CHAINW + 48) d → DigAt t 0x20040 d) ∧
      RegsExcept s t [.x6, .x7, .x13, .x14, .x15, .x16, .x28] ∧
      Frame s t (fun A => A = 0x20048 ∨ A = 0x20040) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode (c := 1) (by norm_num)) runSR_eq s hpc (no_obl s) (no_br s)
  refine ⟨_, hst, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, fun d hd => ⟨?_, ?_⟩, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem]
    rw [memEval_mwc_ne _ _ _ (by norm_num) (by norm_num) (by norm_num), memEval_mwc_self _ _ _ _ (by norm_num)]
    exact hd.1
  · rw [pres_getMem]
    rw [memEval_mwc_self _ _ _ _ (by norm_num)]
    exact hd.2
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expSR, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by norm_num)] <;> simp

end steps

/-- Cycle bound of one lower seed (SEED + `qp` 25 cycles, at most 38 Horner steps, RET). -/
abbrev lowerSeedC := ClaudeWCT.W9.Machine.Sign.lowerSeedC

/-- One v6 lower seed: from `SEED` (leaf `L`, chain `j`, the family coefficients in `FB`) to `1074` with
`familyEval coefs ((L % 7) · 43 + j + 1)` at `SEEDS`, `x13..x16` restored. -/
theorem lower_seed {im : Image} (hcode : Code im) (s : MachineState) (hpc : s.pc = pcOf seedI) {L j : Nat}
    (h18 : s.getReg .x18 = BitVec.ofNat 64 L) (hL : L < 2 ^ 32)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 j) (hj : j < 43) {coefs : List Digest} (hcoef : FamBuf s coefs) :
    ∃ u k c, Steps im s k c u ∧ c ≤ lowerSeedC ∧ u.pc = pcOf 1074 ∧ u.getReg .x28 = BitVec.ofNat 64 0 ∧
      DigAt u 0x20040 (familyEval coefs (L % 7 * 43 + j + 1)) ∧
      RegsExcept s u [.x1, .x6, .x7, .x10, .x11, .x12, .x17, .x28, .x29] ∧
      Frame s u (fun A => (COEF + 1504 ≤ A ∧ A < COEF + 1536) ∨ A = CHAINW + 48 ∨ A = CHAINW + 56 ∨
        A = 0x20048 ∨ A = 0x20040) := by
  obtain ⟨t, st, tpc, t1, t6, t7, t10, t11, t28, m13, m14, m15, m16, tr, tf⟩ :=
    step_SP hcode s hpc h18 hL h19 (by omega)
  obtain ⟨n, hn⟩ : ∃ n, coefs.length = n + 1 := ⟨coefs.length - 1, by have := hcoef.pos; omega⟩
  have hle := hcoef.le
  have hcoef' : CoefAtB FB (n + 1) t coefs := fun k hk =>
    (hcoef.coef k (by omega)).frame tf (by unfold FB COEF; omega) (by unfold FB COEF; omega)
      (by unfold FB COEF; omega)
  have hk : HkSt t FB (L % 7 * 43 + j + 1) coefs (n + 1) t := by
    refine ⟨tpc, t6, ?_, t28, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [t7, hcoef.fend, hn]
    · rw [t10, t11, List.drop_eq_nil_of_le (by omega), familyEval_nil]
      unfold lim2; simp
  obtain ⟨u, n', c, su, hc, upc, ud, ur, uf⟩ := horner_loopB hcode (B := FB) (N := n + 1)
    (by unfold FB COEF; omega) (by unfold FB COEF MEMORY_BYTES; omega) (by omega) hn hcoef' n (by omega) t hk
  rw [t1, show pcOf retI &&& BitVec.ofNat 64 (2 ^ 64 - 2) = pcOf retI from pcOf_and_max retI] at upc
  obtain ⟨v, sv, vpc, v28, v13, v14, v15, v16, vd, vr, vf⟩ := step_SR hcode u upc
  have mu : ∀ A, COEF + 1504 ≤ A → A < COEF + 1536 →
      u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A h1 h2 => uf.get (by aoc) (by aoc)
  refine ⟨v, 19 + (n' + 13), 25 + (c + 13), st.trans (su.trans sv), ?_, vpc, v28, vd _ ud, fun r hr => ?_, ?_⟩
  · unfold lowerSeedC ClaudeWCT.W9.Machine.Sign.lowerSeedC
    unfold hornStepC at hc
    unfold ClaudeWCT.W9.Machine.Sign.hornStepC
    omega
  · by_cases h13 : r = .x13
    · subst h13; rw [v13, mu _ (by omega) (by omega), m13]
    by_cases h14 : r = .x14
    · subst h14; rw [v14, mu _ (by omega) (by omega), m14]
    by_cases h15 : r = .x15
    · subst h15; rw [v15, mu _ (by omega) (by omega), m15]
    by_cases h16 : r = .x16
    · subst h16; rw [v16, mu _ (by omega) (by omega), m16]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n1, n6, n7, n10, n11, n12, n17, n28, n29⟩ := hr
    rw [vr.get (by simp [*]), ur.get (by simp [hornRegs, *]), tr.get (by simp [*])]
  · exact ((tf.trans uf).trans vf).mono (fun A _ h => by simp only [COEF, CHAINW] at h ⊢; omega)

end ClaudeWCT.W9.Machine.Sign.SharedSeed


namespace ClaudeWCT.W9.Machine.Sign.SharedSeed
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
open Gf ClaudeWCT.Arith
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem installed_code : Code Images.signImage := by
  constructor
  · apply SigGolfCandidate.T3M.codeAt_sign_current_slice <;> decide +kernel
  · apply SigGolfCandidate.T3M.codeAt_sign_current_slice <;> decide +kernel
  · apply SigGolfCandidate.T3M.codeAt_sign_current_slice <;> decide +kernel
  · apply SigGolfCandidate.T3M.codeAt_sign_current_slice <;> decide +kernel
theorem installed_seed_hook : CodeAt Images.signImage (pcOf 1055) Sign.seedHookCode := by
  apply SigGolfCandidate.T3M.codeAt_sign_current_slice <;> decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedSeed
