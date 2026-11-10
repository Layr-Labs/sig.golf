import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge028
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge075
import SigGolfCandidate.Merge084
import SigGolfCandidate.Merge094

-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_LowerRuns ====
section

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
  rw [List.drop_eq_getElem_cons hm, ClaudeWCT.Arith.familyEval_cons, List.getD_eq_getElem _ _ hm]

theorem coefAddrB (B m : Nat) (hB : B + 16 * (m + 1) < 2 ^ 64) :
    BitVec.ofNat 64 (B + 16 * (m + 1)) + BitVec.ofNat 64 (2 ^ 64 - 16) = BitVec.ofNat 64 (B + 16 * m) := by
  rw [ofNat_add_ofNat, SigGolfCandidate.T3M.ofNat_eq_iff]; omega

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
end
-- ==== merged from T3M_Sign_TopLeaf ====
section

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest chainCount width maxDigit chain chainInput buildLeaf leafHash privatePair
  shortHash header pad64 zero16 privateInput)
open SphincsSecurity (bytesLE bytesLE_length)
structure LeafPreS (sk : BitVec 256) (s : MachineState) (A : LeafArgs) : Prop where
  x1 : s.getReg .x1 = pcOf A.ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 A.lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 A.tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf
  x22 : s.getReg .x22 = BitVec.ofNat 64 A.digp
  x23 : s.getReg .x23 = BitVec.ofNat 64 A.valp
  x25 : s.getReg .x25 = BitVec.ofNat 64 A.dest
  x26 : s.getReg .x26 = BitVec.ofNat 64 A.n
  x27 : s.getReg .x27 = BitVec.ofNat 64 (n4 A.lay)
  x31 : s.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0)
  htree : A.tree < 2 ^ 32
  hleaf : A.leaf < 2 ^ 32
  hroute : A.tree * 2 ^ T3.height A.lay + A.leaf < 2 ^ 31
  hleafHeight : A.leaf < 2 ^ T3.height A.lay
  hsteps : ∀ i < A.n, A.e i ≤ 8
  p0 : s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : s.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : s.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : s.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : s.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : s.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  z0 : s.getMem (BitVec.ofNat 64 CHAIN) = 0
  z8 : s.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
  hsl : A.so = false → A.lay ≠ 0
  hdig : ∀ i < A.n, s.getByte (BitVec.ofNat 64 (A.digp + i)) = BitVec.ofNat 8 (A.d i)
  hdigb : ∀ i < A.n, A.d i < 256 ∧ (A.so = false → A.d i ≤ maxDigit A.lay i)
  hdigp : A.digp + A.n ≤ 2 ^ 24
  hdigW : ∀ i < A.n, ¬ LeafW A ((A.digp + i) / 8 * 8)
  /-- Pairing stage 1: the digits stay clear of the widened chain scratch `CHAIN+32 .. CHAIN+112`. -/
  hdigC : A.digp + A.n ≤ 0x201C0 ∨ 0x20210 ≤ A.digp
  hv8 : A.valp % 8 = 0
  hv : A.valp + 16 * A.n ≤ 2 ^ 24
  hvs : A.valp + 16 * A.n ≤ PRIV ∨ LEAFPK + 960 ≤ A.valp
  hd8 : A.so = false → A.dest % 8 = 0
  hd : A.dest + 16 ≤ 2 ^ 24
  hds : A.dest + 16 ≤ PRIV ∨ LEAFPK + 960 ≤ A.dest ∨ (CHAIN + 80 ≤ A.dest ∧ A.dest + 16 ≤ LOUT)
  hdv : A.dest + 16 ≤ A.valp ∨ A.valp + 16 * A.n ≤ A.dest
theorem chainCount_low {lay : Layer} (h0 : lay ≠ 0) : chainCount lay = 43 := by
  revert h0; revert lay; decide
theorem leafInput_wordsS (A : LeafArgs) (h0 : A.lay ≠ 0) (ends : List Digest) (hlen : ends.length = A.n) :
    wordsOf (pad64 (T3.leafInput A.lay A.tree A.leaf ends)) =
      wordsOf (bytesLE 16 (ends.getD 0 0)) ++
        [T3.hyperWord A.lay.val (A.tree * 2 ^ T3.height A.lay + A.leaf), 0] ++
        wordsOf ((ends.drop 1).flatMap (bytesLE 16)) := by
  have hn : A.n = 43 := chainCount_low h0
  have hfl : ((ends.drop 1).flatMap (bytesLE 16)).length = 16 * (A.n - 1) := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen]; ring
  unfold T3.leafInput
  rw [if_neg h0, pad64_of_aligned _ (by simp only [List.length_append, bytesLE_length, hfl, hn]),
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length] <;> omega),
    wordsOf_append _ _ (by simp only [bytesLE_length] <;> omega), wordsOf_bytesLE16 (T3.leafTweak _ _ _)]
  unfold T3.leafTweak
  rw [T3.append64_low, BitVec.extractLsb'_append_eq_left]
  rfl
theorem leafInput_lengthS (A : LeafArgs) (h0 : A.lay ≠ 0) (ends : List Digest) (hlen : ends.length = A.n) :
    (pad64 (T3.leafInput A.lay A.tree A.leaf ends)).length = 64 * leafBlocks A.lay := by
  have hn : A.n = 43 := chainCount_low h0
  have hfl : ((ends.drop 1).flatMap (bytesLE 16)).length = 16 * (A.n - 1) := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen]; ring
  unfold T3.leafInput
  rw [if_neg h0, pad64_length, List.length_append, List.length_append, bytesLE_length, bytesLE_length, hfl]
  unfold leafBlocks
  rw [show chainCount A.lay = A.n from rfl, hn]
end SigGolfCandidate.T3M.Sign
end
-- ==== merged from T3M_Sign_SeedIndependent ====
section

namespace SigGolfCandidate.T3M.Sign.SeedIndependent
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open Keygen
def sub27S : List (BitVec 32) := [33171,0x79c0006f]
def sub29S : List (BitVec 32) := List.replicate 11 0x13
def sub40S : List (BitVec 32) := [2451]
def sub80S : List (BitVec 32) := [4824595,623715]
/-- C2 (lower node tweak): words 1147/1148 compute `t1 = s5 + s8 + 1407` (the packed node word
`hyperWord (lay - 1) tree + lowerK + heap`, lowerK = 1407) and 1151 sets the high tweak word `t2 = 0`. -/
def sub120S : List (BitVec 32) := [6037011,3018291,134967,537857811,930563,9319299,7286819,8336419,134967,588189459,17707779,26096515,7286819,8336419,25854771,1475543827,4268699683,55221779,915,1477329635]
/-- Pairing stage 1: the header words `b + 9 .. b + 17` (1022..1030) still agree with the keygen's `sub_9` prefix; the
old HASH-argument setup 1031..1035, HASH 1036 and C3 tail jump 1037 are replaced by `1031: jal zero,1760` (witness stack; was 1732; the G/F
step block, `Seed.StepCode`) and nops. -/
def sub9S : List (BitVec 32) := [0x7340006f,21201843,33788691,17047315,31679283,269706003,134711,437128723,7223331]
def sub18S : List (BitVec 32) := [0x3650006f]
def sub19S : List (BitVec 32) := List.replicate 7 0x13
/-- C3 chain tramp at 1667: if `s3 = 0` (chain 0), `s0 ≠ 0` (lower layer) and `s4 = 6`, copy the high half
`0x201E0..0x201F0` of the hash just written at `CHAIN + 48` onto the value slot `CHAIN + 48`; then `s4 += 1` and back
to 1014. -/
def chainTrampS : List (BitVec 32) := [34181731,33816675,6292243,6954083,134711,504247043,512635779,476985379,
  478034979,1706515,3662671983]
/-- C2 (lower leaf half): 1119 `jal zero,1660` (leaf tramp), 1120 nop. -/
def sub106S : List (BitVec 32) := [122683503,19]
/-- The leaf value copy 1121..1124 (`ld t1,0(t4); ld t2,8(t4); sd t1,0(s9); sd t2,8(s9)`). -/
def sub108S : List (BitVec 32) := [963331,9352067,7122979,8172579]
/-- C2 (lower node half): 1160..1163 `slli t3,s8,4; add t3,t3,sp; jal zero,1653; nop`. -/
def sub147S : List (BitVec 32) := [4988435,3018291,2059403375,19]
/-- The node value copy 1164..1169 (`ld; ld; sd; sd; addi s8,s8,1; jal zero,1131`). -/
def sub151S : List (BitVec 32) := [963331,9352067,7221283,8270883,1838099,4137676911]
/-- C2 node tramp at 1653: `t4 = NOUT + 16 * (1 - s8 % 2)` (high half for even heaps), back to 1164. -/
def nodeTrampS : List (BitVec 32) := [1864467,1262355,4395795,134839,604933779,7245491,2220879983]
/-- C2 leaf tramp at 1660: `t4 = LOUT + 16 * (1 - s2 % 2)` (high half for even leaves), back to 1121. -/
def leafTrampS : List (BitVec 32) := [1667859,1262355,4395795,134839,1007586963,7245491,4157599855]
def sub157S : List (BitVec 32) := [1726995,0x5f00006f]
/-- Campaign T8D: the sign words at `1013 + 42 .. 1013 + 75` that the keygen image no longer shares (the keygen's
top hooks at 157/159..161/192 changed); the sign keeps its own copies so that `Keygen` edits cannot reach it.
Offsets 42..71 are dead in the T8D sign image (top seeds via TOPSEED/HORN, lower seeds via stage B's SEED). -/
def sub42S : List (BitVec 32) := [0x3ac1306f,67310179]
def sub44S : List (BitVec 32) := [1695251,17044243,34479891,31679283,1270547,295827,34152211,31712179,134711,7223331,8272931,132407,67110291,132663,67503635]
def sub59S : List (BitVec 32) := [115]
def sub60S : List (BitVec 32) := [1703443,5119507,134839,68062867,31329843,134967,487526163,930563,9319299,7286819,8336419,20647475]
def sub75S : List (BitVec 32) := [0x6750006f]
/-- Campaign T8D: the leaf prologue `1528..1541` ends with `j 1554` (PRE: `bne s0` / `jal ra,COEFGEN` / `j 1053`). -/
def hpS : List (BitVec 32) := [0xf49333,19071795,16978707,538141459,50601747,31679283,0xc100f13,59711251,31679283,134711,0x600e0e13,7223331,932899,0x340006f]
def hpmS : List (BitVec 32) := [17078931,538634899,0xfff40313,50533139,7006899,0xc100313,58921747,7006899,0xa75ff06f]
def norootS : List (BitVec 32) := [1049363,0xa06a08e3,0x961ff06f]
/-- The sign's leaf code at `b = 1013` (explicit: the shared `Keygen.sub_*` names only where the sign and keygen
words agree and the shared run lemmas are used). -/
def signSubL : Rv.Layout := [(0, sub_0), (1, sub_1), (2, sub_2), (8, sub_8), (9, sub9S), (18, sub18S), (19, sub19S),
  (26, sub_26), (27, sub27S), (29, sub29S), (40, sub40S), (41, sub_41), (42, sub42S), (44, sub44S), (59, sub59S),
  (60, sub60S), (72, sub_72), (73, sub_73), (75, sub75S), (76, sub_76), (77, sub_77), (78, sub_78), (79, sub_79),
  (80, sub80S), (82, sub_82), (83, sub_83), (92, sub_92), (95, sub_95), (96, sub_96), (105, sub_105), (106, sub106S),
  (108, sub108S), (112, sub_112), (113, sub_113), (116, sub_116), (117, sub_117), (118, sub_118), (120, sub120S), (140, sub_140),
  (146, sub_146), (147, sub147S), (151, sub151S), (157, sub157S), (159, sub_159)]
def SeedIndependentAt (image : Image) (b : Nat) : Prop :=
  (∀ off code, (off, code) ∈ signSubL → CodeAt image (pcOf (b + off)) code) ∧
  (b = 117 ∨ b = 1013) ∧
  (CodeAt image (pcOf (b + 1000)) Sign.maxDigitCodeS ∧
   CodeAt image (pcOf (b + 1004)) revCode ∧
   (image = Images.signReferenceImage ∧ b = 1013))
private theorem signSubL_ok : layoutOk 0 signSubL = true := by decide +kernel
private theorem signSubAt : CodeAt Images.signReferenceImage (pcOf 1013) (layoutCode signSubL) :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem seedIndependentAt_sign : SeedIndependentAt Images.signReferenceImage 1013 := by
  refine ⟨?_, Or.inr rfl, Sign.codeAt_maxDigit, Sign.codeAt_2017, rfl, rfl⟩
  intro off code hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  exact codeAt_sublayout signSubAt signSubL_ok hi
theorem codeAt_sub_0 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 0)) sub_0 :=
  h.1 0 sub_0 (by decide +kernel)
theorem codeAt_sub_1 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 1)) sub_1 :=
  h.1 1 sub_1 (by decide +kernel)
theorem codeAt_sub_2 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 2)) sub_2 :=
  h.1 2 sub_2 (by decide +kernel)
theorem codeAt_sub_8 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 8)) sub_8 :=
  h.1 8 sub_8 (by decide +kernel)
theorem codeAt_sub9S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 9)) sub9S :=
  h.1 9 sub9S (by decide +kernel)
theorem codeAt_sub18S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 18)) sub18S :=
  h.1 18 sub18S (by decide +kernel)
theorem codeAt_sub_26 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 26)) sub_26 :=
  h.1 26 sub_26 (by decide +kernel)
theorem codeAt_sub27S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 27)) sub27S :=
  h.1 27 sub27S (by decide +kernel)
theorem codeAt_sub40S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 40)) sub40S :=
  h.1 40 sub40S (by decide +kernel)
theorem codeAt_sub_41 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 41)) sub_41 :=
  h.1 41 sub_41 (by decide +kernel)
theorem codeAt_sub_72 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 72)) sub_72 :=
  h.1 72 sub_72 (by decide +kernel)
theorem codeAt_sub_73 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 73)) sub_73 :=
  h.1 73 sub_73 (by decide +kernel)
theorem codeAt_sub_75 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 75)) sub75S :=
  h.1 75 sub75S (by decide +kernel)
theorem codeAt_sub_76 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 76)) sub_76 :=
  h.1 76 sub_76 (by decide +kernel)
theorem codeAt_sub_77 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 77)) sub_77 :=
  h.1 77 sub_77 (by decide +kernel)
theorem codeAt_sub_78 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 78)) sub_78 :=
  h.1 78 sub_78 (by decide +kernel)
theorem codeAt_sub_79 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 79)) sub_79 :=
  h.1 79 sub_79 (by decide +kernel)
theorem codeAt_sub80S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 80)) sub80S :=
  h.1 80 sub80S (by decide +kernel)
theorem codeAt_sub_82 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 82)) sub_82 :=
  h.1 82 sub_82 (by decide +kernel)
theorem codeAt_sub_83 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 83)) sub_83 :=
  h.1 83 sub_83 (by decide +kernel)
theorem codeAt_sub_92 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 92)) sub_92 :=
  h.1 92 sub_92 (by decide +kernel)
theorem codeAt_sub_95 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 95)) sub_95 :=
  h.1 95 sub_95 (by decide +kernel)
theorem codeAt_sub_96 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 96)) sub_96 :=
  h.1 96 sub_96 (by decide +kernel)
theorem codeAt_sub_105 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 105)) sub_105 :=
  h.1 105 sub_105 (by decide +kernel)
theorem codeAt_sub106S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 106)) sub106S :=
  h.1 106 sub106S (by decide +kernel)
theorem codeAt_sub108S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 108)) sub108S :=
  h.1 108 sub108S (by decide +kernel)
theorem codeAt_sub_112 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 112)) sub_112 :=
  h.1 112 sub_112 (by decide +kernel)
theorem codeAt_sub_113 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 113)) sub_113 :=
  h.1 113 sub_113 (by decide +kernel)
theorem codeAt_sub_116 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 116)) sub_116 :=
  h.1 116 sub_116 (by decide +kernel)
theorem codeAt_sub_117 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 117)) sub_117 :=
  h.1 117 sub_117 (by decide +kernel)
theorem codeAt_sub_118 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 118)) sub_118 :=
  h.1 118 sub_118 (by decide +kernel)
theorem codeAt_sub120S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 120)) sub120S :=
  h.1 120 sub120S (by decide +kernel)
theorem codeAt_sub_140 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 140)) sub_140 :=
  h.1 140 sub_140 (by decide +kernel)
theorem codeAt_sub_146 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 146)) sub_146 :=
  h.1 146 sub_146 (by decide +kernel)
theorem codeAt_sub147S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 147)) sub147S :=
  h.1 147 sub147S (by decide +kernel)
theorem codeAt_sub151S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 151)) sub151S :=
  h.1 151 sub151S (by decide +kernel)
theorem codeAt_sub157S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 157)) sub157S :=
  h.1 157 sub157S (by decide +kernel)
theorem codeAt_sub_159 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 159)) sub_159 :=
  h.1 159 sub_159 (by decide +kernel)
theorem codeAt_rev {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 1004)) revCode := h.2.2.2.1
theorem codeAt_maxLow {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 1000)) Sign.maxLowS := by
  have q := codeAt_sublayout (L := Sign.maxLayoutS) (b := b + 1000) h.2.2.1 Sign.maxLayoutS_ok
    (i := 0) (o := 0) (seg := Sign.maxLowS) (by kernel_rfl)
  simpa only [Nat.add_zero] using q
theorem codeAt_maxHigh {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 1002)) maxHigh := by
  have q := codeAt_sublayout (L := Sign.maxLayoutS) (b := b + 1000) h.2.2.1 Sign.maxLayoutS_ok
    (i := 1) (o := 2) (seg := maxHigh) (by kernel_rfl)
  simpa [Nat.add_assoc] using q
theorem codeAt_sub_61 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 61)) (sub_60.drop 1) := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_hpS {image : Image} {b : Nat} (h : SeedIndependentAt image b) : CodeAt image (pcOf 1528) hpS := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_hpmS {image : Image} {b : Nat} (h : SeedIndependentAt image b) : CodeAt image (pcOf 1542) hpmS := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_norootS {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf 1551) norootS := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
def norootJ : List (BitVec 32) := [0x961ff06f]
theorem codeAt_norootJ {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf 1553) norootJ := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem b_eq {image : Image} {b : Nat} (h : SeedIndependentAt image b) : b = 1013 := h.2.2.2.2.2
/-- Campaign T8D: PRE at 1554 (`bne s0,zero,1053`). -/
def preS : List (BitVec 32) := [0x820416e3]
theorem codeAt_preS {image : Image} {b : Nat} (h : SeedIndependentAt image b) : CodeAt image (pcOf 1554) preS := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_nodeTrampS {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf 1653) nodeTrampS := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_chainTrampS {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf 1667) chainTrampS := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_leafTrampS {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf 1660) leafTrampS := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
/-- Campaign T8D: the top chains enter the old seed copy at `b + 71` (`add t3,s6,s3`) after TOPSEED. -/
def sub71S : List (BitVec 32) := [20647475]
theorem codeAt_sub71S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 71)) sub71S := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
sym_block blkS_27 := symRun { noAlias := true } sub27S (pcOf (1013 + 27)) 100
sym_block blkS_40 := symRun { noAlias := true } sub40S (pcOf (1013 + 40)) 100
sym_block blkS_80 := symRun { noAlias := true } sub80S (pcOf (1013 + 80)) 100
sym_block blkS_120 := symRun { noAlias := true } sub120S (pcOf (1013 + 120)) 100
sym_block blkS_106 := symRun { noAlias := true } sub106S (pcOf (1013 + 106)) 100
sym_block blkS_108 := symRun { noAlias := true } sub108S (pcOf (1013 + 108)) 100
sym_block blkS_147 := symRun { noAlias := true } sub147S (pcOf (1013 + 147)) 100
sym_block blkS_151 := symRun { noAlias := true } sub151S (pcOf (1013 + 151)) 100
sym_block blkS_ntr := symRun { noAlias := true } nodeTrampS (pcOf 1653) 100
sym_block blkS_ltr := symRun { noAlias := true } leafTrampS (pcOf 1660) 100
sym_block blkS_ctr := symRun { noAlias := true } chainTrampS (pcOf 1667) 100
sym_block blkS_157 := symRun { noAlias := true } sub157S (pcOf (1013 + 157)) 100
sym_block blkS_hp := symRun { noAlias := true } hpS (pcOf 1528) 100
sym_block blkS_hpm := symRun { noAlias := true } hpmS (pcOf 1542) 100
sym_block blkS_noroot := symRun { noAlias := true } norootS (pcOf 1551) 100
sym_block blkS_nrj := symRun { noAlias := true } norootJ (pcOf 1553) 100
sym_block blkS_pre := symRun { noAlias := true } preS (pcOf 1554) 100
sym_block blkS_71 := symRun { noAlias := true } sub71S (pcOf (1013 + 71)) 100
sym_block blkS_75 := symRun { noAlias := true } sub75S (pcOf (1013 + 75)) 100
sym_block blkS_maxLow := symRun { noAlias := true } Sign.maxLowS (pcOf (1013 + 1000)) 100
/-- Campaign T51: word 1088 (`b + 75`) is `j 1937`, the T51 top cap block 1937..1947: `s5 = maxDigit 0 i`
(5 for `i < 27`, 4 for `i < 48`, 6 for `i < 50`, else 5; `t5` clobbered), back to 1089 (`b + 76`). The reference
image keeps #938's `j 2013` (`sub75S`). -/
def sub75T : List (BitVec 32) := [0x5450006f]
def capAS : List (BitVec 32) := [0x00500a93, 0x01b00f13, 0xabe9cc63]
def capBS : List (BitVec 32) := [0x00400a93, 0x03000f13, 0xabe9c663]
def capCS : List (BitVec 32) := [0x00600a93, 0x03200f13, 0xabe9c063]
def capDS : List (BitVec 32) := [0x00500a93, 0xa98ff06f]
sym_block blkS_75T := symRun { noAlias := true } sub75T (pcOf (1013 + 75)) 100
sym_block blkS_capA := symRun { noAlias := true } capAS (pcOf 1937) 100
sym_block blkS_capB := symRun { noAlias := true } capBS (pcOf 1940) 100
sym_block blkS_capC := symRun { noAlias := true } capCS (pcOf 1943) 100
sym_block blkS_capD := symRun { noAlias := true } capDS (pcOf 1946) 100
end SigGolfCandidate.T3M.Sign.SeedIndependent


namespace SigGolfCandidate.T3M.Sign.SharedLeafCode
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Sign.SeedIndependent
structure Code (image : Image) (b : Nat) : Prop where
  base : b = 1013
  codeAt_hpS : CodeAt image (pcOf 1528) hpS
  codeAt_capA : CodeAt image (pcOf 1937) capAS
  codeAt_capB : CodeAt image (pcOf 1940) capBS
  codeAt_capC : CodeAt image (pcOf 1943) capCS
  codeAt_capD : CodeAt image (pcOf 1946) capDS
  codeAt_preS : CodeAt image (pcOf 1554) preS
  codeAt_sub27S : CodeAt image (pcOf (b + 27)) sub27S
  codeAt_sub40S : CodeAt image (pcOf (b + 40)) sub40S
  codeAt_sub71S : CodeAt image (pcOf (b + 71)) sub71S
  codeAt_sub80S : CodeAt image (pcOf (b + 80)) sub80S
  codeAt_sub_105 : CodeAt image (pcOf (b + 105)) sub_105
  codeAt_sub106S : CodeAt image (pcOf (b + 106)) sub106S
  codeAt_sub108S : CodeAt image (pcOf (b + 108)) sub108S
  codeAt_leafTrampS : CodeAt image (pcOf 1660) leafTrampS
  codeAt_sub_112 : CodeAt image (pcOf (b + 112)) sub_112
  codeAt_sub_41 : CodeAt image (pcOf (b + 41)) sub_41
  codeAt_sub_72 : CodeAt image (pcOf (b + 72)) sub_72
  codeAt_sub_73 : CodeAt image (pcOf (b + 73)) sub_73
  codeAt_sub_75 : CodeAt image (pcOf (b + 75)) sub75T
  codeAt_sub_76 : CodeAt image (pcOf (b + 76)) sub_76
  codeAt_sub_77 : CodeAt image (pcOf (b + 77)) sub_77
  codeAt_sub_78 : CodeAt image (pcOf (b + 78)) sub_78
  codeAt_sub_79 : CodeAt image (pcOf (b + 79)) sub_79
  codeAt_sub_82 : CodeAt image (pcOf (b + 82)) sub_82
  codeAt_sub_83 : CodeAt image (pcOf (b + 83)) sub_83
  codeAt_sub_92 : CodeAt image (pcOf (b + 92)) sub_92
  codeAt_sub_95 : CodeAt image (pcOf (b + 95)) sub_95
  codeAt_sub_96 : CodeAt image (pcOf (b + 96)) sub_96
end SigGolfCandidate.T3M.Sign.SharedLeafCode

namespace SigGolfCandidate.T3M.Sign.SharedLeafCode
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
 theorem installed_code : Code Images.signImage 1013 := by
  constructor
  · rfl
  all_goals (apply codeAt_sign_current_slice <;> decide +kernel)

end SigGolfCandidate.T3M.Sign.SharedLeafCode

namespace SigGolfCandidate.T3M.Sign.SharedTreeCode
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Sign.SeedIndependent
structure Code (image : Image) (b : Nat) : Prop where
  base : b=1013
  codeAt_sub_113 : CodeAt image (pcOf (b + 113)) sub_113
  codeAt_sub_116 : CodeAt image (pcOf (b + 116)) sub_116
  codeAt_sub_117 : CodeAt image (pcOf (b + 117)) sub_117
  codeAt_sub_118 : CodeAt image (pcOf (b + 118)) sub_118
  codeAt_sub120S : CodeAt image (pcOf (b + 120)) sub120S
  codeAt_rev : CodeAt image (pcOf (b + 1004)) revCode
  codeAt_sub_140 : CodeAt image (pcOf (b + 140)) sub_140
  codeAt_sub_146 : CodeAt image (pcOf (b + 146)) sub_146
  codeAt_sub147S : CodeAt image (pcOf (b + 147)) sub147S
  codeAt_sub151S : CodeAt image (pcOf (b + 151)) sub151S
  codeAt_nodeTrampS : CodeAt image (pcOf 1653) nodeTrampS
  codeAt_sub157S : CodeAt image (pcOf (b + 157)) sub157S
  codeAt_norootS : CodeAt image (pcOf 1551) norootS
  codeAt_norootJ : CodeAt image (pcOf 1553) norootJ
  codeAt_sub_159 : CodeAt image (pcOf (b + 159)) sub_159
end SigGolfCandidate.T3M.Sign.SharedTreeCode

namespace SigGolfCandidate.T3M.Sign.SharedTreeCode
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : Code Images.signImage 1013 := by
  constructor
  · rfl
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
  · apply codeAt_sign_current_slice <;> decide +kernel
end SigGolfCandidate.T3M.Sign.SharedTreeCode
end
-- ==== merged from T3M_Sign_PairStep ====
section

/-! # The sign chain step block (G/F), witness stack (charge 86)

The sign chain routine at 1013 ends its header at 1030 (`sd t1,16(t3)` with `t3 = CHAIN`); 1031 jumps to the step
block at 1760 (the stage-1 block 1732..1757 is dead):

* G path (lower: `s0 ≠ 0`, `s3` odd; top: `s0 = 0`, `s3` even `≤ 52`): copy the header to `CHAIN+64/72`, zero
  `CHAIN+80 .. CHAIN+112`, hash the 64 bytes at `CHAIN+48` (`value | header | 0 | 0`) to `CHAIN+32` (interior steps:
  the HIGH half lands in the value slot) or to `CHAIN+48` (the terminal step: lower 6, top `maxDigit 0 i - 1`), then
  `s4 += 1; jal 1014`.
* F path: zero `CHAIN+32 .. CHAIN+48`, hash the 64 bytes at `CHAIN` to `CHAIN+48`, then the C3 tail trampoline at 1667
  (`jal 1667` at 1797).

`pair_rung` is the whole block from 1031 as a `TSim` of `WCT9.halfHash (chainHigh) (chainInputW)`. -/

namespace SigGolfCandidate.T3M.Sign.Seed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open Keygen Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest chainInput pad64 zero16 height chainHeader)
open SphincsSecurity (bytesLE bytesLE_length)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-! ### C3 (FULL): the chain tail trampoline at 1667 (moved here from `SeedChain`) -/
def ctr0 : List (BitVec 32) := [34181731]
def ctr1 : List (BitVec 32) := [33816675]
def ctr2 : List (BitVec 32) := [6292243,6954083]
def ctr3 : List (BitVec 32) := [134711,504247043,512635779,476985379,478034979,1706515,3662671983]
def ctr4 : List (BitVec 32) := [1706515,3662671983]
sym_block blkC0 := symRun { noAlias := true } ctr0 (pcOf 1667) 100
sym_block blkC1 := symRun { noAlias := true } ctr1 (pcOf 1668) 100
sym_block blkC2 := symRun { noAlias := true } ctr2 (pcOf 1669) 100
sym_block blkC3 := symRun { noAlias := true } ctr3 (pcOf 1671) 100
sym_block blkC4 := symRun { noAlias := true } ctr4 (pcOf 1676) 100
theorem blkC3_regs (t : MachineState) : RegsExcept t (blkC3.res.toState t) [.x6, .x7, .x20, .x28] := by
  intro r hr; simp at hr; cases r <;> simp_all [blkC3.res, rv_simp] <;> rfl
/-- C3 (FULL): does the chain tail take the high half (chain 0 of a lower layer, after step 6)? -/
def hiSel (lay i m : Nat) : Prop := lay ≠ 0 ∧ i = 0 ∧ m = 6
instance (lay i m : Nat) : Decidable (hiSel lay i m) := by unfold hiSel; infer_instance
/-- C3 (FULL): extra steps of the F chain tail trampoline (from `jal 1667`) over 2. -/
def trX0 (lay i m : Nat) : Nat := if i ≠ 0 then 2 else if lay = 0 then 3 else if m = 6 then 10 else 5

/-! ### Witness stack (charge 86): the step block 1760..1797 (top rule added; the old block 1732..1757 is dead)
* 1760 `beq s0,zero,1766`. Lower: 1761/1762 `andi t1,s3,1; beq t1,zero,1791` (F), 1763..1765 `t1 = 6; t2 = 0;
  jal 1776` (G). Top: 1766..1768 `t1 = s3 & 1; t2 = 0; bne t1,t2,1791` (odd: F), 1769/1770 `t2 = 52; blt t2,s3,1791`,
  1771..1774 `t1 = maxDigit 0 i - 1` (3, or 6 for `i ≥ 51`), 1775 `ld t2,24(t3)` (header high word).
* G body 1776..1788: copy the header `CHAIN+16` / `t2` to `CHAIN+64/72`, zero `CHAIN+80 .. CHAIN+112`, HASH the 64 bytes
  at `CHAIN+48` to `CHAIN+32` (interior: the HIGH half lands in the value slot) or to `CHAIN+48` (`s4 = t1`, the
  terminal step), then 1789/1790 `addi s4,s4,1; jal 1014`.
* F body 1791..1796 (unchanged) and 1797 `jal 1667` (the C3 trampoline). -/
def jmpS : List (BitVec 32) := [0x3650006f]
def sel0S : List (BitVec 32) := [0x00040c63]
def lselS : List (BitVec 32) := [0x0019f313, 0x06030a63]
def lgS : List (BitVec 32) := [0x00600313, 0x00000393, 0x02c0006f]
def tselS : List (BitVec 32) := [0x0019f313, 0x00000393, 0x04731e63]
/-- Campaign T51: 1769 `jal 1927` (the old 1769..1774 test/cap words are dead nops), and the GT block 1927..1936:
`t1 = 4 - [27 ≤ i < 48] + [i = 48]` (`maxDigit 0 i - 1` on the even chains `0 < i ≤ 50`), `bne s3,zero,1775`;
chain 0: `t1 = 7` (never the step index: chain 0 keeps the HIGH half on every step), `jal 1775`. -/
def tjS : List (BitVec 32) := [0x2780006f]
def gtAS : List (BitVec 32) := [0x00400313, 0xfe598393, 0x0153b393, 0x40730333, 0xfd098393, 0x0013b393, 0x00730333,
  0xd80992e3]
def gtBS : List (BitVec 32) := [0x00700313, 0xd7dff06f]
def thdrS : List (BitVec 32) := [0x018e3383]
def gS : List (BitVec 32) := [0x010e3f03, 0x05ee3023, 0x047e3423, 0x040e3823, 0x040e3c23, 0x060e3023, 0x060e3423,
  0x030e0513, 0x04000593, 0x020e0613, 0x006a1463]
def g6S : List (BitVec 32) := [0x030e0613]
def ecallS : List (BitVec 32) := [0x00000073]
def gtailS : List (BitVec 32) := [0x001a0a13, 0xbe0ff06f]
def fS : List (BitVec 32) := [0x020e3023,0x020e3423,0x000e0513,0x04000593,0x030e0613]
def ftailS : List (BitVec 32) := [0xdf9ff06f]
sym_block blkJ := symRun { noAlias := true } jmpS (pcOf 1031) 100
sym_block blkSel0 := symRun { noAlias := true } sel0S (pcOf 1760) 100
sym_block blkLsel := symRun { noAlias := true } lselS (pcOf 1761) 100
sym_block blkLg := symRun { noAlias := true } lgS (pcOf 1763) 100
sym_block blkTsel := symRun { noAlias := true } tselS (pcOf 1766) 100
sym_block blkTj := symRun { noAlias := true } tjS (pcOf 1769) 100
sym_block blkGtA := symRun { noAlias := true } gtAS (pcOf 1927) 100
sym_block blkGtB := symRun { noAlias := true } gtBS (pcOf 1935) 100
sym_block blkThdr := symRun { noAlias := true } thdrS (pcOf 1775) 100
sym_block blkG := symRun { noAlias := true } gS (pcOf 1776) 100
sym_block blkG6 := symRun { noAlias := true } g6S (pcOf 1787) 100
sym_block blkGt := symRun { noAlias := true } gtailS (pcOf 1789) 100
sym_block blkF := symRun { noAlias := true } fS (pcOf 1791) 100
sym_block blkFt := symRun { noAlias := true } ftailS (pcOf 1797) 100

/-- The step block, its two HASH sites and the C3 trampoline. -/
structure StepCode (im : Image) : Prop where
  jmp : CodeAt im (pcOf 1031) jmpS
  sel0 : CodeAt im (pcOf 1760) sel0S
  lsel : CodeAt im (pcOf 1761) lselS
  lg : CodeAt im (pcOf 1763) lgS
  tsel : CodeAt im (pcOf 1766) tselS
  tj : CodeAt im (pcOf 1769) tjS
  gtA : CodeAt im (pcOf 1927) gtAS
  gtB : CodeAt im (pcOf 1935) gtBS
  thdr : CodeAt im (pcOf 1775) thdrS
  g : CodeAt im (pcOf 1776) gS
  g6 : CodeAt im (pcOf 1787) g6S
  gcall : CodeAt im (pcOf 1788) ecallS
  gtail : CodeAt im (pcOf 1789) gtailS
  f : CodeAt im (pcOf 1791) fS
  fcall : CodeAt im (pcOf 1796) ecallS
  ftail : CodeAt im (pcOf 1797) ftailS
  tramp0 : CodeAt im (pcOf 1667) ctr0
  tramp1 : CodeAt im (pcOf 1668) ctr1
  tramp2 : CodeAt im (pcOf 1669) ctr2
  tramp3 : CodeAt im (pcOf 1671) ctr3
  tramp4 : CodeAt im (pcOf 1676) ctr4

/-- Witness stack: is the chain a top G chain (even, `≤ 50`, on the top tree; T51)? -/
def topG (lay i : Nat) : Prop := lay = 0 ∧ i % 2 = 0 ∧ i ≤ 50
instance (lay i : Nat) : Decidable (topG lay i) := by unfold topG; infer_instance

/-- Extra steps of one chain rung over `rungK` (old header + HASH + `addi; jal`). Lower G: the block (18 steps, 19 at
step 6) and `addi; jal`; top G: 22 steps (+1 for `i ≥ 51`, +1 at the terminal step `maxDigit 0 i - 1`) and
`addi; jal`; F: the block (9 below, 10 for an odd top chain, 12 for an even top chain `> 52`) and the C3 trampoline. -/
def trX (lay i m : Nat) : Nat :=
  if lay ≠ 0 ∧ i % 2 = 1 then (if m = 6 then 14 else 13)
  else if topG lay i then
    21 + (if i = 0 then 2 else 0) + (if i ≠ 0 ∧ m + 1 = SigGolfCandidate.T3.maxDigit 0 i then 1 else 0)
  else (if lay = 0 then (if i % 2 = 1 then 5 else 7) else 4) + trX0 lay i m

theorem ne_of' {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x != BitVec.ofNat 64 y) = decide (x ≠ y) := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
    simp [hxy, this]
theorem eq_of' {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
    simp [hxy, this]
theorem and1_ofNat (x : Nat) : BitVec.ofNat 64 x &&& 1#64 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (1 : Nat) % 2 ^ 64 = 1 by norm_num, Nat.and_one_is_mod]
  omega

/-- C3 (FULL): the F chain tail `1797: jal 1667` and the trampoline 1667..1677. The HIGH half `hv` replaces the value
on chain 0 of a lower layer after step 6. -/
theorem tramp_spec {image : Image} (h : StepCode image) (s : MachineState)
    (hpc : s.pc = pcOf 1797) (lay i m : Nat) (hlay : lay < 2 ^ 64) (hi : i < 2 ^ 64) (hm : m < 2 ^ 63)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (lo hv : Digest) (hlo : DigAt s (CHAIN + 48) lo)
    (hhv : DigAt s (CHAIN + 64) hv) :
    ∃ t, Steps image s (2 + trX0 lay i m) (2 + trX0 lay i m) t ∧ t.pc = pcOf (1013 + 1) ∧
      t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧ DigAt t (CHAIN + 48) (if hiSel lay i m then hv else lo) ∧
      RegsExcept s t [.x6, .x7, .x20, .x28] ∧ Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  -- 1797: jal 1667
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1667 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound blkFt h.ftail s hpc (by simp [blkFt.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [blkFt.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  -- the final `addi s4,s4,1; jal 1014` at 1676
  have last : ∀ u : MachineState, u.pc = pcOf 1676 → u.getReg .x20 = BitVec.ofNat 64 m →
      ∃ t, Steps image u 2 2 t ∧ t.pc = pcOf (1013 + 1) ∧ t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
        RegsExcept u t [.x20] ∧ Frame u t (fun _ => False) := by
    intro u hu hu20
    refine ⟨_, symRun_sound blkC4 h.tramp4 u hu (by simp [blkC4.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [blkC4.res, E.eval]
    · simp only [Result.toState_getReg, blkC4.res, rv_simp, hu20]
      rw [ofNat_add_ofNat]
    · intro r hr; simp at hr; cases r <;> simp_all [blkC4.res, rv_simp] <;> rfl
    · intro A _ _; simp [blkC4.res, rv_simp]
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps image t0 1 1 t ∧ t.pc = (if i ≠ 0 then pcOf 1676 else pcOf 1668) ∧
      RegsExcept t0 t [] ∧ Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound blkC0 h.tramp0 t0 p0 (by simp [blkC0.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, blkC0.res, E.eval, CmpOp.eval, r0.get (by simp), h19]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ne_of' hi (by norm_num)]
      by_cases hi0 : i = 0 <;> simp [hi0]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g1 : ∀ r, r ∉ ([] : List Reg) → t1.getReg r = s.getReg r := fun r hr => (r0.trans r1).get hr
  by_cases hi0 : i ≠ 0
  · rw [if_pos hi0] at p1
    obtain ⟨t2, s2, p2, x2, r2, f2⟩ := last t1 p1 (by rw [g1 _ (by simp)]; exact h20)
    have hs : ¬ hiSel lay i m := fun hh => hi0 hh.2.1
    refine ⟨t2, ((s0.trans s1).trans s2).of_eq (by simp [trX0, hi0]) (by simp [trX0, hi0]), p2, x2, ?_,
      ((r0.trans r1).trans r2).mono (by simp), ((f0.trans f1).trans f2).mono (fun A _ hA => by simp_all)⟩
    rw [if_neg hs]
    exact hlo.frame ((f0.trans f1).trans f2) (by decide) (by simp) (by simp)
  have hi0' : i = 0 := by omega
  rw [if_neg hi0] at p1
  obtain ⟨t2, s2, p2, r2, f2⟩ : ∃ t, Steps image t1 1 1 t ∧ t.pc = (if lay = 0 then pcOf 1676 else pcOf 1669) ∧
      RegsExcept t1 t [] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound blkC1 h.tramp1 t1 p1 (by simp [blkC1.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, blkC1.res, E.eval, CmpOp.eval, g1 _ (by simp), h8]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, eq_of' hlay (by norm_num)]
      by_cases hl0 : lay = 0 <;> simp [hl0]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g2 : ∀ r, r ∉ ([] : List Reg) → t2.getReg r = s.getReg r := fun r hr => ((r0.trans r1).trans r2).get hr
  have f02 : Frame s t2 (fun _ => False) := ((f0.trans f1).trans f2).mono (fun A _ hA => by simp_all)
  by_cases hl0 : lay = 0
  · rw [if_pos hl0] at p2
    obtain ⟨t3, s3, p3, x3, r3, f3⟩ := last t2 p2 (by rw [g2 _ (by simp)]; exact h20)
    have hs : ¬ hiSel lay i m := fun hh => hh.1 hl0
    refine ⟨t3, (((s0.trans s1).trans s2).trans s3).of_eq (by simp [trX0, hi0', hl0]) (by simp [trX0, hi0', hl0]),
      p3, x3, ?_, (((r0.trans r1).trans r2).trans r3).mono (by simp),
      (f02.trans f3).mono (fun A _ hA => by simp_all)⟩
    rw [if_neg hs]
    exact hlo.frame (f02.trans f3) (by decide) (by simp) (by simp)
  rw [if_neg hl0] at p2
  obtain ⟨t3, s3, p3, r3, f3⟩ : ∃ t, Steps image t2 2 2 t ∧ t.pc = (if m ≠ 6 then pcOf 1676 else pcOf 1671) ∧
      RegsExcept t2 t [.x6] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound blkC2 h.tramp2 t2 p2 (by simp [blkC2.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, blkC2.res, E.eval, CmpOp.eval, g2 _ (by simp), h20]
      rw [show (6#64 : Word) = BitVec.ofNat 64 6 from rfl, ne_of' (by omega) (by norm_num)]
      by_cases hm6 : m = 6 <;> simp [hm6]
    · intro r hr; simp at hr; cases r <;> simp_all [blkC2.res, rv_simp] <;> rfl
    · intro A hA hn; simp [blkC2.res, rv_simp]
  have f03 : Frame s t3 (fun _ => False) := (f02.trans f3).mono (fun A _ hA => by simp_all)
  have g3 : ∀ r, r ∉ [.x6] → t3.getReg r = s.getReg r := fun r hr => ((((r0.trans r1).trans r2).trans r3)).get
    (by simpa using hr)
  by_cases hm6 : m ≠ 6
  · rw [if_pos hm6] at p3
    obtain ⟨t4, s4, p4, x4, r4, f4⟩ := last t3 p3 (by rw [g3 _ (by simp)]; exact h20)
    have hs : ¬ hiSel lay i m := fun hh => hm6 hh.2.2
    refine ⟨t4, ((((s0.trans s1).trans s2).trans s3).trans s4).of_eq (by simp [trX0, hi0', hl0, hm6])
      (by simp [trX0, hi0', hl0, hm6]), p4, x4, ?_, ((((r0.trans r1).trans r2).trans r3).trans r4).mono (by simp),
      (f03.trans f4).mono (fun A _ hA => by simp_all)⟩
    rw [if_neg hs]
    exact hlo.frame (f03.trans f4) (by decide) (by simp) (by simp)
  have hm6' : m = 6 := by omega
  rw [if_neg hm6] at p3
  have hs : hiSel lay i m := ⟨hl0, hi0', hm6'⟩
  have hobl : Oblig.all t3 blkC3.res.st.obl := by simp [blkC3.res, rv_simp]
  refine ⟨_, ((((s0.trans s1).trans s2).trans s3).trans (symRun_sound blkC3 h.tramp3 t3 p3 hobl)).of_eq
    (by simp [trX0, hi0', hl0, hm6', blkC3.res]) (by simp [trX0, hi0', hl0, hm6', blkC3.res]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blkC3.res, E.eval]
  · simp only [Result.toState_getReg, blkC3.res, rv_simp]
    rw [g3 .x20 (by simp), h20, hm6']; rfl
  · rw [if_pos hs]
    have hv3 := hhv.frame f03 (by decide) (by simp) (by simp)
    constructor
    · simp only [Result.toState_getMem, blkC3.res]
      t3n []
      exact hv3.1
    · simp only [Result.toState_getMem, blkC3.res]
      t3n []
      exact hv3.2
  · exact ((((r0.trans r1).trans r2).trans r3).trans (blkC3_regs t3)).mono (by simp)
  · have f4 : Frame t3 (blkC3.res.toState t3) (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
      intro A hA hn
      simp only [Result.toState_getMem, blkC3.res]
      t3n []
      have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
      rw [hA', if_neg (by simp only [CHAIN] at hn; omega), if_neg (by simp only [CHAIN] at hn; omega)]
    exact (f03.trans f4).mono (fun A _ hA => by simp_all)


/-- 1031 `jal 1760`, 1760 `beq s0,zero,1766`. -/
theorem jsel_spec {im : Image} (hc : StepCode im) (s : MachineState) (hpc : s.pc = pcOf 1031)
    (lay : Nat) (hlay : lay < 2 ^ 64) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if lay = 0 then pcOf 1766 else pcOf 1761) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have st0 := symRun_sound blkJ hc.jmp s hpc (by simp [blkJ.res, rv_simp])
  set u0 := blkJ.res.toState s with hu0
  have u0pc : u0.pc = pcOf 1760 := by simp [hu0, blkJ.res, E.eval]
  have u0r : ∀ r, u0.getReg r = s.getReg r := by intro r; cases r <;> rfl
  have u0m : ∀ A, u0.getMem A = s.getMem A := by intro A; rfl
  have st1 := symRun_sound blkSel0 hc.sel0 u0 u0pc (by simp [blkSel0.res, rv_simp])
  refine ⟨_, (st0.trans st1).of_eq (by simp [blkJ.res, blkSel0.res]) (by simp [blkJ.res, blkSel0.res]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blkSel0.res, E.eval, CmpOp.eval, u0r, h8]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, eq_of' hlay (by norm_num)]
    by_cases hl0 : lay = 0 <;> simp [hl0]
  · intro r _; rw [← u0r r]; cases r <;> simp [blkSel0.res, rv_simp] <;> rfl
  · intro A _ _; rw [← u0m (BitVec.ofNat 64 A)]; simp [blkSel0.res, rv_simp]

/-- 1761 `andi t1,s3,1`, 1762 `beq t1,zero,1791`. -/
theorem lsel_spec {im : Image} (hc : StepCode im) (s : MachineState) (hpc : s.pc = pcOf 1761) (i : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if i % 2 = 0 then pcOf 1791 else pcOf 1763) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blkLsel hc.lsel s hpc (by simp [blkLsel.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blkLsel.res, E.eval, CmpOp.eval, BinOp.eval, rv_simp, h19, and1_ofNat]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, eq_of' (by omega) (by norm_num)]
    by_cases h0 : i % 2 = 0 <;> simp [h0]
  · intro r hr; simp at hr; cases r <;> simp_all [blkLsel.res, rv_simp] <;> rfl
  · intro A _ _; simp [blkLsel.res, rv_simp]

/-- 1763..1765 `addi t1,zero,6; addi t2,zero,0; jal 1776` (lower G). -/
theorem lg_spec {im : Image} (hc : StepCode im) (s : MachineState) (hpc : s.pc = pcOf 1763) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 1776 ∧ t.getReg .x6 = BitVec.ofNat 64 6 ∧
      t.getReg .x7 = BitVec.ofNat 64 0 ∧ RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blkLg hc.lg s hpc (by simp [blkLg.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blkLg.res, E.eval]
  · simp [blkLg.res, rv_simp]
  · simp [blkLg.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blkLg.res, rv_simp] <;> rfl
  · intro A _ _; simp [blkLg.res, rv_simp]

/-- 1766..1768 `andi t1,s3,1; addi t2,zero,0; bne t1,t2,1791` (top). -/
theorem tsel_spec {im : Image} (hc : StepCode im) (s : MachineState) (hpc : s.pc = pcOf 1766) (i : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if i % 2 = 0 then pcOf 1769 else pcOf 1791) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blkTsel hc.tsel s hpc (by simp [blkTsel.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blkTsel.res, E.eval, CmpOp.eval, BinOp.eval, rv_simp, h19, and1_ofNat]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ne_of' (by omega) (by norm_num)]
    by_cases h0 : i % 2 = 0 <;> simp [h0]
  · intro r hr; simp at hr; cases r <;> simp_all [blkTsel.res, rv_simp] <;> rfl
  · intro A _ _; simp [blkTsel.res, rv_simp]

/-- Campaign T51: the GT block's step index (`t1`). -/
def gtT (i : Nat) : Nat := if i = 0 then 7 else if 27 ≤ i ∧ i < 48 then 3 else if i = 48 then 5 else 4
theorem gtT_top {i : Nat} (hi0 : i ≠ 0) (he : i % 2 = 0) : gtT i = SigGolfCandidate.T3.maxDigit 0 i - 1 := by
  unfold gtT SigGolfCandidate.T3.maxDigit
  simp only [if_pos rfl, if_neg hi0]
  split_ifs <;> omega
theorem maxDigit_top_bounds (i : Nat) : 4 ≤ SigGolfCandidate.T3.maxDigit 0 i ∧ SigGolfCandidate.T3.maxDigit 0 i ≤ 6 := by
  unfold SigGolfCandidate.T3.maxDigit
  simp only [if_pos rfl]
  split_ifs <;> omega
theorem gtA_x6 (i : Nat) (hi : i < 2 ^ 63) :
    ((4#64 - if (BitVec.ofNat 64 i - 27#64).ult 21#64 = true then 1#64 else 0#64) +
      if (BitVec.ofNat 64 i - 48#64).ult 1#64 = true then 1#64 else 0#64) =
    BitVec.ofNat 64 (if 27 ≤ i ∧ i < 48 then 3 else if i = 48 then 5 else 4) := by
  have e1 : (BitVec.ofNat 64 i - 27#64).ult 21#64 = decide (27 ≤ i ∧ i < 48) := by
    simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, decide_eq_decide]
    omega
  have e2 : (BitVec.ofNat 64 i - 48#64).ult 1#64 = decide (i = 48) := by
    simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, decide_eq_decide]
    omega
  rw [e1, e2]
  by_cases h1 : 27 ≤ i ∧ i < 48
  · have h2 : i ≠ 48 := by omega
    simp [h1, h2]
  · by_cases h2 : i = 48
    · subst h2; simp
    · simp [h1, h2]

/-- 1769 `jal 1927`, the GT block 1927..1936 (`t1 = gtT i`) and 1775 `ld t2,24(t3)` (header high word). -/
theorem gt_spec {im : Image} (hc : StepCode im) (s : MachineState) (hpc : s.pc = pcOf 1769) (i : Nat)
    (hi : i < 2 ^ 63) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s (10 + (if i = 0 then 2 else 0)) (10 + (if i = 0 then 2 else 0)) t ∧ t.pc = pcOf 1776 ∧
      t.getReg .x6 = BitVec.ofNat 64 (gtT i) ∧
      t.getReg .x7 = s.getMem (BitVec.ofNat 64 (CHAIN + 24)) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  have s0 := symRun_sound blkTj hc.tj s hpc (by simp [blkTj.res, rv_simp])
  set u0 := blkTj.res.toState s with hu0
  have u0pc : u0.pc = pcOf 1927 := by simp [hu0, blkTj.res, E.eval]
  have u0r : ∀ r, u0.getReg r = s.getReg r := by intro r; cases r <;> rfl
  have u0m : ∀ A, u0.getMem A = s.getMem A := by intro A; rfl
  have st := symRun_sound blkGtA hc.gtA u0 u0pc (by simp [blkGtA.res, rv_simp])
  set u := blkGtA.res.toState u0 with hu
  have upc : u.pc = (if i ≠ 0 then pcOf 1775 else pcOf 1935) := by
    simp only [hu, Result.toState_pc, blkGtA.res, E.eval, CmpOp.eval, u0r, h19]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ne_of' (by omega) (by norm_num)]
    by_cases h : i = 0 <;> simp [h]
  have u6 : u.getReg .x6 = BitVec.ofNat 64 (if 27 ≤ i ∧ i < 48 then 3 else if i = 48 then 5 else 4) := by
    simp only [hu, Result.toState_getReg, blkGtA.res, rv_simp, u0r, h19]
    exact gtA_x6 i hi
  have ur : RegsExcept u0 u [.x6, .x7] := by
    intro r hr; simp at hr; cases r <;> simp_all [hu, blkGtA.res, rv_simp] <;> rfl
  have um : ∀ A, u.getMem A = u0.getMem A := by intro A; simp [hu, blkGtA.res, rv_simp]
  obtain ⟨v, kv, sv, hkv, vpc, v6, vr, vm⟩ : ∃ v kv, Steps im u kv kv v ∧ kv = (if i = 0 then 2 else 0) ∧
      v.pc = pcOf 1775 ∧ v.getReg .x6 = BitVec.ofNat 64 (gtT i) ∧
      RegsExcept u v [.x6] ∧ (∀ A, v.getMem A = u.getMem A) := by
    by_cases h0 : i = 0
    · rw [if_neg (by simpa using h0)] at upc
      refine ⟨_, 2, symRun_sound blkGtB hc.gtB u upc (by simp [blkGtB.res, rv_simp]), by simp [h0],
        by simp [blkGtB.res, E.eval], ?_, ?_, ?_⟩
      · simp [blkGtB.res, rv_simp, gtT, h0]
      · intro r hr; simp at hr; cases r <;> simp_all [blkGtB.res, rv_simp] <;> rfl
      · intro A; simp [blkGtB.res, rv_simp]
    · rw [if_pos h0] at upc
      refine ⟨u, 0, Steps.refl _, by simp [h0], upc, ?_, fun _ _ => rfl, fun _ => rfl⟩
      rw [u6]; simp only [gtT, if_neg h0]
  have v28 : v.getReg .x28 = BitVec.ofNat 64 CHAIN := by
    rw [vr.get (by simp), ur.get (by simp), u0r]; exact h28
  have hobl : Oblig.all v blkThdr.res.st.obl := by
    simp only [blkThdr.res]
    t3n [v28, CHAIN]
    try norm_num
  have sw := symRun_sound blkThdr hc.thdr v vpc hobl
  have wr : RegsExcept v (blkThdr.res.toState v) [.x7] := by
    intro r hr; simp at hr; cases r <;> simp_all [blkThdr.res, rv_simp] <;> rfl
  have wm : ∀ A, (blkThdr.res.toState v).getMem A = v.getMem A := by intro A; simp [blkThdr.res, rv_simp]
  have w7 : (blkThdr.res.toState v).getReg .x7 = v.getMem (BitVec.ofNat 64 (CHAIN + 24)) := by
    simp only [Result.toState_getReg, blkThdr.res, rv_simp, v28]
    t3n [CHAIN]
  have u0r' : RegsExcept s u0 [] := fun r _ => u0r r
  refine ⟨_, (((s0.trans st).trans sv).trans sw).of_eq (by simp [hkv, blkTj.res, blkGtA.res, blkThdr.res]; omega)
    (by simp [hkv, blkTj.res, blkGtA.res, blkThdr.res]; omega), by simp [blkThdr.res, E.eval], ?_, ?_, ?_, ?_⟩
  · rw [wr.get (by simp)]; exact v6
  · rw [w7, vm, um, u0m]
  · exact (((u0r'.trans ur).trans vr).trans wr).mono (by simp)
  · intro A _ _; rw [wm, vm, um, u0m]

/-- The G body 1776..1786 (and 1787 at the terminal step `s4 = t1`): header copy, pads, HASH arguments. -/
theorem g_spec {im : Image} (hc : StepCode im) (s : MachineState) (hpc : s.pc = pcOf 1776) (m T : Nat)
    (hm : m < 2 ^ 63) (hT : T < 2 ^ 63) (h6 : s.getReg .x6 = BitVec.ofNat 64 T)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s (11 + (if m = T then 1 else 0)) (11 + (if m = T then 1 else 0)) t ∧ t.pc = pcOf 1788 ∧
      t.getReg .x10 = BitVec.ofNat 64 (CHAIN + 48) ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (if m = T then CHAIN + 48 else CHAIN + 32) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 64)) = s.getMem (BitVec.ofNat 64 (CHAIN + 16)) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 72)) = s.getReg .x7 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 80)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 88)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 96)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 104)) = 0 ∧
      RegsExcept s t [.x10, .x11, .x12, .x30] ∧ Frame s t (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) := by
  have hobl : Oblig.all s blkG.res.st.obl := by
    simp only [blkG.res]
    t3n [h28, CHAIN]
    try norm_num
  have st := symRun_sound blkG hc.g s hpc hobl
  set u := blkG.res.toState s with hu
  have upc : u.pc = (if m = T then pcOf 1787 else pcOf 1788) := by
    simp only [hu, Result.toState_pc, blkG.res, E.eval, CmpOp.eval, h20, h6]
    rw [ne_of' (by omega) (by omega)]
    by_cases h : m = T <;> simp [h]
  have ur : RegsExcept s u [.x10, .x11, .x12, .x30] := by
    intro r hr; simp at hr; cases r <;> simp_all [hu, blkG.res, rv_simp] <;> rfl
  have uf : Frame s u (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) := by
    intro A hA hn
    have hn' : ¬ (131552 ≤ A ∧ A < 131600) := by simpa [CHAIN] using hn
    simp only [hu, Result.toState_getMem, blkG.res]
    t3n [h28, CHAIN, Nat.mod_eq_of_lt hA]
    try (split_ifs <;> first | rfl | omega)
  have u10 : u.getReg .x10 = BitVec.ofNat 64 (CHAIN + 48) := by
    simp only [hu, Result.toState_getReg, blkG.res, rv_simp, h28]; rfl
  have u11 : u.getReg .x11 = BitVec.ofNat 64 64 := by
    simp only [hu, Result.toState_getReg, blkG.res, rv_simp]
  have u12 : u.getReg .x12 = BitVec.ofNat 64 (CHAIN + 32) := by
    simp only [hu, Result.toState_getReg, blkG.res, rv_simp, h28]; rfl
  have umem : u.getMem (BitVec.ofNat 64 (CHAIN + 64)) = s.getMem (BitVec.ofNat 64 (CHAIN + 16)) ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 72)) = s.getReg .x7 ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 80)) = 0 ∧ u.getMem (BitVec.ofNat 64 (CHAIN + 88)) = 0 ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 96)) = 0 ∧ u.getMem (BitVec.ofNat 64 (CHAIN + 104)) = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [hu, Result.toState_getMem, blkG.res]
      t3n [h28, CHAIN]
  by_cases ht : m = T
  · rw [if_pos ht] at upc
    have st6 := symRun_sound blkG6 hc.g6 u upc (by simp [blkG6.res, rv_simp])
    have wm : ∀ A, (blkG6.res.toState u).getMem A = u.getMem A := by intro A; simp [blkG6.res, rv_simp]
    have wr : RegsExcept u (blkG6.res.toState u) [.x12] := by
      intro r hr; simp at hr; cases r <;> simp_all [blkG6.res, rv_simp] <;> rfl
    refine ⟨_, (st.trans st6).of_eq (by simp [ht, blkG.res, blkG6.res]) (by simp [ht, blkG.res, blkG6.res]),
      by simp [blkG6.res, E.eval], by rw [wr.get (by simp)]; exact u10, by rw [wr.get (by simp)]; exact u11, ?_,
      by rw [wm]; exact umem.1, by rw [wm]; exact umem.2.1, by rw [wm]; exact umem.2.2.1,
      by rw [wm]; exact umem.2.2.2.1, by rw [wm]; exact umem.2.2.2.2.1, by rw [wm]; exact umem.2.2.2.2.2,
      (ur.trans wr).mono (by simp), fun A hA hn => (wm _).trans (uf A hA hn)⟩
    simp only [Result.toState_getReg, blkG6.res, rv_simp, if_pos ht, ur.get (show Reg.x28 ∉ _ by simp), h28]
    rfl
  · rw [if_neg ht] at upc
    refine ⟨u, st.of_eq (by simp [ht, blkG.res]) (by simp [ht, blkG.res]), upc, u10, u11, ?_, umem.1,
      umem.2.1, umem.2.2.1, umem.2.2.2.1, umem.2.2.2.2.1, umem.2.2.2.2.2, ur, uf⟩
    rw [if_neg ht]; exact u12

/-- The F body 1791..1795: zero the pad `CHAIN+32 .. CHAIN+48`, HASH arguments. -/
theorem f_spec {im : Image} (hc : StepCode im) (s : MachineState) (hpc : s.pc = pcOf 1791)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 1796 ∧
      t.getReg .x10 = BitVec.ofNat 64 CHAIN ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (CHAIN + 48) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0 ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun A => A = CHAIN + 32 ∨ A = CHAIN + 40) := by
  have hobl : Oblig.all s blkF.res.st.obl := by
    simp only [blkF.res]
    t3n [h28, CHAIN]
    try norm_num
  refine ⟨_, symRun_sound blkF hc.f s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blkF.res, E.eval]
  · simp only [Result.toState_getReg, blkF.res, rv_simp, h28]
  · simp only [Result.toState_getReg, blkF.res, rv_simp]
  · simp only [Result.toState_getReg, blkF.res, rv_simp, h28]; rfl
  · simp only [Result.toState_getMem, blkF.res]; t3n [h28, CHAIN]
  · simp only [Result.toState_getMem, blkF.res]; t3n [h28, CHAIN]
  · intro r hr; simp at hr; cases r <;> simp_all [blkF.res, rv_simp] <;> rfl
  · intro A hA hn
    have hn' : ¬ (A = 131520 ∨ A = 131528) := by simpa [CHAIN] using hn
    simp only [Result.toState_getMem, blkF.res]
    t3n [h28, CHAIN, Nat.mod_eq_of_lt hA]
    try (split_ifs <;> first | rfl | omega)

/-- 1789 `addi s4,s4,1`, 1790 `jal 1014`. -/
theorem gtail_spec {im : Image} (hc : StepCode im) (s : MachineState) (hpc : s.pc = pcOf 1789) (m : Nat)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf (1013 + 1) ∧ t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blkGt hc.gtail s hpc (by simp [blkGt.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [blkGt.res, E.eval]
  · simp only [Result.toState_getReg, blkGt.res, rv_simp, h20]
    rw [ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [blkGt.res, rv_simp] <;> rfl
  · intro A _ _; simp [blkGt.res, rv_simp]

/-! ### The whole rung after the header -/
theorem wordsOf_chainInputW_G {lay : Layer} {i : Nat} (hG : ClaudeWCT.WCT9.isG lay i = true) (tree leaf step : Nat)
    (v : Digest) :
    wordsOf (ClaudeWCT.WCT9.chainInputW lay tree leaf i step v) =
      [v.extractLsb' 0 64, v.extractLsb' 64 64, (chainHeader lay tree leaf i step).extractLsb' 0 64,
        (chainHeader lay tree leaf i step).extractLsb' 64 64, 0, 0, 0, 0] := by
  rw [ClaudeWCT.WCT9.chainInputW_G hG]
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]),
    wordsOf_append _ _ (by simp [bytesLE_length, zero16]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_zero16, wordsOf_bytesLE16,
    wordsOf_bytesLE16]
  rfl

theorem chainInputW_blocks (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (toQ (pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i step v))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [ClaudeWCT.WCT9.chainInputW_length]),
    blocks_toQ ⟨by rw [ClaudeWCT.WCT9.chainInputW_length]; omega, by rw [ClaudeWCT.WCT9.chainInputW_length]⟩,
    ClaudeWCT.WCT9.chainInputW_length]

/-- On an F chain the kept half is C3's `hiSel`. -/
theorem halfOf_chainHigh_F (lay : Layer) (i m : Nat) (hG : ClaudeWCT.WCT9.isG lay i = false) (a : BitVec 256) :
    ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.chainHigh lay i m) a =
      if hiSel lay.val i m then a.extractLsb' 128 128 else a.extractLsb' 0 128 := by
  have hl : (lay ≠ 0) ↔ lay.val ≠ 0 := ⟨fun h h' => h (Fin.ext h'), fun h h' => h (by rw [h']; rfl)⟩
  have h := ClaudeWCT.WCT9.chainHigh_eq_true_F (step := m) hG
  unfold hiSel
  cases hb : ClaudeWCT.WCT9.chainHigh lay i m
  · rw [if_neg]
    · rfl
    · intro hs
      have := h.mpr ⟨hl.mpr hs.1, hs.2.1, hs.2.2⟩
      rw [hb] at this; exact absurd this (by simp)
  · rw [if_pos]
    · rfl
    · obtain ⟨h1, h2, h3⟩ := h.mp hb; exact ⟨hl.mp h1, h2, h3⟩

/-- Witness stack: the G tail of a rung, from 1776 (`t1 = T`, `t2` = the header high word): the G body, its HASH
(`HIGH` half unless `m = T`) and `addi s4,s4,1; jal 1014`. -/
theorem g_rung {im : Image} (hc : StepCode im) (sk : BitVec 256) (t u : MachineState) (k : Nat)
    (su : Steps im t k k u) (upc : u.pc = pcOf 1776) (lay : Layer) (tree leaf i m T : Nat) (v : Digest)
    (hG : ClaudeWCT.WCT9.isG lay i = true) (hm : m < 2 ^ 63) (hT : T < 2 ^ 63)
    (hhi : m ≠ T → ClaudeWCT.WCT9.chainHigh lay i m = true)
    (hlo : m = T → ClaudeWCT.WCT9.chainHigh lay i m = false)
    (ur : RegsExcept t u [.x6, .x7]) (uf : Frame t u (fun _ => False))
    (h5 : t.getReg .x5 = 0) (h20 : t.getReg .x20 = BitVec.ofNat 64 m)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 CHAIN) (u6 : u.getReg .x6 = BitVec.ofNat 64 T)
    (u7 : u.getReg .x7 = (chainHeader lay tree leaf i m).extractLsb' 64 64)
    (h16 : t.getMem (BitVec.ofNat 64 (CHAIN + 16)) = (chainHeader lay tree leaf i m).extractLsb' 0 64)
    (hv : DigAt t (CHAIN + 48) v) :
    TSim im sk t (k + 14 + (if m = T then 1 else 0)) (k + 21 + (if m = T then 1 else 0)) 1 1
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i m)
        (ClaudeWCT.WCT9.chainInputW lay tree leaf i m v))
      (fun v' w => w.pc = pcOf (1013 + 1) ∧ w.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
        DigAt w (CHAIN + 48) v' ∧ RegsExcept t w [.x6, .x7, .x10, .x11, .x12, .x20, .x30] ∧
        Frame t w (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112)) := by
  rw [ClaudeWCT.WCT9.halfHash_eq]
  have g0 : ∀ r, r ∉ [Reg.x6, .x7] → u.getReg r = t.getReg r := fun r hr => ur.get hr
  obtain ⟨u2, su2, u2pc, u210, u211, u212, u264, u272, u280, u288, u296, u2104, u2r, u2f⟩ :=
    g_spec hc u upc m T hm hT u6 (by rw [g0 _ (by simp)]; exact h20) (by rw [g0 _ (by simp)]; exact h28)
  have f02 : Frame t u2 (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) :=
    (uf.trans u2f).mono (fun A _ h => by rcases h with h | h <;> simp_all)
  have r02 : RegsExcept t u2 [.x6, .x7, .x10, .x11, .x12, .x30] := (ur.trans u2r).mono (by simp)
  have v2 := hv.frame f02 (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)
  have hq : hashInput u2 = toQ (pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i m v)) := by
    have hl := ClaudeWCT.WCT9.chainInputW_length lay tree leaf i m v
    rw [pad64_of_aligned _ (by rw [hl])]
    refine hashInput_toQ u2 _ 0 (CHAIN + 48) hl u210 (by decide) (by decide) u211 (by decide) ?_
    rw [wordsOf_chainInputW_G hG, readWords_eight]
    rw [show CHAIN + 48 + 8 = CHAIN + 56 from rfl, show CHAIN + 48 + 16 = CHAIN + 64 from rfl,
      show CHAIN + 48 + 24 = CHAIN + 72 from rfl, show CHAIN + 48 + 32 = CHAIN + 80 from rfl,
      show CHAIN + 48 + 40 = CHAIN + 88 from rfl, show CHAIN + 48 + 48 = CHAIN + 96 from rfl,
      show CHAIN + 48 + 56 = CHAIN + 104 from rfl]
    rw [v2.1, v2.2, u264, u272, u280, u288, u296, u2104, uf.get (A := CHAIN + 16) (by decide) (by simp), h16, u7]
  have hvalid : hashArgumentsValid u2 = true := by
    by_cases ht : m = T
    · rw [if_pos ht] at u212
      exact hashArgs_const u2 (CHAIN + 48) 64 (CHAIN + 48) u210 u211 u212 (by decide) (by decide) (by decide)
        (by decide) (by decide)
    · rw [if_neg ht] at u212
      exact hashArgs_const u2 (CHAIN + 48) 64 (CHAIN + 32) u210 u211 u212 (by decide) (by decide) (by decide)
        (by decide) (by decide)
  have h5' : u2.getReg .x5 = 0 := by rw [r02.get (by simp)]; exact h5
  have hf2 : fetch im u2 = some (.base .ECALL) := (hc.gcall.fetch u2 u2pc).trans rfl
  refine (TSim.steps (su.trans su2) (TSim.publicHash_bind (k := 2) (c := 2) (n := 0) (b := 0)
    hf2 h5' hvalid hq (fun a => ?_))).of_eq rfl ?_ ?_ ?_ ?_
  · have hw20 : (writeHash u2 a).getReg .x20 = BitVec.ofNat 64 m := by
      rw [getReg_writeHash, r02.get (by simp)]; exact h20
    obtain ⟨w, sw, wpc, w20, wr, wf⟩ := gtail_spec hc (writeHash u2 a)
      (by rw [pc_writeHash, u2pc, pcOf_add4]) m hw20
    have hB : ∀ B, u2.getReg .x12 = BitVec.ofNat 64 B → B = CHAIN + 32 ∨ B = CHAIN + 48 →
        Frame u2 (writeHash u2 a) (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) := fun B h12 hB =>
      (Frame.writeHash u2 a B h12 (by rcases hB with rfl | rfl <;> decide)).mono
        (fun A _ h => by simp only [CHAIN] at hB ⊢; omega)
    have hwf : Frame u2 (writeHash u2 a) (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) := by
      by_cases ht : m = T
      · rw [if_pos ht] at u212; exact hB _ u212 (Or.inr rfl)
      · rw [if_neg ht] at u212; exact hB _ u212 (Or.inl rfl)
    have hval : DigAt (writeHash u2 a) (CHAIN + 48)
        (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.chainHigh lay i m) a) := by
      by_cases ht : m = T
      · rw [if_pos ht] at u212
        rw [hlo ht]
        exact DigAt.writeHash_lo u2 a (CHAIN + 48) u212 (by decide)
      · rw [if_neg ht] at u212
        rw [hhi ht]
        exact DigAt.writeHash_hi u2 a (CHAIN + 32) u212 (by decide)
    refine TSim.pure_steps sw ⟨wpc, w20, hval.frame wf (by decide) (by simp) (by simp), ?_, ?_⟩
    · have rr : RegsExcept u2 (writeHash u2 a) [] := fun r _ => getReg_writeHash u2 a r
      exact ((r02.trans rr).trans wr).mono (by simp)
    · exact ((f02.trans hwf).trans wf).mono (fun A _ h => by
        simp only [CHAIN] at h ⊢; rcases h with (h | h) | h <;> first | omega | exact h.elim)
  all_goals (try simp only [chainInputW_blocks])
  all_goals (by_cases ht : m = T <;> (try simp [ht]) <;> omega)

/-- Witness stack: one chain rung from the end of the header (pc 1031, `t3 = CHAIN`, header words stored) to the
loop head 1014: the step block 1760.., its HASH, and the tail (G: `addi; jal`; F: the C3 trampoline). It computes
`WCT9.halfHash (chainHigh) (chainInputW)` (top G chains: the top rule, terminal step `maxDigit 0 i - 1`) and writes
only `CHAIN+32 .. CHAIN+112`. -/
theorem pair_rung {im : Image} (hc : StepCode im) (sk : BitVec 256) (t : MachineState)
    (hpc : t.pc = pcOf 1031) (lay : Layer) (tree leaf i m : Nat) (v : Digest)
    (hi : i < 51) (hm : m < 8) (hm7 : lay.val ≠ 0 → m < 7)
    (hmt : lay.val = 0 → m < SigGolfCandidate.T3.maxDigit 0 i)
    (h5 : t.getReg .x5 = 0) (h8 : t.getReg .x8 = BitVec.ofNat 64 lay.val)
    (h19 : t.getReg .x19 = BitVec.ofNat 64 i) (h20 : t.getReg .x20 = BitVec.ofNat 64 m)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 CHAIN)
    (hz0 : t.getMem (BitVec.ofNat 64 CHAIN) = 0) (hz8 : t.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0)
    (h16 : t.getMem (BitVec.ofNat 64 (CHAIN + 16)) = (chainHeader lay tree leaf i m).extractLsb' 0 64)
    (h24 : t.getMem (BitVec.ofNat 64 (CHAIN + 24)) = (chainHeader lay tree leaf i m).extractLsb' 64 64)
    (hhz : (chainHeader lay tree leaf i m).extractLsb' 64 64 = 0)
    (hv : DigAt t (CHAIN + 48) v) :
    TSim im sk t (8 + trX lay.val i m) (15 + trX lay.val i m) 1 1
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i m)
        (ClaudeWCT.WCT9.chainInputW lay tree leaf i m v))
      (fun v' w => w.pc = pcOf (1013 + 1) ∧ w.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
        DigAt w (CHAIN + 48) v' ∧ RegsExcept t w [.x6, .x7, .x10, .x11, .x12, .x20, .x28, .x30] ∧
        Frame t w (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) ∧
        (¬ (lay.val ≠ 0 ∧ i % 2 = 1) → ¬ topG lay.val i → w.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0 ∧
          w.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0 ∧
          Frame t w (fun A => A = CHAIN + 32 ∨ A = CHAIN + 40 ∨ (CHAIN + 48 ≤ A ∧ A < CHAIN + 80)))) := by
  have hlay : lay.val < 4 := lay.isLt
  have hl : (lay ≠ 0) ↔ lay.val ≠ 0 := ⟨fun h h' => h (Fin.ext h'), fun h h' => h (by rw [h']; rfl)⟩
  obtain ⟨u, su, upc, ur, uf⟩ := jsel_spec hc t hpc lay.val (by omega) h8
  have g0 : ∀ r, r ∉ ([] : List Reg) → u.getReg r = t.getReg r := fun r hr => ur.get hr
  by_cases hLG : lay.val ≠ 0 ∧ i % 2 = 1
  · -- lower G
    rw [if_neg hLG.1] at upc
    obtain ⟨u1, su1, u1pc, u1r, u1f⟩ := lsel_spec hc u upc i (by rw [g0 _ (by simp)]; exact h19)
    rw [if_neg (by omega)] at u1pc
    obtain ⟨u2, su2, u2pc, u26, u27, u2r, u2f⟩ := lg_spec hc u1 u1pc
    have hGb : ClaudeWCT.WCT9.isG lay i = true := ClaudeWCT.WCT9.isG_eq_true.mpr (Or.inl ⟨hl.mpr hLG.1, hLG.2⟩)
    have hm6 := hm7 hLG.1
    have run := g_rung hc sk t u2 _ (su.trans (su1.trans su2)) u2pc lay tree leaf i m 6 v hGb (by omega) (by norm_num)
      (fun h => ClaudeWCT.WCT9.chainHigh_eq_true.mpr (Or.inl ⟨hl.mpr hLG.1, Or.inr ⟨hLG.2, by omega⟩⟩))
      (fun h => by subst h; exact ClaudeWCT.WCT9.chainHigh_six (by omega))
      ((ur.trans (u1r.trans u2r)).mono (by simp)) ((uf.trans (u1f.trans u2f)).mono (fun A _ h => by simp_all))
      h5 h20 h28 u26 (by rw [u27, hhz]; rfl) h16 hv
    refine (run.of_eq rfl ?_ ?_ rfl rfl).mono ?_
    · simp only [trX, if_pos hLG]; split_ifs <;> omega
    · simp only [trX, if_pos hLG]; split_ifs <;> omega
    · intro v' w hw
      exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1.mono (by simp), hw.2.2.2.2, fun hF => absurd hLG hF⟩
  by_cases hTG : topG lay.val i
  · -- top G
    obtain ⟨hl0, he, h50⟩ := hTG
    have hl0' : lay = 0 := Fin.ext hl0
    rw [if_pos hl0] at upc
    obtain ⟨u1, su1, u1pc, u1r, u1f⟩ := tsel_spec hc u upc i (by rw [g0 _ (by simp)]; exact h19)
    rw [if_pos he] at u1pc
    obtain ⟨u3, su3, u3pc, u36, u37, u3r, u3f⟩ := gt_spec hc u1 u1pc i (by omega)
      (by rw [u1r.get (by simp), g0 _ (by simp)]; exact h19)
      (by rw [u1r.get (by simp), g0 _ (by simp)]; exact h28)
    have f01 : Frame t u1 (fun _ => False) := (uf.trans u1f).mono (fun A _ h => by simp_all)
    have hGb : ClaudeWCT.WCT9.isG lay i = true := ClaudeWCT.WCT9.isG_eq_true.mpr (Or.inr ⟨hl0', he, h50⟩)
    have hmd := hmt hl0
    have hmb := maxDigit_top_bounds i
    have key : m = gtT i ↔ (i ≠ 0 ∧ m + 1 = SigGolfCandidate.T3.maxDigit 0 i) := by
      by_cases hi0 : i = 0
      · subst hi0; simp only [gtT, if_true]; constructor
        · intro h; omega
        · intro h; exact absurd rfl h.1
      · rw [gtT_top hi0 he]; constructor
        · intro h; exact ⟨hi0, by omega⟩
        · intro h; omega
    have run := g_rung hc sk t u3 _ (su.trans (su1.trans su3)) u3pc lay tree leaf i m
      (gtT i) v hGb (by omega) (by unfold gtT; split_ifs <;> omega)
      (fun h => ClaudeWCT.WCT9.chainHigh_eq_true.mpr (Or.inr ⟨hl0', ⟨he, h50⟩, by
        by_cases hi0 : i = 0
        · exact Or.inr hi0
        · left; have := gtT_top hi0 he; omega⟩))
      (fun h => by
        cases hb : ClaudeWCT.WCT9.chainHigh lay i m
        · rfl
        · rcases ClaudeWCT.WCT9.chainHigh_eq_true.mp hb with ⟨h1, -⟩ | ⟨-, -, h3⟩
          · exact absurd hl0' h1
          · have := key.mp h; omega)
      ((ur.trans (u1r.trans u3r)).mono (by simp))
      ((f01.trans u3f).mono (fun A _ h => by simp_all))
      h5 h20 h28 u36 (by rw [u37, f01.get (by decide) (by simp)]; exact h24) h16 hv
    refine (run.of_eq rfl ?_ ?_ rfl rfl).mono ?_
    · have hnLG : ¬ (lay.val ≠ 0 ∧ i % 2 = 1) := fun h => h.1 hl0
      have hT : topG lay.val i := ⟨hl0, he, h50⟩
      simp only [trX, if_neg hnLG, if_pos hT]
      by_cases hi0 : i = 0 <;> by_cases ht : m = gtT i <;>
        simp only [hi0, ht, if_true, if_false] <;> split_ifs <;> simp_all <;> omega
    · have hnLG : ¬ (lay.val ≠ 0 ∧ i % 2 = 1) := fun h => h.1 hl0
      have hT : topG lay.val i := ⟨hl0, he, h50⟩
      simp only [trX, if_neg hnLG, if_pos hT]
      by_cases hi0 : i = 0 <;> by_cases ht : m = gtT i <;>
        simp only [hi0, ht, if_true, if_false] <;> split_ifs <;> simp_all <;> omega
    · intro v' w hw
      exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1.mono (by simp), hw.2.2.2.2,
        fun _ hF => absurd ⟨hl0, he, h50⟩ hF⟩
  -- F path
  have hGb : ClaudeWCT.WCT9.isG lay i = false := by
    cases hb : ClaudeWCT.WCT9.isG lay i
    · rfl
    · rcases ClaudeWCT.WCT9.isG_eq_true.mp hb with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · exact absurd ⟨hl.mp h1, h2⟩ hLG
      · exact absurd ⟨by rw [h1]; rfl, h2, h3⟩ hTG
  rw [ClaudeWCT.WCT9.halfHash_eq, ClaudeWCT.WCT9.chainInputW_F hGb]
  -- reach 1791
  obtain ⟨u1, k1, su1, hk1, u1pc, u1r, u1f⟩ : ∃ u1 k1, Steps im t (2 + k1) (2 + k1) u1 ∧
      k1 = (if lay.val = 0 then (if i % 2 = 1 then 3 else 5) else 2) ∧ u1.pc = pcOf 1791 ∧
      RegsExcept t u1 [.x6, .x7] ∧ Frame t u1 (fun _ => False) := by
    by_cases hl0 : lay.val = 0
    · rw [if_pos hl0] at upc
      obtain ⟨u2, su2, u2pc, u2r, u2f⟩ := tsel_spec hc u upc i (by rw [g0 _ (by simp)]; exact h19)
      by_cases ho : i % 2 = 1
      · rw [if_neg (by omega)] at u2pc
        exact ⟨u2, 3, su.trans su2, by rw [if_pos hl0, if_pos ho], u2pc, (ur.trans u2r).mono (by simp),
          (uf.trans u2f).mono (fun A _ h => by simp_all)⟩
      · exact absurd ⟨hl0, by omega, by omega⟩ hTG
    · rw [if_neg hl0] at upc
      obtain ⟨u2, su2, u2pc, u2r, u2f⟩ := lsel_spec hc u upc i (by rw [g0 _ (by simp)]; exact h19)
      rw [if_pos (by omega)] at u2pc
      exact ⟨u2, 2, su.trans su2, by rw [if_neg hl0], u2pc, (ur.trans u2r).mono (by simp),
        (uf.trans u2f).mono (fun A _ h => by simp_all)⟩
  have g1 : ∀ r, r ∉ [Reg.x6, .x7] → u1.getReg r = t.getReg r := fun r hr => u1r.get hr
  obtain ⟨u2, su2, u2pc, u210, u211, u212, u232, u240, u2r, u2f⟩ :=
    f_spec hc u1 u1pc (by rw [g1 _ (by simp)]; exact h28)
  have f02 : Frame t u2 (fun A => A = CHAIN + 32 ∨ A = CHAIN + 40) :=
    (u1f.trans u2f).mono (fun A _ h => by rcases h with h | h; exact False.elim h; exact h)
  have r02 : RegsExcept t u2 [.x6, .x7, .x10, .x11, .x12] := (u1r.trans u2r).mono (by simp)
  have v2 := hv.frame f02 (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)
  have hq : hashInput u2 = toQ (pad64 (chainInput lay tree leaf i m v)) := by
    have hl := Keygen.chainInput_length lay tree leaf i m v
    rw [pad64_of_aligned _ (by rw [hl])]
    refine hashInput_toQ u2 _ 0 CHAIN hl u210 (by decide) (by decide) u211 (by decide) ?_
    rw [Keygen.wordsOf_chainInput, readWords_eight,
      f02 CHAIN (by decide) (by simp only [CHAIN]; omega), f02 (CHAIN + 8) (by decide) (by simp only [CHAIN]; omega),
      f02 (CHAIN + 16) (by decide) (by simp only [CHAIN]; omega),
      f02 (CHAIN + 24) (by decide) (by simp only [CHAIN]; omega), hz0, hz8, h16, h24, u232, u240, v2.1, v2.2]
  have hvalid : hashArgumentsValid u2 = true :=
    hashArgs_const u2 CHAIN 64 (CHAIN + 48) u210 u211 u212 (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have h5' : u2.getReg .x5 = 0 := by rw [r02.get (by simp)]; exact h5
  have hf2 : fetch im u2 = some (.base .ECALL) := (hc.fcall.fetch u2 u2pc).trans rfl
  refine (TSim.steps (su1.trans su2) (TSim.publicHash_bind (k := 2 + trX0 lay.val i m)
    (c := 2 + trX0 lay.val i m) (n := 0) (b := 0)
    (f := fun a => pure (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.chainHigh lay i m) a))
    hf2 h5' hvalid hq (fun a => ?_))).of_eq rfl ?_ ?_ ?_ ?_
  · obtain ⟨w, sw, wpc, w20, wv, wr, wf⟩ := tramp_spec hc (writeHash u2 a)
      (by rw [pc_writeHash, u2pc, pcOf_add4]) lay.val i m (by omega) (by omega) (by omega)
      (by rw [getReg_writeHash, r02.get (by simp)]; exact h8)
      (by rw [getReg_writeHash, r02.get (by simp)]; exact h19)
      (by rw [getReg_writeHash, r02.get (by simp)]; exact h20) _ _
      (DigAt.writeHash_lo u2 a (CHAIN + 48) u212 (by decide))
      (DigAt.writeHash_hi u2 a (CHAIN + 48) u212 (by decide))
    have hwf := Frame.writeHash u2 a (CHAIN + 48) u212 (by decide)
    have rr : RegsExcept u2 (writeHash u2 a) [] := fun r _ => getReg_writeHash u2 a r
    have fw : Frame u2 w (fun A => (CHAIN + 48 ≤ A ∧ A < CHAIN + 80) ∨ (A = CHAIN + 48 ∨ A = CHAIN + 56)) :=
      hwf.trans wf
    refine TSim.pure_steps sw ⟨wpc, w20, ?_, ((r02.trans rr).trans wr).mono (by simp), ?_, fun _ _ => ⟨?_, ?_, ?_⟩⟩
    · rw [halfOf_chainHigh_F lay i m hGb]; exact wv
    · exact (f02.trans fw).mono (fun A _ h => by
        simp only [CHAIN] at h ⊢; omega)
    · rw [fw.get (by decide) (by simp only [CHAIN]; omega)]; exact u232
    · rw [fw.get (by decide) (by simp only [CHAIN]; omega)]; exact u240
    · exact (f02.trans fw).mono (fun A _ h => by
        simp only [CHAIN] at h ⊢; omega)
  all_goals simp only [trX, if_neg hLG, if_neg hTG, hk1, Keygen.toQ_chainInput_blocks]
  all_goals by_cases hl0 : lay.val = 0 <;> by_cases ho : i % 2 = 1 <;> simp [hl0, ho] <;> omega

/-! ### Sign chain loop state (pairing stage 1)
`ChainPreS` is `Keygen.ChainPre` without the pad zeros `CHAIN+32/40` (the F path now clears them itself and a G step
overwrites them), with the value slot kept clear of the widened scratch `CHAIN+32 .. CHAIN+112` and lower chains of at
most 7 steps. `ChainWS` is the widened chain write set. -/
structure ChainPreS (s : MachineState) (lay : Layer) (tree leaf i cap e valp ret : Nat) : Prop where
  x5 : s.getReg .x5 = 0
  x1 : s.getReg .x1 = pcOf ret
  x8 : s.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 cap
  x19 : s.getReg .x19 = BitVec.ofNat 64 i
  x21 : s.getReg .x21 = BitVec.ofNat 64 e
  x23 : s.getReg .x23 = BitVec.ofNat 64 valp
  htree : tree < 2 ^ 32
  hi : i < 51
  hroute : tree * 2 ^ T3.height lay + leaf < 2 ^ 31
  hleaf : leaf < 2 ^ T3.height lay
  hcap : cap ≤ e
  he : e ≤ 8
  hlow : lay.val ≠ 0 → e ≤ 7
  hv8 : valp % 8 = 0
  hv : valp + 16 ≤ 2 ^ 24
  hvc : valp + 16 ≤ CHAIN ∨ CHAIN + 112 ≤ valp
  z0 : s.getMem (BitVec.ofNat 64 CHAIN) = 0
  z8 : s.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
def ChainWS (valp A : Nat) : Prop :=
  (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 112) ∨ (valp ≤ A ∧ A < valp + 16)
structure ChainHeadS (b : Nat) (s0 : MachineState) (valp m : Nat) (v : Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf (b + 1)
  x20 : t.getReg .x20 = BitVec.ofNat 64 m
  regs : RegsExcept s0 t chainRegs
  frame : Frame s0 t (ChainWS valp)
  val : DigAt t (CHAIN + 48) v
theorem ChainWS_of_chainW {valp A : Nat} (h : ChainW valp A) : ChainWS valp A := by
  unfold ChainW at h; unfold ChainWS; simp only [CHAIN] at *; omega

/-- The F pad words `CHAIN+32/40` are zero. -/
def Z32 (t : MachineState) : Prop :=
  t.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0
/-- An F chain (not a pairing-stage-1 G chain). -/
def FCh (lay : Layer) (i : Nat) : Prop := ¬ (lay.val ≠ 0 ∧ i % 2 = 1)
theorem Z32.frame {s t : MachineState} {W : Nat → Prop} (h : Z32 s) (hf : Frame s t W)
    (h32 : ¬ W (CHAIN + 32)) (h40 : ¬ W (CHAIN + 40)) : Z32 t :=
  ⟨(hf.get (by decide) h32).trans h.1, (hf.get (by decide) h40).trans h.2⟩
theorem FCh_top (i : Nat) : FCh 0 i := fun h => h.1 rfl

end SigGolfCandidate.T3M.Sign.Seed
end
-- ==== merged from T3M_Sign_SeedChain ====
section

namespace SigGolfCandidate.T3M.Sign.Seed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open Keygen Keygen.PackedBlocks
open SeedIndependent (SeedIndependentAt)
open SigGolfCandidate.T3 (Layer Digest chainInput chain shortHash header pad64 zero16 height chainHeader)
open SphincsSecurity (bytesLE bytesLE_length)
set_option backward.isDefEq.respectTransparency false
/-- Pairing stage 1: the header ends at `b + 18` (`jal 1760`, witness stack) with `t3 = CHAIN`. -/
theorem shared_header {image : Image} {b : Nat} (h : SeedIndependentAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (b + 9)) (lay : Layer)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) :
    ∃ t, Steps image s (headerK lay - 5) (headerK lay - 5) t ∧ t.pc = pcOf (b + 18) ∧
      SignHeaderPost s t (height lay) := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  fin_cases lay
  · exact sign_header_0 s hpc h8
  · exact sign_header_1 s hpc h8
  · exact sign_header_2 s hpc h8
  · exact sign_header_3 s hpc h8
theorem shared_header_source {image : Image} {b : Nat} (h : SeedIndependentAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (b + 9)) (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ height lay)
    (hi : i < 64) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    ∃ t, Steps image s (headerK lay - 5) (headerK lay - 5) t ∧ t.pc = pcOf (b + 18) ∧
      t.getReg .x28 = BitVec.ofNat 64 0x201A0 ∧
      t.getMem (BitVec.ofNat 64 (0x201A0 + 16)) = (chainHeader lay tree leaf i step).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (0x201A0 + 24)) = (chainHeader lay tree leaf i step).extractLsb' 64 64 ∧
      RegsExcept s t [.x6, .x7, .x28, .x30] ∧
      Frame s t (fun A => A = 0x201A0 + 16 ∨ A = 0x201A0 + 24) := by
  obtain ⟨t, st, pc, post⟩ := shared_header h s hpc lay h8
  refine ⟨t, st, pc, post.x28,
    post.low.trans (packedAt_source s lay tree leaf i step hr hf hi hs h8 h9 h18 h19 h20),
    ?_, post.regs, post.frame⟩
  exact (post.high.trans (routedAt_high_zero s lay tree leaf hr h9 h18)).trans
    (source_high_actual lay tree leaf i step hr hf hi hs).symm
theorem sub0_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 1) ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_0 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_0 h) s hpc (by simp [st_0, blk117_0.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_0, Result.toState_pc, E.eval]
  · simp [st_0, blk117_0.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_0, blk117_0.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_0, blk117_0.res, rv_simp]
theorem sub1_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1)) (m cap : Nat) (hm : m < 2 ^ 64) (hcap : cap < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h17 : s.getReg .x17 = BitVec.ofNat 64 cap) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if m = cap then pcOf (b + 2) else pcOf (b + 8)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_1 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_1 h) s hpc (by simp [st_1, blk117_1.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_1, rebase, blk117_1.res, E.eval, CmpOp.eval, h20, h17]
    by_cases hmc : m = cap
    · subst hmc; simp
    · rw [if_neg hmc]
      have : BitVec.ofNat 64 m ≠ BitVec.ofNat 64 cap := fun he => hmc ((ofNat_inj hm hcap).mp he)
      simp [this]
  · intro r hr; cases r <;> simp_all [st_1, blk117_1.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_1, blk117_1.res, rv_simp]
theorem sub2_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 2)) (valp : Nat) (h23 : s.getReg .x23 = BitVec.ofNat 64 valp)
    (hv8 : valp % 8 = 0) (hv : valp + 16 ≤ 2 ^ 24) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (b + 8) ∧
      t.getMem (BitVec.ofNat 64 valp) = s.getMem (BitVec.ofNat 64 (CHAIN + 48)) ∧
      t.getMem (BitVec.ofNat 64 (valp + 8)) = s.getMem (BitVec.ofNat 64 (CHAIN + 56)) ∧
      RegsExcept s t [.x6, .x7, .x29] ∧ Frame s t (fun A => A = valp ∨ A = valp + 8) := by
  have hrun := run_2 h.2.1
  have hobl : Oblig.all s st_2.obl := by
    simp only [st_2, blk117_2.res]
    t3n [h23]
    omega
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_2 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_2, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, st_2, blk117_2.res]
    t3n [h23]
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, st_2, blk117_2.res]
    t3n [h23]
  · intro r hr; simp at hr; cases r <;> simp_all [st_2, blk117_2.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, st_2, blk117_2.res]
    t3n [h23]
    rw [if_neg (by omega), if_neg (by omega)]
theorem sub8_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 8)) (m e : Nat) (hm : m < 2 ^ 64) (he : e < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h21 : s.getReg .x21 = BitVec.ofNat 64 e) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if m = e then pcOf (b + 26) else pcOf (b + 9)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_8 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_8 h) s hpc (by simp [st_8, blk117_8.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_8, rebase, blk117_8.res, E.eval, CmpOp.eval, h20, h21]
    by_cases hme : m = e
    · subst hme; simp
    · rw [if_neg hme]
      have : BitVec.ofNat 64 m ≠ BitVec.ofNat 64 e := fun he' => hme ((ofNat_inj hm he).mp he')
      simp [this]
  · intro r hr; cases r <;> simp_all [st_8, blk117_8.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_8, blk117_8.res, rv_simp]
abbrev sub9_spec {image : Image} {b : Nat} := @shared_header_source image b
theorem sub26_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 26)) (k : Nat) (h1 : s.getReg .x1 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_26 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_26 h) s hpc (by simp [st_26, blk117_26.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_26, blk117_26.res, rv_simp, h1, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_26, blk117_26.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_26, blk117_26.res, rv_simp]
theorem sumTo_split (F : Nat → Nat) (a : Nat) : ∀ n, sumTo F (a + 1 + n) = sumTo F a + F a + sumTo (fun j => F (a + 1 + j)) n
  | 0 => by simp [sumTo]
  | n + 1 => by
    rw [show a + 1 + (n + 1) = (a + 1 + n) + 1 by omega, sumTo, sumTo_split F a n, sumTo]; omega
/-- C3 (FULL): steps of one chain run of `e` hashes (entry 1, per step `rungK + trX`, exit 9). -/
def chainK (lay : Layer) (i e : Nat) : Nat := sumTo (fun m => rungK lay + trX lay.val i m) e + 10
/-- C3 (FULL): cycles of one chain run of `e` hashes. -/
def chainCy (lay : Layer) (i e : Nat) : Nat := sumTo (fun m => rungC lay + trX lay.val i m) e + 10
/-- C2: the half of a lower leaf / node hash output kept by the machine (`16` = the HIGH half, for even indices). -/
def hiO (x : Nat) : Nat := if x % 2 = 0 then 16 else 0
theorem halfSel_eval (x : Nat) :
    BinOp.eval .sll (BinOp.eval .xor (BinOp.eval .and (BitVec.ofNat 64 x) 1#64) 1#64) 4#64 =
      BitVec.ofNat 64 (hiO x) := by
  show BinOp.eval .sll (BinOp.eval .xor (BitVec.ofNat 64 x &&& 1#64) 1#64) 4#64 = _
  rw [and1_ofNat]; unfold hiO
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> simp [h] <;> decide
theorem DigAt.writeHash_lowerHalf (t : MachineState) (a : BitVec 256) (B lay x : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 B) (hB : B + 32 < 2 ^ 64) (hl : 1 ≤ lay ∧ lay < 4) :
    DigAt (writeHash t a) (B + hiO x) (ClaudeWCT.WCT9.lowerHalf lay x a) := by
  unfold hiO ClaudeWCT.WCT9.lowerHalf ClaudeWCT.WCT9.halfOf ClaudeWCT.WCT9.lowerHigh
  by_cases hx : x % 2 = 0
  · simp only [hx, hl, if_true, decide_true, Bool.and_self]; exact DigAt.writeHash_hi t a B h12 hB
  · simp only [hx, hl, if_false, decide_true, decide_false, Bool.and_false, Bool.false_eq_true, Nat.add_zero]
    exact DigAt.writeHash_lo t a B h12 hB
/- Witness stack: the reference-image chain loop (`chain_entry` .. `chainRun_tsim` over `SeedIndependentAt`,
  i.e. `Images.signReferenceImage`) was removed: it had no users and the reference image does not contain the new
  step block 1760..1797. The installed chain is `ClaudeWCT.W9.Machine.Sign.SharedChain` below. -/
end SigGolfCandidate.T3M.Sign.Seed

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 10000
abbrev buffer (lay chain step : Nat) : Nat := 0x6e000 + 8192 * lay + 128 * chain + 16 * step
def copyCode : List (BitVec 32) := [0x6ee37,0xe0e13,0xd41393,0x7e0e33,0x799393,0x7e0e33,0x4a1393,0x7e0e33,0x20eb7,0x1d0e8e93,0xeb303,0x8eb383,0x6e3023,0x7e3423]
sym_block prefix_copy := symRun { noAlias := true } copyCode (pcOf 22032) 100
theorem buffer_bounds {lay chain step : Nat} (hl : 1 ≤ lay) (hh : lay ≤ 3)
    (hc : chain < 43) (hs : step < 8) :
    0x70000 ≤ buffer lay chain step ∧ buffer lay chain step + 16 ≤ 0x75580 ∧
    buffer lay chain step % 8 = 0 := by
  simp only [buffer]
  omega

theorem copy_steps {im : Image} (hc : CodeAt im (pcOf 22032) copyCode)
    (s : MachineState) (hp : s.pc = pcOf 22032) (lay chain step : Nat)
    (hl : 1 ≤ lay) (hh : lay ≤ 3) (hj : chain < 43) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 chain)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    ∃ t, Steps im s 14 14 t ∧ t.pc = pcOf 22046 ∧
      t.getMem (BitVec.ofNat 64 (buffer lay chain step)) = s.getMem 0x201d0 ∧
      t.getMem (BitVec.ofNat 64 (buffer lay chain step + 8)) = s.getMem 0x201d8 ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = buffer lay chain step ∨ A = buffer lay chain step + 8) := by
  have hb := buffer_bounds hl hh hj hs
  have ho : Oblig.all s prefix_copy.res.st.obl := by
    simp only [prefix_copy.res]
    t3n [h8, h19, h20]
    omega
  refine ⟨_, symRun_sound prefix_copy hc s hp ho, ?_, ?_, ?_, ?_, ?_⟩
  · simp [prefix_copy.res, Result.toState_pc, E.eval, pcOf]
  · simp only [Result.toState_getMem, prefix_copy.res]
    t3n [h8, h19, h20, buffer]
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, prefix_copy.res]
    t3n [h8, h19, h20, buffer]
    rw [if_pos (by omega)]
  · intro r hr; simp at hr; cases r <;> simp_all [prefix_copy.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, prefix_copy.res]
    t3n [h8, h19, h20, buffer]
    simp only [buffer] at hn
    rw [if_neg (by omega), if_neg (by omega)]
end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.Legacy.Riscv

/-- Bind the checked prefix copy to the installed Sign program. -/
theorem copy_codeAt : CodeAt Images.signImage (pcOf 22032) copyCode := by
  apply codeAt_sign_last <;> decide +kernel

end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

def entryCode : List (BitVec 32) := [0x6040c63]

sym_block prefix_entry := symRun { noAlias := true } entryCode (pcOf 22016) 100

theorem entry_steps {im : Image} (hc : CodeAt im (pcOf 22016) entryCode)
    (s : MachineState) (hp : s.pc = pcOf 22016) :
    Steps im s 1 1 (prefix_entry.res.toState s) := by
  apply symRun_sound prefix_entry hc s hp
  simp [prefix_entry.res, rv_simp, accessValid_iff, MEMORY_BYTES]


def loadIndexCode : List (BitVec 32) := [0x20e37,0x550e0e13,0xe3303,0xfff40393,0x38a63]

sym_block prefix_loadIndex := symRun { noAlias := true } loadIndexCode (pcOf 22017) 100

theorem loadIndex_steps {im : Image} (hc : CodeAt im (pcOf 22017) loadIndexCode)
    (s : MachineState) (hp : s.pc = pcOf 22017) :
    Steps im s 5 5 (prefix_loadIndex.res.toState s) := by
  apply symRun_sound prefix_loadIndex hc s hp
  simp [prefix_loadIndex.res, rv_simp, accessValid_iff, MEMORY_BYTES]


def testLayer2Code : List (BitVec 32) := [0xffe40393,0x38c63]

sym_block prefix_testLayer2 := symRun { noAlias := true } testLayer2Code (pcOf 22022) 100

theorem testLayer2_steps {im : Image} (hc : CodeAt im (pcOf 22022) testLayer2Code)
    (s : MachineState) (hp : s.pc = pcOf 22022) :
    Steps im s 2 2 (prefix_testLayer2.res.toState s) := by
  apply symRun_sound prefix_testLayer2 hc s hp
  simp [prefix_testLayer2.res, rv_simp, accessValid_iff, MEMORY_BYTES]


def select3Code : List (BitVec 32) := [0x3f37313,0x180006f]

sym_block prefix_select3 := symRun { noAlias := true } select3Code (pcOf 22024) 100

theorem select3_steps {im : Image} (hc : CodeAt im (pcOf 22024) select3Code)
    (s : MachineState) (hp : s.pc = pcOf 22024) :
    Steps im s 2 2 (prefix_select3.res.toState s) := by
  apply symRun_sound prefix_select3 hc s hp
  simp [prefix_select3.res, rv_simp, accessValid_iff, MEMORY_BYTES]


def select1Code : List (BitVec 32) := [0xc35313,0x7f37313,0xc0006f]

sym_block prefix_select1 := symRun { noAlias := true } select1Code (pcOf 22026) 100

theorem select1_steps {im : Image} (hc : CodeAt im (pcOf 22026) select1Code)
    (s : MachineState) (hp : s.pc = pcOf 22026) :
    Steps im s 3 3 (prefix_select1.res.toState s) := by
  apply symRun_sound prefix_select1 hc s hp
  simp [prefix_select1.res, rv_simp, accessValid_iff, MEMORY_BYTES]


def select2Code : List (BitVec 32) := [0x635313,0x3f37313]

sym_block prefix_select2 := symRun { noAlias := true } select2Code (pcOf 22029) 100

theorem select2_steps {im : Image} (hc : CodeAt im (pcOf 22029) select2Code)
    (s : MachineState) (hp : s.pc = pcOf 22029) :
    Steps im s 2 2 (prefix_select2.res.toState s) := by
  apply symRun_sound prefix_select2 hc s hp
  simp [prefix_select2.res, rv_simp, accessValid_iff, MEMORY_BYTES]


def selectedCode : List (BitVec 32) := [0x3231e63]

sym_block prefix_selected := symRun { noAlias := true } selectedCode (pcOf 22031) 100

theorem selected_steps {im : Image} (hc : CodeAt im (pcOf 22031) selectedCode)
    (s : MachineState) (hp : s.pc = pcOf 22031) :
    Steps im s 1 1 (prefix_selected.res.toState s) := by
  apply symRun_sound prefix_selected hc s hp
  simp [prefix_selected.res, rv_simp, accessValid_iff, MEMORY_BYTES]


def resumeCode : List (BitVec 32) := [0x11a0463]

sym_block prefix_resume := symRun { noAlias := true } resumeCode (pcOf 22046) 100

theorem resume_steps {im : Image} (hc : CodeAt im (pcOf 22046) resumeCode)
    (s : MachineState) (hp : s.pc = pcOf 22046) :
    Steps im s 1 1 (prefix_resume.res.toState s) := by
  apply symRun_sound prefix_resume hc s hp
  simp [prefix_resume.res, rv_simp, accessValid_iff, MEMORY_BYTES]


theorem entry_pc (s : MachineState) :
    (prefix_entry.res.toState s).pc =
      if s.getReg .x8 = 0 then pcOf 22046 else pcOf 22017 := by
  simp [Result.toState_pc, prefix_entry.res, E.eval, CmpOp.eval, pcOf]

theorem loadIndex_mem (s : MachineState) :
    (prefix_loadIndex.res.toState s).getReg .x6 = s.getMem 0x20550 := by
  simp [prefix_loadIndex.res, rv_simp]

theorem selected_pc (s : MachineState) :
    (prefix_selected.res.toState s).pc =
      if s.getReg .x6 = s.getReg .x18 then pcOf 22032 else pcOf 22046 := by
  simp [Result.toState_pc, prefix_selected.res, E.eval, CmpOp.eval, pcOf]

theorem resume_pc (s : MachineState) :
    (prefix_resume.res.toState s).pc =
      if s.getReg .x20 = s.getReg .x17 then pcOf 22048 else pcOf 22047 := by
  simp [Result.toState_pc, prefix_resume.res, E.eval, CmpOp.eval, pcOf]

end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
structure GuardAt (im : Image) : Prop where
  entry : CodeAt im (pcOf 22016) entryCode
  loadIndex : CodeAt im (pcOf 22017) loadIndexCode
  testLayer2 : CodeAt im (pcOf 22022) testLayer2Code
  select3 : CodeAt im (pcOf 22024) select3Code
  select1 : CodeAt im (pcOf 22026) select1Code
  select2 : CodeAt im (pcOf 22029) select2Code
  selected : CodeAt im (pcOf 22031) selectedCode

def selectionWord (index : Word) (lay : Nat) : Word :=
  if lay = 1 then (index >>> (12 : Word)) &&& 127
  else if lay = 2 then (index >>> (6 : Word)) &&& 63 else index &&& 63

/-- Every valid lower-layer prefix guard reaches exactly the selected-leaf branch.
It costs at most eleven ordinary instructions and writes no memory. -/
theorem guard_steps {im : Image} (hc : GuardAt im) (s : MachineState)
    (hp : s.pc = pcOf 22016) (lay : Nat) (hl : 1 ≤ lay) (hh : lay ≤ 3)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ n t, n ≤ 11 ∧ Steps im s n n t ∧
      t.pc = (if selectionWord (s.getMem 0x20550) lay = s.getReg .x18
        then pcOf 22032 else pcOf 22046) ∧
      t.getReg .x6 = selectionWord (s.getMem 0x20550) lay ∧
      RegsExcept s t [.x6, .x7, .x28] ∧ Frame s t (fun _ => False) := by
  interval_cases lay
  ·
    let t0 := prefix_entry.res.toState s
    have r0 := entry_steps hc.entry s hp
    let t1 := prefix_loadIndex.res.toState t0
    have p1 : t0.pc = pcOf 22017 := by simp [t0, prefix_entry.res, rv_simp, h8, pcOf]
    have r1 := loadIndex_steps hc.loadIndex t0 p1
    let t2 := prefix_select1.res.toState t1
    have p2 : t1.pc = pcOf 22026 := by simp [t0, t1, prefix_entry.res, prefix_loadIndex.res, rv_simp, h8, pcOf]
    have r2 := select1_steps hc.select1 t1 p2
    let t3 := prefix_selected.res.toState t2
    have p3 : t2.pc = pcOf 22031 := by simp [t0, t1, t2, prefix_entry.res, prefix_loadIndex.res, prefix_select1.res, rv_simp, h8, pcOf]
    have r3 := selected_steps hc.selected t2 p3
    refine ⟨10, t3, by decide, (((r0.trans r1).trans r2).trans r3), ?_, ?_, ?_, ?_⟩
    · simp [t0, t1, t2, t3, prefix_entry.res, prefix_loadIndex.res, prefix_select1.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
    · simp [t0, t1, t2, t3, prefix_entry.res, prefix_loadIndex.res, prefix_select1.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
    · intro r hr; cases r <;> simp_all [t0, t1, t2, t3, prefix_entry.res, prefix_loadIndex.res, prefix_select1.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord] <;> rfl
    · intro A hA hn; simp [t0, t1, t2, t3, prefix_entry.res, prefix_loadIndex.res, prefix_select1.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
  ·
    let t0 := prefix_entry.res.toState s
    have r0 := entry_steps hc.entry s hp
    let t1 := prefix_loadIndex.res.toState t0
    have p1 : t0.pc = pcOf 22017 := by simp [t0, prefix_entry.res, rv_simp, h8, pcOf]
    have r1 := loadIndex_steps hc.loadIndex t0 p1
    let t2 := prefix_testLayer2.res.toState t1
    have p2 : t1.pc = pcOf 22022 := by simp [t0, t1, prefix_entry.res, prefix_loadIndex.res, rv_simp, h8, pcOf]
    have r2 := testLayer2_steps hc.testLayer2 t1 p2
    let t3 := prefix_select2.res.toState t2
    have p3 : t2.pc = pcOf 22029 := by simp [t0, t1, t2, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, rv_simp, h8, pcOf]
    have r3 := select2_steps hc.select2 t2 p3
    let t4 := prefix_selected.res.toState t3
    have p4 : t3.pc = pcOf 22031 := by simp [t0, t1, t2, t3, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select2.res, rv_simp, h8, pcOf]
    have r4 := selected_steps hc.selected t3 p4
    refine ⟨11, t4, by decide, ((((r0.trans r1).trans r2).trans r3).trans r4), ?_, ?_, ?_, ?_⟩
    · simp [t0, t1, t2, t3, t4, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select2.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
    · simp [t0, t1, t2, t3, t4, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select2.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
    · intro r hr; cases r <;> simp_all [t0, t1, t2, t3, t4, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select2.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord] <;> rfl
    · intro A hA hn; simp [t0, t1, t2, t3, t4, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select2.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
  ·
    let t0 := prefix_entry.res.toState s
    have r0 := entry_steps hc.entry s hp
    let t1 := prefix_loadIndex.res.toState t0
    have p1 : t0.pc = pcOf 22017 := by simp [t0, prefix_entry.res, rv_simp, h8, pcOf]
    have r1 := loadIndex_steps hc.loadIndex t0 p1
    let t2 := prefix_testLayer2.res.toState t1
    have p2 : t1.pc = pcOf 22022 := by simp [t0, t1, prefix_entry.res, prefix_loadIndex.res, rv_simp, h8, pcOf]
    have r2 := testLayer2_steps hc.testLayer2 t1 p2
    let t3 := prefix_select3.res.toState t2
    have p3 : t2.pc = pcOf 22024 := by simp [t0, t1, t2, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, rv_simp, h8, pcOf]
    have r3 := select3_steps hc.select3 t2 p3
    let t4 := prefix_selected.res.toState t3
    have p4 : t3.pc = pcOf 22031 := by simp [t0, t1, t2, t3, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select3.res, rv_simp, h8, pcOf]
    have r4 := selected_steps hc.selected t3 p4
    refine ⟨11, t4, by decide, ((((r0.trans r1).trans r2).trans r3).trans r4), ?_, ?_, ?_, ?_⟩
    · simp [t0, t1, t2, t3, t4, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select3.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
    · simp [t0, t1, t2, t3, t4, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select3.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
    · intro r hr; cases r <;> simp_all [t0, t1, t2, t3, t4, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select3.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord] <;> rfl
    · intro A hA hn; simp [t0, t1, t2, t3, t4, prefix_entry.res, prefix_loadIndex.res, prefix_testLayer2.res, prefix_select3.res, prefix_selected.res, rv_simp, h8, pcOf, selectionWord]
end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

def resumeMissWord : BitVec 32 := 4153323631
def resumeHitWord : BitVec 32 := 4123963503

sym_block prefix_resumeMiss := symRun { noAlias := true } [resumeMissWord] (pcOf 22047) 10
sym_block prefix_resumeHit := symRun { noAlias := true } [resumeHitWord] (pcOf 22048) 10

/-- Return to the original chain branch with no additional HASH or memory write. -/
theorem resume_full_steps {im : Image}
    (hc : CodeAt im (pcOf 22046) resumeCode)
    (hm : CodeAt im (pcOf 22047) [resumeMissWord])
    (hh : CodeAt im (pcOf 22048) [resumeHitWord])
    (s : MachineState) (hp : s.pc = pcOf 22046) :
    ∃ t, Steps im s 2 2 t ∧
      t.pc = (if s.getReg .x20 = s.getReg .x17 then pcOf 1015 else pcOf 1021) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  let u := prefix_resume.res.toState s
  have first := resume_steps hc s hp
  have hpc : u.pc = if s.getReg .x20 = s.getReg .x17 then pcOf 22048 else pcOf 22047 := resume_pc s
  by_cases he : s.getReg .x20 = s.getReg .x17
  · rw [if_pos he] at hpc ⊢
    have last := symRun_sound prefix_resumeHit hh u hpc (by simp [prefix_resumeHit.res, rv_simp])
    refine ⟨prefix_resumeHit.res.toState u, first.trans last, ?_, ?_, ?_⟩
    · simp [prefix_resumeHit.res, rv_simp, pcOf]
    · intro r hr; cases r <;> simp [u, prefix_resume.res, prefix_resumeHit.res, rv_simp] <;> rfl
    · intro A hA hn; simp [u, prefix_resume.res, prefix_resumeHit.res, rv_simp]
  · rw [if_neg he] at hpc ⊢
    have last := symRun_sound prefix_resumeMiss hm u hpc (by simp [prefix_resumeMiss.res, rv_simp])
    refine ⟨prefix_resumeMiss.res.toState u, first.trans last, ?_, ?_, ?_⟩
    · simp [prefix_resumeMiss.res, rv_simp, pcOf]
    · intro r hr; cases r <;> simp [u, prefix_resume.res, prefix_resumeMiss.res, rv_simp] <;> rfl
    · intro A hA hn; simp [u, prefix_resume.res, prefix_resumeMiss.res, rv_simp]

end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Preserve each selected lower-chain prefix and resume the original branch.
The extra storage is disjoint from all original producer buffers. -/
theorem prefix_steps {im : Image} (hg : GuardAt im)
    (hc : CodeAt im (pcOf 22032) copyCode)
    (hr : CodeAt im (pcOf 22046) resumeCode)
    (hm : CodeAt im (pcOf 22047) [resumeMissWord])
    (hhit : CodeAt im (pcOf 22048) [resumeHitWord])
    (s : MachineState) (hp : s.pc = pcOf 22016) (lay chain step : Nat)
    (hl : 1 ≤ lay) (hh : lay ≤ 3) (hj : chain < 43) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 chain)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    ∃ n t, n ≤ 27 ∧ Steps im s n n t ∧
      t.pc = (if s.getReg .x20 = s.getReg .x17 then pcOf 1015 else pcOf 1021) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = buffer lay chain step ∨ A = buffer lay chain step + 8) ∧
      (selectionWord (s.getMem 0x20550) lay = s.getReg .x18 →
        t.getMem (BitVec.ofNat 64 (buffer lay chain step)) = s.getMem 0x201d0 ∧
        t.getMem (BitVec.ofNat 64 (buffer lay chain step + 8)) = s.getMem 0x201d8) := by
  obtain ⟨n,u,hn,gu,upc,u6,ur,uf⟩ := guard_steps hg s hp lay hl hh h8
  by_cases selected : selectionWord (s.getMem 0x20550) lay = s.getReg .x18
  · rw [if_pos selected] at upc
    obtain ⟨v,cv,vpc,v0,v8,vr,vf⟩ := copy_steps hc u upc lay chain step hl hh hj hs
      (by rw [ur.get (by decide)]; exact h8)
      (by rw [ur.get (by decide)]; exact h19)
      (by rw [ur.get (by decide)]; exact h20)
    obtain ⟨t,rt,tpc,tr,tf⟩ := resume_full_steps hr hm hhit v vpc
    have v20 : v.getReg .x20 = s.getReg .x20 := (vr.get (by decide)).trans (ur.get (by decide))
    have v17 : v.getReg .x17 = s.getReg .x17 := (vr.get (by decide)).trans (ur.get (by decide))
    rw [v20,v17] at tpc
    refine ⟨n+16,t,by omega,gu.trans (cv.trans rt),tpc,?_,?_,?_⟩
    · exact ((ur.trans vr).trans tr).mono (by decide)
    · exact ((uf.trans vf).trans tf).mono (by intro A hA h; simpa using h)
    · intro _
      constructor
      · rw [tf _ (by have := buffer_bounds hl hh hj hs; omega) (by simp),v0]
        exact uf 0x201d0 (by decide) (by simp)
      · rw [tf _ (by have := buffer_bounds hl hh hj hs; omega) (by simp),v8]
        exact uf 0x201d8 (by decide) (by simp)
  · rw [if_neg selected] at upc
    obtain ⟨t,rt,tpc,tr,tf⟩ := resume_full_steps hr hm hhit u upc
    rw [ur.get (r := .x20) (by decide),ur.get (r := .x17) (by decide)] at tpc
    refine ⟨n+2,t,by omega,gu.trans rt,tpc,?_,?_,fun h => (selected h).elim⟩
    · exact (ur.trans tr).mono (by decide)
    · exact (uf.trans tf).mono (by intro A hA h; simp at h)

end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M

/-- Prefix storage identifies the layer, chain, step, and 64-bit half uniquely. -/
theorem buffer_word_injective {lay lay' chain chain' step step' half half' : Nat}
    (hc : chain < 43) (hc' : chain' < 43) (hs : step < 8) (hs' : step' < 8)
    (hh : half < 2) (hh' : half' < 2)
    (he : buffer lay chain step + 8 * half = buffer lay' chain' step' + 8 * half') :
    lay = lay' ∧ chain = chain' ∧ step = step' ∧ half = half' := by
  simp only [buffer] at he
  omega

/-- Every saved prefix lies above the original chain/FTS scratch regions. -/
theorem buffer_above_scratch {lay chain step half : Nat} (hl : 1 ≤ lay) :
    0x67000 < buffer lay chain step + 8 * half := by
  simp only [buffer]
  omega

end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.Legacy.Riscv
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every prefix-retention fragment is present in the executable Sign image. -/
theorem installed_guardAt : GuardAt Images.signImage := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> apply codeAt_sign_last <;> decide +kernel

theorem installed_resume : CodeAt Images.signImage (pcOf 22046) resumeCode := by
  apply codeAt_sign_last <;> decide +kernel

theorem installed_resumeMiss : CodeAt Images.signImage (pcOf 22047) [resumeMissWord] := by
  apply codeAt_sign_last <;> decide +kernel

theorem installed_resumeHit : CodeAt Images.signImage (pcOf 22048) [resumeHitWord] := by
  apply codeAt_sign_last <;> decide +kernel

theorem installed_prefixHook : CodeAt Images.signImage (pcOf 1014) [43073647] := by
  apply codeAt_sign_current_slice <;> decide +kernel

end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 10000

sym_block prefix_hook := symRun { noAlias := true } [43073647] (pcOf 1014) 100

theorem hook_steps {im : Image} (hc : CodeAt im (pcOf 1014) [43073647])
    (s : MachineState) (hp : s.pc = pcOf 1014) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 22016 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound prefix_hook hc s hp (by simp [prefix_hook.res,rv_simp]),?_,?_,?_⟩
  · simp [prefix_hook.res, Result.toState_pc, E.eval, pcOf]
  · intro r hr; cases r <;> simp [prefix_hook.res, rv_simp] <;> rfl
  · intro A hA hn; simp [prefix_hook.res, rv_simp]

/-- The top tree takes the guard's constant-time skip path without memory writes. -/
theorem top_steps {im : Image} (hg : GuardAt im)
    (hr : CodeAt im (pcOf 22046) resumeCode)
    (hm : CodeAt im (pcOf 22047) [resumeMissWord])
    (hhit : CodeAt im (pcOf 22048) [resumeHitWord])
    (s : MachineState) (hp : s.pc = pcOf 22016) (h8 : s.getReg .x8 = 0) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if s.getReg .x20 = s.getReg .x17 then pcOf 1015 else pcOf 1021) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have st := entry_steps hg.1 s hp
  have ep : (prefix_entry.res.toState s).pc = pcOf 22046 := by rw [entry_pc, if_pos h8]
  obtain ⟨t,rt,tpc,tr,tf⟩ := resume_full_steps hr hm hhit _ ep
  have er : RegsExcept s (prefix_entry.res.toState s) [] := by
    intro r hr; cases r <;> simp [prefix_entry.res,rv_simp] <;> rfl
  have ef : Frame s (prefix_entry.res.toState s) (fun _ => False) := by
    intro A hA hn; simp [prefix_entry.res,rv_simp]
  rw [er.get (r := .x20) (by simp), er.get (r := .x17) (by simp)] at tpc
  exact ⟨t,st.trans rt,tpc,er.trans tr,(ef.trans tf).mono (by simp)⟩

end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- The hooked lower-tree boundary saves the exact current chain value and
resumes the original branch. All additional instructions have unit tariff. -/
theorem hooked_steps {im : Image} (h0 : CodeAt im (pcOf 1014) [43073647])
    (hg : GuardAt im) (hc : CodeAt im (pcOf 22032) copyCode)
    (hr : CodeAt im (pcOf 22046) resumeCode)
    (hm : CodeAt im (pcOf 22047) [resumeMissWord])
    (hhit : CodeAt im (pcOf 22048) [resumeHitWord])
    (s : MachineState) (hp : s.pc = pcOf 1014) (lay chain step : Nat)
    (hl : 1 ≤ lay) (hh : lay ≤ 3) (hj : chain < 43) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 chain)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    ∃ n t, n ≤ 28 ∧ Steps im s n n t ∧
      t.pc = (if s.getReg .x20 = s.getReg .x17 then pcOf 1015 else pcOf 1021) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = buffer lay chain step ∨ A = buffer lay chain step + 8) ∧
      (selectionWord (s.getMem 0x20550) lay = s.getReg .x18 →
        t.getMem (BitVec.ofNat 64 (buffer lay chain step)) = s.getMem 0x201d0 ∧
        t.getMem (BitVec.ofNat 64 (buffer lay chain step + 8)) = s.getMem 0x201d8) := by
  obtain ⟨u,hu,upc,ur,uf⟩ := hook_steps h0 s hp
  obtain ⟨n,t,hn,ht,tpc,tr,tf,hval⟩ := prefix_steps hg hc hr hm hhit u upc lay chain step
    hl hh hj hs (by rw [ur.get (by simp)]; exact h8)
    (by rw [ur.get (by simp)]; exact h19) (by rw [ur.get (by simp)]; exact h20)
  rw [ur.get (r := .x20) (by simp),ur.get (r := .x17) (by simp)] at tpc
  refine ⟨1+n,t,by omega,hu.trans ht,tpc,(ur.trans tr).mono (by simp),?_,?_⟩
  · exact (uf.trans tf).mono (by intro A hA h; simpa using h)
  · intro h
    have hindex : u.getMem 0x20550 = s.getMem 0x20550 := uf 0x20550 (by decide) (by simp)
    rw [hindex,ur.get (r := .x18) (by simp)] at hval
    obtain ⟨hlo,hhi⟩ := hval h
    exact ⟨hlo.trans (uf 0x201d0 (by decide) (by simp)),
      hhi.trans (uf 0x201d8 (by decide) (by simp))⟩

end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedHeader
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
structure Code (im : Image) : Prop where
  entry : CodeAt im (pcOf 1022) sign_entry
  layer0 : CodeAt im (pcOf 1483) sign_layer0
  layer1 : CodeAt im (pcOf 1485) sign_layer1
  layer23 : CodeAt im (pcOf 1487) sign_layer23
  inc : CodeAt im (pcOf 1488) sign_inc
  body : CodeAt im (pcOf 1489) sign_body
  store : CodeAt im (pcOf 1028) sign_store
theorem steps_sign_entry {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1022) :
    Steps im s 1 1 (run_sign_entry.res.toState s) := by
  exact symRun_sound run_sign_entry hc.entry s hpc (by simp [run_sign_entry.res, rv_simp])
theorem steps_sign_layer0 {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1483) :
    Steps im s 2 2 (run_sign_layer0.res.toState s) := by
  exact symRun_sound run_sign_layer0 hc.layer0 s hpc (by simp [run_sign_layer0.res, rv_simp])
theorem steps_sign_layer1 {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1485) :
    Steps im s 2 2 (run_sign_layer1.res.toState s) := by
  exact symRun_sound run_sign_layer1 hc.layer1 s hpc (by simp [run_sign_layer1.res, rv_simp])
theorem steps_sign_layer23 {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1487) :
    Steps im s 2 2 (run_sign_layer23.res.toState s) := by
  exact symRun_sound run_sign_layer23 hc.layer23 s hpc (by simp [run_sign_layer23.res, rv_simp])
theorem steps_sign_inc {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1488) :
    Steps im s 1 1 (run_sign_inc.res.toState s) := by
  exact symRun_sound run_sign_inc hc.inc s hpc (by simp [run_sign_inc.res, rv_simp])
theorem steps_sign_body {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1489) :
    Steps im s 19 19 (run_sign_body.res.toState s) := by
  exact symRun_sound run_sign_body hc.body s hpc (by simp [run_sign_body.res, rv_simp])
theorem steps_sign_store {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1028) :
    Steps im s 3 3 (run_sign_store.res.toState s) := by
  exact symRun_sound run_sign_store hc.store s hpc (by simp [run_sign_store.res, rv_simp])
theorem sign_header_0 {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1022)
    (h8 : s.getReg .x8 = 0#64) :
    ∃ t, Steps im s 25 25 t ∧ t.pc = pcOf 1031 ∧ SignHeaderPost s t 12 := by
  let s0 := run_sign_entry.res.toState s
  have h0 := steps_sign_entry hc s hpc
  let s1 := run_sign_layer0.res.toState s0
  have h1 := steps_sign_layer0 hc s0 (by simp [s0, run_sign_entry.res, rv_simp, h8])
  let s2 := run_sign_body.res.toState s1
  have h2 := steps_sign_body hc s1 (by simp [s0, s1, run_sign_entry.res, run_sign_layer0.res, rv_simp, h8])
  let s3 := run_sign_store.res.toState s2
  have h3 := steps_sign_store hc s2 (by simp [s0, s1, s2, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, rv_simp, h8])
  refine ⟨s3, (((h0.trans h1).trans h2).trans h3), ?_, ?_⟩
  · simp [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp]
  · constructor
    · simp [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp, packedAt, routedAt]
    · simp [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp, routedAt]
    · simp [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem sign_header_1 {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1022)
    (h8 : s.getReg .x8 = 1#64) :
    ∃ t, Steps im s 28 28 t ∧ t.pc = pcOf 1031 ∧ SignHeaderPost s t 7 := by
  let s0 := run_sign_entry.res.toState s
  have h0 := steps_sign_entry hc s hpc
  let s1 := run_sign_layer0.res.toState s0
  have h1 := steps_sign_layer0 hc s0 (by simp [s0, run_sign_entry.res, rv_simp, h8])
  let s2 := run_sign_layer1.res.toState s1
  have h2 := steps_sign_layer1 hc s1 (by simp [s0, s1, run_sign_entry.res, run_sign_layer0.res, rv_simp, h8])
  let s3 := run_sign_inc.res.toState s2
  have h3 := steps_sign_inc hc s2 (by simp [s0, s1, s2, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, rv_simp, h8])
  let s4 := run_sign_body.res.toState s3
  have h4 := steps_sign_body hc s3 (by simp [s0, s1, s2, s3, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, rv_simp, h8])
  let s5 := run_sign_store.res.toState s4
  have h5 := steps_sign_store hc s4 (by simp [s0, s1, s2, s3, s4, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem sign_header_2 {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1022)
    (h8 : s.getReg .x8 = 2#64) :
    ∃ t, Steps im s 29 29 t ∧ t.pc = pcOf 1031 ∧ SignHeaderPost s t 6 := by
  let s0 := run_sign_entry.res.toState s
  have h0 := steps_sign_entry hc s hpc
  let s1 := run_sign_layer0.res.toState s0
  have h1 := steps_sign_layer0 hc s0 (by simp [s0, run_sign_entry.res, rv_simp, h8])
  let s2 := run_sign_layer1.res.toState s1
  have h2 := steps_sign_layer1 hc s1 (by simp [s0, s1, run_sign_entry.res, run_sign_layer0.res, rv_simp, h8])
  let s3 := run_sign_layer23.res.toState s2
  have h3 := steps_sign_layer23 hc s2 (by simp [s0, s1, s2, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, rv_simp, h8])
  let s4 := run_sign_body.res.toState s3
  have h4 := steps_sign_body hc s3 (by simp [s0, s1, s2, s3, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, rv_simp, h8])
  let s5 := run_sign_store.res.toState s4
  have h5 := steps_sign_store hc s4 (by simp [s0, s1, s2, s3, s4, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem sign_header_3 {im : Image} (hc : Code im) (s : MachineState) (hpc : s.pc = pcOf 1022)
    (h8 : s.getReg .x8 = 3#64) :
    ∃ t, Steps im s 29 29 t ∧ t.pc = pcOf 1031 ∧ SignHeaderPost s t 6 := by
  let s0 := run_sign_entry.res.toState s
  have h0 := steps_sign_entry hc s hpc
  let s1 := run_sign_layer0.res.toState s0
  have h1 := steps_sign_layer0 hc s0 (by simp [s0, run_sign_entry.res, rv_simp, h8])
  let s2 := run_sign_layer1.res.toState s1
  have h2 := steps_sign_layer1 hc s1 (by simp [s0, s1, run_sign_entry.res, run_sign_layer0.res, rv_simp, h8])
  let s3 := run_sign_layer23.res.toState s2
  have h3 := steps_sign_layer23 hc s2 (by simp [s0, s1, s2, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, rv_simp, h8])
  let s4 := run_sign_body.res.toState s3
  have h4 := steps_sign_body hc s3 (by simp [s0, s1, s2, s3, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, rv_simp, h8])
  let s5 := run_sign_store.res.toState s4
  have h5 := steps_sign_store hc s4 (by simp [s0, s1, s2, s3, s4, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem header {im : Image} (hc : Code im) (s : MachineState)
    (hp : s.pc = pcOf 1022) (lay : SigGolfCandidate.T3.Layer)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) :
    ∃ t, Steps im s (headerK lay - 5) (headerK lay - 5) t ∧ t.pc = pcOf 1031 ∧
      SignHeaderPost s t (SigGolfCandidate.T3.height lay) := by
  fin_cases lay
  · exact sign_header_0 hc s hp h8
  · exact sign_header_1 hc s hp h8
  · exact sign_header_2 hc s hp h8
  · exact sign_header_3 hc s hp h8
end ClaudeWCT.W9.Machine.Sign.SharedHeader

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest chainInput chain shortHash header pad64 zero16 height chainHeader)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
/-- The chain code of the installed producer. Pairing stage 1: the header ends at 1030 and 1031 jumps to the G/F step
block (`Seed.StepCode`: witness stack block 1760..1797, HASH at 1788/1796, the C3 tail trampoline 1667..1677). -/
structure Code (im : Image) : Prop where
  reset : CodeAt im (pcOf 1013) sub_0
  capCopy : CodeAt im (pcOf 1015) sub_2
  stop : CodeAt im (pcOf 1021) sub_8
  ret : CodeAt im (pcOf 1039) sub_26
  step : SigGolfCandidate.T3M.Sign.Seed.StepCode im
  header : SharedHeader.Code im
theorem sub0_spec {image : Image} (h : Code image) (s : MachineState)
    (hpc : s.pc = pcOf (1013 + 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (1013 + 1) ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_0 (b := 1013) (Or.inr rfl)
  refine ⟨_, symRun_sound hrun h.reset s hpc (by simp [st_0, blk117_0.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_0, Result.toState_pc, E.eval]
  · simp [st_0, blk117_0.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_0, blk117_0.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_0, blk117_0.res, rv_simp]

theorem sub2_spec {image : Image} (h : Code image) (s : MachineState)
    (hpc : s.pc = pcOf (1013 + 2)) (valp : Nat) (h23 : s.getReg .x23 = BitVec.ofNat 64 valp)
    (hv8 : valp % 8 = 0) (hv : valp + 16 ≤ 2 ^ 24) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (1013 + 8) ∧
      t.getMem (BitVec.ofNat 64 valp) = s.getMem (BitVec.ofNat 64 (CHAIN + 48)) ∧
      t.getMem (BitVec.ofNat 64 (valp + 8)) = s.getMem (BitVec.ofNat 64 (CHAIN + 56)) ∧
      RegsExcept s t [.x6, .x7, .x29] ∧ Frame s t (fun A => A = valp ∨ A = valp + 8) := by
  have hrun := run_2 (b := 1013) (Or.inr rfl)
  have hobl : Oblig.all s st_2.obl := by
    simp only [st_2, blk117_2.res]
    t3n [h23]
    omega
  refine ⟨_, symRun_sound hrun h.capCopy s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_2, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, st_2, blk117_2.res]
    t3n [h23]
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, st_2, blk117_2.res]
    t3n [h23]
  · intro r hr; simp at hr; cases r <;> simp_all [st_2, blk117_2.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, st_2, blk117_2.res]
    t3n [h23]
    rw [if_neg (by omega), if_neg (by omega)]

theorem sub8_spec {image : Image} (h : Code image) (s : MachineState)
    (hpc : s.pc = pcOf (1013 + 8)) (m e : Nat) (hm : m < 2 ^ 64) (he : e < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h21 : s.getReg .x21 = BitVec.ofNat 64 e) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if m = e then pcOf (1013 + 26) else pcOf (1013 + 9)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_8 (b := 1013) (Or.inr rfl)
  refine ⟨_, symRun_sound hrun h.stop s hpc (by simp [st_8, blk117_8.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_8, rebase, blk117_8.res, E.eval, CmpOp.eval, h20, h21]
    by_cases hme : m = e
    · subst hme; simp
    · rw [if_neg hme]
      have : BitVec.ofNat 64 m ≠ BitVec.ofNat 64 e := fun he' => hme ((ofNat_inj hm he).mp he')
      simp [this]
  · intro r hr; cases r <;> simp_all [st_8, blk117_8.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_8, blk117_8.res, rv_simp]

theorem sub26_spec {image : Image} (h : Code image) (s : MachineState)
    (hpc : s.pc = pcOf (1013 + 26)) (k : Nat) (h1 : s.getReg .x1 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_26 (b := 1013) (Or.inr rfl)
  refine ⟨_, symRun_sound hrun h.ret s hpc (by simp [st_26, blk117_26.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_26, blk117_26.res, rv_simp, h1, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_26, blk117_26.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_26, blk117_26.res, rv_simp]


theorem shared_header_source {image : Image} (h : Code image)
    (s : MachineState) (hpc : s.pc = pcOf (1013 + 9)) (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ height lay)
    (hi : i < 64) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    ∃ t, Steps image s (headerK lay - 5) (headerK lay - 5) t ∧ t.pc = pcOf (1013 + 18) ∧
      t.getReg .x28 = BitVec.ofNat 64 0x201A0 ∧
      t.getMem (BitVec.ofNat 64 (0x201A0 + 16)) = (chainHeader lay tree leaf i step).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (0x201A0 + 24)) = (chainHeader lay tree leaf i step).extractLsb' 64 64 ∧
      RegsExcept s t [.x6, .x7, .x28, .x30] ∧
      Frame s t (fun A => A = 0x201A0 + 16 ∨ A = 0x201A0 + 24) := by
  obtain ⟨t, st, pc, post⟩ := SharedHeader.header h.header s hpc lay h8
  refine ⟨t, st, pc, post.x28,
    post.low.trans (packedAt_source s lay tree leaf i step hr hf hi hs h8 h9 h18 h19 h20),
    ?_, post.regs, post.frame⟩
  exact (post.high.trans (routedAt_high_zero s lay tree leaf hr h9 h18)).trans
    (source_high_actual lay tree leaf i step hr hf hi hs).symm

end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3M.Sign SigGolfCandidate.Rv
/-- The chain instructions (stage 2: with the C3 tail trampoline) and domain header occur in the installed
producer. -/
theorem installed_code : Code Images.signImage := by
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> (apply codeAt_sign_current_slice <;> decide +kernel)

end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

structure PrefixCode (im : Image) : Prop where
  hook : CodeAt im (pcOf 1014) [43073647]
  guard : SharedPrefixes.GuardAt im
  copy : CodeAt im (pcOf 22032) SharedPrefixes.copyCode
  resume : CodeAt im (pcOf 22046) SharedPrefixes.resumeCode
  miss : CodeAt im (pcOf 22047) [SharedPrefixes.resumeMissWord]
  hit : CodeAt im (pcOf 22048) [SharedPrefixes.resumeHitWord]

def boundaryWrites (lay chain step valp A : Nat) : Prop :=
  A = SharedPrefixes.buffer lay chain step ∨ A = SharedPrefixes.buffer lay chain step + 8 ∨
  A = valp ∨ A = valp + 8

/-- Each lower-chain boundary preserves its prefix before the old capture branch.
Its new instructions do not call HASH; all memory writes are explicit.
Stage 2: the cost is split as `28` plus the capture store (`6`, only at `step = cap`), so that the C3 tail
trampoline fits the unchanged chain budget `80 * e + 37` (`loopW_le`). -/
theorem boundary {im : Image} (hc : Code im) (hpref : PrefixCode im)
    (s : MachineState) (hp : s.pc = pcOf 1014) (lay chain step valp cap : Nat)
    (hl : 1 ≤ lay) (hh : lay ≤ 3) (hj : chain < 43) (hs : step < 8) (hcap : cap < 2 ^ 64)
    (hv8 : valp % 8 = 0) (hv : valp + 16 ≤ 0x67000)
    (hvc : valp + 16 ≤ CHAIN ∨ CHAIN + 80 ≤ valp)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 cap)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 chain)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 valp) (v : Digest)
    (hval : DigAt s (CHAIN + 48) v) :
    ∃ n t, n ≤ 28 + (if step = cap then 6 else 0) ∧ Steps im s n n t ∧ t.pc = pcOf 1021 ∧
      RegsExcept s t [.x6,.x7,.x28,.x29] ∧ Frame s t (boundaryWrites lay chain step valp) ∧
      DigAt t (CHAIN + 48) v ∧
      (SharedPrefixes.selectionWord (s.getMem 0x20550) lay = s.getReg .x18 →
        DigAt t (SharedPrefixes.buffer lay chain step) v) := by
  obtain ⟨n,u,hn,hu,upc,ur,uf,usave⟩ := SharedPrefixes.hooked_steps
    hpref.hook hpref.guard hpref.copy hpref.resume hpref.miss hpref.hit s hp lay chain step
    hl hh hj hs h8 h19 h20
  have hb := SharedPrefixes.buffer_bounds hl hh hj hs
  have hba := SharedPrefixes.buffer_above_scratch (chain := chain) (step := step) (half := 0) hl
  simp only [Nat.mul_zero, Nat.add_zero] at hba
  have uv : DigAt u (CHAIN + 48) v := hval.frame uf (by decide)
    (by dsimp [CHAIN]; omega) (by dsimp [CHAIN]; omega)
  have saved : SharedPrefixes.selectionWord (s.getMem 0x20550) lay = s.getReg .x18 →
      DigAt u (SharedPrefixes.buffer lay chain step) v := by
    intro hh
    obtain ⟨h0,h8⟩ := usave hh
    exact ⟨h0.trans hval.1,h8.trans hval.2⟩
  by_cases hcap' : s.getReg .x20 = s.getReg .x17
  · rw [if_pos hcap'] at upc
    have hsc : step = cap := (ofNat_inj (by omega) hcap).mp (h20.symm.trans (hcap'.trans h17))
    obtain ⟨t,ht,tpc,t0,t8,tr,tf⟩ := sub2_spec hc u upc valp
      (by rw [ur.get (by decide)]; exact h23) hv8 (by omega)
    refine ⟨n+6,t,by rw [if_pos hsc]; omega,hu.trans ht,tpc,(ur.trans tr).mono (by decide),?_,?_,?_⟩
    · exact (uf.trans tf).mono (by intro A hA h; simp only [boundaryWrites]; tauto)
    · exact uv.frame tf (by decide) (by omega) (by omega)
    · intro hsel
      exact (saved hsel).frame tf (by omega) (by omega) (by omega)
  · rw [if_neg hcap'] at upc
    exact ⟨n,u,by split <;> omega,hu,upc,ur,uf.mono (by
      intro A hA h; simp only [boundaryWrites]; tauto),uv,saved⟩

end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest chainInput shortHash pad64)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def hashWrites (A : Nat) : Prop :=
  (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 112)

/-- The HASH rung follows prefix retention with its exact chain query. Pairing stage 1: the header, then the G/F step
block (`Seed.pair_rung`, `Seed.trX` extra steps); the rung keeps the half `WCT9.chainHigh lay i m` of
`WCT9.chainInputW`. -/
theorem hash_rung {im : Image} (hc : Code im) (sk : BitVec 256)
    (s : MachineState) (hp : s.pc = pcOf 1021) (lay : Layer)
    (tree leaf i m e cap valp ret : Nat) (v : Digest)
    (hpre : ChainPreS s lay tree leaf i cap e valp ret) (hm : m < e)
    (hmt : lay.val = 0 → m < SigGolfCandidate.T3.maxDigit 0 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (hval : DigAt s (CHAIN + 48) v) :
    TSim im sk s (headerK lay + 4 + SigGolfCandidate.T3M.Sign.Seed.trX lay.val i m)
      (headerK lay + 11 + SigGolfCandidate.T3M.Sign.Seed.trX lay.val i m) 1 1
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i m) (ClaudeWCT.WCT9.chainInputW lay tree leaf i m v))
      (fun v' t => t.pc = pcOf 1014 ∧ t.getReg .x20 = BitVec.ofNat 64 (m+1) ∧
        DigAt t (CHAIN + 48) v' ∧ RegsExcept s t SigGolfCandidate.T3M.Keygen.chainRegs ∧ Frame s t hashWrites ∧
        (SigGolfCandidate.T3M.Sign.Seed.FCh lay i → ¬ SigGolfCandidate.T3M.Sign.Seed.topG lay.val i →
          SigGolfCandidate.T3M.Sign.Seed.Z32 t ∧
          Frame s t (fun A => (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ A = CHAIN + 32 ∨ A = CHAIN + 40 ∨
            (CHAIN + 48 ≤ A ∧ A < CHAIN + 80)))) := by
  have he := hpre.he
  obtain ⟨u,hu,upc,ur,uf⟩ := sub8_spec hc s hp m e (by omega) (by omega) h20 hpre.x21
  rw [if_neg (by omega)] at upc
  obtain ⟨t,ht,tpc,t28,t16,t24,tr,tf⟩ := shared_header_source hc u upc lay tree leaf i m
    hpre.hroute hpre.hleaf (by have := hpre.hi; omega) (by omega)
    (by rw [ur.get (by simp)]; exact hpre.x8)
    (by rw [ur.get (by simp)]; exact hpre.x9)
    (by rw [ur.get (by simp)]; exact hpre.x18)
    (by rw [ur.get (by simp)]; exact hpre.x19)
    (by rw [ur.get (by simp)]; exact h20)
  have fr : Frame s t (fun A => A = CHAIN+16 ∨ A = CHAIN+24) :=
    (uf.trans tf).mono (by intro A hA h; simpa only [false_or] using h)
  have regs : RegsExcept s t [.x6,.x7,.x28,.x30] := (ur.trans tr).mono (by simp)
  have tv := hval.frame fr (by decide) (by simp) (by simp)
  have run := SigGolfCandidate.T3M.Sign.Seed.pair_rung hc.step sk t (by rw [tpc]) lay tree leaf i m v
    hpre.hi (by omega) (fun hl => by have := hpre.hlow hl; omega) hmt
    (by rw [regs.get (by simp)]; exact hpre.x5) (by rw [regs.get (by simp)]; exact hpre.x8)
    (by rw [regs.get (by simp)]; exact hpre.x19) (by rw [regs.get (by simp)]; exact h20) t28
    (by rw [fr.get (by decide) (by simp only [CHAIN]; omega)]; exact hpre.z0)
    (by rw [fr.get (by decide) (by simp only [CHAIN]; omega)]; exact hpre.z8)
    t16 t24 (source_high_actual lay tree leaf i m hpre.hroute hpre.hleaf (by have := hpre.hi; omega) (by omega)) tv
  refine ((TSim.steps (hu.trans ht) run).of_eq rfl ?_ ?_ rfl rfl).mono ?_
  · unfold headerK; split_ifs <;> omega
  · unfold headerK; split_ifs <;> omega
  · intro v' w hw
    exact ⟨hw.1, hw.2.1, hw.2.2.1, (regs.trans hw.2.2.2.1).mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs]),
      (fr.trans hw.2.2.2.2.1).mono (by
        intro A hA h; simp only [hashWrites]; rcases h with h | h
        · exact Or.inl h
        · exact Or.inr h), fun hF hT => by
        obtain ⟨z1, z2, zf⟩ := hw.2.2.2.2.2 hF hT
        exact ⟨⟨z1, z2⟩, (fr.trans zf).mono (fun A _ h => by
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr h)⟩⟩

end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open SigGolfCandidate.T3M
/-- Every prefix-retention block is bound to the installed Sign image. -/
theorem installed_prefix_code : PrefixCode Images.signImage :=
  ⟨SharedPrefixes.installed_prefixHook, SharedPrefixes.installed_guardAt,
    SharedPrefixes.copy_codeAt, SharedPrefixes.installed_resume,
    SharedPrefixes.installed_resumeMiss, SharedPrefixes.installed_resumeHit⟩
end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer)

/-- Prefix storage is above all chain-domain padding, so the chain precondition
survives every complete rung and the optional capture store. -/
theorem pre_preserved {s t : MachineState} {lay : Layer} {tree leaf i cap e valp ret : Nat}
    (hpre : ChainPreS s lay tree leaf i cap e valp ret)
    (hr : RegsExcept s t SigGolfCandidate.T3M.Keygen.chainRegs)
    (hf : Frame s t (fun A => ChainWS valp A ∨ 0x67000 < A)) :
    ChainPreS t lay tree leaf i cap e valp ret := by
  have hvc := hpre.hvc
  simp only [CHAIN] at hvc
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,hpre.htree,hpre.hi,hpre.hroute,hpre.hleaf,
    hpre.hcap,hpre.he,hpre.hlow,hpre.hv8,hpre.hv,hpre.hvc,?_,?_⟩
  · exact (hr.get (by decide)).trans hpre.x5
  · exact (hr.get (by decide)).trans hpre.x1
  · exact (hr.get (by decide)).trans hpre.x8
  · exact (hr.get (by decide)).trans hpre.x9
  · exact (hr.get (by decide)).trans hpre.x18
  · exact (hr.get (by decide)).trans hpre.x17
  · exact (hr.get (by decide)).trans hpre.x19
  · exact (hr.get (by decide)).trans hpre.x21
  · exact (hr.get (by decide)).trans hpre.x23
  · exact (hf _ (by decide) (by simp only [ChainWS,CHAIN]; omega)).trans hpre.z0
  · exact (hf _ (by decide) (by simp only [ChainWS,CHAIN]; omega)).trans hpre.z8

end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest chainInput shortHash)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def rungWrites (lay i m valp A : Nat) : Prop :=
  ChainWS valp A ∨ A = SharedPrefixes.buffer lay i m ∨ A = SharedPrefixes.buffer lay i m + 8

/-- Stage 2: cycle bound of one lower rung `m`: boundary `28` (+ the capture store `6` at `m = cap`), header
`headerK ≤ 34`, the HASH `11`, and the C3 tail trampoline `Seed.trX`. -/
def rungW (lay i cap m : Nat) : Nat :=
  73 + SigGolfCandidate.T3M.Sign.Seed.trX lay i m + (if m = cap then 6 else 0)

/-- Stage 2: cycle bound of the rungs `m .. m + count - 1` and the exit (`30`, + the capture store at `cap`). -/
def loopW (lay i cap : Nat) : Nat → Nat → Nat
  | m, 0 => 30 + (if m = cap then 6 else 0)
  | m, count + 1 => rungW lay i cap m + loopW lay i cap (m + 1) count

/-- Witness stack: the largest lower-layer `Seed.trX` per step (G interior `13`; G step 6 and chain 0 at step 6:
`14`). -/
def trXmax (m : Nat) : Nat := if m = 6 then 14 else 13

theorem trX_le_max {lay : Nat} (hl : lay ≠ 0) (i m : Nat) : SigGolfCandidate.T3M.Sign.Seed.trX lay i m ≤ trXmax m := by
  unfold SigGolfCandidate.T3M.Sign.Seed.trX SigGolfCandidate.T3M.Sign.Seed.trX0 SigGolfCandidate.T3M.Sign.Seed.topG trXmax
  split_ifs <;> omega

def loopWmax (cap : Nat) : Nat → Nat → Nat
  | m, 0 => 30 + (if m = cap then 6 else 0)
  | m, count + 1 => 73 + trXmax m + (if m = cap then 6 else 0) + loopWmax cap (m + 1) count

theorem loopW_le_max {lay : Nat} (hl : lay ≠ 0) (i cap : Nat) :
    ∀ count m, loopW lay i cap m count ≤ loopWmax cap m count
  | 0, _ => le_refl _
  | count + 1, m => by
    have h1 := trX_le_max hl i m
    have h2 := loopW_le_max hl i cap count (m + 1)
    simp only [loopW, loopWmax, rungW]
    omega

theorem loopW_worst : ∀ e, e < 9 → ∀ cap, cap ≤ e → 1 + loopWmax cap 0 e ≤ 87 * e + 37 := by
  decide +kernel

/-- Pairing stage 1: the G/F step block, the C3 trampoline and the capture store fit the chain budget `87 * e + 37`
(was `80 * e + 37`; stage 1 `85 * e + 37`; witness stack: the lower G path is 2 steps longer). -/
theorem loopW_le {lay : Nat} (hl : lay ≠ 0) (i cap e : Nat) (he : e ≤ 8) (hcap : cap ≤ e) :
    1 + loopW lay i cap 0 e ≤ 87 * e + 37 := by
  have h1 := loopW_le_max hl i cap e 0
  have h2 := loopW_worst e (by omega) cap hcap
  omega

/-- One installed prefix boundary and HASH rung, with the saved prefix framed. Stage 2: the rung keeps the half
`WCT9.chainHigh lay i m` (C3) and costs `rungW`. -/
theorem retained_rung {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : BitVec 256)
    (s : MachineState) (hp : s.pc = pcOf 1014) (lay : Layer)
    (tree leaf i m e cap valp ret : Nat) (v : Digest)
    (hpre : ChainPreS s lay tree leaf i cap e valp ret)
    (hl : 1 ≤ lay.val) (hi : i < 43) (he : e < 8) (hm : m < e)
    (hv : valp + 16 ≤ 0x67000)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (hval : DigAt s (CHAIN + 48) v) :
    TBSim im sk s (rungW lay.val i cap m)
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i m) (ClaudeWCT.WCT9.chainInputW lay tree leaf i m v))
      (fun v' t => t.pc = pcOf 1014 ∧ t.getReg .x20 = BitVec.ofNat 64 (m+1) ∧
        DigAt t (CHAIN + 48) v' ∧ RegsExcept s t SigGolfCandidate.T3M.Keygen.chainRegs ∧
        Frame s t (rungWrites lay.val i m valp) ∧
        (SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val = s.getReg .x18 →
          DigAt t (SharedPrefixes.buffer lay.val i m) v) ∧
        (SigGolfCandidate.T3M.Sign.Seed.FCh lay i → SigGolfCandidate.T3M.Sign.Seed.Z32 t)) := by
  obtain ⟨n,u,hn,hu,upc,ur,uf,uv,usave⟩ := boundary hc hpref s hp lay.val i m valp cap
    hl (by omega) hi (by omega) (by have := hpre.hcap; omega) hpre.hv8 hv (hpre.hvc.imp id (fun h => by simp only [CHAIN] at *; omega)) hpre.x8 hpre.x17 hpre.x19 h20
    hpre.x23 v hval
  have ub : Frame s u (fun A => ChainWS valp A ∨ 0x67000 < A) := uf.mono (by
    intro A hA h
    have hb := SharedPrefixes.buffer_above_scratch (chain := i) (step := m) (half := 0) hl
    simp only [Nat.mul_zero,Nat.add_zero] at hb
    simp only [boundaryWrites] at h
    unfold ChainWS
    omega)
  have preu := pre_preserved hpre (ur.mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs])) ub
  have run := hash_rung hc sk u upc lay tree leaf i m e cap valp ret v preu hm (fun h => absurd h (by omega))
    (by rw [ur.get (by decide)]; exact h20) uv
  have all := TSim.steps hu run
  refine all.toTBSim (by omega) |>.mono ?_ ?_
  · have hk : headerK lay ≤ 34 := by unfold headerK; split_ifs <;> omega
    unfold rungW
    omega
  · intro v' t ht
    refine ⟨ht.1,ht.2.1,ht.2.2.1,(ur.trans ht.2.2.2.1).mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs]),?_,?_,
      fun hF => (ht.2.2.2.2.2 hF (fun h => absurd h.1 (by omega))).1⟩
    · exact (uf.trans ht.2.2.2.2.1).mono (by
        intro A hA h
        simp only [boundaryWrites,hashWrites,rungWrites,ChainWS] at *
        omega)
    · intro hs
      have hb := SharedPrefixes.buffer_above_scratch (chain := i) (step := m) (half := 0) hl
      simp only [Nat.mul_zero,Nat.add_zero] at hb
      have hb8 := SharedPrefixes.buffer_bounds hl (by omega) hi (show m<8 by omega)
      exact (usave hs).frame ht.2.2.2.2.1 (by omega)
        (by simp only [hashWrites,CHAIN]; omega)
        (by simp only [hashWrites,CHAIN]; omega)

end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem retained_exit {α : Type} (a : α) {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : BitVec 256)
    (s : MachineState) (hp : s.pc = pcOf 1014) (lay : Layer)
    (tree leaf i e cap valp ret : Nat) (v : Digest)
    (hpre : ChainPreS s lay tree leaf i cap e valp ret)
    (hl : 1 ≤ lay.val) (hi : i < 43) (he : e < 8) (hv : valp + 16 ≤ 0x67000)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 e) (hval : DigAt s (CHAIN + 48) v) :
    TBSim im sk s (30 + (if e = cap then 6 else 0)) (pure a)
      (fun a' t => a' = a ∧ t.pc = pcOf ret ∧ DigAt t (CHAIN + 48) v ∧
        RegsExcept s t SigGolfCandidate.T3M.Keygen.chainRegs ∧ Frame s t (rungWrites lay.val i e valp) ∧
        (SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val = s.getReg .x18 →
          DigAt t (SharedPrefixes.buffer lay.val i e) v) ∧
        (SigGolfCandidate.T3M.Sign.Seed.Z32 s → SigGolfCandidate.T3M.Sign.Seed.Z32 t)) := by
  obtain ⟨n,u,hn,hu,upc,ur,uf,uv,usave⟩ := boundary hc hpref s hp lay.val i e valp cap
    hl (by omega) hi he (by have := hpre.hcap; omega) hpre.hv8 hv (hpre.hvc.imp id (fun h => by simp only [CHAIN] at *; omega)) hpre.x8 hpre.x17 hpre.x19 h20
    hpre.x23 v hval
  obtain ⟨t,ht,tpc,tr,tf⟩ := sub8_spec hc u upc e e (by omega) (by omega)
    (by rw [ur.get (by decide)]; exact h20)
    (by rw [ur.get (by decide)]; exact hpre.x21)
  rw [if_pos rfl] at tpc
  obtain ⟨w,hw,wpc,wr,wf⟩ := sub26_spec hc t tpc ret
    (by rw [tr.get (by simp),ur.get (by decide)]; exact hpre.x1)
  have fr : Frame u w (fun _ => False) := (tf.trans wf).mono (by simp)
  have rr : RegsExcept u w [] := (tr.trans wr).mono (by simp)
  exact (TSim.pure_steps (hu.trans (ht.trans hw)) ⟨rfl,wpc,
    uv.frame fr (by decide) (by simp) (by simp),
    (ur.trans rr).mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs]),
    (uf.trans fr).mono (by
      intro A hA h
      simp only [boundaryWrites] at h
      rcases h with (h | h | h | h) | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl (Or.inr (Or.inr (by omega)))
      · exact Or.inl (Or.inr (Or.inr (by omega)))
      · exact h.elim),fun hs => (usave hs).frame fr (by
        have hb := SharedPrefixes.buffer_bounds hl (by omega) hi he
        omega) (by simp) (by simp), fun hz => by
        have hvc := hpre.hvc
        have hb := SharedPrefixes.buffer_above_scratch (chain := i) (step := e) (half := 0) hl
        simp only [Nat.mul_zero,Nat.add_zero] at hb
        simp only [CHAIN] at hvc
        exact hz.frame (uf.trans fr) (by intro h; simp only [boundaryWrites,CHAIN,or_false] at h; omega)
          (by intro h; simp only [boundaryWrites,CHAIN,or_false] at h; omega)⟩).toTBSim (by omega) |>.mono (by omega) (fun _ _ h => h)

end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest)
open SigGolfCandidate.Research.SharedForest (chainPrefixes)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def loopWrites (lay i lo hi valp A : Nat) : Prop :=
  ChainWS valp A ∨ (SharedPrefixes.buffer lay i lo ≤ A ∧ A < SharedPrefixes.buffer lay i hi + 16)

/-- Stage 2 (C3, #866): one step of the retained-prefix chain keeps the half `WCT9.chainHigh lay i start`, i.e. the
spec `SharedForest.chainPrefixes` hashes with `WCT9.halfHash (WCT9.chainHigh lay i start)` as `WCT9.chainW` does. -/
theorem chainPrefixes_succ (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    chainPrefixes lay tree leaf i start (count + 1) value = (do
      let next ← ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i start)
        (ClaudeWCT.WCT9.chainInputW lay tree leaf i start value)
      let tail ← chainPrefixes lay tree leaf i (start + 1) count next
      pure (value :: tail)) := rfl

/-- The full retained-prefix chain executes every ordinary chain query once and
leaves each selected leaf prefix in its disjoint slot. -/
theorem retained_loop {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : BitVec 256)
    (lay : Layer) (tree leaf i e cap valp ret : Nat)
    (hl : 1 ≤ lay.val) (hi : i < 43) (he : e < 8) (hv : valp + 16 ≤ 0x67000)
    (hvi : valp + 16 ≤ 0x20550 ∨ 0x20558 ≤ valp) :
    ∀ (count m : Nat), m+count=e → ∀ (v : Digest) (s : MachineState),
    ChainPreS s lay tree leaf i cap e valp ret → s.pc = pcOf 1014 →
    s.getReg .x20 = BitVec.ofNat 64 m → DigAt s (CHAIN+48) v →
    TBSim im sk s (loopW lay.val i cap m count) (chainPrefixes lay tree leaf i m count v)
      (fun vs t => vs.length=count+1 ∧ t.pc=pcOf ret ∧ DigAt t (CHAIN+48) (vs.getD count 0) ∧
        RegsExcept s t SigGolfCandidate.T3M.Keygen.chainRegs ∧ Frame s t (loopWrites lay.val i m e valp) ∧
        (SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val = s.getReg .x18 →
          ∀ j, j≤count → DigAt t (SharedPrefixes.buffer lay.val i (m+j)) (vs.getD j 0)) ∧
        (SigGolfCandidate.T3M.Sign.Seed.FCh lay i → SigGolfCandidate.T3M.Sign.Seed.Z32 s ∨ 0 < count → SigGolfCandidate.T3M.Sign.Seed.Z32 t)) := by
  intro count
  induction count with
  | zero =>
    intro m hm v s hpre hp h20 hval
    have hme : m=e := by omega
    subst m
    simpa only [chainPrefixes,loopW] using
      (retained_exit [v] hc hpref sk s hp lay tree leaf i e cap valp ret v hpre hl hi he hv h20 hval).mono
        (le_refl _) (fun vs t ht => by
          rcases ht with ⟨rfl,ht⟩
          refine ⟨rfl,ht.1,?_,ht.2.2.1,?_,?_,fun _ hz => ht.2.2.2.2.2 (hz.resolve_right (by omega))⟩
          · simpa only [List.getD_cons_zero] using ht.2.1
          · exact ht.2.2.2.1.mono (by
              intro A hA h
              change ChainWS valp A ∨ A = SharedPrefixes.buffer lay.val i e ∨ A = SharedPrefixes.buffer lay.val i e + 8 at h
              change ChainWS valp A ∨ (SharedPrefixes.buffer lay.val i e ≤ A ∧ A < SharedPrefixes.buffer lay.val i e + 16)
              rcases h with h | h | h
              · exact Or.inl h
              · right; omega
              · right; omega)
          · intro hs j hj
            have hj0 : j=0 := by omega
            subst j
            simpa only [Nat.add_zero,List.getD_cons_zero] using ht.2.2.2.2.1 hs)
  | succ count ih =>
    intro m hm v s hpre hp h20 hval
    have hm' : m<e := by omega
    have one := retained_rung hc hpref sk s hp lay tree leaf i m e cap valp ret v
      hpre hl hi he hm' hv h20 hval
    rw [chainPrefixes_succ]
    show TBSim im sk s (rungW lay.val i cap m + loopW lay.val i cap (m+1) count) _ _
    refine TBSim.bind (W₁ := rungW lay.val i cap m) (W₂ := loopW lay.val i cap (m+1) count) one
      (fun v' u hu => ?_)
    have uf := hu.2.2.2.2.1
    have ub : Frame s u (fun A => ChainWS valp A ∨ 0x67000<A) := uf.mono (by
      intro A hA h
      have hb := SharedPrefixes.buffer_above_scratch (chain := i) (step := m) (half := 0) hl
      simp only [Nat.mul_zero,Nat.add_zero] at hb
      change ChainWS valp A ∨ A = SharedPrefixes.buffer lay.val i m ∨ A = SharedPrefixes.buffer lay.val i m + 8 at h
      rcases h with h | h | h
      · exact Or.inl h
      · right; omega
      · right; omega)
    have upre := pre_preserved hpre hu.2.2.2.1 ub
    have tail := ih (m+1) (by omega) v' u upre hu.1 hu.2.1 hu.2.2.1
    refine TBSim.bind (W₁ := loopW lay.val i cap (m+1) count) (W₂ := 0) tail (fun vs t ht => TBSim.pure ?_)
    refine ⟨by simpa only [List.length_cons] using congrArg (·+1) ht.1,ht.2.1,?_,
      (hu.2.2.2.1.trans ht.2.2.2.1).mono (by simp),?_,?_,
      fun hF _ => ht.2.2.2.2.2.2 hF (Or.inl (hu.2.2.2.2.2.2 hF))⟩
    · simpa only [List.getD_cons_succ] using ht.2.2.1
    · exact (uf.trans ht.2.2.2.2.1).mono (by
        intro A hA h
        change rungWrites lay.val i m valp A ∨ loopWrites lay.val i (m+1) e valp A at h
        change ChainWS valp A ∨ (SharedPrefixes.buffer lay.val i m ≤ A ∧ A < SharedPrefixes.buffer lay.val i e + 16)
        rcases h with (h | h | h) | (h | h)
        · exact Or.inl h
        · right; simp only [SharedPrefixes.buffer] at h ⊢; omega
        · right; simp only [SharedPrefixes.buffer] at h ⊢; omega
        · exact Or.inl h
        · right; simp only [SharedPrefixes.buffer] at h ⊢; omega)
    · intro hs j hj
      have usel : SharedPrefixes.selectionWord (u.getMem 0x20550) lay.val = u.getReg .x18 := by
        have idx : u.getMem (BitVec.ofNat 64 0x20550) = s.getMem (BitVec.ofNat 64 0x20550) :=
          uf 0x20550 (by decide) (by
            simp only [rungWrites,ChainWS,CHAIN,SharedPrefixes.buffer]
            omega)
        exact (congrArg (fun x => SharedPrefixes.selectionWord x lay.val) idx).trans
          (hs.trans (hu.2.2.2.1.get (by simp [SigGolfCandidate.T3M.Keygen.chainRegs])).symm)
      cases j with
      | zero =>
        have saved := hu.2.2.2.2.2.1 hs
        have hb := SharedPrefixes.buffer_bounds hl (by omega) hi (show m<8 by omega)
        have lo := SharedPrefixes.buffer_above_scratch (chain := i) (step := m) (half := 0) hl
        simp only [Nat.mul_zero,Nat.add_zero] at lo
        simpa only [List.getD_cons_zero,Nat.add_zero] using saved.frame ht.2.2.2.2.1
          (by omega) (by simp only [loopWrites,ChainWS,CHAIN,SharedPrefixes.buffer] at *; omega)
          (by simp only [loopWrites,ChainWS,CHAIN,SharedPrefixes.buffer] at *; omega)
      | succ j =>
        have saved := ht.2.2.2.2.2.1 usel j (by omega)
        simpa only [List.getD_cons_succ,show m+(j+1)=m+1+j by omega] using saved
end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest)
open SigGolfCandidate.Research.SharedForest (chainPrefixes)
set_option maxHeartbeats 2000000

theorem retained_chain {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : BitVec 256)
    (s : MachineState) (hp : s.pc = pcOf 1013) (lay : Layer)
    (tree leaf i e cap valp ret : Nat) (v : Digest)
    (hpre : ChainPreS s lay tree leaf i cap e valp ret)
    (hl : 1 ≤ lay.val) (hi : i < 43) (he : e < 8) (hv : valp + 16 ≤ 0x67000)
    (hvi : valp + 16 ≤ 0x20550 ∨ 0x20558 ≤ valp) (hval : DigAt s (CHAIN+48) v) :
    TBSim im sk s (87*e+37) (chainPrefixes lay tree leaf i 0 e v)
      (fun vs t => vs.length=e+1 ∧ t.pc=pcOf ret ∧ DigAt t (CHAIN+48) (vs.getD e 0) ∧
        RegsExcept s t SigGolfCandidate.T3M.Keygen.chainRegs ∧ Frame s t (loopWrites lay.val i 0 e valp) ∧
        (SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val = s.getReg .x18 →
          ∀ j, j≤e → DigAt t (SharedPrefixes.buffer lay.val i j) (vs.getD j 0)) ∧
        (SigGolfCandidate.T3M.Sign.Seed.FCh lay i → 0 < e → SigGolfCandidate.T3M.Sign.Seed.Z32 t)) := by
  obtain ⟨u,hu,upc,u20,ur,uf⟩ := sub0_spec hc s hp
  have preu := pre_preserved hpre (ur.mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs]))
    (uf.mono (by intro A hA h; exact h.elim))
  have run := retained_loop hc hpref sk lay tree leaf i e cap valp ret hl hi he hv hvi e 0
    (by omega) v u preu upc u20 (hval.frame uf (by decide) (by simp) (by simp))
  refine (TBSim.steps hu run).mono (loopW_le (by omega) i cap e hpre.he hpre.hcap) ?_
  intro vs t ht
  refine ⟨ht.1,ht.2.1,ht.2.2.1,(ur.trans ht.2.2.2.1).mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs]),
    (uf.trans ht.2.2.2.2.1).mono (by intro A hA h; exact h.elim False.elim id),?_,
    fun hF he0 => ht.2.2.2.2.2.2 hF (Or.inr he0)⟩
  intro hs j hj
  have us : SharedPrefixes.selectionWord (u.getMem 0x20550) lay.val = u.getReg .x18 := by
    have idx := uf 0x20550 (by decide) (by simp)
    exact (congrArg (fun x => SharedPrefixes.selectionWord x lay.val) idx).trans
      (hs.trans (ur.get (by decide)).symm)
  simpa only [Nat.zero_add] using ht.2.2.2.2.2.1 us j hj

end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest chainInput shortHash)
open SigGolfCandidate.Research.SharedForest (chainPrefixes)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem unselected_boundary {im : Image} (hc : Code im) (hpref : PrefixCode im)
    (s : MachineState) (hp : s.pc=pcOf 1014) (lay valp step cap : Nat)
    (hl : 1≤lay) (hh : lay≤3) (hv8 : valp%8=0) (hv : valp+16≤0x67000)
    (hs : step<2^64) (hcap : cap<2^64)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) (h23 : s.getReg .x23=BitVec.ofNat 64 valp)
    (h17 : s.getReg .x17=BitVec.ofNat 64 cap) (h20 : s.getReg .x20=BitVec.ofNat 64 step)
    (hmiss : SharedPrefixes.selectionWord (s.getMem 0x20550) lay ≠ s.getReg .x18) :
    ∃ n t, n≤28+(if step=cap then 6 else 0) ∧ Steps im s n n t ∧ t.pc=pcOf 1021 ∧
      RegsExcept s t [.x6,.x7,.x28,.x29] ∧ Frame s t (fun A => A=valp ∨ A=valp+8) := by
  obtain ⟨u,hu,upc,ur,uf⟩ := SharedPrefixes.hook_steps hpref.hook s hp
  obtain ⟨n,v,hn,hv',vpc,_,vr,vf⟩ := SharedPrefixes.guard_steps hpref.guard u upc lay hl hh
    (by rw [ur.get (by simp)]; exact h8)
  have missu : SharedPrefixes.selectionWord (u.getMem 0x20550) lay ≠ u.getReg .x18 := by
    have idx : u.getMem 0x20550=s.getMem 0x20550 := uf 0x20550 (by decide) (by simp)
    rw [idx,ur.get (by simp)]
    exact hmiss
  rw [if_neg missu] at vpc
  obtain ⟨w,hw,wpc,wr,wf⟩ := SharedPrefixes.resume_full_steps hpref.resume hpref.miss hpref.hit v vpc
  have rr : RegsExcept s w [.x6,.x7,.x28,.x29] := ((ur.trans vr).trans wr).mono (by simp)
  have fr : Frame s w (fun _ => False) := ((uf.trans vf).trans wf).mono (by simp)
  rw [vr.get (r:=.x20) (by decide),vr.get (r:=.x17) (by decide),
      ur.get (r:=.x20) (by simp),ur.get (r:=.x17) (by simp)] at wpc
  by_cases hcap' : s.getReg .x20=s.getReg .x17
  · rw [if_pos hcap'] at wpc
    have hsc : step=cap := (ofNat_inj hs hcap).mp (h20.symm.trans (hcap'.trans h17))
    obtain ⟨t,ht,tpc,_,_,tr,tf⟩ := sub2_spec hc w wpc valp
      (by rw [rr.get (by decide)]; exact h23) hv8 (by omega)
    exact ⟨1+n+2+6,t,by rw [if_pos hsc]; omega,((hu.trans hv').trans hw).trans ht,tpc,
      (rr.trans tr).mono (by simp),(fr.trans tf).mono (by simp)⟩
  · rw [if_neg hcap'] at wpc
    exact ⟨1+n+2,w,by split <;> omega,(hu.trans hv').trans hw,wpc,rr,fr.mono (by simp)⟩

theorem unselected_rung {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : BitVec 256)
    (s : MachineState) (hp : s.pc=pcOf 1014) (lay : Layer)
    (tree leaf i m e cap valp ret : Nat) (v : Digest)
    (hpre : ChainPreS s lay tree leaf i cap e valp ret)
    (hl : 1≤lay.val) (hm : m<e) (hv : valp+16≤0x67000)
    (h20 : s.getReg .x20=BitVec.ofNat 64 m) (hval : DigAt s (CHAIN+48) v)
    (hmiss : SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val ≠ s.getReg .x18) :
    TBSim im sk s (rungW lay.val i cap m)
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i m) (ClaudeWCT.WCT9.chainInputW lay tree leaf i m v))
      (fun v' t => t.pc=pcOf 1014 ∧ t.getReg .x20=BitVec.ofNat 64 (m+1) ∧
        DigAt t (CHAIN+48) v' ∧ RegsExcept s t SigGolfCandidate.T3M.Keygen.chainRegs ∧ Frame s t (ChainWS valp) ∧
        (SigGolfCandidate.T3M.Sign.Seed.FCh lay i → SigGolfCandidate.T3M.Sign.Seed.Z32 t)) := by
  obtain ⟨n,u,hn,hu,upc,ur,uf⟩ := unselected_boundary hc hpref s hp lay.val valp m cap hl
    (by have := lay.isLt; omega) hpre.hv8 hv (by have := hpre.he; omega) (by have := hpre.hcap; have := hpre.he; omega)
    hpre.x8 hpre.x23 hpre.x17 h20 hmiss
  have ub : Frame s u (fun A => ChainWS valp A ∨ 0x67000<A) := uf.mono (by
    intro A hA h; unfold ChainWS; omega)
  have preu := pre_preserved hpre (ur.mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs])) ub
  have uv := hval.frame uf (by decide) (by have := hpre.hvc; omega) (by have := hpre.hvc; omega)
  have run := hash_rung hc sk u upc lay tree leaf i m e cap valp ret v preu hm (fun h => absurd h (by omega))
    (by rw [ur.get (by decide)]; exact h20) uv
  refine (TSim.steps hu run).toTBSim (by omega) |>.mono ?_ ?_
  · have hk : headerK lay≤34 := by unfold headerK; split_ifs <;> omega
    unfold rungW
    omega
  · intro v' t ht
    refine ⟨ht.1,ht.2.1,ht.2.2.1,(ur.trans ht.2.2.2.1).mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs]),?_,
      fun hF => (ht.2.2.2.2.2 hF (fun h => absurd h.1 (by omega))).1⟩
    exact (uf.trans ht.2.2.2.2.1).mono (by intro A hA h; simp only [hashWrites,ChainWS] at *; omega)

theorem unselected_exit {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : BitVec 256)
    (s : MachineState) (hp : s.pc=pcOf 1014) (lay : Layer)
    (tree leaf i e cap valp ret : Nat) (v : Digest)
    (hpre : ChainPreS s lay tree leaf i cap e valp ret)
    (hl : 1≤lay.val) (hv : valp+16≤0x67000)
    (h20 : s.getReg .x20=BitVec.ofNat 64 e) (hval : DigAt s (CHAIN+48) v)
    (hmiss : SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val ≠ s.getReg .x18) :
    TBSim im sk s (30+(if e=cap then 6 else 0)) (pure [v])
      (fun vs t => vs=[v] ∧ t.pc=pcOf ret ∧ DigAt t (CHAIN+48) v ∧
        RegsExcept s t SigGolfCandidate.T3M.Keygen.chainRegs ∧ Frame s t (ChainWS valp) ∧
        (SigGolfCandidate.T3M.Sign.Seed.Z32 s → SigGolfCandidate.T3M.Sign.Seed.Z32 t)) := by
  obtain ⟨n,u,hn,hu,upc,ur,uf⟩ := unselected_boundary hc hpref s hp lay.val valp e cap hl
    (by have := lay.isLt; omega) hpre.hv8 hv (by have := hpre.he; omega) (by have := hpre.hcap; have := hpre.he; omega)
    hpre.x8 hpre.x23 hpre.x17 h20 hmiss
  obtain ⟨t,ht,tpc,tr,tf⟩ := sub8_spec hc u upc e e (by have := hpre.he; omega) (by have := hpre.he; omega)
    (by rw [ur.get (by decide)]; exact h20) (by rw [ur.get (by decide)]; exact hpre.x21)
  rw [if_pos rfl] at tpc
  obtain ⟨w,hw,wpc,wr,wf⟩ := sub26_spec hc t tpc ret
    (by rw [tr.get (by simp),ur.get (by decide)]; exact hpre.x1)
  have fr : Frame s w (fun A => A=valp ∨ A=valp+8) := ((uf.trans tf).trans wf).mono (by simp)
  exact (TSim.pure_steps (hu.trans (ht.trans hw)) ⟨rfl,wpc,
    hval.frame fr (by decide) (by have := hpre.hvc; omega) (by have := hpre.hvc; omega),
    ((ur.trans tr).trans wr).mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs]),fr.mono (by intro A hA h; unfold ChainWS; omega),
    fun hz => by
      have hvc := hpre.hvc
      exact hz.frame fr (by simp only [CHAIN] at *; omega) (by simp only [CHAIN] at *; omega)⟩).toTBSim
    (by omega) |>.mono (by omega) (fun _ _ h => h)

end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest)
open SigGolfCandidate.Research.SharedForest (chainPrefixes)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem unselected_loop {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : BitVec 256)
    (lay : Layer) (tree leaf i e cap valp ret : Nat)
    (hl : 1≤lay.val) (hv : valp+16≤0x67000) (hvi : valp+16≤0x20550 ∨ 0x20558≤valp) :
    ∀ (count m : Nat), m+count=e → ∀ (v : Digest) (s : MachineState),
    ChainPreS s lay tree leaf i cap e valp ret → s.pc=pcOf 1014 →
    s.getReg .x20=BitVec.ofNat 64 m → DigAt s (CHAIN+48) v →
    SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val ≠ s.getReg .x18 →
    TBSim im sk s (loopW lay.val i cap m count) (chainPrefixes lay tree leaf i m count v)
      (fun vs t => vs.length=count+1 ∧ t.pc=pcOf ret ∧ DigAt t (CHAIN+48) (vs.getD count 0) ∧
        RegsExcept s t SigGolfCandidate.T3M.Keygen.chainRegs ∧ Frame s t (ChainWS valp) ∧
        (SigGolfCandidate.T3M.Sign.Seed.FCh lay i → SigGolfCandidate.T3M.Sign.Seed.Z32 s ∨ 0 < count → SigGolfCandidate.T3M.Sign.Seed.Z32 t)) := by
  intro count
  induction count with
  | zero =>
      intro m hm v s hpre hp h20 hval hmiss
      have hme : m=e := by omega
      subst m
      simpa only [chainPrefixes,loopW] using
        (unselected_exit hc hpref sk s hp lay tree leaf i e cap valp ret v hpre hl hv h20 hval hmiss).mono
          (le_refl _) (fun vs t ht => by
            rcases ht with ⟨rfl,ht⟩
            exact ⟨rfl,ht.1,by simpa only [List.getD_cons_zero] using ht.2.1,ht.2.2.1,ht.2.2.2.1,
              fun _ hz => ht.2.2.2.2 (hz.resolve_right (by omega))⟩)
  | succ count ih =>
      intro m hm v s hpre hp h20 hval hmiss
      have run := unselected_rung hc hpref sk s hp lay tree leaf i m e cap valp ret v hpre hl
        (by omega) hv h20 hval hmiss
      rw [chainPrefixes_succ]
      show TBSim im sk s (rungW lay.val i cap m + loopW lay.val i cap (m+1) count) _ _
      refine TBSim.bind (W₂:=loopW lay.val i cap (m+1) count) run (fun v' u hu => ?_)
      obtain ⟨upc,u20,uval,ur,uf,uz⟩ := hu
      have preu := pre_preserved hpre ur (uf.mono (by intro A hA h; exact Or.inl h))
      have idx : u.getMem 0x20550=s.getMem 0x20550 := uf 0x20550 (by decide) (by unfold ChainWS CHAIN; omega)
      have missu : SharedPrefixes.selectionWord (u.getMem 0x20550) lay.val ≠ u.getReg .x18 := by
        rw [idx,ur.get (by decide)]
        exact hmiss
      have rest := ih (m+1) (by omega) v' u preu upc u20 uval missu
      refine TBSim.bind (W₂:=0) rest (fun vs t ht => TBSim.pure ?_) |>.mono (by omega) (fun _ _ h => h)
      obtain ⟨hlen,tpc,tval,tr,tf,tz⟩ := ht
      exact ⟨by simp only [List.length_cons,hlen],tpc,
        by simpa only [List.getD_cons_succ] using tval,
        (ur.trans tr).mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs]),(uf.trans tf).mono (by simp),
        fun hF _ => tz hF (Or.inl (uz hF))⟩

theorem unselected_chain {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : BitVec 256)
    (s : MachineState) (hp : s.pc=pcOf 1013) (lay : Layer)
    (tree leaf i e cap valp ret : Nat) (v : Digest)
    (hpre : ChainPreS s lay tree leaf i cap e valp ret)
    (hl : 1≤lay.val) (hv : valp+16≤0x67000)
    (hvi : valp+16≤0x20550 ∨ 0x20558≤valp) (hval : DigAt s (CHAIN+48) v)
    (hmiss : SharedPrefixes.selectionWord (s.getMem 0x20550) lay.val ≠ s.getReg .x18) :
    TBSim im sk s (87*e+37) (chainPrefixes lay tree leaf i 0 e v)
      (fun vs t => vs.length=e+1 ∧ t.pc=pcOf ret ∧ DigAt t (CHAIN+48) (vs.getD e 0) ∧
        RegsExcept s t SigGolfCandidate.T3M.Keygen.chainRegs ∧ Frame s t (ChainWS valp) ∧
        (SigGolfCandidate.T3M.Sign.Seed.FCh lay i → 0 < e → SigGolfCandidate.T3M.Sign.Seed.Z32 t)) := by
  obtain ⟨u,hu,upc,u20,ur,uf⟩ := sub0_spec hc s hp
  have preu := pre_preserved hpre (ur.mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs]))
    (uf.mono (by intro A hA h; exact h.elim))
  have missu : SharedPrefixes.selectionWord (u.getMem 0x20550) lay.val ≠ u.getReg .x18 := by
    have idx : u.getMem 0x20550=s.getMem 0x20550 := uf 0x20550 (by decide) (by simp)
    rw [idx,ur.get (by decide)]
    exact hmiss
  have run := unselected_loop hc hpref sk lay tree leaf i e cap valp ret hl hv hvi e 0
    (by omega) v u preu upc u20 (hval.frame uf (by decide) (by simp) (by simp)) missu
  refine (TBSim.steps hu run).mono (loopW_le (by omega) i cap e hpre.he hpre.hcap) ?_
  intro vs t ht
  exact ⟨ht.1,ht.2.1,ht.2.2.1,(ur.trans ht.2.2.2.1).mono (by simp [SigGolfCandidate.T3M.Keygen.chainRegs]),
    (uf.trans ht.2.2.2.2.1).mono (by simp), fun hF he0 => ht.2.2.2.2.2 hF (Or.inr he0)⟩

end ClaudeWCT.W9.Machine.Sign.SharedChain

namespace ClaudeWCT.W9.Machine.Sign.SharedPrefixes
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route)
set_option maxRecDepth 10000
theorem selection_mask (a m : Nat) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 (2 ^ m - 1) = BitVec.ofNat 64 (a % 2 ^ m) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and]
  by_cases h : i < m <;> simp [h]
theorem selection_route (index : Nat) (hi : index<2^31) (lay : Layer) (hl : lay≠0) :
    selectionWord (BitVec.ofNat 64 index) lay.val=BitVec.ofNat 64 (route index lay).1 := by
  fin_cases lay
  · exact (hl rfl).elim
  · change (BitVec.ofNat 64 index >>> (12 : Nat)) &&& 127 = BitVec.ofNat 64 (index/2^12%2^7)
    rw [ofNat_shr index 12 (by omega)]
    exact selection_mask (index/2^12) 7
  · change (BitVec.ofNat 64 index >>> (6 : Nat)) &&& 63 = BitVec.ofNat 64 (index/2^6%2^6)
    rw [ofNat_shr index 6 (by omega)]
    exact selection_mask (index/2^6) 6
  · simpa [selectionWord,route,SigGolfCandidate.T3.height] using selection_mask index 6
end ClaudeWCT.W9.Machine.Sign.SharedPrefixes

namespace ClaudeWCT.W9.Machine.Sign.SharedChain
open SigGolfCandidate.T3M.Sign.Seed (ChainPreS ChainWS ChainHeadS)
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Keygen.PackedBlocks
open SigGolfCandidate.T3M.Sign.Seed
open SigGolfCandidate.T3 (Layer Digest chain chainInput shortHash)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem top_boundary {im : Image} (hpref : PrefixCode im) (s : MachineState)
    (hp : s.pc = pcOf 1014) (h8 : s.getReg .x8 = 0) :
    ∃ t, Steps im s 4 4 t ∧
      t.pc = (if s.getReg .x20 = s.getReg .x17 then pcOf 1015 else pcOf 1021) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨u,hu,up,ur,uf⟩ := SharedPrefixes.hook_steps hpref.hook s hp
  obtain ⟨t,ht,tp,tr,tf⟩ := SharedPrefixes.top_steps hpref.guard hpref.resume hpref.miss hpref.hit u up
    ((ur.get (by simp)).trans h8)
  rw [ur.get (r := .x20) (by simp),ur.get (r := .x17) (by simp)] at tp
  exact ⟨t,hu.trans ht,tp,(ur.trans tr).mono (by simp),(uf.trans tf).mono (by simp)⟩

theorem chainW_zero (lay : Layer) (tree leaf i start : Nat) (value : Digest) :
    ClaudeWCT.WCT9.chainW lay tree leaf i start 0 value = pure value := rfl

/-- Witness stack: steps of one top rung (boundary `4`, header, the step block `Seed.trX 0 i m`). -/
def topRungK (i m : Nat) : Nat := headerK 0 + 8 + SigGolfCandidate.T3M.Sign.Seed.trX 0 i m
def topRungC (i m : Nat) : Nat := headerK 0 + 15 + SigGolfCandidate.T3M.Sign.Seed.trX 0 i m

section
variable {im : Image} (hc : Code im) (hpref : PrefixCode im) (sk : SecretKey)
  {s0 : MachineState} {tree leaf i e valp ret : Nat}
  (hpre : ChainPreS s0 0 tree leaf i e e valp ret)
include hc hpref hpre

/-- The top-chain loop state: the chain head (witness stack: the chain scratch `ChainW` includes the G area
`CHAIN+32 .. CHAIN+112`). -/
def TopHead (s0 : MachineState) (valp m : Nat) (v : Digest) (t : MachineState) : Prop :=
  Keygen.ChainHead 1013 s0 valp m v t

omit hc hpref in
theorem TopHead.pre {m : Nat} {v : Digest} {t : MachineState} (ht : TopHead s0 valp m v t) :
    ChainPreS t 0 tree leaf i e e valp ret :=
  pre_preserved hpre ht.regs (ht.frame.mono (by
    intro A hA h; left; exact SigGolfCandidate.T3M.Sign.Seed.ChainWS_of_chainW h))

theorem top_step {m : Nat} (hm : m < e) (hmt : m < SigGolfCandidate.T3.maxDigit 0 i) {v : Digest} {t : MachineState}
    (ht : TopHead s0 valp m v t) :
    TSim im sk t (topRungK i m) (topRungC i m) 1 1
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh 0 i m) (ClaudeWCT.WCT9.chainInputW 0 tree leaf i m v))
      (fun v' u => TopHead s0 valp (m+1) v' u) := by
  have he := hpre.he
  have pt := ht.pre hpre
  obtain ⟨u,hu,up,ur,uf⟩ := top_boundary hpref t ht.pc pt.x8
  have hne : t.getReg .x20 ≠ t.getReg .x17 := by
    rw [ht.x20,pt.x17]
    intro hn
    have hn := congrArg BitVec.toNat hn
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show m < 2^64 by omega), Nat.mod_eq_of_lt (show e < 2^64 by omega)] at hn
    omega
  rw [if_neg hne] at up
  have pu := pre_preserved pt (ur.mono (by simp)) (uf.mono (by simp))
  have hv := ht.val.frame uf (by decide) (by simp) (by simp)
  have hx : SigGolfCandidate.T3M.Sign.Seed.trX (0 : Layer).val i m = SigGolfCandidate.T3M.Sign.Seed.trX 0 i m := rfl
  refine (TSim.steps hu (hash_rung hc sk u up 0 tree leaf i m e e valp ret v pu hm (fun _ => hmt)
    ((ur.get (by simp)).trans ht.x20) hv)).of_eq rfl
    (by unfold topRungK; omega) (by unfold topRungC; omega) rfl rfl |>.mono ?_
  intro v' w hw
  refine ⟨hw.1,hw.2.1,((ht.regs.trans ur).trans hw.2.2.2.1).mono (by simp),?_,hw.2.2.1⟩
  exact ((ht.frame.trans uf).trans hw.2.2.2.2.1).mono (by
    intro A hA h
    rcases h with (h|h)|h
    · exact h
    · exact h.elim
    · unfold hashWrites at h
      rcases h with h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h))

theorem top_exit {v : Digest} {t : MachineState}
    (ht : TopHead s0 valp e v t) :
    ∃ u, Steps im t 12 12 u ∧ u.pc = pcOf ret ∧ DigAt u valp v ∧
      RegsExcept t u [.x6,.x7,.x29] ∧ Frame t u (fun A => valp ≤ A ∧ A < valp+16) := by
  have he := hpre.he
  have pt := ht.pre hpre
  obtain ⟨t1,st1,t1pc,t1r,t1f⟩ := top_boundary hpref t ht.pc pt.x8
  rw [if_pos (ht.x20.trans pt.x17.symm)] at t1pc
  obtain ⟨t2,st2,t2pc,t2v0,t2v8,t2r,t2f⟩ := sub2_spec hc t1 t1pc valp
    ((t1r.get (by simp)).trans pt.x23) pt.hv8 pt.hv
  have hv1:=ht.val.frame t1f (by decide) (by simp) (by simp)
  obtain ⟨t3,st3,t3pc,t3r,t3f⟩ := sub8_spec hc t2 t2pc e e (by omega) (by omega)
    ((t2r.get (by simp)).trans ((t1r.get (by simp)).trans ht.x20))
    ((t2r.get (by simp)).trans ((t1r.get (by simp)).trans pt.x21))
  rw [if_pos rfl] at t3pc
  obtain ⟨t4,st4,t4pc,t4r,t4f⟩ := sub26_spec hc t3 t3pc ret
    ((t3r.get (by simp)).trans ((t2r.get (by simp)).trans ((t1r.get (by simp)).trans pt.x1)))
  refine ⟨t4,st1.trans (st2.trans (st3.trans st4)),t4pc,?_,
    (((t1r.trans t2r).trans t3r).trans t4r).mono (by simp),?_⟩
  · exact (show DigAt t2 valp v from ⟨t2v0.trans hv1.1,t2v8.trans hv1.2⟩).frame
      (t3f.trans t4f) (by have := pt.hv; omega) (by simp) (by simp)
  · exact (((t1f.trans t2f).trans t3f).trans t4f).mono (by
      intro A hA h
      rcases h with ((h|h)|h)|h
      · exact h.elim
      · rcases h with h|h <;> omega
      · exact h.elim
      · exact h.elim)

/-- A top chain (witness stack: `WCT9.chainW 0`, i.e. `T3.topChain` on tree 0; G chains are the even `i ≤ 52`). Each
rung pays the step block (`Seed.trX 0 i m`). Needs `e ≤ maxDigit 0 i` (the block's terminal step is
`maxDigit 0 i - 1`). -/
theorem top_chain {v : Digest} (hp : s0.pc = pcOf 1013) (hv : DigAt s0 (CHAIN+48) v)
    (hmt : e ≤ SigGolfCandidate.T3.maxDigit 0 i) :
    TSim im sk s0 (sumTo (topRungK i) e + 13) (sumTo (topRungC i) e + 13) e e
      (do let a ← ClaudeWCT.WCT9.chainW 0 tree leaf i 0 e v; pure (a,a))
      (fun r t => t.pc = pcOf ret ∧ DigAt t valp r.1 ∧ DigAt t (CHAIN+48) r.2 ∧
        RegsExcept s0 t Keygen.chainRegs ∧ Frame s0 t (ChainW valp)) := by
  obtain ⟨u,hu,up,u20,ur,uf⟩ := sub0_spec hc s0 hp
  have h0 : TopHead s0 valp 0 v u :=
    ⟨up,u20,ur.mono (by simp [Keygen.chainRegs]),uf.mono (by simp),hv.frame uf (by decide) (by simp) (by simp)⟩
  have run : TSim im sk u (sumTo (topRungK i) e) (sumTo (topRungC i) e)
      (sumTo (fun _ => 1) e) (sumTo (fun _ => 1) e) (ClaudeWCT.WCT9.chainW 0 tree leaf i 0 e v)
      (fun a t => TopHead s0 valp e a t) := by
    unfold ClaudeWCT.WCT9.chainW
    exact TSim.foldlM_range' 0 e _ v (fun j a t => TopHead s0 valp j a t) _ _ _ _
      (fun j hj a t ht => by simpa using top_step hc hpref sk hpre hj (by omega) ht) h0
  have rest : ∀ a t, TopHead s0 valp e a t →
      TSim im sk t 12 12 0 0 (pure (a,a))
        (fun r w => w.pc = pcOf ret ∧ DigAt w valp r.1 ∧ DigAt w (CHAIN+48) r.2 ∧
          RegsExcept s0 w Keygen.chainRegs ∧ Frame s0 w (ChainW valp)) := by
    intro a t ht
    obtain ⟨w,hw,wp,wv,wr,wf⟩ := top_exit hc hpref hpre ht
    have hvc:=hpre.hvc
    exact TSim.pure_steps hw ⟨wp,wv,ht.val.frame wf (by decide) (by simp; omega) (by simp; omega),
      (ht.regs.trans wr).mono (by simp [Keygen.chainRegs]),(ht.frame.trans wf).mono (by
        intro A hA h; rcases h with h|h; exact h; exact Or.inr (Or.inr h))⟩
  refine (TSim.steps hu (TSim.bind run rest)).of_eq rfl ?_ ?_ ?_ ?_
  all_goals (try simp only [sumTo_const])
  all_goals omega
end
end ClaudeWCT.W9.Machine.Sign.SharedChain
end
-- ==== merged from T3M_Sign_SeedLeafPhases ====
section

section


namespace SigGolfCandidate.T3M.Sign.Seed
open SigGolfCandidate.T3M.Sign.SeedIndependent
open SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
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
theorem sub27_pre_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 27)) (lay : T3.Layer) (tree leaf : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 32)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h15 : tree = 0 ∨ s.getReg .x15 = BitVec.ofNat 64 (T3.height lay)) :
    ∃ t, Steps image s 16 16 t ∧ t.pc = pcOf 1554 ∧ t.getReg .x3 = s.getReg .x1 ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧
      RegsExcept s t [.x3, .x6, .x28, .x30] ∧
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
  obtain ⟨t2, s2, p2, m16, m24, r2, f2⟩ : ∃ t, Steps image t1 14 14 t ∧ t.pc = pcOf 1554 ∧
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
  refine ⟨t2, s1.trans s2, p2, ?_, m16, m24, (r1.trans r2).mono (by decide),
    (f1.trans f2).mono (fun A _ h => by simp_all)⟩
  rw [r2.get (by decide), x3]
/-- Lower leaves (`lay ≠ 0`): the prologue, PRE (`bne s0` taken) and `li s3,0`; at `b + 41`. -/
theorem sub27_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 27)) (lay : T3.Layer) (tree leaf : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 32)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h15 : tree = 0 ∨ s.getReg .x15 = BitVec.ofNat 64 (T3.height lay)) (hlay : lay ≠ 0) :
    ∃ t, Steps image s 18 18 t ∧ t.pc = pcOf (b + 41) ∧ t.getReg .x3 = s.getReg .x1 ∧
      t.getReg .x19 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧
      RegsExcept s t [.x3, .x6, .x7, .x19, .x28, .x30] ∧
      Frame s t (fun A => A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
  have hb := SeedIndependent.b_eq h
  subst hb
  obtain ⟨t1, s1, p1, x3, m16, m24, r1, f1⟩ := sub27_pre_spec h s hpc lay tree leaf hr h8 h9 h18 h15
  have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [r1.get (by decide), h8]
  have hl0 : BitVec.ofNat 64 lay.val ≠ 0#64 := by
    intro he
    have := congrArg BitVec.toNat he
    rw [toNat_ofNat_lt (by have := lay.isLt; omega)] at this
    exact hlay (Fin.ext this)
  obtain ⟨t2, s2, p2, r2, f2⟩ : ∃ t, Steps image t1 1 1 t ∧ t.pc = pcOf (1013 + 40) ∧
      RegsExcept t1 t [] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_pre (SeedIndependent.codeAt_preS h) t1 p1
      (by simp [SeedIndependent.blkS_pre.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_pre.res, E.eval, CmpOp.eval, g8, hl0]
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_pre.res, rv_simp] <;> rfl
    · intro A _ _; simp [SeedIndependent.blkS_pre.res, rv_simp]
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
  · rw [f3.get (by simp only [LEAFPK]; omega) (by simp), f2.get (by simp only [LEAFPK]; omega) (by simp), m16]
  · rw [f3.get (by simp only [LEAFPK]; omega) (by simp), f2.get (by simp only [LEAFPK]; omega) (by simp), m24]
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
theorem sub71_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 71)) (i digp : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 digp) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 72) ∧ t.getReg .x28 = BitVec.ofNat 64 (digp + i) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have hb := SeedIndependent.b_eq h
  subst hb
  refine ⟨_, symRun_sound SeedIndependent.blkS_71 (SeedIndependent.codeAt_sub71S h) s hpc
    (by simp [SeedIndependent.blkS_71.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [SeedIndependent.blkS_71.res, E.eval]
  · simp only [Result.toState_getReg, SeedIndependent.blkS_71.res]; t3n [h19, h22]
  · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_71.res, rv_simp] <;> rfl
  · intro A _ _; simp [SeedIndependent.blkS_71.res, rv_simp]
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
  have hb := SeedIndependent.b_eq h
  subst hb
  refine ⟨_, symRun_sound SeedIndependent.blkS_75 (SeedIndependent.codeAt_sub_75 h) s hpc
    (by simp [SeedIndependent.blkS_75.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [SeedIndependent.blkS_75.res, E.eval]
  · intro r hr; cases r <;> simp_all [SeedIndependent.blkS_75.res, rv_simp] <;> rfl
  · intro A _ _; simp [SeedIndependent.blkS_75.res, rv_simp]
/-- Campaign T8D: the sign's selector sets `x21 = 7` (radix-8 top chains `≥ n4 = 51`), then `4` below `n4`. -/
theorem maxLow_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1000)) (i n4 : Nat) (hi : i < 2 ^ 63) (hn : n4 < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h27 : s.getReg .x27 = BitVec.ofNat 64 n4) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i < n4 then pcOf (b + 1002) else pcOf (b + 76)) ∧
      t.getReg .x21 = BitVec.ofNat 64 7 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hb := SeedIndependent.b_eq h
  subst hb
  refine ⟨_, symRun_sound SeedIndependent.blkS_maxLow (SeedIndependent.codeAt_maxLow h) s hpc
    (by simp [SeedIndependent.blkS_maxLow.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, SeedIndependent.blkS_maxLow.res, E.eval, CmpOp.eval, h19, h27,
      ofNat_slt i n4 hi hn]
    by_cases hin : i < n4 <;> simp [hin]
  · simp [SeedIndependent.blkS_maxLow.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_maxLow.res, rv_simp] <;> rfl
  · intro A _ _; simp [SeedIndependent.blkS_maxLow.res, rv_simp]
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
theorem ltr_x29 (s : MachineState) (leaf : Nat) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    (SeedIndependent.blkS_ltr.res.toState s).getReg .x29 = BitVec.ofNat 64 (LOUT + hiO leaf) := by
  show BinOp.eval .add (BinOp.eval .sll (BinOp.eval .xor (BinOp.eval .and (s.getReg .x18) 1#64) 1#64) 4#64)
    132032#64 = _
  rw [h18, halfSel_eval]
  show BitVec.ofNat 64 (hiO leaf) + BitVec.ofNat 64 132032 = _
  rw [ofNat_add_ofNat, Nat.add_comm]
theorem sub106W_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 106)) (leaf dest : Nat) (hd : dest % 8 = 0) (hd' : dest + 16 ≤ 2 ^ 24)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h25 : s.getReg .x25 = BitVec.ofNat 64 dest) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf (b + 112) ∧
      t.getMem (BitVec.ofNat 64 dest) = s.getMem (BitVec.ofNat 64 (LOUT + hiO leaf)) ∧
      t.getMem (BitVec.ofNat 64 (dest + 8)) = s.getMem (BitVec.ofNat 64 (LOUT + hiO leaf + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29] ∧ Frame s t (fun A => A = dest ∨ A = dest + 8) := by
  obtain rfl := SeedIndependent.b_eq h
  have hho : hiO leaf ≤ 16 := by unfold hiO; split_ifs <;> omega
  -- 1119: jal 1660
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1660 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_106 (SeedIndependent.codeAt_sub106S h) s hpc
      (by simp [SeedIndependent.blkS_106.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_106.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  -- 1660..1666: t4 = LOUT + hiO leaf
  obtain ⟨t1, s1, p1, x29, r1, f1⟩ : ∃ t, Steps image t0 7 7 t ∧ t.pc = pcOf (1013 + 108) ∧
      t.getReg .x29 = BitVec.ofNat 64 (LOUT + hiO leaf) ∧ RegsExcept t0 t [.x6, .x29] ∧
      Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_ltr (SeedIndependent.codeAt_leafTrampS h) t0 p0
      (by simp [SeedIndependent.blkS_ltr.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_ltr.res, E.eval]
    · exact ltr_x29 t0 leaf (by rw [r0.get (by simp)]; exact h18)
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_ltr.res, rv_simp] <;> rfl
    · intro A hA hn; rfl
  have g1 : ∀ r, r ∉ [Reg.x6, .x29] → t1.getReg r = s.getReg r := fun r hr => (r0.trans r1).get (by simpa using hr)
  have hm : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA => by
    rw [f1.get hA (fun h => h), f0.get hA (fun h => h)]
  have hh2 : hiO leaf = 0 ∨ hiO leaf = 16 := by unfold hiO; split_ifs <;> simp
  -- 1121..1124: copy
  have hobl : Oblig.all t1 SeedIndependent.blkS_108.res.st.obl := by
    simp only [SeedIndependent.blkS_108.res]
    t3n [x29, g1 .x25 (by simp), h25]
    simp only [LOUT]
    omega
  refine ⟨_, ((s0.trans s1).trans (symRun_sound SeedIndependent.blkS_108 (SeedIndependent.codeAt_sub108S h) t1 p1
    hobl)).of_eq (by simp [SeedIndependent.blkS_108.res]) (by simp [SeedIndependent.blkS_108.res]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [SeedIndependent.blkS_108.res, E.eval]
  · simp only [Result.toState_getMem, SeedIndependent.blkS_108.res]
    t3n [x29, g1 .x25 (by simp), h25]
    rw [if_neg (by omega), if_pos (by omega), hm _ (by simp only [LOUT]; omega)]
  · simp only [Result.toState_getMem, SeedIndependent.blkS_108.res]
    t3n [x29, g1 .x25 (by simp), h25]
    rw [hm _ (by simp only [LOUT]; omega)]
  · have r2 : RegsExcept t1 (SeedIndependent.blkS_108.res.toState t1) [.x6, .x7] := by
      intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_108.res, rv_simp] <;> rfl
    exact ((r0.trans r1).trans r2).mono (by simp)
  · intro A hA hn
    simp only [Result.toState_getMem, SeedIndependent.blkS_108.res]
    t3n [x29, g1 .x25 (by simp), h25]
    have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
    rw [hA', if_neg (by omega), if_neg (by omega), hm A hA]
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
/-- C3 (FULL): the sign's chain program (`Keygen.chainProg` with `WCT9.chainW`: lower chain 0 keeps the high half of
its step-6 output). -/
def chainProgW (A : LeafArgs) (i : Nat) (seed : Digest) : T3.M (Digest × Digest) := do
  let v ← ClaudeWCT.WCT9.chainW A.lay A.tree A.leaf i 0 (A.d i) seed
  let last ← ClaudeWCT.WCT9.chainW A.lay A.tree A.leaf i (A.d i) (A.e i - A.d i) v
  pure (v, last)
theorem chainK_le_chainCy (lay : Layer) (i e : Nat) : chainK lay i e ≤ chainCy lay i e := by
  unfold chainK chainCy
  have : ∀ n, sumTo (fun m => rungK lay + trX lay.val i m) n ≤ sumTo (fun m => rungC lay + trX lay.val i m) n := by
    intro n; induction n with
    | zero => simp [sumTo]
    | succ n ih => simp only [sumTo]; have : rungK lay ≤ rungC lay := by unfold rungK rungC; omega
                   omega
  have := this e; omega
theorem slot_low {lay : Layer} (h : lay ≠ 0) (c : Nat) :
    slot lay c = if c = 0 then LEAFPK else LEAFPK + 16 * (c + 1) := by
  simp [slot, h]
theorem slotK_low {lay : Layer} (h : lay ≠ 0) (c : Nat) : slotK lay c = if c = 0 then 0 else 1 := by
  simp [slotK, h]
end SigGolfCandidate.T3M.Sign.Seed
end


section
set_option maxRecDepth 100000
namespace SigGolfCandidate.T3M.Sign.SharedLeaf
open SigGolfCandidate.T3M.Sign.Seed
open SigGolfCandidate.T3M.Sign.SeedIndependent
open SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
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
theorem sub27_pre_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 27)) (lay : T3.Layer) (tree leaf : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 32)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h15 : tree = 0 ∨ s.getReg .x15 = BitVec.ofNat 64 (T3.height lay)) :
    ∃ t, Steps image s 16 16 t ∧ t.pc = pcOf 1554 ∧ t.getReg .x3 = s.getReg .x1 ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧
      RegsExcept s t [.x3, .x6, .x28, .x30] ∧
      Frame s t (fun A => A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
  obtain rfl := h.base
  obtain ⟨t1, s1, p1, x3, r1, f1⟩ : ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 1528 ∧
      t.getReg .x3 = s.getReg .x1 ∧ RegsExcept s t [.x3] ∧ Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_27 (SharedLeafCode.Code.codeAt_sub27S h) s hpc
      (by simp [SeedIndependent.blkS_27.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_27.res, E.eval]
    · simp [SeedIndependent.blkS_27.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_27.res, rv_simp] <;> rfl
    · intro A _ _; simp [SeedIndependent.blkS_27.res, rv_simp]
  have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [r1.get (by decide), h8]
  have g9 : t1.getReg .x9 = BitVec.ofNat 64 tree := by rw [r1.get (by decide), h9]
  have g18 : t1.getReg .x18 = BitVec.ofNat 64 leaf := by rw [r1.get (by decide), h18]
  obtain ⟨t2, s2, p2, m16, m24, r2, f2⟩ : ∃ t, Steps image t1 14 14 t ∧ t.pc = pcOf 1554 ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧
      RegsExcept t1 t [.x6, .x28, .x30] ∧ Frame t1 t (fun A => A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_hp (SharedLeafCode.Code.codeAt_hpS h) t1 p1
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
  refine ⟨t2, s1.trans s2, p2, ?_, m16, m24, (r1.trans r2).mono (by decide),
    (f1.trans f2).mono (fun A _ h => by simp_all)⟩
  rw [r2.get (by decide), x3]
/-- Lower leaves (`lay ≠ 0`): the prologue, PRE (`bne s0` taken) and `li s3,0`; at `b + 41`. -/
theorem sub27_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 27)) (lay : T3.Layer) (tree leaf : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 32)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h15 : tree = 0 ∨ s.getReg .x15 = BitVec.ofNat 64 (T3.height lay)) (hlay : lay ≠ 0) :
    ∃ t, Steps image s 18 18 t ∧ t.pc = pcOf (b + 41) ∧ t.getReg .x3 = s.getReg .x1 ∧
      t.getReg .x19 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧
      RegsExcept s t [.x3, .x6, .x7, .x19, .x28, .x30] ∧
      Frame s t (fun A => A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
  have hb := h.base
  subst hb
  obtain ⟨t1, s1, p1, x3, m16, m24, r1, f1⟩ := sub27_pre_spec h s hpc lay tree leaf hr h8 h9 h18 h15
  have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [r1.get (by decide), h8]
  have hl0 : BitVec.ofNat 64 lay.val ≠ 0#64 := by
    intro he
    have := congrArg BitVec.toNat he
    rw [toNat_ofNat_lt (by have := lay.isLt; omega)] at this
    exact hlay (Fin.ext this)
  obtain ⟨t2, s2, p2, r2, f2⟩ : ∃ t, Steps image t1 1 1 t ∧ t.pc = pcOf (1013 + 40) ∧
      RegsExcept t1 t [] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_pre (SharedLeafCode.Code.codeAt_preS h) t1 p1
      (by simp [SeedIndependent.blkS_pre.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_pre.res, E.eval, CmpOp.eval, g8, hl0]
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_pre.res, rv_simp] <;> rfl
    · intro A _ _; simp [SeedIndependent.blkS_pre.res, rv_simp]
  obtain ⟨t3, s3, p3, x19, r3, f3⟩ : ∃ t, Steps image t2 1 1 t ∧ t.pc = pcOf (1013 + 41) ∧
      t.getReg .x19 = BitVec.ofNat 64 0 ∧ RegsExcept t2 t [.x19] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_40 (SharedLeafCode.Code.codeAt_sub40S h) t2 p2
      (by simp [SeedIndependent.blkS_40.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_40.res, E.eval]
    · simp [SeedIndependent.blkS_40.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_40.res, rv_simp] <;> rfl
    · intro A _ _; simp [SeedIndependent.blkS_40.res, rv_simp]
  refine ⟨t3, (s1.trans s2).trans s3, p3, ?_, x19, ?_, ?_, ((r1.trans r2).trans r3).mono (by decide),
    ((f1.trans f2).trans f3).mono (fun A _ h => by simp_all)⟩
  · rw [r3.get (by decide), r2.get (by decide), x3]
  · rw [f3.get (by simp only [LEAFPK]; omega) (by simp), f2.get (by simp only [LEAFPK]; omega) (by simp), m16]
  · rw [f3.get (by simp only [LEAFPK]; omega) (by simp), f2.get (by simp only [LEAFPK]; omega) (by simp), m24]
theorem sub41_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 41)) (i n : Nat) (hi : i < 2 ^ 63) (hn : n < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if i < n then pcOf (b + 42) else pcOf (b + 95)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_41 (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (SharedLeafCode.Code.codeAt_sub_41 h) s hpc (by simp [st_41, blk117_41.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_41, rebase, blk117_41.res, E.eval, CmpOp.eval, h19, h26,
      ofNat_slt i n hi hn]
    by_cases hin : i < n <;> simp [hin]
  · intro r hr; cases r <;> simp_all [st_41, blk117_41.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_41, blk117_41.res, rv_simp]
theorem sub71_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 71)) (i digp : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 digp) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 72) ∧ t.getReg .x28 = BitVec.ofNat 64 (digp + i) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have hb := h.base
  subst hb
  refine ⟨_, symRun_sound SeedIndependent.blkS_71 (SharedLeafCode.Code.codeAt_sub71S h) s hpc
    (by simp [SeedIndependent.blkS_71.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [SeedIndependent.blkS_71.res, E.eval]
  · simp only [Result.toState_getReg, SeedIndependent.blkS_71.res]; t3n [h19, h22]
  · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_71.res, rv_simp] <;> rfl
  · intro A _ _; simp [SeedIndependent.blkS_71.res, rv_simp]
theorem sub72_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 72)) (a : Nat) (ha : a + 1 ≤ 2 ^ 24) (d : Nat) (hd : d < 256)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 a) (hbyte : s.getByte (BitVec.ofNat 64 a) = BitVec.ofNat 8 d) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 73) ∧ t.getReg .x17 = BitVec.ofNat 64 d ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun _ => False) := by
  have hoff : s.getReg .x28 + signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 a := by
    rw [h28]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
  have st := steps_lbu (rd := .x17) (rs := .x28) (off := 0) (SharedLeafCode.Code.codeAt_sub_72 h) hpc rfl
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
theorem sub73_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 73)) (lay : Nat) (hlay : lay < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if lay = 0 then pcOf (b + 75) else pcOf (b + 76)) ∧
      t.getReg .x21 = BitVec.ofNat 64 7 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hrun := run_73 (Or.inr h.base)
  have hz : (BitVec.ofNat 64 lay = 0#64) ↔ lay = 0 := by
    constructor
    · intro e
      have q := congrArg BitVec.toNat e
      simpa [toNat_ofNat_lt (show lay < 2 ^ 64 by omega)] using q
    · intro e; subst lay; rfl
  refine ⟨_, symRun_sound hrun (SharedLeafCode.Code.codeAt_sub_73 h) s hpc (by simp [st_73, blk117_73.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, pcE_73, rebase, blk117_73.res, E.eval, CmpOp.eval, h8, hz]
  · simp [st_73, blk117_73.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_73, blk117_73.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_73, blk117_73.res, rv_simp]
theorem sub75_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 75)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1937 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hb := h.base
  subst hb
  refine ⟨_, symRun_sound SeedIndependent.blkS_75T (SharedLeafCode.Code.codeAt_sub_75 h) s hpc
    (by simp [SeedIndependent.blkS_75T.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [SeedIndependent.blkS_75T.res, E.eval]
  · intro r hr; cases r <;> simp_all [SeedIndependent.blkS_75T.res, rv_simp] <;> rfl
  · intro A _ _; simp [SeedIndependent.blkS_75T.res, rv_simp]
/-- Campaign T51: cap block A (1937..1939): `x21 = 5`, `t5 = 27`, back to 1089 if `i < 27`. -/
theorem capA_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf 1937) (i : Nat) (hi : i < 2 ^ 63) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = (if i < 27 then pcOf (b + 76) else pcOf 1940) ∧
      t.getReg .x21 = BitVec.ofNat 64 5 ∧ RegsExcept s t [.x21, .x30] ∧ Frame s t (fun _ => False) := by
  have hb := h.base
  subst hb
  refine ⟨_, symRun_sound SeedIndependent.blkS_capA (SharedLeafCode.Code.codeAt_capA h) s hpc
    (by simp [SeedIndependent.blkS_capA.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, SeedIndependent.blkS_capA.res, E.eval, CmpOp.eval, h19,
      ofNat_slt i 27 hi (by norm_num)]
    by_cases hin : i < 27 <;> simp [hin]
  · simp [SeedIndependent.blkS_capA.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_capA.res, rv_simp] <;> rfl
  · intro A _ _; simp [SeedIndependent.blkS_capA.res, rv_simp]
/-- Cap block B (1940..1942): `x21 = 4`, back to 1089 if `i < 48`. -/
theorem capB_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf 1940) (i : Nat) (hi : i < 2 ^ 63) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = (if i < 48 then pcOf (b + 76) else pcOf 1943) ∧
      t.getReg .x21 = BitVec.ofNat 64 4 ∧ RegsExcept s t [.x21, .x30] ∧ Frame s t (fun _ => False) := by
  have hb := h.base
  subst hb
  refine ⟨_, symRun_sound SeedIndependent.blkS_capB (SharedLeafCode.Code.codeAt_capB h) s hpc
    (by simp [SeedIndependent.blkS_capB.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, SeedIndependent.blkS_capB.res, E.eval, CmpOp.eval, h19,
      ofNat_slt i 48 hi (by norm_num)]
    by_cases hin : i < 48 <;> simp [hin]
  · simp [SeedIndependent.blkS_capB.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_capB.res, rv_simp] <;> rfl
  · intro A _ _; simp [SeedIndependent.blkS_capB.res, rv_simp]
/-- Cap block C (1943..1945): `x21 = 6` (the r7 pair), back to 1089 if `i < 50`. -/
theorem capC_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf 1943) (i : Nat) (hi : i < 2 ^ 63) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = (if i < 50 then pcOf (b + 76) else pcOf 1946) ∧
      t.getReg .x21 = BitVec.ofNat 64 6 ∧ RegsExcept s t [.x21, .x30] ∧ Frame s t (fun _ => False) := by
  have hb := h.base
  subst hb
  refine ⟨_, symRun_sound SeedIndependent.blkS_capC (SharedLeafCode.Code.codeAt_capC h) s hpc
    (by simp [SeedIndependent.blkS_capC.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, SeedIndependent.blkS_capC.res, E.eval, CmpOp.eval, h19,
      ofNat_slt i 50 hi (by norm_num)]
    by_cases hin : i < 50 <;> simp [hin]
  · simp [SeedIndependent.blkS_capC.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_capC.res, rv_simp] <;> rfl
  · intro A _ _; simp [SeedIndependent.blkS_capC.res, rv_simp]
/-- Cap block D (1946/1947): `x21 = 5` (the checksum chain), `j 1089`. -/
theorem capD_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf 1946) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 76) ∧ t.getReg .x21 = BitVec.ofNat 64 5 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hb := h.base
  subst hb
  refine ⟨_, symRun_sound SeedIndependent.blkS_capD (SharedLeafCode.Code.codeAt_capD h) s hpc
    (by simp [SeedIndependent.blkS_capD.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [SeedIndependent.blkS_capD.res, Result.toState_pc, E.eval]
  · simp [SeedIndependent.blkS_capD.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_capD.res, rv_simp] <;> rfl
  · intro A _ _; simp [SeedIndependent.blkS_capD.res, rv_simp]
/-- Campaign T51: the top selector from `b + 75` (`j 1937` and the cap block) sets `x21 = maxDigit 0 i` in
`selectorExtra 0 i` steps (4 / 7 / 10 / 12). -/
theorem sel_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 75)) (lay : T3.Layer) (hl : lay = 0) (i : Nat) (hi : i < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s (selectorExtra lay i) (selectorExtra lay i) t ∧ t.pc = pcOf (b + 76) ∧
      t.getReg .x21 = BitVec.ofNat 64 (SigGolfCandidate.T3.maxDigit lay i) ∧ RegsExcept s t [.x21, .x30] ∧
      Frame s t (fun _ => False) := by
  subst hl
  obtain ⟨ta, sta, tapc, tar, taf⟩ := sub75_spec h s hpc
  obtain ⟨tb, stb, tbpc, tbx21, tbr, tbf⟩ := capA_spec h ta tapc i hi (by rw [tar.get (by simp)]; exact h19)
  by_cases h27 : i < 27
  · rw [if_pos h27] at tbpc
    refine ⟨tb, Steps.of_eq (sta.trans stb) ?_ ?_, tbpc, ?_, (tar.trans tbr).mono (by simp),
      (taf.trans tbf).mono (by simp)⟩
    · simp [selectorExtra, h27]
    · simp [selectorExtra, h27]
    · rw [tbx21]; simp [SigGolfCandidate.T3.maxDigit, h27]
  rw [if_neg h27] at tbpc
  have eb := tar.trans tbr
  obtain ⟨tc, stc, tcpc, tcx21, tcr, tcf⟩ := capB_spec h tb tbpc i hi (by rw [eb.get (by simp)]; exact h19)
  by_cases h48 : i < 48
  · rw [if_pos h48] at tcpc
    refine ⟨tc, Steps.of_eq ((sta.trans stb).trans stc) ?_ ?_, tcpc, ?_, (eb.trans tcr).mono (by simp),
      ((taf.trans tbf).trans tcf).mono (by simp)⟩
    · simp [selectorExtra, h27, h48]
    · simp [selectorExtra, h27, h48]
    · rw [tcx21]; simp [SigGolfCandidate.T3.maxDigit, h27, h48]
  rw [if_neg h48] at tcpc
  have ec := eb.trans tcr
  obtain ⟨td, std, tdpc, tdx21, tdr, tdf⟩ := capC_spec h tc tcpc i hi (by rw [ec.get (by simp)]; exact h19)
  by_cases h50 : i < 50
  · rw [if_pos h50] at tdpc
    refine ⟨td, Steps.of_eq (((sta.trans stb).trans stc).trans std) ?_ ?_, tdpc, ?_, (ec.trans tdr).mono (by simp),
      (((taf.trans tbf).trans tcf).trans tdf).mono (by simp)⟩
    · simp [selectorExtra, h27, h48, h50]
    · simp [selectorExtra, h27, h48, h50]
    · rw [tdx21]; simp [SigGolfCandidate.T3.maxDigit, h27, h48, h50]
  rw [if_neg h50] at tdpc
  obtain ⟨te, ste, tepc, tex21, ter, tef⟩ := capD_spec h td tdpc
  refine ⟨te, Steps.of_eq ((((sta.trans stb).trans stc).trans std).trans ste) ?_ ?_, tepc, ?_,
    ((ec.trans tdr).trans ter).mono (by simp), ((((taf.trans tbf).trans tcf).trans tdf).trans tef).mono (by simp)⟩
  · simp [selectorExtra, h27, h48, h50]
  · simp [selectorExtra, h27, h48, h50]
  · rw [tex21]; simp [SigGolfCandidate.T3.maxDigit, h27, h48, h50]
theorem sub76_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 76)) (so : Bool) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if so then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if so then pcOf (b + 77) else pcOf (b + 78)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_76 (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (SharedLeafCode.Code.codeAt_sub_76 h) s hpc (by simp [st_76, blk117_76.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_76, rebase, blk117_76.res, E.eval, CmpOp.eval, h31]
    cases so <;> simp
  · intro r hr; cases r <;> simp_all [st_76, blk117_76.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_76, blk117_76.res, rv_simp]
theorem sub77_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 77)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 78) ∧ t.getReg .x21 = s.getReg .x17 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hrun := run_77 (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (SharedLeafCode.Code.codeAt_sub_77 h) s hpc (by simp [st_77, blk117_77.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_77, Result.toState_pc, E.eval]
  · simp [st_77, blk117_77.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_77, blk117_77.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_77, blk117_77.res, rv_simp]
theorem sub78_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 78)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf b ∧ t.getReg .x1 = pcOf (b + 79) ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) := by
  have hrun := run_78 (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (SharedLeafCode.Code.codeAt_sub_78 h) s hpc (by simp [st_78, blk117_78.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_78, Result.toState_pc, E.eval]
  · simp [st_78, blk117_78.res, rv_simp, RegFile.set]
  · intro r hr; simp at hr; cases r <;> simp_all [st_78, blk117_78.res, rv_simp, RegFile.set] <;> rfl
  · intro A _ _; simp [st_78, blk117_78.res, rv_simp]
theorem sub79_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 79)) (so : Bool) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if so then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if so then pcOf (b + 92) else pcOf (b + 80)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_79 (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (SharedLeafCode.Code.codeAt_sub_79 h) s hpc (by simp [st_79, blk117_79.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_79, rebase, blk117_79.res, E.eval, CmpOp.eval, h31]
    cases so <;> simp
  · intro r hr; cases r <;> simp_all [st_79, blk117_79.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_79, blk117_79.res, rv_simp]
theorem sub80_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 80)) (i : Nat) (hi : i < 2 ^ 32) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i = 0 then pcOf (b + 83) else pcOf (b + 82)) ∧
      t.getReg .x28 = BitVec.ofNat 64 (16 * i) ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  obtain rfl := h.base
  refine ⟨_, symRun_sound SeedIndependent.blkS_80 (SharedLeafCode.Code.codeAt_sub80S h) s hpc
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
theorem sub82_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 82)) (o : Nat) (h28 : s.getReg .x28 = BitVec.ofNat 64 o) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 83) ∧ t.getReg .x28 = BitVec.ofNat 64 (o + 16) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have hrun := run_82 (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (SharedLeafCode.Code.codeAt_sub_82 h) s hpc (by simp [st_82, blk117_82.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_82, Result.toState_pc, E.eval]
  · t3n [st_82, blk117_82.res, h28]
  · intro r hr; simp at hr; cases r <;> simp_all [st_82, blk117_82.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_82, blk117_82.res, rv_simp]
theorem sub83_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 83)) (o : Nat) (ho : o % 8 = 0) (ho' : LEAFPK + o + 16 ≤ 2 ^ 24)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 o) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf (b + 92) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + o)) = s.getMem (BitVec.ofNat 64 (CHAIN + 48)) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + o + 8)) = s.getMem (BitVec.ofNat 64 (CHAIN + 56)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = LEAFPK + o ∨ A = LEAFPK + o + 8) := by
  have hrun := run_83 (Or.inr h.base)
  have hobl : Oblig.all s st_83.obl := by
    simp only [st_83, blk117_83.res]
    t3n [h28]
    simp only [LEAFPK] at ho'
    omega
  refine ⟨_, symRun_sound hrun (SharedLeafCode.Code.codeAt_sub_83 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
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
theorem sub92_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 92)) (i v : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 v) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 41) ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      t.getReg .x23 = BitVec.ofNat 64 (v + 16) ∧ RegsExcept s t [.x19, .x23] ∧
      Frame s t (fun _ => False) := by
  have hrun := run_92 (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (SharedLeafCode.Code.codeAt_sub_92 h) s hpc (by simp [st_92, blk117_92.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_92, Result.toState_pc, E.eval]
  · t3n [st_92, blk117_92.res, h19]
  · t3n [st_92, blk117_92.res, h23]
  · intro r hr; simp at hr; cases r <;> simp_all [st_92, blk117_92.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_92, blk117_92.res, rv_simp]
theorem sub95_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 95)) (so : Bool) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if so then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if so then pcOf (b + 112) else pcOf (b + 96)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_95 (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (SharedLeafCode.Code.codeAt_sub_95 h) s hpc (by simp [st_95, blk117_95.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_95, rebase, blk117_95.res, E.eval, CmpOp.eval, h31]
    cases so <;> simp
  · intro r hr; cases r <;> simp_all [st_95, blk117_95.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_95, blk117_95.res, rv_simp]
theorem sub96_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 96)) (n : Nat) (hn : n = 51 ∨ n = 43)
    (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf (b + 105) ∧ t.getReg .x10 = BitVec.ofNat 64 LEAFPK ∧
      t.getReg .x11 = BitVec.ofNat 64 ((16 * (n + 1) + 63) / 64 * 64) ∧
      t.getReg .x12 = BitVec.ofNat 64 LOUT ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      Frame s t (fun _ => False) := by
  have hrun := run_96 (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (SharedLeafCode.Code.codeAt_sub_96 h) s hpc (by simp [st_96, blk117_96.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_96, Result.toState_pc, E.eval]
  · simp [st_96, blk117_96.res, rv_simp]
  · simp only [Result.toState_getReg, st_96, blk117_96.res, rv_simp, h26]
    rcases hn with rfl | rfl <;> decide
  · simp [st_96, blk117_96.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_96, blk117_96.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_96, blk117_96.res, rv_simp]
theorem fetch_sub105 {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 105)) : fetch image s = some (.base .ECALL) :=
  ((SharedLeafCode.Code.codeAt_sub_105 h).fetch s hpc).trans rfl
theorem ltr_x29 (s : MachineState) (leaf : Nat) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    (SeedIndependent.blkS_ltr.res.toState s).getReg .x29 = BitVec.ofNat 64 (LOUT + hiO leaf) := by
  show BinOp.eval .add (BinOp.eval .sll (BinOp.eval .xor (BinOp.eval .and (s.getReg .x18) 1#64) 1#64) 4#64)
    132032#64 = _
  rw [h18, halfSel_eval]
  show BitVec.ofNat 64 (hiO leaf) + BitVec.ofNat 64 132032 = _
  rw [ofNat_add_ofNat, Nat.add_comm]
theorem sub106W_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 106)) (leaf dest : Nat) (hd : dest % 8 = 0) (hd' : dest + 16 ≤ 2 ^ 24)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h25 : s.getReg .x25 = BitVec.ofNat 64 dest) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf (b + 112) ∧
      t.getMem (BitVec.ofNat 64 dest) = s.getMem (BitVec.ofNat 64 (LOUT + hiO leaf)) ∧
      t.getMem (BitVec.ofNat 64 (dest + 8)) = s.getMem (BitVec.ofNat 64 (LOUT + hiO leaf + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29] ∧ Frame s t (fun A => A = dest ∨ A = dest + 8) := by
  obtain rfl := h.base
  have hho : hiO leaf ≤ 16 := by unfold hiO; split_ifs <;> omega
  -- 1119: jal 1660
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1660 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_106 (SharedLeafCode.Code.codeAt_sub106S h) s hpc
      (by simp [SeedIndependent.blkS_106.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_106.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  -- 1660..1666: t4 = LOUT + hiO leaf
  obtain ⟨t1, s1, p1, x29, r1, f1⟩ : ∃ t, Steps image t0 7 7 t ∧ t.pc = pcOf (1013 + 108) ∧
      t.getReg .x29 = BitVec.ofNat 64 (LOUT + hiO leaf) ∧ RegsExcept t0 t [.x6, .x29] ∧
      Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_ltr (SharedLeafCode.Code.codeAt_leafTrampS h) t0 p0
      (by simp [SeedIndependent.blkS_ltr.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_ltr.res, E.eval]
    · exact ltr_x29 t0 leaf (by rw [r0.get (by simp)]; exact h18)
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_ltr.res, rv_simp] <;> rfl
    · intro A hA hn; rfl
  have g1 : ∀ r, r ∉ [Reg.x6, .x29] → t1.getReg r = s.getReg r := fun r hr => (r0.trans r1).get (by simpa using hr)
  have hm : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA => by
    rw [f1.get hA (fun h => h), f0.get hA (fun h => h)]
  have hh2 : hiO leaf = 0 ∨ hiO leaf = 16 := by unfold hiO; split_ifs <;> simp
  -- 1121..1124: copy
  have hobl : Oblig.all t1 SeedIndependent.blkS_108.res.st.obl := by
    simp only [SeedIndependent.blkS_108.res]
    t3n [x29, g1 .x25 (by simp), h25]
    simp only [LOUT]
    omega
  refine ⟨_, ((s0.trans s1).trans (symRun_sound SeedIndependent.blkS_108 (SharedLeafCode.Code.codeAt_sub108S h) t1 p1
    hobl)).of_eq (by simp [SeedIndependent.blkS_108.res]) (by simp [SeedIndependent.blkS_108.res]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [SeedIndependent.blkS_108.res, E.eval]
  · simp only [Result.toState_getMem, SeedIndependent.blkS_108.res]
    t3n [x29, g1 .x25 (by simp), h25]
    rw [if_neg (by omega), if_pos (by omega), hm _ (by simp only [LOUT]; omega)]
  · simp only [Result.toState_getMem, SeedIndependent.blkS_108.res]
    t3n [x29, g1 .x25 (by simp), h25]
    rw [hm _ (by simp only [LOUT]; omega)]
  · have r2 : RegsExcept t1 (SeedIndependent.blkS_108.res.toState t1) [.x6, .x7] := by
      intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_108.res, rv_simp] <;> rfl
    exact ((r0.trans r1).trans r2).mono (by simp)
  · intro A hA hn
    simp only [Result.toState_getMem, SeedIndependent.blkS_108.res]
    t3n [x29, g1 .x25 (by simp), h25]
    have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
    rw [hA', if_neg (by omega), if_neg (by omega), hm A hA]
theorem sub112_spec {image : Image} {b : Nat} (h : SharedLeafCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 112)) (k : Nat) (h3 : s.getReg .x3 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_112 (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (SharedLeafCode.Code.codeAt_sub_112 h) s hpc (by simp [st_112, blk117_112.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_112, blk117_112.res, rv_simp, h3, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_112, blk117_112.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_112, blk117_112.res, rv_simp]
end SigGolfCandidate.T3M.Sign.SharedLeaf
end

section



namespace SigGolfCandidate.T3M.Sign.SharedLeaf
open SigGolfCandidate.T3M.Sign.Seed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3M.Sign.SeedIndependent
open SigGolfCandidate.T3 (Layer Digest chainCount width maxDigit chain chainInput buildLeaf leafHash privatePair
  shortHash header pad64 zero16 privateInput)
open SphincsSecurity (bytesLE bytesLE_length)
theorem chainK_le_chainCy (lay : Layer) (i e : Nat) : chainK lay i e ≤ chainCy lay i e := by
  unfold chainK chainCy
  have : ∀ n, sumTo (fun m => rungK lay + trX lay.val i m) n ≤ sumTo (fun m => rungC lay + trX lay.val i m) n := by
    intro n; induction n with
    | zero => simp [sumTo]
    | succ n ih => simp only [sumTo]; have : rungK lay ≤ rungC lay := by unfold rungK rungC; omega
                   omega
  have := this e; omega
theorem slot_low {lay : Layer} (h : lay ≠ 0) (c : Nat) :
    slot lay c = if c = 0 then LEAFPK else LEAFPK + 16 * (c + 1) := by
  simp [slot, h]
theorem slotK_low {lay : Layer} (h : lay ≠ 0) (c : Nat) : slotK lay c = if c = 0 then 0 else 1 := by
  simp [slotK, h]
section leaf
variable {image : Image} {b : Nat} (hsub : SharedLeafCode.Code image b) (sk : BitVec 256) {s0 : MachineState}
  {A : LeafArgs} (hpre : LeafPreS sk s0 A)
include hsub hpre
set_option maxHeartbeats 1000000 in
theorem leaf_prechainFrom61S {j : Nat} (hj : j < A.n) (hlowe : A.lay.val ≠ 0 → A.e j ≤ 7) {st : List Digest × List Digest} {t : MachineState}
    (ht : LeafInv s0 A j st t) (hpc : t.pc = pcOf (b + 61)) (seed : Digest) (half : Nat) (hhalf : half < 2)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 half)
    (hcopy : CodeAt image (pcOf (b + 61)) sub61)
    (hseed : DigAt t (SEEDS + 16 * half) seed) :
    ∃ u, Steps image t (16 + selectorExtra A.lay j + (if A.so then 1 else 0))
        (16 + selectorExtra A.lay j + (if A.so then 1 else 0)) u ∧ u.pc = pcOf b ∧
      ChainPreS u A.lay A.tree A.leaf j (A.d j) (A.e j) (A.valp + 16 * j) (b + 79) ∧
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
  obtain ⟨t1, st1, t1pc, t1x28, t1c48, t1c56, t1r, t1f⟩ := sub61_spec (Or.inr hsub.base) hcopy t hpc j A.digp half hhalf ht.x19 r22 h28
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
      t4.getReg .x21 = BitVec.ofNat 64 (maxDigit A.lay j) ∧ RegsExcept t3 t4 [.x21, .x30] ∧
      Frame t3 t4 (fun _ => False) := by
    have hlay0 : A.lay.val = 0 ↔ A.lay = 0 := by simp
    by_cases hl : A.lay = 0
    · rw [if_pos (hlay0.mpr hl)] at t3pc
      exact sel_spec hsub t3 t3pc A.lay hl j (by change A.n = 51 ∨ A.n = 43 at hn; omega)
        (by rw [(e12.trans t3r).get (by simp)]; exact ht.x19)
    · rw [if_neg (fun hv => hl (hlay0.mp hv))] at t3pc
      exact ⟨t3, by simpa [selectorExtra, hl] using Steps.refl t3, t3pc,
        by simpa [SigGolfCandidate.T3.maxDigit, hl] using t3x21, RegsExcept.refl _ _, Frame.refl _ _⟩
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
  have hL : ∀ X, (X = CHAIN ∨ X = CHAIN + 8) → ¬ LeafW A X := by
    intro X hX hw'
    simp only [LeafW, CHAIN, PRIV, SEEDS, LEAFPK, LOUT] at hX hw' hvs
    have := hpre.hds
    have := hpre.hdv
    simp only [CHAIN, PRIV, SEEDS, LEAFPK, LOUT] at *
    split_ifs at hw' <;> omega
  refine ⟨u, ?_, upc, {
      x5 := ?_, x1 := ux1, x8 := ?_, x9 := ?_, x18 := ?_
      x17 := ?_, x19 := ?_, x21 := ?_, x23 := ?_, htree := hpre.htree
      hi := by change j < 51; change A.n = 51 ∨ A.n = 43 at hn; omega
      hroute := hpre.hroute, hleaf := hpre.hleafHeight
      hcap := ?_, he := hpre.hsteps j hj, hlow := ?_, hv8 := ?_, hv := ?_, hvc := ?_
      z0 := ?_, z8 := ?_ },
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
  · exact hlowe
  · omega
  · omega
  · simp only [CHAIN, PRIV, LEAFPK] at hvs ⊢; omega
  · rw [fr CHAIN (by decide) (hL _ (by simp)) (by decide) (by decide), hpre.z0]
  · rw [fr (CHAIN + 8) (by decide) (hL _ (by simp)) (by decide) (by decide), hpre.z8]
set_option maxHeartbeats 1000000 in
theorem leaf_prechainFrom71S {j : Nat} (hj : j < A.n) (hlowe : A.lay.val ≠ 0 → A.e j ≤ 7) {st : List Digest × List Digest} {t : MachineState}
    (ht : LeafInv s0 A j st t) (hpc : t.pc = pcOf (b + 71)) (seed : Digest)
    (hseed : DigAt t (CHAIN + 48) seed) :
    ∃ u, Steps image t (6 + selectorExtra A.lay j + (if A.so then 1 else 0))
        (6 + selectorExtra A.lay j + (if A.so then 1 else 0)) u ∧ u.pc = pcOf b ∧
      ChainPreS u A.lay A.tree A.leaf j (A.d j) (A.e j) (A.valp + 16 * j) (b + 79) ∧
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
  obtain ⟨t1, st1, t1pc, t1x28, t1r, t1f⟩ := sub71_spec hsub t hpc j A.digp ht.x19 r22
  have hw := hpre.hdigW j hj
  have hbyte : t1.getByte (BitVec.ofNat 64 (A.digp + j)) = BitVec.ofNat 8 (A.d j) := by
    rw [t1f.getByte (by have := hpre.hdigp; omega) (fun h => h.elim),
      ht.frame.getByte (by have := hpre.hdigp; omega) hw, hpre.hdig j hj]
  obtain ⟨t2, st2, t2pc, t2x17, t2r, t2f⟩ := sub72_spec hsub t1 t1pc (A.digp + j)
    (by have := hpre.hdigp; omega) (A.d j) hdb.1 t1x28 hbyte
  have e12 : RegsExcept t t2 [.x6, .x7, .x17, .x28, .x29, .x30] := (t1r.trans t2r).mono (by simp)
  have r8 : t.getReg .x8 = BitVec.ofNat 64 A.lay.val := by rw [g _ (by simp [leafRegs]), hpre.x8]
  obtain ⟨t3, st3, t3pc, t3x21, t3r, t3f⟩ := sub73_spec hsub t2 t2pc A.lay.val
    (by have := A.lay.isLt; omega) (by rw [e12.get (by simp)]; exact r8)
  have hseedv : DigAt t1 (CHAIN + 48) seed := hseed.frame t1f (by decide) (by simp) (by simp)
  obtain ⟨t4, st4, t4pc, t4x21, t4r, t4f⟩ : ∃ t4, Steps image t3 (selectorExtra A.lay j)
      (selectorExtra A.lay j) t4 ∧ t4.pc = pcOf (b + 76) ∧
      t4.getReg .x21 = BitVec.ofNat 64 (maxDigit A.lay j) ∧ RegsExcept t3 t4 [.x21, .x30] ∧
      Frame t3 t4 (fun _ => False) := by
    have hlay0 : A.lay.val = 0 ↔ A.lay = 0 := by simp
    by_cases hl : A.lay = 0
    · rw [if_pos (hlay0.mpr hl)] at t3pc
      exact sel_spec hsub t3 t3pc A.lay hl j (by change A.n = 51 ∨ A.n = 43 at hn; omega)
        (by rw [(e12.trans t3r).get (by simp)]; exact ht.x19)
    · rw [if_neg (fun hv => hl (hlay0.mp hv))] at t3pc
      exact ⟨t3, by simpa [selectorExtra, hl] using Steps.refl t3, t3pc,
        by simpa [SigGolfCandidate.T3.maxDigit, hl] using t3x21, RegsExcept.refl _ _, Frame.refl _ _⟩
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
      simp only [or_false, false_or] at h)
  have f2u : Frame t2 u (fun _ => False) :=
    ((((t3f.trans t4f).trans t5f).trans t6f).trans uf).mono (fun X _ h => by simp_all)
  have gu : ∀ r, r ∉ leafRegs → r ∉ [.x1, .x6, .x7, .x17, .x21, .x28, .x29, .x30] →
      u.getReg r = s0.getReg r := fun r h1 h2 => (e1u.get h2).trans (g r h1)
  have fr : ∀ X, X < 2 ^ 64 → ¬ LeafW A X → X ≠ CHAIN + 48 → X ≠ CHAIN + 56 →
      u.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := fun X hX h1 h2 h3 =>
    (f1u.get hX (by simp [h2, h3])).trans (ht.frame.get hX h1)
  have hL : ∀ X, (X = CHAIN ∨ X = CHAIN + 8) → ¬ LeafW A X := by
    intro X hX hw'
    simp only [LeafW, CHAIN, PRIV, SEEDS, LEAFPK, LOUT] at hX hw' hvs
    have := hpre.hds
    have := hpre.hdv
    simp only [CHAIN, PRIV, SEEDS, LEAFPK, LOUT] at *
    split_ifs at hw' <;> omega
  refine ⟨u, ?_, upc, {
      x5 := ?_, x1 := ux1, x8 := ?_, x9 := ?_, x18 := ?_
      x17 := ?_, x19 := ?_, x21 := ?_, x23 := ?_, htree := hpre.htree
      hi := by change j < 51; change A.n = 51 ∨ A.n = 43 at hn; omega
      hroute := hpre.hroute, hleaf := hpre.hleafHeight
      hcap := ?_, he := hpre.hsteps j hj, hlow := ?_, hv8 := ?_, hv := ?_, hvc := ?_
      z0 := ?_, z8 := ?_ },
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
  · exact hlowe
  · omega
  · omega
  · simp only [CHAIN, PRIV, LEAFPK] at hvs ⊢; omega
  · rw [fr CHAIN (by decide) (hL _ (by simp)) (by decide) (by decide), hpre.z0]
  · rw [fr (CHAIN + 8) (by decide) (hL _ (by simp)) (by decide) (by decide), hpre.z8]
set_option maxHeartbeats 1000000 in
theorem leaf_postchainS {j : Nat} (hj : j < A.n) {st : List Digest × List Digest} {t u : MachineState}
    (ht : LeafInv s0 A j st t) (hupc : u.pc = pcOf (b + 79))
    (hur : RegsExcept t u ([.x1, .x6, .x7, .x17, .x21, .x28, .x29, .x30] ++ SigGolfCandidate.T3M.Keygen.chainRegs))
    (huf : Frame t u (fun X => (X = CHAIN + 48 ∨ X = CHAIN + 56) ∨ ChainW (A.valp + 16 * j) X))
    (v last : Digest) (hv : DigAt u (A.valp + 16 * j) v) (hl : DigAt u (CHAIN + 48) last) :
    ∃ w, Steps image u (4 + (if A.so then 0 else 11 + slotK A.lay j))
        (4 + (if A.so then 0 else 11 + slotK A.lay j)) w ∧ w.pc = pcOf (b + 41) ∧
      LeafInv s0 A (j + 1) (if A.so then (st.1, st.2 ++ [v]) else (st.1 ++ [last], st.2 ++ [v])) w ∧
      Frame u w (fun X => slot A.lay j ≤ X ∧ X < slot A.lay j + 16) := by
  have hn : A.n = 51 ∨ A.n = 43 := chainCount_cases A.lay
  have hvs := hpre.hvs
  have hvb := hpre.hv
  have hv8 := hpre.hv8
  have g : ∀ r, r ∉ leafRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r31 : u.getReg .x31 = BitVec.ofNat 64 (if A.so then 1 else 0) := by
    rw [hur.get (by simp [SigGolfCandidate.T3M.Keygen.chainRegs]), g _ (by simp [leafRegs]), hpre.x31]
  obtain ⟨u1, st1, u1pc, u1r, u1f⟩ := sub79_spec hsub u hupc A.so r31
  obtain ⟨u2, st2, u2pc, u2r, u2f, u2s⟩ : ∃ u2, Steps image u1 (if A.so then 0 else 11 + slotK A.lay j)
      (if A.so then 0 else 11 + slotK A.lay j) u2 ∧ u2.pc = pcOf (b + 92) ∧
      RegsExcept u1 u2 [.x6, .x7, .x28, .x29] ∧
      Frame u1 u2 (fun X => slot A.lay j ≤ X ∧ X < slot A.lay j + 16) ∧
      (A.so = false → DigAt u2 (slot A.lay j) last) := by
    cases hso : A.so
    · rw [hso, if_neg (by simp)] at u1pc
      have r19 : u1.getReg .x19 = BitVec.ofNat 64 j := by
        rw [u1r.get (by simp), hur.get (by simp [SigGolfCandidate.T3M.Keygen.chainRegs])]; exact ht.x19
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
    rw [u2r.get (by simp), u1r.get (by simp), hur.get (by simp [SigGolfCandidate.T3M.Keygen.chainRegs])]; exact ht.x19
  have r23' : u2.getReg .x23 = BitVec.ofNat 64 (A.valp + 16 * j) := by
    rw [u2r.get (by simp), u1r.get (by simp), hur.get (by simp [SigGolfCandidate.T3M.Keygen.chainRegs])]; exact ht.x23
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
  · rw [wr.get (by simp), u2r.get (by simp), u1r.get (by simp), hur.get (by simp [SigGolfCandidate.T3M.Keygen.chainRegs])]; exact ht.x3
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
    TSim image sk t (if A.so then 3 else 25) (if A.so then 3 else 24 + 8 * leafBlocks A.lay)
      (if A.so then 0 else 1) (if A.so then 0 else leafBlocks A.lay)
      (if A.so then pure (0, st.2) else
        (ClaudeWCT.WCT9.lowerLeafHash A.lay A.tree A.leaf st.1 >>= fun root => pure (root, st.2)))
      (fun r u => u.pc = pcOf A.ret ∧ (A.so = false → DigAt u A.dest r.1) ∧ DigsAt u A.valp r.2 ∧
        r.2.length = A.n ∧ u.getReg .x23 = BitVec.ofNat 64 (A.valp + 16 * A.n) ∧ RegsExcept s0 u leafRegs ∧
        Frame s0 u (LeafW A) ∧
        Frame t u (fun X => (LOUT ≤ X ∧ X < LOUT + 32) ∨ (X = A.dest ∨ X = A.dest + 8))) := by
  have hn : A.n = 51 ∨ A.n = 43 := chainCount_cases A.lay
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
    have hnb : leafBlocks A.lay = 13 ∨ leafBlocks A.lay = 11 := by
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
    rw [ClaudeWCT.WCT9.lowerLeafHash_eq, ClaudeWCT.WCT9.lowerHash_eq, bind_assoc]
    simp only [pure_bind]
    refine (TSim.steps (st1.trans (st2.trans st3)) (TSim.publicHash_bind (k := 13) (c := 13) (n := 0) (b := 0)
      (f := fun a => pure (ClaudeWCT.WCT9.lowerHalf A.lay.val A.leaf a, st.2)) (fetch_sub105 hsub t3 t3pc) h5 hv hq
      (fun a => ?_))).of_eq rfl (by omega) (by rw [hblk]; omega) (by omega) (by rw [hblk]; omega)
    have hds := hpre.hds
    have hdv := hpre.hdv
    have hvs := hpre.hvs
    have hdb := hpre.hd
    have hd8 := (hpre.hd8 hso)
    have hwf := Frame.writeHash t3 a LOUT t3x12 (by decide)
    obtain ⟨u2, st5, u2pc, u2a, u2b, u2r, u2f⟩ := sub106W_spec hsub (writeHash t3 a)
      (by rw [pc_writeHash, t3pc, pcOf_add4]) A.leaf A.dest hd8 hdb
      (by rw [getReg_writeHash, r13.get (by simp), g _ (by simp [leafRegs]), hpre.x18])
      (by rw [getReg_writeHash, r13.get (by simp), g _ (by simp [leafRegs]), hpre.x25])
    have hlay4 : 1 ≤ A.lay.val ∧ A.lay.val < 4 := ⟨by
      rcases Nat.eq_zero_or_pos A.lay.val with h0 | h0
      · exact absurd (Fin.ext h0) hl0
      · exact h0, A.lay.isLt⟩
    have hlo := DigAt.writeHash_lowerHalf t3 a LOUT A.lay.val A.leaf t3x12 (by decide) hlay4
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
    · have hd2 : DigAt u2 A.dest (ClaudeWCT.WCT9.lowerHalf A.lay.val A.leaf a) :=
        ⟨u2a.trans hlo.1, by rw [u2b]; exact hlo.2⟩
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
end SigGolfCandidate.T3M.Sign.SharedLeaf
end

namespace SigGolfCandidate.T3M.Sign.SharedLeaf
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem installed_copy : CodeAt Images.signImage (pcOf (1013+61)) Seed.sub61 := by
  apply codeAt_sign_current_slice <;> decide +kernel
end SigGolfCandidate.T3M.Sign.SharedLeaf
end
-- ==== merged from T3M_Sign_SeedTree ====
section

namespace SigGolfCandidate.T3M.Sign.Seed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open Keygen
open SeedIndependent (SeedIndependentAt)
open SigGolfCandidate.T3 (Digest buildLevels buildLevel nodeHash shortHash header pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
theorem sub113_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 113)) (hh : Nat) (h1 : 1 ≤ hh) (h2 : hh ≤ 32)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 116) ∧ t.getReg .x20 = BitVec.ofNat 64 (2 ^ (hh - 1)) ∧
      RegsExcept s t [.x6, .x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_113 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_113 h) s hpc (by simp [st_113, blk117_113.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_113, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, st_113, blk117_113.res, rv_simp, h15]
    apply BitVec.eq_of_toNat_eq
    have e : (BitVec.ofNat 64 hh - 1#64).toNat = hh - 1 := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    rw [BitVec.toNat_shiftLeft, e, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show hh - 1 < 64 by omega)]
    have : 2 ^ (hh - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    simp only [Nat.one_mod, Nat.one_mul, Nat.mod_eq_of_lt this]
  · intro r hr; simp at hr; cases r <;> simp_all [st_113, blk117_113.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_113, blk117_113.res, rv_simp]
theorem sub116_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 116)) (lo : Nat) (hlo : lo < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if lo = 0 then pcOf (b + 159) else pcOf (b + 117)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_116 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_116 h) s hpc (by simp [st_116, blk117_116.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_116, rebase, blk117_116.res, E.eval, CmpOp.eval, h20]
    by_cases h0 : lo = 0
    · subst h0; simp
    · have : BitVec.ofNat 64 lo ≠ 0#64 := fun he => h0 (by
        have := congrArg BitVec.toNat he; rwa [toNat_ofNat_lt hlo] at this)
      simp [h0, this]
  · intro r hr; cases r <;> simp_all [st_116, blk117_116.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_116, blk117_116.res, rv_simp]
theorem sub117_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 117)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 118) ∧ t.getReg .x24 = s.getReg .x20 ∧
      RegsExcept s t [.x24] ∧ Frame s t (fun _ => False) := by
  have hrun := run_117 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_117 h) s hpc (by simp [st_117, blk117_117.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_117, Result.toState_pc, E.eval]
  · simp [st_117, blk117_117.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_117, blk117_117.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_117, blk117_117.res, rv_simp]
theorem sub118_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 118)) (lo k : Nat) (hlo : lo < 2 ^ 40) (hk : k < 2 ^ 40)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if k < 2 * lo then pcOf (b + 120) else pcOf (b + 157)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hrun := run_118 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_118 h) s hpc (by simp [st_118, blk117_118.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_118, rebase, blk117_118.res, rv_simp, h20, h24]
    rw [ofNat_shl, show (1#64 : Word).toNat % 64 = 1 from rfl, ofNat_slt k (lo * 2 ^ 1) (by omega) (by omega)]
    by_cases hkl : k < 2 * lo
    · simp [hkl, show k < lo * 2 by omega]
    · simp [hkl, show ¬ k < lo * 2 by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_118, blk117_118.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_118, blk117_118.res, rv_simp]
theorem sub120_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 120)) (arena k tree h0 : Nat) (ha8 : arena % 8 = 0)
    (hk : 32 * k + 32 + arena ≤ 2 ^ 24) (htree : tree < 2 ^ 32)
    (hdis : NODE + 64 ≤ arena + 32 * k ∨ arena + 32 * k + 32 ≤ NODE)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) (h21 : s.getReg .x21 = BitVec.ofNat 64 h0) :
    ∃ t, Steps image s 20 20 t ∧
      t.pc = (if 2048 ≤ h0 % 4096 then pcOf (b + 1004) else pcOf (b + 140)) ∧
      t.getReg .x7 = 0 ∧ t.getReg .x30 = BitVec.ofNat 64 (NODE + 48) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (arena + 32 * k)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = s.getReg .x21 + BitVec.ofNat 64 (k + 1407) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 24)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x30] ∧
      Frame s t (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 48 ∨ X = NODE + 56) := by
  obtain rfl := SeedIndependent.b_eq h
  have hobl : Oblig.all s SeedIndependent.blkS_120.res.st.obl := by
    simp only [SeedIndependent.blkS_120.res]
    t3n [h2, h24]
    simp only [NODE] at hdis
    omega
  refine ⟨_, symRun_sound SeedIndependent.blkS_120 (SeedIndependent.codeAt_sub120S h) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, SeedIndependent.blkS_120.res, E.eval, CmpOp.eval, BinOp.eval, h21]
    simp only [slt_shl52, slt_shl52', slt_shl52n, slt_shl52n']
    by_cases hc : 2048 ≤ h0 % 4096 <;> simp [hc]
  · simp [SeedIndependent.blkS_120.res, rv_simp]
  · simp [SeedIndependent.blkS_120.res, rv_simp]
  · simp only [Result.toState_getMem, SeedIndependent.blkS_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, SeedIndependent.blkS_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, SeedIndependent.blkS_120.res, NODE]
    t3n [h24]
    rw [BitVec.add_assoc, ofNat_add_ofNat]
  · simp only [Result.toState_getMem, SeedIndependent.blkS_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, SeedIndependent.blkS_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_120.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, SeedIndependent.blkS_120.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem sub214_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1004)) (k : Nat) (hk : k < 2 ^ 12) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 28 28 t ∧ t.pc = pcOf (b + 140) ∧
      t.getReg .x7 = BitVec.ofNat 64 (T3.Rev.revBits 64 k) ∧
      RegsExcept s t [.x6, .x7, .x28] ∧ Frame s t (fun _ => False) := by
  have hrun := run_rev h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_rev h) s hpc (by simp [st_rev, blk117_rev.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_rev, Result.toState_pc, E.eval]
  · rw [Result.toState_getReg, ← RevNet.revNetBV_eq k hk, ← h24]
    rfl
  · intro r hr; simp at hr; cases r <;> simp_all [st_rev, blk117_rev.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_rev, blk117_rev.res, rv_simp]
theorem sub140_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 140)) (h30 : s.getReg .x30 = BitVec.ofNat 64 (NODE + 48)) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (b + 146) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = s.getReg .x7 ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun X => X = NODE + 24) := by
  have hrun := run_140 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_140 h) s hpc (sub140_obl s h30), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_140, Result.toState_pc, E.eval]
  · simp [st_140, blk117_140.res, rv_simp]
  · simp [st_140, blk117_140.res, rv_simp]
  · simp [st_140, blk117_140.res, rv_simp]
  · rw [Result.toState_getMem]; exact sub140_m24 s h30
  · intro r hr; simp at hr; cases r <;> simp_all [st_140, blk117_140.res, rv_simp] <;> rfl
  · intro X hX hn
    rw [Result.toState_getMem]
    exact sub140_frame s h30 X hX (by simp only [NODE] at hn; omega)
theorem sub120_full {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 120)) (tag lay arena k tree : Nat) (htag : tag = 3) (hl1 : 1 ≤ lay) (hl4 : lay < 4)
    (ha8 : arena % 8 = 0) (hk : 32 * k + 32 + arena ≤ 2 ^ 24) (hk' : k < 2 ^ 12) (htree : tree < 2 ^ 32)
    (hdis : NODE + 64 ≤ arena + 32 * k ∨ arena + 32 * k + 32 ≤ NODE)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 (nodeLo lay tree)) :
    ∃ t, Steps image s (26 + revX tag) (26 + revX tag) t ∧ t.pc = pcOf (b + 146) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (arena + 32 * k)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = ClaudeWCT.WCT9.lowerNodeWord (lay - 1) tree k ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 24)) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
        X = NODE + 56) := by
  obtain ⟨t1, st1, t1pc, t1x7, t1x30, m0, m8, m16, m48, m56, t1r, t1f⟩ :=
    sub120_spec h s hpc arena k tree (nodeLo lay tree) ha8 hk htree hdis h2 h24 h9 h21
  have hmod := nodeLo_mod lay tree
  have mid : ∃ u, Steps image t1 (revX tag) (revX tag) u ∧ u.pc = pcOf (b + 140) ∧
      u.getReg .x7 = 0 ∧ RegsExcept t1 u [.x6, .x7, .x28] ∧
      Frame t1 u (fun _ => False) := by
    subst htag
    rw [if_neg (by omega)] at t1pc
    exact ⟨t1, (Steps.refl _).of_eq (by decide) (by decide), t1pc, t1x7, RegsExcept.refl _ _, Frame.refl _ _⟩
  obtain ⟨u, stu, upc, ux7, ur, uf⟩ := mid
  obtain ⟨t, stt, tpc, tx10, tx11, tx12, tm24, tr, tf⟩ := sub140_spec h u upc
    (by rw [ur.get (by simp)]; exact t1x30)
  have g : ∀ X, X < 2 ^ 64 → X ≠ NODE + 24 → t.getMem (BitVec.ofNat 64 X) = t1.getMem (BitVec.ofNat 64 X) :=
    fun X hX hn => (tf.get hX hn).trans (uf.get hX (fun h => h))
  refine ⟨t, (st1.trans (stu.trans stt)).of_eq (by omega) (by omega),
    tpc, tx10, tx11, tx12, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g NODE (by decide) (by decide), m0]
  · rw [g (NODE + 8) (by decide) (by decide), m8]
  · rw [g (NODE + 16) (by decide) (by decide), m16, h21]
    unfold ClaudeWCT.WCT9.lowerNodeWord ClaudeWCT.WCT9.lowerK nodeLo
    rw [if_neg (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq, Nat.add_comm k]
  · rw [tm24, ux7]
  · rw [g (NODE + 48) (by decide) (by decide), m48]
  · rw [g (NODE + 56) (by decide) (by decide), m56]
  · exact ((t1r.trans ur).trans tr).mono (by decide)
  · refine ((t1f.trans uf).trans tf).mono (fun X _ hX => ?_)
    rcases hX with (hX | hX) | hX
    · rcases hX with hX | hX | hX | hX | hX <;> simp [hX]
    · exact hX.elim
    · simp [hX]
theorem fetch_sub146 {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 146)) : fetch image s = some (.base .ECALL) :=
  ((SeedIndependent.codeAt_sub_146 h).fetch s hpc).trans rfl
theorem ntr_x29 (s : MachineState) (k : Nat) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    (SeedIndependent.blkS_ntr.res.toState s).getReg .x29 = BitVec.ofNat 64 (NOUT + hiO k) := by
  show BinOp.eval .add (BinOp.eval .sll (BinOp.eval .xor (BinOp.eval .and (s.getReg .x24) 1#64) 1#64) 4#64)
    131648#64 = _
  rw [h24, halfSel_eval]
  show BitVec.ofNat 64 (hiO k) + BitVec.ofNat 64 131648 = _
  rw [ofNat_add_ofNat, Nat.add_comm]
/-- C2: the node value copy. `t3 = sp + 16 * s8`, then the trampoline at 1653 selects the HIGH half (`NOUT + 16`)
for an even heap, and 1164..1169 copy it to the heap slot, `s8 += 1`, back to `b + 118`. -/
theorem sub147_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 147)) (arena k : Nat) (ha8 : arena % 8 = 0) (hk : arena + 16 * k + 16 ≤ 2 ^ 24)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 16 16 t ∧ t.pc = pcOf (b + 118) ∧ t.getReg .x24 = BitVec.ofNat 64 (k + 1) ∧
      t.getMem (BitVec.ofNat 64 (arena + 16 * k)) = s.getMem (BitVec.ofNat 64 (NOUT + hiO k)) ∧
      t.getMem (BitVec.ofNat 64 (arena + 16 * k + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + hiO k + 8)) ∧
      RegsExcept s t [.x6, .x7, .x24, .x28, .x29] ∧
      Frame s t (fun X => X = arena + 16 * k ∨ X = arena + 16 * k + 8) := by
  obtain rfl := SeedIndependent.b_eq h
  have hh2 : hiO k = 0 ∨ hiO k = 16 := by unfold hiO; split_ifs <;> simp
  -- 1160..1162: t3 = sp + 16 * s8, jal 1653
  obtain ⟨t0, s0, p0, x28, r0, f0⟩ : ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 1653 ∧
      t.getReg .x28 = BitVec.ofNat 64 (arena + 16 * k) ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_147 (SeedIndependent.codeAt_sub147S h) s hpc
      (by simp [SeedIndependent.blkS_147.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_147.res, E.eval]
    · simp only [Result.toState_getReg, SeedIndependent.blkS_147.res]
      t3n [h2, h24]
      congr 1; omega
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_147.res, rv_simp] <;> rfl
    · intro A hA hn; rfl
  -- 1653..1659: t4 = NOUT + hiO k
  obtain ⟨t1, s1, p1, x29, r1, f1⟩ : ∃ t, Steps image t0 7 7 t ∧ t.pc = pcOf (1013 + 151) ∧
      t.getReg .x29 = BitVec.ofNat 64 (NOUT + hiO k) ∧ RegsExcept t0 t [.x6, .x29] ∧
      Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_ntr (SeedIndependent.codeAt_nodeTrampS h) t0 p0
      (by simp [SeedIndependent.blkS_ntr.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_ntr.res, E.eval]
    · exact ntr_x29 t0 k (by rw [r0.get (by simp)]; exact h24)
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_ntr.res, rv_simp] <;> rfl
    · intro A hA hn; rfl
  have g1 : ∀ r, r ∉ [Reg.x28, .x6, .x29] → t1.getReg r = s.getReg r := fun r hr =>
    (r0.trans r1).get (by simpa using hr)
  have x28' : t1.getReg .x28 = BitVec.ofNat 64 (arena + 16 * k) := by rw [r1.get (by simp)]; exact x28
  have hm : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA => by
    rw [f1.get hA (fun h => h), f0.get hA (fun h => h)]
  -- 1164..1169: copy, s8 += 1, back to b + 118
  have hobl : Oblig.all t1 SeedIndependent.blkS_151.res.st.obl := by
    simp only [SeedIndependent.blkS_151.res]
    t3n [x29, x28']
    simp only [NOUT]
    omega
  refine ⟨_, ((s0.trans s1).trans (symRun_sound SeedIndependent.blkS_151 (SeedIndependent.codeAt_sub151S h) t1 p1
    hobl)).of_eq (by simp [SeedIndependent.blkS_151.res]) (by simp [SeedIndependent.blkS_151.res]), ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [SeedIndependent.blkS_151.res, E.eval]
  · simp only [Result.toState_getReg, SeedIndependent.blkS_151.res]
    t3n [g1 .x24 (by simp), h24]
  · simp only [Result.toState_getMem, SeedIndependent.blkS_151.res]
    t3n [x29, x28']
    rw [if_neg (by omega), if_pos (by omega), hm _ (by simp only [NOUT]; omega)]
  · simp only [Result.toState_getMem, SeedIndependent.blkS_151.res]
    t3n [x29, x28']
    rw [hm _ (by simp only [NOUT]; omega)]
  · have r2 : RegsExcept t1 (SeedIndependent.blkS_151.res.toState t1) [.x6, .x7, .x24] := by
      intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_151.res, rv_simp] <;> rfl
    exact ((r0.trans r1).trans r2).mono (by simp)
  · intro A hA hn
    simp only [Result.toState_getMem, SeedIndependent.blkS_151.res]
    t3n [x29, x28']
    have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
    rw [hA', if_neg (by omega), if_neg (by omega), hm A hA]
theorem sub157_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 157)) (lo : Nat) (hlo : lo < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s (if lo / 2 = 1 then 4 else 5) (if lo / 2 = 1 then 4 else 5) t ∧
      t.pc = (if lo / 2 = 1 then pcOf (b + 159) else pcOf (b + 116)) ∧
      t.getReg .x20 = BitVec.ofNat 64 (lo / 2) ∧
      RegsExcept s t [.x6, .x20] ∧ Frame s t (fun _ => False) := by
  obtain rfl := SeedIndependent.b_eq h
  obtain ⟨t1, s1, p1, x20, r1, f1⟩ : ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 1551 ∧
      t.getReg .x20 = BitVec.ofNat 64 (lo / 2) ∧ RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_157 (SeedIndependent.codeAt_sub157S h) s hpc
      (by simp [SeedIndependent.blkS_157.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_157.res, E.eval]
    · simp only [Result.toState_getReg, SeedIndependent.blkS_157.res, rv_simp, h20]
      rw [ofNat_shr _ _ hlo]; rfl
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_157.res, rv_simp] <;> rfl
    · intro A _ _; simp [SeedIndependent.blkS_157.res, rv_simp]
  obtain ⟨t2, s2, p2, r2, f2⟩ : ∃ t, Steps image t1 2 2 t ∧
      t.pc = (if lo / 2 = 1 then pcOf (1013 + 159) else pcOf 1553) ∧ RegsExcept t1 t [.x6] ∧
      Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_noroot (SeedIndependent.codeAt_norootS h) t1 p1
      (by simp [SeedIndependent.blkS_noroot.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, SeedIndependent.blkS_noroot.res, E.eval, CmpOp.eval, BinOp.eval, x20]
      by_cases h1 : lo / 2 = 1
      · simp [h1]
      · have : BitVec.ofNat 64 (lo / 2) ≠ 1#64 := fun he => h1 (by
          have := congrArg BitVec.toNat he; rwa [toNat_ofNat_lt (by omega)] at this)
        simp [h1, this]
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_noroot.res, rv_simp] <;> rfl
    · intro A _ _; simp [SeedIndependent.blkS_noroot.res, rv_simp]
  by_cases h1 : lo / 2 = 1
  · rw [if_pos h1] at p2
    refine ⟨t2, (s1.trans s2).of_eq (by simp [h1]) (by simp [h1]), by rw [if_pos h1]; exact p2, ?_,
      (r1.trans r2).mono (by decide), (f1.trans f2).mono (fun A _ h => by simp_all)⟩
    rw [r2.get (by decide), x20]
  · rw [if_neg h1] at p2
    obtain ⟨t3, s3, p3, r3, f3⟩ : ∃ t, Steps image t2 1 1 t ∧ t.pc = pcOf (1013 + 116) ∧
        RegsExcept t2 t [] ∧ Frame t2 t (fun _ => False) := by
      refine ⟨_, symRun_sound SeedIndependent.blkS_nrj (SeedIndependent.codeAt_norootJ h) t2 p2
        (by simp [SeedIndependent.blkS_nrj.res, rv_simp]), ?_, ?_, ?_⟩
      · simp [SeedIndependent.blkS_nrj.res, E.eval]
      · intro r hr; cases r <;> rfl
      · intro A hA hn; rfl
    refine ⟨t3, ((s1.trans s2).trans s3).of_eq (by simp [h1]) (by simp [h1]), by rw [if_neg h1]; exact p3, ?_,
      ((r1.trans r2).trans r3).mono (by decide), ((f1.trans f2).trans f3).mono (fun A _ h => by simp_all)⟩
    rw [r3.get (by decide), r2.get (by decide), x20]
theorem sub159_spec {image : Image} {b : Nat} (h : SeedIndependentAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 159)) (k : Nat) (h1 : s.getReg .x1 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_159 h.2.1
  refine ⟨_, symRun_sound hrun (SeedIndependent.codeAt_sub_159 h) s hpc (by simp [st_159, blk117_159.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_159, blk117_159.res, rv_simp, h1, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_159, blk117_159.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_159, blk117_159.res, rv_simp]
def levKB (B : LevArgs) : Nat :=
  3 + sumTo (fun j => 8 + (if j + 2 = B.h then 0 else 1) + (45 + revX B.tag) * 2 ^ (B.h - 1 - j)) (B.h - 1) + 1
def levCB (B : LevArgs) : Nat :=
  3 + sumTo (fun j => 8 + (if j + 2 = B.h then 0 else 1) + (52 + revX B.tag) * 2 ^ (B.h - 1 - j)) (B.h - 1) + 1
theorem merkleNodeInput_length (lay tree heap : Nat) (l r : Digest) :
    (ClaudeWCT.WCT9.merkleNodeInput lay tree heap l r).length = 64 := by
  simp [ClaudeWCT.WCT9.merkleNodeInput, bytesLE_length, zero16]
theorem wordsOf_merkleNodeInput {lay : Nat} (hl : lay ≠ 0) (tree heap : Nat) (l r : Digest) :
    wordsOf (ClaudeWCT.WCT9.merkleNodeInput lay tree heap l r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, ClaudeWCT.WCT9.lowerNodeWord (lay - 1) tree heap, 0, 0, 0,
        r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  unfold ClaudeWCT.WCT9.merkleNodeInput
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_zero16,
    wordsOf_bytesLE16, ClaudeWCT.WCT9.merkleTweak_lower hl, ClaudeWCT.WCT9.lowerTweak_low,
    ClaudeWCT.WCT9.lowerTweak_high]
  rfl
/-- C2: the levels below the root pair of a lower tree (the text of S23's `WCT9.buildLevelsBelow`). -/
def levelsBelowW (lay tree h : Nat) (leaves : List Digest) : T3.M (List (List Digest)) :=
  (List.range' 1 (h - 1)).foldlM (fun levels level => do
    let nodes ← ClaudeWCT.WCT9.lowerLevel lay tree h level (levels.getD (level - 1) [])
    pure (levels ++ [nodes])) [leaves]
/-- Stage 2: `WCT9.buildLevelsBelow` (C2, `lowerLevel`) is `levelsBelowW` by definition. -/
theorem buildLevelsBelow_eq_levelsBelowW (tag lay tree h : Nat) (leaves : List Digest) :
    ClaudeWCT.WCT9.buildLevelsBelow tag lay tree h leaves = levelsBelowW lay tree h leaves := rfl
def levNB (B : LevArgs) : Nat := sumTo (fun j => 2 ^ (B.h - 1 - j)) (B.h - 1)
section lev
variable {image : Image} {b : Nat} (hsub : SeedIndependentAt image b) (sk : BitVec 256) {s0 : MachineState}
  {B : LevArgs} {leaves : List Digest} (hpre : LevPre s0 B leaves)
include hsub hpre
theorem lev_node (hl1 : 1 ≤ B.lay) {ℓ : Nat} (hl : ℓ < B.h) {levels : List (List Digest)} {pre : List Digest}
    (hi : pre.length < 2 ^ (B.h - ℓ - 1)) {t : MachineState} (ht : NodeInv s0 B ℓ levels pre t)
    (hpc : t.pc = pcOf (b + 118)) :
    TSim image sk t (45 + revX B.tag) (52 + revX B.tag) 1 1
      (ClaudeWCT.WCT9.lowerNodeHash B.lay B.tree (2 ^ (B.h - (ℓ + 1)) + pre.length)
        ((levels.getD ℓ []).getD (2 * pre.length) 0) ((levels.getD ℓ []).getD (2 * pre.length + 1) 0))
      (fun v u => u.pc = pcOf (b + 118) ∧ NodeInv s0 B ℓ levels (pre ++ [v]) u) := by
  have hh := hpre.hh
  have ha := hpre.ha
  have has := hpre.has
  have ha8 := hpre.ha8
  set lo := 2 ^ (B.h - ℓ - 1) with hlo_def
  set i := pre.length with hi_def
  have hY : 2 ^ (B.h - ℓ) = 2 * lo := two_pow_split hl
  have hYZ : 2 ^ (B.h - ℓ) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hW : 2 ^ (B.h + 1) = 2 * 2 ^ B.h := by rw [Nat.pow_succ]; ring
  have hZ : 2 ^ B.h ≤ 4096 := by
    calc 2 ^ B.h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
      _ = 4096 := by norm_num
  have hlo1 : 1 ≤ lo := Nat.one_le_two_pow
  have hk' : 2 ^ (B.h - (ℓ + 1)) = lo := by rw [hlo_def]; congr 1
  have g : ∀ r, r ∉ levRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r2 : t.getReg .x2 = BitVec.ofNat 64 B.arena := by rw [g _ (by simp [levRegs]), hpre.x2]
  have r9 : t.getReg .x9 = BitVec.ofNat 64 B.tree := by rw [g _ (by simp [levRegs]), hpre.x9]
  have r5 : t.getReg .x5 = 0 := by rw [g _ (by simp [levRegs]), hpre.x5]
  have r21 : t.getReg .x21 = BitVec.ofNat 64 (nodeLo B.lay B.tree) := by
    rw [g _ (by simp [levRegs]), hpre.x21]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub118_spec hsub t hpc lo (lo + i) (by omega) (by omega) ht.x20 ht.x24
  rw [if_pos (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x10, t2x11, t2x12, t2n0, t2n8, t2n16, t2n24, t2n48, t2n56, t2r, t2f⟩ :=
    sub120_full hsub t1 t1pc B.tag B.lay B.arena (lo + i) B.tree hpre.tag3 hl1 hpre.hlay ha8 (by omega) (by omega)
      hpre.htree
      (by simp only [NODE, NOUT] at has ⊢; omega) (by rw [t1r.get (by simp)]; exact r2)
      (by rw [t1r.get (by simp)]; exact ht.x24) (by rw [t1r.get (by simp)]; exact r9)
      (by rw [t1r.get (by simp)]; exact r21)
  obtain ⟨hlen, hlev⟩ := ht.heap
  obtain ⟨hll, hlv⟩ := hlev ℓ le_rfl
  have hL : DigAt t (B.arena + 32 * (lo + i)) ((levels.getD ℓ []).getD (2 * i) 0) := by
    have := hlv.get (i := 2 * i) (by rw [hll, hY]; omega)
    rwa [hY, show B.arena + 16 * (2 * lo) + 16 * (2 * i) = B.arena + 32 * (lo + i) by ring] at this
  have hR : DigAt t (B.arena + 32 * (lo + i) + 16) ((levels.getD ℓ []).getD (2 * i + 1) 0) := by
    have := hlv.get (i := 2 * i + 1) (by rw [hll, hY]; omega)
    rwa [hY, show B.arena + 16 * (2 * lo) + 16 * (2 * i + 1) = B.arena + 32 * (lo + i) + 16 by ring] at this
  have hL1 := hL.frame t1f (by omega) (by simp) (by simp)
  have hR1 := hR.frame t1f (by omega) (by simp) (by simp)
  have fr : ∀ X, (X = NODE + 32 ∨ X = NODE + 40) → t2.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := by
    intro X hX
    have hX' : X < 2 ^ 64 := by rcases hX with h | h <;> (rw [h]; decide)
    rw [t2f.get hX' (by simp only [NODE] at hX ⊢; omega), t1f.get hX' (by simp),
      ht.frame.get hX' (by unfold LevW; simp only [NODE, NOUT] at hX has ⊢; omega)]
  have hq : hashInput t2 = toQ (pad64 (ClaudeWCT.WCT9.merkleNodeInput B.lay B.tree (lo + i)
      ((levels.getD ℓ []).getD (2 * i) 0) ((levels.getD ℓ []).getD (2 * i + 1) 0))) := by
    rw [pad64_of_aligned _ (by rw [merkleNodeInput_length])]
    refine hashInput_toQ t2 _ 0 NODE (merkleNodeInput_length _ _ _ _ _) t2x10 (by decide) (by decide) t2x11
      (by decide) ?_
    rw [wordsOf_merkleNodeInput (by omega), readWords_eight, t2n0, t2n8, t2n16, t2n24, fr (NODE + 32) (by simp),
      fr (NODE + 40) (by simp), t2n48, t2n56, hpre.z32, hpre.z40, hL1.1, hL1.2, hR1.1, hR1.2]
  have hv : hashArgumentsValid t2 = true :=
    hashArgs_const t2 NODE 64 NOUT t2x10 t2x11 t2x12 (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have h5 : t2.getReg .x5 = 0 := by rw [t2r.get (by simp), t1r.get (by simp), r5]
  have hblk : (toQ (pad64 (ClaudeWCT.WCT9.merkleNodeInput B.lay B.tree (lo + i)
      ((levels.getD ℓ []).getD (2 * i) 0) ((levels.getD ℓ []).getD (2 * i + 1) 0)))).blocks = 1 := by
    rw [pad64_of_aligned _ (by rw [merkleNodeInput_length]),
      blocks_toQ ⟨by rw [merkleNodeInput_length]; omega, by rw [merkleNodeInput_length]⟩, merkleNodeInput_length]
  unfold ClaudeWCT.WCT9.lowerNodeHash
  rw [hk', ClaudeWCT.WCT9.lowerHash_eq]
  refine (TSim.steps (st1.trans st2)
    (TSim.publicHash_bind (k := 16) (c := 16) (n := 0) (b := 0)
      (fetch_sub146 hsub t2 t2pc) h5 hv hq (fun a => ?_))).of_eq rfl ?_ ?_ ?_ ?_
  · have hwf := Frame.writeHash t2 a NOUT t2x12 (by decide)
    obtain ⟨u, st3, upc, ux24, um0, um8, ur, uf⟩ := sub147_spec hsub (writeHash t2 a)
      (by rw [pc_writeHash, t2pc, pcOf_add4]) B.arena (lo + i) ha8 (by omega)
      (by rw [getReg_writeHash, t2r.get (by simp), t1r.get (by simp)]; exact r2)
      (by rw [getReg_writeHash, t2r.get (by simp), t1r.get (by simp)]; exact ht.x24)
    have hlo := DigAt.writeHash_lowerHalf t2 a NOUT B.lay (lo + i) t2x12 (by decide) ⟨hl1, hpre.hlay⟩
    have hnew : DigAt u (B.arena + 16 * (lo + i)) (ClaudeWCT.WCT9.lowerHalf B.lay (lo + i) a) :=
      ⟨um0.trans hlo.1, by rw [um8]; exact hlo.2⟩
    have fall : Frame t u (fun X => (X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨
        X = NODE + 48 ∨ X = NODE + 56) ∨ (NOUT ≤ X ∧ X < NOUT + 32) ∨
        (X = B.arena + 16 * (lo + i) ∨ X = B.arena + 16 * (lo + i) + 8)) :=
      ((t1f.trans t2f).trans (hwf.trans uf)).mono (fun X _ h => by
        rcases h with (h | h) | (h | h)
        · exact h.elim
        · left; exact h
        · right; left; exact h
        · right; right; exact h)
    refine TSim.pure_steps st3 ⟨upc, ⟨?_, ?_, ?_, ?_, ⟨hlen, fun l hl' => ?_⟩, ?_⟩⟩
    · rw [ur.get (by simp), getReg_writeHash, t2r.get (by simp), t1r.get (by simp)]; exact ht.x20
    · rw [ux24, List.length_append, List.length_singleton]; congr 1
    · have hw0 : RegsExcept t2 (writeHash t2 a) [] := fun r _ => getReg_writeHash t2 a r
      exact (ht.regs.trans (((t1r.trans t2r).trans hw0).trans ur)).mono (by decide)
    · refine (ht.frame.trans fall).mono (fun X _ h => ?_)
      unfold LevW at *
      rcases h with h | (h | h | h)
      · exact h
      · rcases h with h | h | h | h | h | h <;> simp_all
      · right; right; right; right; right; right; left; exact h
      · right; right; right; right; right; right; right; simp only [NODE, NOUT] at has; omega
    · obtain ⟨hl1, hl2⟩ := hlev l hl'
      have hYl : 2 * lo ≤ 2 ^ (B.h - l) := by
        rw [← hY]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hYlZ : 2 ^ (B.h - l) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
      refine ⟨hl1, hl2.frame fall (by rw [hl1]; omega) (fun X h1 h2 h => ?_)⟩
      rw [hl1] at h2
      simp only [NODE, NOUT] at h has
      omega
    · refine (ht.cur.frame fall (by omega) (fun X h1 h2 h => ?_)).snoc ?_
      · simp only [NODE, NOUT] at h has
        omega
      · rw [show B.arena + 16 * lo + 16 * i = B.arena + 16 * (lo + i) by ring]; exact hnew
  all_goals (try rw [hblk])
  all_goals (first | rfl | omega)
theorem lev_level (hlay1 : 1 ≤ B.lay) {ℓ : Nat} (hl1 : ℓ + 1 < B.h) {levels : List (List Digest)} {t : MachineState}
    (ht : LevInv s0 B ℓ levels t) (hpc : t.pc = pcOf (b + 116)) :
    TSim image sk t (8 + (if ℓ + 2 = B.h then 0 else 1) + (45 + revX B.tag) * 2 ^ (B.h - 1 - ℓ))
      (8 + (if ℓ + 2 = B.h then 0 else 1) + (52 + revX B.tag) * 2 ^ (B.h - 1 - ℓ))
      (2 ^ (B.h - 1 - ℓ))
      (2 ^ (B.h - 1 - ℓ))
      (do let nodes ← ClaudeWCT.WCT9.lowerLevel B.lay B.tree B.h (1 + ℓ) (levels.getD (1 + ℓ - 1) [])
          pure (levels ++ [nodes]))
      (fun levels' u => u.pc = (if ℓ + 2 = B.h then pcOf (b + 159) else pcOf (b + 116)) ∧
        LevInv s0 B (ℓ + 1) levels' u) := by
  have hl : ℓ < B.h := by omega
  have hh := hpre.hh
  set lo := 2 ^ (B.h - ℓ - 1) with hlo_def
  have hY : 2 ^ (B.h - ℓ) = 2 * lo := two_pow_split hl
  have hlo1 : 1 ≤ lo := Nat.one_le_two_pow
  have hloZ : lo ≤ 2048 := by
    calc lo ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2048 := by norm_num
  have hx20 : 2 ^ B.h / 2 ^ (ℓ + 1) = lo := by
    rw [hlo_def, show B.h = (ℓ + 1) + (B.h - ℓ - 1) by omega, Nat.pow_add, Nat.mul_div_cancel_left _
      (by positivity)]
    congr 1; omega
  have hx20' : 2 ^ B.h / 2 ^ (ℓ + 1 + 1) = lo / 2 := by
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hx20]
  have hl1 : 2 ^ (B.h - 1 - ℓ) = lo := by rw [hlo_def]; congr 1; omega
  have r20 : t.getReg .x20 = BitVec.ofNat 64 lo := by rw [ht.x20, hx20]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub116_spec hsub t hpc lo (by omega) r20
  rw [if_neg (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x24, t2r, t2f⟩ := sub117_spec hsub t1 t1pc
  have f02 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp_all)
  have h0 : NodeInv s0 B ℓ levels [] t2 := by
    refine ⟨?_, ?_, ?_, (ht.frame.trans f02).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim),
      ⟨ht.heap.1, fun l hl' => ⟨(ht.heap.2 l hl').1, (ht.heap.2 l hl').2.frame f02 (by
        rw [(ht.heap.2 l hl').1]
        have := hpre.ha
        have : 2 ^ (B.h - l) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 2 ^ (B.h + 1) = 2 * 2 ^ B.h := by rw [Nat.pow_succ]; ring
        omega) (fun X _ _ h => h.elim)⟩⟩, DigsAt.nil _ _⟩
    · rw [t2r.get (by simp), t1r.get (by simp), r20]
    · rw [t2x24, t1r.get (by simp), r20, List.length_nil, Nat.add_zero]
    · exact (ht.regs.trans (t1r.trans t2r)).mono (by decide)
  have hnodes : (levels.getD (1 + ℓ - 1) []).length / 2 = lo := by
    rw [show 1 + ℓ - 1 = ℓ by omega, (ht.heap.2 ℓ le_rfl).1, hY]; omega
  unfold ClaudeWCT.WCT9.lowerLevel
  rw [hnodes]
  refine (TSim.steps (st1.trans st2) (TSim.bind (k₂ := 6 + (if ℓ + 2 = B.h then 0 else 1))
    (c₂ := 6 + (if ℓ + 2 = B.h then 0 else 1)) (n₂ := 0) (b₂ := 0)
    (TSim.mapM_range lo _ (fun _ => 45 + revX B.tag) (fun _ => 52 + revX B.tag) (fun _ => 1) (fun _ => 1)
      (fun pre w => w.pc = pcOf (b + 118) ∧ NodeInv s0 B ℓ levels pre w)
      (fun pre w hpre' hw => ?_) ⟨t2pc, h0⟩) (fun nodes w hw => ?_))).of_eq rfl ?_ ?_ ?_ ?_
  · rw [show 1 + ℓ - 1 = ℓ by omega, show 1 + ℓ = ℓ + 1 by omega]
    exact lev_node hsub sk hpre hlay1 hl hpre' hw.2 hw.1
  · obtain ⟨hlen, wpc, hw⟩ := hw
    obtain ⟨w1, st3, w1pc, w1r, w1f⟩ := sub118_spec hsub w wpc lo (lo + nodes.length) (by omega) (by omega)
      hw.x20 (by rw [hw.x24])
    rw [if_neg (by omega)] at w1pc
    obtain ⟨w2, st4, w2pc, w2x20, w2r, w2f⟩ := sub157_spec hsub w1 w1pc lo (by omega)
      (by rw [w1r.get (by simp)]; exact hw.x20)
    have hlo2 : lo / 2 = 2 ^ (B.h - ℓ - 2) := by
      rw [hlo_def, show B.h - ℓ - 1 = (B.h - ℓ - 2) + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have hiff : lo / 2 = 1 ↔ ℓ + 2 = B.h := by
      rw [hlo2]
      constructor
      · intro he
        by_contra hne
        have : 2 ≤ 2 ^ (B.h - ℓ - 2) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (B.h - ℓ - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · intro he; rw [show B.h - ℓ - 2 = 0 by omega]; rfl
    have st34 : Steps image w (6 + (if ℓ + 2 = B.h then 0 else 1)) (6 + (if ℓ + 2 = B.h then 0 else 1)) w2 :=
      (st3.trans st4).of_eq (by by_cases hE : ℓ + 2 = B.h <;> simp [hE, hiff]) (by by_cases hE : ℓ + 2 = B.h <;> simp [hE, hiff])
    have p2 : w2.pc = if ℓ + 2 = B.h then pcOf (b + 159) else pcOf (b + 116) := by
      rw [w2pc]; by_cases hE : ℓ + 2 = B.h <;> simp [hE, hiff]
    have f12 : Frame w w2 (fun _ => False) := (w1f.trans w2f).mono (fun X _ h => by simp_all)
    refine TSim.pure_steps st34 ⟨p2, ?_, ?_, ?_, ?_⟩
    · rw [w2x20, hx20']
    · exact (hw.regs.trans (w1r.trans w2r)).mono (by decide)
    · exact (hw.frame.trans f12).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
    · obtain ⟨hlen0, hlev⟩ := hw.heap
      refine ⟨by simp [hlen0], fun l hl' => ?_⟩
      have hZ : 2 ^ (B.h + 1) = 2 * 2 ^ B.h := by rw [Nat.pow_succ]; ring
      have := hpre.ha
      by_cases hle : l ≤ ℓ
      · have hg : (levels ++ [nodes]).getD l [] = levels.getD l [] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show l < levels.length by omega)]
        rw [hg]
        obtain ⟨h1, h2⟩ := hlev l hle
        have : 2 ^ (B.h - l) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact ⟨h1, h2.frame f12 (by rw [h1]; omega) (fun X _ _ h => h.elim)⟩
      · have hl2 : l = ℓ + 1 := by omega
        subst hl2
        have hg : (levels ++ [nodes]).getD (ℓ + 1) [] = nodes := by
          simp [List.getD_eq_getElem?_getD, hlen0]
        rw [hg, show B.h - (ℓ + 1) = B.h - ℓ - 1 by omega]
        have : lo ≤ 2 ^ B.h := by
          have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show B.h - ℓ - 1 ≤ B.h by omega)
          omega
        exact ⟨hlen, hw.cur.frame f12 (by rw [hlen]; omega) (fun X _ _ h => h.elim)⟩
  all_goals simp only [sumTo_const, hl1]
  all_goals (first | omega | ring)
theorem buildLevelsBelow_tsim (hlay1 : 1 ≤ B.lay) (hh2 : 2 ≤ B.h) (hpc : s0.pc = pcOf (b + 113)) :
    TSim image sk s0 (levKB B) (levCB B) (levNB B) (levNB B)
      (levelsBelowW B.lay B.tree B.h leaves)
      (fun levels t => t.pc = pcOf B.ret ∧ HeapAt t B (B.h - 1) levels ∧ RegsExcept s0 t levRegs ∧
        Frame s0 t (LevW B)) := by
  have hh := hpre.hh
  have hh1 := hpre.hh1
  have ha := hpre.ha
  have hZ : 2 ^ (B.h + 1) = 2 * 2 ^ B.h := by rw [Nat.pow_succ]; ring
  obtain ⟨t1, st1, t1pc, t1x20, t1r, t1f⟩ := sub113_spec hsub s0 hpc B.h hh1 (by omega) hpre.x15
  have h0 : LevInv s0 B 0 [leaves] t1 := by
    refine ⟨?_, t1r.mono (by decide), t1f.mono (fun X _ h => h.elim), ⟨rfl, fun l hl => ?_⟩⟩
    · rw [t1x20]; congr 1
      rw [show B.h = 1 + (B.h - 1) by omega, Nat.pow_add, Nat.mul_div_cancel_left _ (by norm_num)]
      congr 1; omega
    · have hl0 : l = 0 := by omega
      subst hl0
      simp only [List.getD_cons_zero, Nat.sub_zero]
      exact ⟨hpre.hlen, hpre.hleaves.frame t1f (by rw [hpre.hlen]; omega) (fun X _ _ h => h.elim)⟩
  unfold levelsBelowW
  refine (TSim.steps st1 (TSim.bind (k₂ := 1) (c₂ := 1) (n₂ := 0) (b₂ := 0) (f := Pure.pure)
    (TSim.foldlM_range' 1 (B.h - 1) _ [leaves]
      (fun j levels t => t.pc = (if j + 1 = B.h then pcOf (b + 159) else pcOf (b + 116)) ∧ LevInv s0 B j levels t)
      (fun j => 8 + (if j + 2 = B.h then 0 else 1) + (45 + revX B.tag) * 2 ^ (B.h - 1 - j))
      (fun j => 8 + (if j + 2 = B.h then 0 else 1) + (52 + revX B.tag) * 2 ^ (B.h - 1 - j))
      (fun j => 2 ^ (B.h - 1 - j)) (fun j => 2 ^ (B.h - 1 - j))
      (fun j hj levels t ht => (lev_level hsub sk hpre hlay1 (by omega) ht.2
        (by rw [ht.1, if_neg (by omega)])).mono (fun _ _ h => h))
      ⟨by rw [if_neg (by omega)]; exact t1pc, h0⟩)
    (fun levels t ht => ?_))).of_eq (bind_pure _) ?_ ?_ ?_ ?_
  · obtain ⟨tpc, hinv⟩ := ht
    rw [if_pos (by omega)] at tpc
    obtain ⟨u2, st3, u2pc, u2r, u2f⟩ := sub159_spec hsub t tpc B.ret
      (by rw [hinv.regs.get (by simp [levRegs]), hpre.x1])
    refine TSim.pure_steps st3 ⟨u2pc, ⟨hinv.heap.1, fun l hl => ?_⟩,
      (hinv.regs.trans u2r).mono (by decide),
      (hinv.frame.trans u2f).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)⟩
    obtain ⟨h1, h2⟩ := hinv.heap.2 l hl
    have : 2 ^ (B.h - l) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact ⟨h1, h2.frame u2f (by rw [h1]; omega) (fun X _ _ h => h.elim)⟩
  all_goals simp only [levKB, levCB, levNB]
  all_goals omega
end lev
end SigGolfCandidate.T3M.Sign.Seed

namespace SigGolfCandidate.T3M.Sign.SharedTree
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open Keygen
open SeedIndependent
open Seed
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open SigGolfCandidate.T3 (Digest buildLevels buildLevel nodeHash shortHash header pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
theorem sub113_spec {image : Image} {b : Nat} (h : SharedTreeCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 113)) (hh : Nat) (h1 : 1 ≤ hh) (h2 : hh ≤ 32)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 116) ∧ t.getReg .x20 = BitVec.ofNat 64 (2 ^ (hh - 1)) ∧
      RegsExcept s t [.x6, .x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_113 (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (h.codeAt_sub_113) s hpc (by simp [st_113, blk117_113.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_113, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, st_113, blk117_113.res, rv_simp, h15]
    apply BitVec.eq_of_toNat_eq
    have e : (BitVec.ofNat 64 hh - 1#64).toNat = hh - 1 := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    rw [BitVec.toNat_shiftLeft, e, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show hh - 1 < 64 by omega)]
    have : 2 ^ (hh - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    simp only [Nat.one_mod, Nat.one_mul, Nat.mod_eq_of_lt this]
  · intro r hr; simp at hr; cases r <;> simp_all [st_113, blk117_113.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_113, blk117_113.res, rv_simp]
theorem sub116_spec {image : Image} {b : Nat} (h : SharedTreeCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 116)) (lo : Nat) (hlo : lo < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if lo = 0 then pcOf (b + 159) else pcOf (b + 117)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_116 (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (h.codeAt_sub_116) s hpc (by simp [st_116, blk117_116.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_116, rebase, blk117_116.res, E.eval, CmpOp.eval, h20]
    by_cases h0 : lo = 0
    · subst h0; simp
    · have : BitVec.ofNat 64 lo ≠ 0#64 := fun he => h0 (by
        have := congrArg BitVec.toNat he; rwa [toNat_ofNat_lt hlo] at this)
      simp [h0, this]
  · intro r hr; cases r <;> simp_all [st_116, blk117_116.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_116, blk117_116.res, rv_simp]
theorem sub117_spec {image : Image} {b : Nat} (h : SharedTreeCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 117)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 118) ∧ t.getReg .x24 = s.getReg .x20 ∧
      RegsExcept s t [.x24] ∧ Frame s t (fun _ => False) := by
  have hrun := run_117 (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (h.codeAt_sub_117) s hpc (by simp [st_117, blk117_117.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_117, Result.toState_pc, E.eval]
  · simp [st_117, blk117_117.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_117, blk117_117.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_117, blk117_117.res, rv_simp]
theorem sub118_spec {image : Image} {b : Nat} (h : SharedTreeCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 118)) (lo k : Nat) (hlo : lo < 2 ^ 40) (hk : k < 2 ^ 40)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if k < 2 * lo then pcOf (b + 120) else pcOf (b + 157)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hrun := run_118 (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (h.codeAt_sub_118) s hpc (by simp [st_118, blk117_118.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_118, rebase, blk117_118.res, rv_simp, h20, h24]
    rw [ofNat_shl, show (1#64 : Word).toNat % 64 = 1 from rfl, ofNat_slt k (lo * 2 ^ 1) (by omega) (by omega)]
    by_cases hkl : k < 2 * lo
    · simp [hkl, show k < lo * 2 by omega]
    · simp [hkl, show ¬ k < lo * 2 by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_118, blk117_118.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_118, blk117_118.res, rv_simp]
theorem sub120_spec {image : Image} {b : Nat} (h : SharedTreeCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 120)) (arena k tree h0 : Nat) (ha8 : arena % 8 = 0)
    (hk : 32 * k + 32 + arena ≤ 2 ^ 24) (htree : tree < 2 ^ 32)
    (hdis : NODE + 64 ≤ arena + 32 * k ∨ arena + 32 * k + 32 ≤ NODE)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) (h21 : s.getReg .x21 = BitVec.ofNat 64 h0) :
    ∃ t, Steps image s 20 20 t ∧
      t.pc = (if 2048 ≤ h0 % 4096 then pcOf (b + 1004) else pcOf (b + 140)) ∧
      t.getReg .x7 = 0 ∧ t.getReg .x30 = BitVec.ofNat 64 (NODE + 48) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (arena + 32 * k)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = s.getReg .x21 + BitVec.ofNat 64 (k + 1407) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 24)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x30] ∧
      Frame s t (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 48 ∨ X = NODE + 56) := by
  obtain rfl := h.base
  have hobl : Oblig.all s SeedIndependent.blkS_120.res.st.obl := by
    simp only [SeedIndependent.blkS_120.res]
    t3n [h2, h24]
    simp only [NODE] at hdis
    omega
  refine ⟨_, symRun_sound SeedIndependent.blkS_120 (h.codeAt_sub120S) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, SeedIndependent.blkS_120.res, E.eval, CmpOp.eval, BinOp.eval, h21]
    simp only [slt_shl52, slt_shl52', slt_shl52n, slt_shl52n']
    by_cases hc : 2048 ≤ h0 % 4096 <;> simp [hc]
  · simp [SeedIndependent.blkS_120.res, rv_simp]
  · simp [SeedIndependent.blkS_120.res, rv_simp]
  · simp only [Result.toState_getMem, SeedIndependent.blkS_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, SeedIndependent.blkS_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, SeedIndependent.blkS_120.res, NODE]
    t3n [h24]
    rw [BitVec.add_assoc, ofNat_add_ofNat]
  · simp only [Result.toState_getMem, SeedIndependent.blkS_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, SeedIndependent.blkS_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_120.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, SeedIndependent.blkS_120.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem sub214_spec {image : Image} {b : Nat} (h : SharedTreeCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1004)) (k : Nat) (hk : k < 2 ^ 12) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 28 28 t ∧ t.pc = pcOf (b + 140) ∧
      t.getReg .x7 = BitVec.ofNat 64 (T3.Rev.revBits 64 k) ∧
      RegsExcept s t [.x6, .x7, .x28] ∧ Frame s t (fun _ => False) := by
  have hrun := run_rev (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (h.codeAt_rev) s hpc (by simp [st_rev, blk117_rev.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_rev, Result.toState_pc, E.eval]
  · rw [Result.toState_getReg, ← RevNet.revNetBV_eq k hk, ← h24]
    rfl
  · intro r hr; simp at hr; cases r <;> simp_all [st_rev, blk117_rev.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_rev, blk117_rev.res, rv_simp]
theorem sub140_spec {image : Image} {b : Nat} (h : SharedTreeCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 140)) (h30 : s.getReg .x30 = BitVec.ofNat 64 (NODE + 48)) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (b + 146) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = s.getReg .x7 ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun X => X = NODE + 24) := by
  have hrun := run_140 (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (h.codeAt_sub_140) s hpc (sub140_obl s h30), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_140, Result.toState_pc, E.eval]
  · simp [st_140, blk117_140.res, rv_simp]
  · simp [st_140, blk117_140.res, rv_simp]
  · simp [st_140, blk117_140.res, rv_simp]
  · rw [Result.toState_getMem]; exact sub140_m24 s h30
  · intro r hr; simp at hr; cases r <;> simp_all [st_140, blk117_140.res, rv_simp] <;> rfl
  · intro X hX hn
    rw [Result.toState_getMem]
    exact sub140_frame s h30 X hX (by simp only [NODE] at hn; omega)
theorem sub120_full {image : Image} {b : Nat} (h : SharedTreeCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 120)) (tag lay arena k tree : Nat) (htag : tag = 3) (hl1 : 1 ≤ lay) (hl4 : lay < 4)
    (ha8 : arena % 8 = 0) (hk : 32 * k + 32 + arena ≤ 2 ^ 24) (hk' : k < 2 ^ 12) (htree : tree < 2 ^ 32)
    (hdis : NODE + 64 ≤ arena + 32 * k ∨ arena + 32 * k + 32 ≤ NODE)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 (nodeLo lay tree)) :
    ∃ t, Steps image s (26 + revX tag) (26 + revX tag) t ∧ t.pc = pcOf (b + 146) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (arena + 32 * k)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = ClaudeWCT.WCT9.lowerNodeWord (lay - 1) tree k ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 24)) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
        X = NODE + 56) := by
  obtain ⟨t1, st1, t1pc, t1x7, t1x30, m0, m8, m16, m48, m56, t1r, t1f⟩ :=
    sub120_spec h s hpc arena k tree (nodeLo lay tree) ha8 hk htree hdis h2 h24 h9 h21
  have hmod := nodeLo_mod lay tree
  have mid : ∃ u, Steps image t1 (revX tag) (revX tag) u ∧ u.pc = pcOf (b + 140) ∧
      u.getReg .x7 = 0 ∧ RegsExcept t1 u [.x6, .x7, .x28] ∧
      Frame t1 u (fun _ => False) := by
    subst htag
    rw [if_neg (by omega)] at t1pc
    exact ⟨t1, (Steps.refl _).of_eq (by decide) (by decide), t1pc, t1x7, RegsExcept.refl _ _, Frame.refl _ _⟩
  obtain ⟨u, stu, upc, ux7, ur, uf⟩ := mid
  obtain ⟨t, stt, tpc, tx10, tx11, tx12, tm24, tr, tf⟩ := sub140_spec h u upc
    (by rw [ur.get (by simp)]; exact t1x30)
  have g : ∀ X, X < 2 ^ 64 → X ≠ NODE + 24 → t.getMem (BitVec.ofNat 64 X) = t1.getMem (BitVec.ofNat 64 X) :=
    fun X hX hn => (tf.get hX hn).trans (uf.get hX (fun h => h))
  refine ⟨t, (st1.trans (stu.trans stt)).of_eq (by omega) (by omega),
    tpc, tx10, tx11, tx12, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g NODE (by decide) (by decide), m0]
  · rw [g (NODE + 8) (by decide) (by decide), m8]
  · rw [g (NODE + 16) (by decide) (by decide), m16, h21]
    unfold ClaudeWCT.WCT9.lowerNodeWord ClaudeWCT.WCT9.lowerK nodeLo
    rw [if_neg (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq, Nat.add_comm k]
  · rw [tm24, ux7]
  · rw [g (NODE + 48) (by decide) (by decide), m48]
  · rw [g (NODE + 56) (by decide) (by decide), m56]
  · exact ((t1r.trans ur).trans tr).mono (by decide)
  · refine ((t1f.trans uf).trans tf).mono (fun X _ hX => ?_)
    rcases hX with (hX | hX) | hX
    · rcases hX with hX | hX | hX | hX | hX <;> simp [hX]
    · exact hX.elim
    · simp [hX]
theorem fetch_sub146 {image : Image} {b : Nat} (h : SharedTreeCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 146)) : fetch image s = some (.base .ECALL) :=
  ((h.codeAt_sub_146).fetch s hpc).trans rfl
theorem ntr_x29 (s : MachineState) (k : Nat) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    (SeedIndependent.blkS_ntr.res.toState s).getReg .x29 = BitVec.ofNat 64 (NOUT + hiO k) := by
  show BinOp.eval .add (BinOp.eval .sll (BinOp.eval .xor (BinOp.eval .and (s.getReg .x24) 1#64) 1#64) 4#64)
    131648#64 = _
  rw [h24, halfSel_eval]
  show BitVec.ofNat 64 (hiO k) + BitVec.ofNat 64 131648 = _
  rw [ofNat_add_ofNat, Nat.add_comm]
/-- C2: the node value copy. `t3 = sp + 16 * s8`, then the trampoline at 1653 selects the HIGH half (`NOUT + 16`)
for an even heap, and 1164..1169 copy it to the heap slot, `s8 += 1`, back to `b + 118`. -/
theorem sub147_spec {image : Image} {b : Nat} (h : SharedTreeCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 147)) (arena k : Nat) (ha8 : arena % 8 = 0) (hk : arena + 16 * k + 16 ≤ 2 ^ 24)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 16 16 t ∧ t.pc = pcOf (b + 118) ∧ t.getReg .x24 = BitVec.ofNat 64 (k + 1) ∧
      t.getMem (BitVec.ofNat 64 (arena + 16 * k)) = s.getMem (BitVec.ofNat 64 (NOUT + hiO k)) ∧
      t.getMem (BitVec.ofNat 64 (arena + 16 * k + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + hiO k + 8)) ∧
      RegsExcept s t [.x6, .x7, .x24, .x28, .x29] ∧
      Frame s t (fun X => X = arena + 16 * k ∨ X = arena + 16 * k + 8) := by
  obtain rfl := h.base
  have hh2 : hiO k = 0 ∨ hiO k = 16 := by unfold hiO; split_ifs <;> simp
  -- 1160..1162: t3 = sp + 16 * s8, jal 1653
  obtain ⟨t0, s0, p0, x28, r0, f0⟩ : ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 1653 ∧
      t.getReg .x28 = BitVec.ofNat 64 (arena + 16 * k) ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_147 (h.codeAt_sub147S) s hpc
      (by simp [SeedIndependent.blkS_147.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_147.res, E.eval]
    · simp only [Result.toState_getReg, SeedIndependent.blkS_147.res]
      t3n [h2, h24]
      congr 1; omega
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_147.res, rv_simp] <;> rfl
    · intro A hA hn; rfl
  -- 1653..1659: t4 = NOUT + hiO k
  obtain ⟨t1, s1, p1, x29, r1, f1⟩ : ∃ t, Steps image t0 7 7 t ∧ t.pc = pcOf (1013 + 151) ∧
      t.getReg .x29 = BitVec.ofNat 64 (NOUT + hiO k) ∧ RegsExcept t0 t [.x6, .x29] ∧
      Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_ntr (h.codeAt_nodeTrampS) t0 p0
      (by simp [SeedIndependent.blkS_ntr.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_ntr.res, E.eval]
    · exact ntr_x29 t0 k (by rw [r0.get (by simp)]; exact h24)
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_ntr.res, rv_simp] <;> rfl
    · intro A hA hn; rfl
  have g1 : ∀ r, r ∉ [Reg.x28, .x6, .x29] → t1.getReg r = s.getReg r := fun r hr =>
    (r0.trans r1).get (by simpa using hr)
  have x28' : t1.getReg .x28 = BitVec.ofNat 64 (arena + 16 * k) := by rw [r1.get (by simp)]; exact x28
  have hm : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA => by
    rw [f1.get hA (fun h => h), f0.get hA (fun h => h)]
  -- 1164..1169: copy, s8 += 1, back to b + 118
  have hobl : Oblig.all t1 SeedIndependent.blkS_151.res.st.obl := by
    simp only [SeedIndependent.blkS_151.res]
    t3n [x29, x28']
    simp only [NOUT]
    omega
  refine ⟨_, ((s0.trans s1).trans (symRun_sound SeedIndependent.blkS_151 (h.codeAt_sub151S) t1 p1
    hobl)).of_eq (by simp [SeedIndependent.blkS_151.res]) (by simp [SeedIndependent.blkS_151.res]), ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [SeedIndependent.blkS_151.res, E.eval]
  · simp only [Result.toState_getReg, SeedIndependent.blkS_151.res]
    t3n [g1 .x24 (by simp), h24]
  · simp only [Result.toState_getMem, SeedIndependent.blkS_151.res]
    t3n [x29, x28']
    rw [if_neg (by omega), if_pos (by omega), hm _ (by simp only [NOUT]; omega)]
  · simp only [Result.toState_getMem, SeedIndependent.blkS_151.res]
    t3n [x29, x28']
    rw [hm _ (by simp only [NOUT]; omega)]
  · have r2 : RegsExcept t1 (SeedIndependent.blkS_151.res.toState t1) [.x6, .x7, .x24] := by
      intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_151.res, rv_simp] <;> rfl
    exact ((r0.trans r1).trans r2).mono (by simp)
  · intro A hA hn
    simp only [Result.toState_getMem, SeedIndependent.blkS_151.res]
    t3n [x29, x28']
    have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
    rw [hA', if_neg (by omega), if_neg (by omega), hm A hA]
theorem sub157_spec {image : Image} {b : Nat} (h : SharedTreeCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 157)) (lo : Nat) (hlo : lo < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s (if lo / 2 = 1 then 4 else 5) (if lo / 2 = 1 then 4 else 5) t ∧
      t.pc = (if lo / 2 = 1 then pcOf (b + 159) else pcOf (b + 116)) ∧
      t.getReg .x20 = BitVec.ofNat 64 (lo / 2) ∧
      RegsExcept s t [.x6, .x20] ∧ Frame s t (fun _ => False) := by
  obtain rfl := h.base
  obtain ⟨t1, s1, p1, x20, r1, f1⟩ : ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 1551 ∧
      t.getReg .x20 = BitVec.ofNat 64 (lo / 2) ∧ RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_157 (h.codeAt_sub157S) s hpc
      (by simp [SeedIndependent.blkS_157.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [SeedIndependent.blkS_157.res, E.eval]
    · simp only [Result.toState_getReg, SeedIndependent.blkS_157.res, rv_simp, h20]
      rw [ofNat_shr _ _ hlo]; rfl
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_157.res, rv_simp] <;> rfl
    · intro A _ _; simp [SeedIndependent.blkS_157.res, rv_simp]
  obtain ⟨t2, s2, p2, r2, f2⟩ : ∃ t, Steps image t1 2 2 t ∧
      t.pc = (if lo / 2 = 1 then pcOf (1013 + 159) else pcOf 1553) ∧ RegsExcept t1 t [.x6] ∧
      Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound SeedIndependent.blkS_noroot (h.codeAt_norootS) t1 p1
      (by simp [SeedIndependent.blkS_noroot.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, SeedIndependent.blkS_noroot.res, E.eval, CmpOp.eval, BinOp.eval, x20]
      by_cases h1 : lo / 2 = 1
      · simp [h1]
      · have : BitVec.ofNat 64 (lo / 2) ≠ 1#64 := fun he => h1 (by
          have := congrArg BitVec.toNat he; rwa [toNat_ofNat_lt (by omega)] at this)
        simp [h1, this]
    · intro r hr; simp at hr; cases r <;> simp_all [SeedIndependent.blkS_noroot.res, rv_simp] <;> rfl
    · intro A _ _; simp [SeedIndependent.blkS_noroot.res, rv_simp]
  by_cases h1 : lo / 2 = 1
  · rw [if_pos h1] at p2
    refine ⟨t2, (s1.trans s2).of_eq (by simp [h1]) (by simp [h1]), by rw [if_pos h1]; exact p2, ?_,
      (r1.trans r2).mono (by decide), (f1.trans f2).mono (fun A _ h => by simp_all)⟩
    rw [r2.get (by decide), x20]
  · rw [if_neg h1] at p2
    obtain ⟨t3, s3, p3, r3, f3⟩ : ∃ t, Steps image t2 1 1 t ∧ t.pc = pcOf (1013 + 116) ∧
        RegsExcept t2 t [] ∧ Frame t2 t (fun _ => False) := by
      refine ⟨_, symRun_sound SeedIndependent.blkS_nrj (h.codeAt_norootJ) t2 p2
        (by simp [SeedIndependent.blkS_nrj.res, rv_simp]), ?_, ?_, ?_⟩
      · simp [SeedIndependent.blkS_nrj.res, E.eval]
      · intro r hr; cases r <;> rfl
      · intro A hA hn; rfl
    refine ⟨t3, ((s1.trans s2).trans s3).of_eq (by simp [h1]) (by simp [h1]), by rw [if_neg h1]; exact p3, ?_,
      ((r1.trans r2).trans r3).mono (by decide), ((f1.trans f2).trans f3).mono (fun A _ h => by simp_all)⟩
    rw [r3.get (by decide), r2.get (by decide), x20]
theorem sub159_spec {image : Image} {b : Nat} (h : SharedTreeCode.Code image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 159)) (k : Nat) (h1 : s.getReg .x1 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_159 (Or.inr h.base)
  refine ⟨_, symRun_sound hrun (h.codeAt_sub_159) s hpc (by simp [st_159, blk117_159.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_159, blk117_159.res, rv_simp, h1, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_159, blk117_159.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_159, blk117_159.res, rv_simp]
def levKB (B : LevArgs) : Nat :=
  3 + sumTo (fun j => 8 + (if j + 2 = B.h then 0 else 1) + (45 + revX B.tag) * 2 ^ (B.h - 1 - j)) (B.h - 1) + 1
def levCB (B : LevArgs) : Nat :=
  3 + sumTo (fun j => 8 + (if j + 2 = B.h then 0 else 1) + (52 + revX B.tag) * 2 ^ (B.h - 1 - j)) (B.h - 1) + 1
theorem merkleNodeInput_length (lay tree heap : Nat) (l r : Digest) :
    (ClaudeWCT.WCT9.merkleNodeInput lay tree heap l r).length = 64 := by
  simp [ClaudeWCT.WCT9.merkleNodeInput, bytesLE_length, zero16]
theorem wordsOf_merkleNodeInput {lay : Nat} (hl : lay ≠ 0) (tree heap : Nat) (l r : Digest) :
    wordsOf (ClaudeWCT.WCT9.merkleNodeInput lay tree heap l r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, ClaudeWCT.WCT9.lowerNodeWord (lay - 1) tree heap, 0, 0, 0,
        r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  unfold ClaudeWCT.WCT9.merkleNodeInput
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_zero16,
    wordsOf_bytesLE16, ClaudeWCT.WCT9.merkleTweak_lower hl, ClaudeWCT.WCT9.lowerTweak_low,
    ClaudeWCT.WCT9.lowerTweak_high]
  rfl
def levNB (B : LevArgs) : Nat := sumTo (fun j => 2 ^ (B.h - 1 - j)) (B.h - 1)
section lev
variable {image : Image} {b : Nat} (hsub : SharedTreeCode.Code image b) (sk : BitVec 256) {s0 : MachineState}
  {B : LevArgs} {leaves : List Digest} (hpre : LevPre s0 B leaves)
include hsub hpre
theorem lev_node (hl1 : 1 ≤ B.lay) {ℓ : Nat} (hl : ℓ < B.h) {levels : List (List Digest)} {pre : List Digest}
    (hi : pre.length < 2 ^ (B.h - ℓ - 1)) {t : MachineState} (ht : NodeInv s0 B ℓ levels pre t)
    (hpc : t.pc = pcOf (b + 118)) :
    TSim image sk t (45 + revX B.tag) (52 + revX B.tag) 1 1
      (ClaudeWCT.WCT9.lowerNodeHash B.lay B.tree (2 ^ (B.h - (ℓ + 1)) + pre.length)
        ((levels.getD ℓ []).getD (2 * pre.length) 0) ((levels.getD ℓ []).getD (2 * pre.length + 1) 0))
      (fun v u => u.pc = pcOf (b + 118) ∧ NodeInv s0 B ℓ levels (pre ++ [v]) u) := by
  have hh := hpre.hh
  have ha := hpre.ha
  have has := hpre.has
  have ha8 := hpre.ha8
  set lo := 2 ^ (B.h - ℓ - 1) with hlo_def
  set i := pre.length with hi_def
  have hY : 2 ^ (B.h - ℓ) = 2 * lo := two_pow_split hl
  have hYZ : 2 ^ (B.h - ℓ) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hW : 2 ^ (B.h + 1) = 2 * 2 ^ B.h := by rw [Nat.pow_succ]; ring
  have hZ : 2 ^ B.h ≤ 4096 := by
    calc 2 ^ B.h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
      _ = 4096 := by norm_num
  have hlo1 : 1 ≤ lo := Nat.one_le_two_pow
  have hk' : 2 ^ (B.h - (ℓ + 1)) = lo := by rw [hlo_def]; congr 1
  have g : ∀ r, r ∉ levRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have r2 : t.getReg .x2 = BitVec.ofNat 64 B.arena := by rw [g _ (by simp [levRegs]), hpre.x2]
  have r9 : t.getReg .x9 = BitVec.ofNat 64 B.tree := by rw [g _ (by simp [levRegs]), hpre.x9]
  have r5 : t.getReg .x5 = 0 := by rw [g _ (by simp [levRegs]), hpre.x5]
  have r21 : t.getReg .x21 = BitVec.ofNat 64 (nodeLo B.lay B.tree) := by
    rw [g _ (by simp [levRegs]), hpre.x21]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub118_spec hsub t hpc lo (lo + i) (by omega) (by omega) ht.x20 ht.x24
  rw [if_pos (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x10, t2x11, t2x12, t2n0, t2n8, t2n16, t2n24, t2n48, t2n56, t2r, t2f⟩ :=
    sub120_full hsub t1 t1pc B.tag B.lay B.arena (lo + i) B.tree hpre.tag3 hl1 hpre.hlay ha8 (by omega) (by omega)
      hpre.htree
      (by simp only [NODE, NOUT] at has ⊢; omega) (by rw [t1r.get (by simp)]; exact r2)
      (by rw [t1r.get (by simp)]; exact ht.x24) (by rw [t1r.get (by simp)]; exact r9)
      (by rw [t1r.get (by simp)]; exact r21)
  obtain ⟨hlen, hlev⟩ := ht.heap
  obtain ⟨hll, hlv⟩ := hlev ℓ le_rfl
  have hL : DigAt t (B.arena + 32 * (lo + i)) ((levels.getD ℓ []).getD (2 * i) 0) := by
    have := hlv.get (i := 2 * i) (by rw [hll, hY]; omega)
    rwa [hY, show B.arena + 16 * (2 * lo) + 16 * (2 * i) = B.arena + 32 * (lo + i) by ring] at this
  have hR : DigAt t (B.arena + 32 * (lo + i) + 16) ((levels.getD ℓ []).getD (2 * i + 1) 0) := by
    have := hlv.get (i := 2 * i + 1) (by rw [hll, hY]; omega)
    rwa [hY, show B.arena + 16 * (2 * lo) + 16 * (2 * i + 1) = B.arena + 32 * (lo + i) + 16 by ring] at this
  have hL1 := hL.frame t1f (by omega) (by simp) (by simp)
  have hR1 := hR.frame t1f (by omega) (by simp) (by simp)
  have fr : ∀ X, (X = NODE + 32 ∨ X = NODE + 40) → t2.getMem (BitVec.ofNat 64 X) = s0.getMem (BitVec.ofNat 64 X) := by
    intro X hX
    have hX' : X < 2 ^ 64 := by rcases hX with h | h <;> (rw [h]; decide)
    rw [t2f.get hX' (by simp only [NODE] at hX ⊢; omega), t1f.get hX' (by simp),
      ht.frame.get hX' (by unfold LevW; simp only [NODE, NOUT] at hX has ⊢; omega)]
  have hq : hashInput t2 = toQ (pad64 (ClaudeWCT.WCT9.merkleNodeInput B.lay B.tree (lo + i)
      ((levels.getD ℓ []).getD (2 * i) 0) ((levels.getD ℓ []).getD (2 * i + 1) 0))) := by
    rw [pad64_of_aligned _ (by rw [merkleNodeInput_length])]
    refine hashInput_toQ t2 _ 0 NODE (merkleNodeInput_length _ _ _ _ _) t2x10 (by decide) (by decide) t2x11
      (by decide) ?_
    rw [wordsOf_merkleNodeInput (by omega), readWords_eight, t2n0, t2n8, t2n16, t2n24, fr (NODE + 32) (by simp),
      fr (NODE + 40) (by simp), t2n48, t2n56, hpre.z32, hpre.z40, hL1.1, hL1.2, hR1.1, hR1.2]
  have hv : hashArgumentsValid t2 = true :=
    hashArgs_const t2 NODE 64 NOUT t2x10 t2x11 t2x12 (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have h5 : t2.getReg .x5 = 0 := by rw [t2r.get (by simp), t1r.get (by simp), r5]
  have hblk : (toQ (pad64 (ClaudeWCT.WCT9.merkleNodeInput B.lay B.tree (lo + i)
      ((levels.getD ℓ []).getD (2 * i) 0) ((levels.getD ℓ []).getD (2 * i + 1) 0)))).blocks = 1 := by
    rw [pad64_of_aligned _ (by rw [merkleNodeInput_length]),
      blocks_toQ ⟨by rw [merkleNodeInput_length]; omega, by rw [merkleNodeInput_length]⟩, merkleNodeInput_length]
  unfold ClaudeWCT.WCT9.lowerNodeHash
  rw [hk', ClaudeWCT.WCT9.lowerHash_eq]
  refine (TSim.steps (st1.trans st2)
    (TSim.publicHash_bind (k := 16) (c := 16) (n := 0) (b := 0)
      (fetch_sub146 hsub t2 t2pc) h5 hv hq (fun a => ?_))).of_eq rfl ?_ ?_ ?_ ?_
  · have hwf := Frame.writeHash t2 a NOUT t2x12 (by decide)
    obtain ⟨u, st3, upc, ux24, um0, um8, ur, uf⟩ := sub147_spec hsub (writeHash t2 a)
      (by rw [pc_writeHash, t2pc, pcOf_add4]) B.arena (lo + i) ha8 (by omega)
      (by rw [getReg_writeHash, t2r.get (by simp), t1r.get (by simp)]; exact r2)
      (by rw [getReg_writeHash, t2r.get (by simp), t1r.get (by simp)]; exact ht.x24)
    have hlo := DigAt.writeHash_lowerHalf t2 a NOUT B.lay (lo + i) t2x12 (by decide) ⟨hl1, hpre.hlay⟩
    have hnew : DigAt u (B.arena + 16 * (lo + i)) (ClaudeWCT.WCT9.lowerHalf B.lay (lo + i) a) :=
      ⟨um0.trans hlo.1, by rw [um8]; exact hlo.2⟩
    have fall : Frame t u (fun X => (X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨
        X = NODE + 48 ∨ X = NODE + 56) ∨ (NOUT ≤ X ∧ X < NOUT + 32) ∨
        (X = B.arena + 16 * (lo + i) ∨ X = B.arena + 16 * (lo + i) + 8)) :=
      ((t1f.trans t2f).trans (hwf.trans uf)).mono (fun X _ h => by
        rcases h with (h | h) | (h | h)
        · exact h.elim
        · left; exact h
        · right; left; exact h
        · right; right; exact h)
    refine TSim.pure_steps st3 ⟨upc, ⟨?_, ?_, ?_, ?_, ⟨hlen, fun l hl' => ?_⟩, ?_⟩⟩
    · rw [ur.get (by simp), getReg_writeHash, t2r.get (by simp), t1r.get (by simp)]; exact ht.x20
    · rw [ux24, List.length_append, List.length_singleton]; congr 1
    · have hw0 : RegsExcept t2 (writeHash t2 a) [] := fun r _ => getReg_writeHash t2 a r
      exact (ht.regs.trans (((t1r.trans t2r).trans hw0).trans ur)).mono (by decide)
    · refine (ht.frame.trans fall).mono (fun X _ h => ?_)
      unfold LevW at *
      rcases h with h | (h | h | h)
      · exact h
      · rcases h with h | h | h | h | h | h <;> simp_all
      · right; right; right; right; right; right; left; exact h
      · right; right; right; right; right; right; right; simp only [NODE, NOUT] at has; omega
    · obtain ⟨hl1, hl2⟩ := hlev l hl'
      have hYl : 2 * lo ≤ 2 ^ (B.h - l) := by
        rw [← hY]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hYlZ : 2 ^ (B.h - l) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
      refine ⟨hl1, hl2.frame fall (by rw [hl1]; omega) (fun X h1 h2 h => ?_)⟩
      rw [hl1] at h2
      simp only [NODE, NOUT] at h has
      omega
    · refine (ht.cur.frame fall (by omega) (fun X h1 h2 h => ?_)).snoc ?_
      · simp only [NODE, NOUT] at h has
        omega
      · rw [show B.arena + 16 * lo + 16 * i = B.arena + 16 * (lo + i) by ring]; exact hnew
  all_goals (try rw [hblk])
  all_goals (first | rfl | omega)
theorem lev_level (hlay1 : 1 ≤ B.lay) {ℓ : Nat} (hl1 : ℓ + 1 < B.h) {levels : List (List Digest)} {t : MachineState}
    (ht : LevInv s0 B ℓ levels t) (hpc : t.pc = pcOf (b + 116)) :
    TSim image sk t (8 + (if ℓ + 2 = B.h then 0 else 1) + (45 + revX B.tag) * 2 ^ (B.h - 1 - ℓ))
      (8 + (if ℓ + 2 = B.h then 0 else 1) + (52 + revX B.tag) * 2 ^ (B.h - 1 - ℓ))
      (2 ^ (B.h - 1 - ℓ))
      (2 ^ (B.h - 1 - ℓ))
      (do let nodes ← ClaudeWCT.WCT9.lowerLevel B.lay B.tree B.h (1 + ℓ) (levels.getD (1 + ℓ - 1) [])
          pure (levels ++ [nodes]))
      (fun levels' u => u.pc = (if ℓ + 2 = B.h then pcOf (b + 159) else pcOf (b + 116)) ∧
        LevInv s0 B (ℓ + 1) levels' u) := by
  have hl : ℓ < B.h := by omega
  have hh := hpre.hh
  set lo := 2 ^ (B.h - ℓ - 1) with hlo_def
  have hY : 2 ^ (B.h - ℓ) = 2 * lo := two_pow_split hl
  have hlo1 : 1 ≤ lo := Nat.one_le_two_pow
  have hloZ : lo ≤ 2048 := by
    calc lo ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2048 := by norm_num
  have hx20 : 2 ^ B.h / 2 ^ (ℓ + 1) = lo := by
    rw [hlo_def, show B.h = (ℓ + 1) + (B.h - ℓ - 1) by omega, Nat.pow_add, Nat.mul_div_cancel_left _
      (by positivity)]
    congr 1; omega
  have hx20' : 2 ^ B.h / 2 ^ (ℓ + 1 + 1) = lo / 2 := by
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hx20]
  have hl1 : 2 ^ (B.h - 1 - ℓ) = lo := by rw [hlo_def]; congr 1; omega
  have r20 : t.getReg .x20 = BitVec.ofNat 64 lo := by rw [ht.x20, hx20]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub116_spec hsub t hpc lo (by omega) r20
  rw [if_neg (by omega)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x24, t2r, t2f⟩ := sub117_spec hsub t1 t1pc
  have f02 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun X _ h => by simp_all)
  have h0 : NodeInv s0 B ℓ levels [] t2 := by
    refine ⟨?_, ?_, ?_, (ht.frame.trans f02).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim),
      ⟨ht.heap.1, fun l hl' => ⟨(ht.heap.2 l hl').1, (ht.heap.2 l hl').2.frame f02 (by
        rw [(ht.heap.2 l hl').1]
        have := hpre.ha
        have : 2 ^ (B.h - l) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 2 ^ (B.h + 1) = 2 * 2 ^ B.h := by rw [Nat.pow_succ]; ring
        omega) (fun X _ _ h => h.elim)⟩⟩, DigsAt.nil _ _⟩
    · rw [t2r.get (by simp), t1r.get (by simp), r20]
    · rw [t2x24, t1r.get (by simp), r20, List.length_nil, Nat.add_zero]
    · exact (ht.regs.trans (t1r.trans t2r)).mono (by decide)
  have hnodes : (levels.getD (1 + ℓ - 1) []).length / 2 = lo := by
    rw [show 1 + ℓ - 1 = ℓ by omega, (ht.heap.2 ℓ le_rfl).1, hY]; omega
  unfold ClaudeWCT.WCT9.lowerLevel
  rw [hnodes]
  refine (TSim.steps (st1.trans st2) (TSim.bind (k₂ := 6 + (if ℓ + 2 = B.h then 0 else 1))
    (c₂ := 6 + (if ℓ + 2 = B.h then 0 else 1)) (n₂ := 0) (b₂ := 0)
    (TSim.mapM_range lo _ (fun _ => 45 + revX B.tag) (fun _ => 52 + revX B.tag) (fun _ => 1) (fun _ => 1)
      (fun pre w => w.pc = pcOf (b + 118) ∧ NodeInv s0 B ℓ levels pre w)
      (fun pre w hpre' hw => ?_) ⟨t2pc, h0⟩) (fun nodes w hw => ?_))).of_eq rfl ?_ ?_ ?_ ?_
  · rw [show 1 + ℓ - 1 = ℓ by omega, show 1 + ℓ = ℓ + 1 by omega]
    exact lev_node hsub sk hpre hlay1 hl hpre' hw.2 hw.1
  · obtain ⟨hlen, wpc, hw⟩ := hw
    obtain ⟨w1, st3, w1pc, w1r, w1f⟩ := sub118_spec hsub w wpc lo (lo + nodes.length) (by omega) (by omega)
      hw.x20 (by rw [hw.x24])
    rw [if_neg (by omega)] at w1pc
    obtain ⟨w2, st4, w2pc, w2x20, w2r, w2f⟩ := sub157_spec hsub w1 w1pc lo (by omega)
      (by rw [w1r.get (by simp)]; exact hw.x20)
    have hlo2 : lo / 2 = 2 ^ (B.h - ℓ - 2) := by
      rw [hlo_def, show B.h - ℓ - 1 = (B.h - ℓ - 2) + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have hiff : lo / 2 = 1 ↔ ℓ + 2 = B.h := by
      rw [hlo2]
      constructor
      · intro he
        by_contra hne
        have : 2 ≤ 2 ^ (B.h - ℓ - 2) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (B.h - ℓ - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · intro he; rw [show B.h - ℓ - 2 = 0 by omega]; rfl
    have st34 : Steps image w (6 + (if ℓ + 2 = B.h then 0 else 1)) (6 + (if ℓ + 2 = B.h then 0 else 1)) w2 :=
      (st3.trans st4).of_eq (by by_cases hE : ℓ + 2 = B.h <;> simp [hE, hiff]) (by by_cases hE : ℓ + 2 = B.h <;> simp [hE, hiff])
    have p2 : w2.pc = if ℓ + 2 = B.h then pcOf (b + 159) else pcOf (b + 116) := by
      rw [w2pc]; by_cases hE : ℓ + 2 = B.h <;> simp [hE, hiff]
    have f12 : Frame w w2 (fun _ => False) := (w1f.trans w2f).mono (fun X _ h => by simp_all)
    refine TSim.pure_steps st34 ⟨p2, ?_, ?_, ?_, ?_⟩
    · rw [w2x20, hx20']
    · exact (hw.regs.trans (w1r.trans w2r)).mono (by decide)
    · exact (hw.frame.trans f12).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)
    · obtain ⟨hlen0, hlev⟩ := hw.heap
      refine ⟨by simp [hlen0], fun l hl' => ?_⟩
      have hZ : 2 ^ (B.h + 1) = 2 * 2 ^ B.h := by rw [Nat.pow_succ]; ring
      have := hpre.ha
      by_cases hle : l ≤ ℓ
      · have hg : (levels ++ [nodes]).getD l [] = levels.getD l [] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show l < levels.length by omega)]
        rw [hg]
        obtain ⟨h1, h2⟩ := hlev l hle
        have : 2 ^ (B.h - l) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact ⟨h1, h2.frame f12 (by rw [h1]; omega) (fun X _ _ h => h.elim)⟩
      · have hl2 : l = ℓ + 1 := by omega
        subst hl2
        have hg : (levels ++ [nodes]).getD (ℓ + 1) [] = nodes := by
          simp [List.getD_eq_getElem?_getD, hlen0]
        rw [hg, show B.h - (ℓ + 1) = B.h - ℓ - 1 by omega]
        have : lo ≤ 2 ^ B.h := by
          have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show B.h - ℓ - 1 ≤ B.h by omega)
          omega
        exact ⟨hlen, hw.cur.frame f12 (by rw [hlen]; omega) (fun X _ _ h => h.elim)⟩
  all_goals simp only [sumTo_const, hl1]
  all_goals (first | omega | ring)
theorem buildLevelsBelow_tsim (hlay1 : 1 ≤ B.lay) (hh2 : 2 ≤ B.h) (hpc : s0.pc = pcOf (b + 113)) :
    TSim image sk s0 (levKB B) (levCB B) (levNB B) (levNB B)
      (levelsBelowW B.lay B.tree B.h leaves)
      (fun levels t => t.pc = pcOf B.ret ∧ HeapAt t B (B.h - 1) levels ∧ RegsExcept s0 t levRegs ∧
        Frame s0 t (LevW B)) := by
  have hh := hpre.hh
  have hh1 := hpre.hh1
  have ha := hpre.ha
  have hZ : 2 ^ (B.h + 1) = 2 * 2 ^ B.h := by rw [Nat.pow_succ]; ring
  obtain ⟨t1, st1, t1pc, t1x20, t1r, t1f⟩ := sub113_spec hsub s0 hpc B.h hh1 (by omega) hpre.x15
  have h0 : LevInv s0 B 0 [leaves] t1 := by
    refine ⟨?_, t1r.mono (by decide), t1f.mono (fun X _ h => h.elim), ⟨rfl, fun l hl => ?_⟩⟩
    · rw [t1x20]; congr 1
      rw [show B.h = 1 + (B.h - 1) by omega, Nat.pow_add, Nat.mul_div_cancel_left _ (by norm_num)]
      congr 1; omega
    · have hl0 : l = 0 := by omega
      subst hl0
      simp only [List.getD_cons_zero, Nat.sub_zero]
      exact ⟨hpre.hlen, hpre.hleaves.frame t1f (by rw [hpre.hlen]; omega) (fun X _ _ h => h.elim)⟩
  unfold levelsBelowW
  refine (TSim.steps st1 (TSim.bind (k₂ := 1) (c₂ := 1) (n₂ := 0) (b₂ := 0) (f := Pure.pure)
    (TSim.foldlM_range' 1 (B.h - 1) _ [leaves]
      (fun j levels t => t.pc = (if j + 1 = B.h then pcOf (b + 159) else pcOf (b + 116)) ∧ LevInv s0 B j levels t)
      (fun j => 8 + (if j + 2 = B.h then 0 else 1) + (45 + revX B.tag) * 2 ^ (B.h - 1 - j))
      (fun j => 8 + (if j + 2 = B.h then 0 else 1) + (52 + revX B.tag) * 2 ^ (B.h - 1 - j))
      (fun j => 2 ^ (B.h - 1 - j)) (fun j => 2 ^ (B.h - 1 - j))
      (fun j hj levels t ht => (lev_level hsub sk hpre hlay1 (by omega) ht.2
        (by rw [ht.1, if_neg (by omega)])).mono (fun _ _ h => h))
      ⟨by rw [if_neg (by omega)]; exact t1pc, h0⟩)
    (fun levels t ht => ?_))).of_eq (bind_pure _) ?_ ?_ ?_ ?_
  · obtain ⟨tpc, hinv⟩ := ht
    rw [if_pos (by omega)] at tpc
    obtain ⟨u2, st3, u2pc, u2r, u2f⟩ := sub159_spec hsub t tpc B.ret
      (by rw [hinv.regs.get (by simp [levRegs]), hpre.x1])
    refine TSim.pure_steps st3 ⟨u2pc, ⟨hinv.heap.1, fun l hl => ?_⟩,
      (hinv.regs.trans u2r).mono (by decide),
      (hinv.frame.trans u2f).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim)⟩
    obtain ⟨h1, h2⟩ := hinv.heap.2 l hl
    have : 2 ^ (B.h - l) ≤ 2 ^ B.h := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact ⟨h1, h2.frame u2f (by rw [h1]; omega) (fun X _ _ h => h.elim)⟩
  all_goals simp only [levKB, levCB, levNB]
  all_goals omega
end lev
end SigGolfCandidate.T3M.Sign.SharedTree
end
-- ==== merged from T3M_Sign_PackedLowTree ====
section

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
end
