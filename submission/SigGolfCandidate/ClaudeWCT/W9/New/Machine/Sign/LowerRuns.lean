import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.HornRun
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.PackedHelper

/-!
# Stage B (campaign X1): the lower-leaf seed code of the sign image

Lower leaves (`lay ≠ 0`) reach the hook `1055 → 20746` once per chain (`x19 = j`):
* `20746 beq s0` (top layer, unchanged), `20747 beq s3,zero` — chain `j ≥ 1` jumps to `SEED` (`D1`);
* chain 0 runs the coefficient prologue `20749..20767` (`D0`: `p = COEF`, an odd leaf copies the carry
  `SEEDS + 16` to `COEF` and starts at `p = COEF + 16`; `x6` = header word of pair `(17 L + (L & 1)) / 2`), the head
  `CQ0 = 11513` (T8: dead tail of FTS segment (0,2), coordinate-0 code; `C0`: `x17 = 2^32`, `x30 = COEF + 272`) and
  the query loop `CQ` (`CQ`: `PRIV + 16 = x6`, `PRIV + 24 = tree`,
  ecall `64 B @ PRIV → SEEDS`; `CP`: copy `SEEDS[0,32)` to `p`, `p += 32`, `x6 += 2^32`, loop while
  `p < COEF + 272`, else `j SEED`);
* `SEED = 12272` (T8: dead tail of FTS segment (1,0), coordinate-1 code; `SP`): spill `x13..x16` to `COEF + 288`,
  `x6 = j + 1`, `x7 = COEF + 272`, `x10 = x11 = 0`, `jal ra,HK` (T8's Horner loop `hkI = 11220` over 17 coefficients);
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
def par18 : E := .bin .and (.reg .x18) (cE 1)
def hdrBE : E :=
  .bin .or (.bin .or (.bin .sll (.bin .srl (.bin .add (.bin .mul (.reg .x18) (cE 17)) par18) (cE 1)) (cE 32))
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
def expC0 : PRes := pres [(.x17, cE (2 ^ 32)), (.x30, cE (COEF + 272))] [] [] cqI false 4 []
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
  pres [(.x1, cE (0x1000 + 4 * retI)), (.x6, .bin .add (.reg .x19) (cE 1)), (.x7, cE (COEF + 272)), (.x10, cE 0),
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
theorem okLower_true : okLower = true := by decide +kernel
theorem lower_runs :
    runD1 = some expD1 ∧ runD0 true = some (expD0 true) ∧ runD0 false = some (expD0 false) ∧
      runC0 = some expC0 ∧ runCQ = some expCQ ∧ runCP true = some (expCP true) ∧
      runCP false = some (expCP false) ∧ runSP = some expSP ∧ runSR = some expSR := by
  have h := okLower_true
  simp only [okLower, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨optBeq_eq h1, optBeq_eq h2, optBeq_eq h3, optBeq_eq h4, optBeq_eq h5, optBeq_eq h6, optBeq_eq h7,
    optBeq_eq h8, optBeq_eq h9⟩

theorem presKC_getReg (regs : List (Reg × E)) (mem : SymMem) (obl : List Oblig) (pc : Nat) (ec : Bool) (k c : Nat)
    (brs : List Br) (s : MachineState) (x : Reg) :
    ((presKC regs mem obl pc ec k c brs).toState s).getReg x = ((regsOf regs).get x).eval s :=
  SymState.toState_getReg _ _ _ _
theorem presKC_regsExcept (regs : List (Reg × E)) (mem : SymMem) (obl : List Oblig) (pc : Nat) (ec : Bool)
    (k c : Nat) (brs : List Br) (s : MachineState) :
    RegsExcept s ((presKC regs mem obl pc ec k c brs).toState s) (regs.map Prod.fst) := by
  intro x hx
  rw [presKC_getReg, regsOf_get_ne _ _ (fun p hp he => hx (List.mem_map.mpr ⟨p, hp, he⟩)), RegFile.init_get_eval]

theorem eq_br_false (s : MachineState) (x : E) {v : Nat} (hx : x.eval s = BitVec.ofNat 64 v) (hv : v < 2 ^ 64)
    (h0 : v ≠ 0) : Br.holds s ⟨.eq, x, cE 0, false⟩ := by
  show ((x.eval s == BitVec.ofNat 64 0) = false)
  rw [hx, beq_eq_false_iff_ne]
  intro he; exact h0 ((ofNat_inj hv (by norm_num)).mp he)
theorem eq_br_true (s : MachineState) (x : E) (hx : x.eval s = BitVec.ofNat 64 0) :
    Br.holds s ⟨.eq, x, cE 0, true⟩ := by
  show ((x.eval s == BitVec.ofNat 64 0) = true)
  rw [hx]; simp

section steps
variable {im : Image}

theorem step_D1 (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 20746) {lay j : Nat}
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (hlay : lay ≠ 0) (hlay' : lay < 256)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 j) (hj : j ≠ 0) (hj' : j < 2 ^ 32) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf seedI ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (tailLook_ok hcode) lower_runs.1 s hpc (no_obl s) (by
    intro b hb
    simp only [expD1, pres, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact eq_br_false s (.reg .x19) h19 (by omega) hj
    · exact eq_br_false s (.reg .x8) h8 (by omega) hlay)
  exact ⟨_, hst, rfl, pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩

theorem eval_par18 (s : MachineState) {L : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 L) (hL : L < 2 ^ 32) :
    par18.eval s = BitVec.ofNat 64 (L % 2) := by
  show s.getReg .x18 &&& BitVec.ofNat 64 1 = _
  rw [h18]; exact PackedLeaf.and_one_ofNat _ (by omega)

/-- The header word of lower seed pair `pair` (tag 0, index 0) for `tree < 2^32`. -/
def hdrB (lay pair : Nat) : Nat := 1 + 65536 * lay + 2 ^ 32 * pair

theorem eval_hdrBE (s : MachineState) {lay L : Nat} (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (hlay : lay < 256)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 L) (hL : L < 2 ^ 20) :
    hdrBE.eval s = BitVec.ofNat 64 (hdrB lay ((17 * L + L % 2) / 2)) := by
  have hp := eval_par18 s h18 (by omega)
  have hpair : (E.bin .srl (.bin .add (.bin .mul (.reg .x18) (cE 17)) par18) (cE 1)).eval s =
      BitVec.ofNat 64 ((17 * L + L % 2) / 2) := by
    show BinOp.eval .srl (BinOp.eval .add (BinOp.eval .mul (s.getReg .x18) (BitVec.ofNat 64 17)) (par18.eval s))
      (BitVec.ofNat 64 1) = _
    rw [h18, hp, binop_srl _ 1 (by norm_num)]
    simp only [BinOp.eval]
    rw [BitVec.ofNat_mul_ofNat, ofNat_add_ofNat, ofNat_shr _ _ (by omega), pow_one, Nat.mul_comm L 17]
  show BinOp.eval .or (BinOp.eval .or (BinOp.eval .sll
    ((E.bin .srl (.bin .add (.bin .mul (.reg .x18) (cE 17)) par18) (cE 1)).eval s) (BitVec.ofNat 64 32))
    (BinOp.eval .sll (s.getReg .x8) (BitVec.ofNat 64 16))) (BitVec.ofNat 64 1) = _
  rw [hpair, h8, binop_sll _ 32 (by norm_num), binop_sll _ 16 (by norm_num), ofNat_shl, ofNat_shl]
  simp only [BinOp.eval]
  rw [BitVec.or_comm (BitVec.ofNat 64 (((17 * L + L % 2) / 2) * 2 ^ 32)),
    PackedLeaf.hdr_or lay _ hlay (by omega)]
  rfl

/-- The coefficient prologue (chain 0 of a lower leaf). -/
theorem step_D0 (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 20746) {lay L : Nat}
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (hlay : lay ≠ 0) (hlay' : lay < 256)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 L) (hL : L < 2 ^ 20) (h19 : s.getReg .x19 = BitVec.ofNat 64 0) :
    ∃ t k c, Steps im s k c t ∧ c ≤ 24 ∧ t.pc = pcOf cq0I ∧
      t.getReg .x6 = BitVec.ofNat 64 (hdrB lay ((17 * L + L % 2) / 2)) ∧
      t.getReg .x29 = BitVec.ofNat 64 (COEF + 16 * (L % 2)) ∧
      (L % 2 = 1 → ∀ d, DigAt s (0x20040 + 16) d → DigAt t COEF d) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x28, .x29] ∧ Frame s t (fun A => A = COEF ∨ A = COEF + 8) := by
  have hp := eval_par18 s h18 (by omega)
  have hb8 : Br.holds s ⟨.eq, .reg .x8, cE 0, false⟩ := eq_br_false s (.reg .x8) h8 (by omega) hlay
  have hb19 : Br.holds s ⟨.eq, .reg .x19, cE 0, true⟩ := eq_br_true s (.reg .x19) h19
  rcases Nat.mod_two_eq_zero_or_one L with hL2 | hL2
  · obtain ⟨hst, -⟩ := run_sound (tailLook_ok hcode) lower_runs.2.1 s hpc (no_obl s) (by
      intro b hb
      simp only [expD0, if_true, presKC, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact eq_br_true s par18 (by rw [hp, hL2])
      · exact hb19
      · exact hb8)
    refine ⟨_, _, _, hst, by simp [expD0, presKC], rfl, ?_, ?_, fun h => absurd h (by omega),
      (presKC_regsExcept _ _ _ _ _ _ _ _ s).mono (by simp), fun A _ _ => rfl⟩
    · rw [PRes.toState_getReg']; exact eval_hdrBE s h8 hlay' h18 hL
    · rw [PRes.toState_getReg', hL2]; rfl
  · obtain ⟨hst, -⟩ := run_sound (tailLook_ok hcode) lower_runs.2.2.1 s hpc (no_obl s) (by
      intro b hb
      simp only [expD0, Bool.false_eq_true, if_false, presKC, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact eq_br_false s par18 (v := 1) (by rw [hp, hL2]) (by norm_num) (by norm_num)
      · exact hb19
      · exact hb8)
    have hm : ∀ a, ((expD0 false).toState s).getMem a =
        memEval s [mwc (COEF + 8) (ldc (0x20040 + 24)), mwc COEF (ldc (0x20040 + 16))] a := fun a => rfl
    refine ⟨_, _, _, hst, by simp [expD0, presKC], rfl, ?_, ?_, fun _ d hd => ⟨?_, ?_⟩,
      (presKC_regsExcept _ _ _ _ _ _ _ _ s).mono (by simp), frame_of_memEval hm _ (fun p hp => ?_)⟩
    · rw [PRes.toState_getReg']; exact eval_hdrBE s h8 hlay' h18 hL
    · rw [PRes.toState_getReg', hL2]; rfl
    · rw [hm, memEval_mwc_ne _ _ _ (by aoc) (by aoc) (by unfold COEF; omega), memEval_mwc_self _ _ _ _ (by aoc)]
      exact hd.1
    · rw [hm, memEval_mwc_self _ _ _ _ (by aoc)]; exact hd.2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by aoc)] <;> simp

theorem step_C0 (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf cq0I) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf cqI ∧ t.getReg .x17 = BitVec.ofNat 64 (2 ^ 32) ∧
      t.getReg .x30 = BitVec.ofNat 64 (COEF + 272) ∧ RegsExcept s t [.x17, .x30] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode (c := 0) (by norm_num)) lower_runs.2.2.2.1 s hpc (no_obl s)
    (no_br s)
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, pres_regsExcept _ _ _ _ _ _ _ s,
    fun A _ _ => rfl⟩

theorem step_CQ (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf cqI) :
    ∃ t, Steps im s 6 6 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf cqeI ∧
      t.getReg .x10 = BitVec.ofNat 64 0x20000 ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 0x20040 ∧ t.getReg .x28 = BitVec.ofNat 64 0x20000 ∧
      t.getMem (BitVec.ofNat 64 0x20010) = s.getReg .x6 ∧ t.getMem (BitVec.ofNat 64 0x20018) = s.getReg .x9 ∧
      RegsExcept s t [.x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = 0x20018 ∨ A = 0x20010) := by
  obtain ⟨hst, hec⟩ := run_pres (coordLook_ok hcode (c := 0) (by norm_num)) lower_runs.2.2.2.2.1 s hpc (no_obl s)
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

/-- One copy step of the query loop: `SEEDS[0,32)` to `p`, `p += 32`, back to `CQ` or on to `SEED`. -/
theorem step_CP (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf (cqeI + 1)) {P : Nat}
    (h28 : s.getReg .x28 = BitVec.ofNat 64 0x20000) (h29 : s.getReg .x29 = BitVec.ofNat 64 P)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 (COEF + 272)) (hP8 : P % 8 = 0) (hP0 : COEF ≤ P)
    (hP : P + 32 ≤ COEF + 288) :
    ∃ t k, Steps im s k k t ∧ k ≤ 12 ∧ t.pc = pcOf (if P + 32 < COEF + 272 then cqI else seedI) ∧
      t.getReg .x29 = BitVec.ofNat 64 (P + 32) ∧ t.getReg .x6 = s.getReg .x6 + s.getReg .x17 ∧
      (∀ d, DigAt s 0x20040 d → DigAt t P d) ∧ (∀ d, DigAt s (0x20040 + 16) d → DigAt t (P + 16) d) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => P ≤ A ∧ A < P + 32) := by
  unfold COEF at *
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
      decide (P + 32 < 329728 + 272) := by
    show BitVec.ult (s.getReg .x29 + BitVec.ofNat 64 32) (s.getReg .x30) = _
    rw [h29, h30, ofNat_add_ofNat, ofNat_ult (by omega) (by omega)]
  have key : ∀ back : Bool, back = decide (P + 32 < 329728 + 272) → ∃ t k, Steps im s k k t ∧ k ≤ 12 ∧
      t.pc = pcOf (if back then cqI else seedI) ∧ (∀ x, t.getReg x = (((expCP back).st.regs).get x).eval s) ∧
      (∀ a, t.getMem a = memEval s (expCP back).st.mem a) := by
    intro back hback
    have hrun : runCP back = some (expCP back) := by
      cases back
      · exact lower_runs.2.2.2.2.2.2.1
      · exact lower_runs.2.2.2.2.2.1
    have hst := (run_sound (coordLook_ok hcode (c := 0) (by norm_num)) hrun s hpc
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
    cases back_eq : decide (P + 32 < 329728 + 272)
    all_goals
      simp only [expCP, pres]
      rw [regsOf_get_ne _ _ (fun p hp he => hx (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> subst he <;> simp)), RegFile.init_get_eval]
  · intro A hA hn
    rw [hmem A hA, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem step_SP (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf seedI) {j : Nat}
    (h19 : s.getReg .x19 = BitVec.ofNat 64 j) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf hkI ∧ t.getReg .x1 = pcOf retI ∧
      t.getReg .x6 = BitVec.ofNat 64 (j + 1) ∧ t.getReg .x7 = BitVec.ofNat 64 (COEF + 16 * 17) ∧
      t.getReg .x10 = BitVec.ofNat 64 0 ∧ t.getReg .x11 = BitVec.ofNat 64 0 ∧ t.getReg .x28 = BitVec.ofNat 64 COEF ∧
      t.getMem (BitVec.ofNat 64 (COEF + 288)) = s.getReg .x13 ∧
      t.getMem (BitVec.ofNat 64 (COEF + 296)) = s.getReg .x14 ∧
      t.getMem (BitVec.ofNat 64 (COEF + 304)) = s.getReg .x15 ∧
      t.getMem (BitVec.ofNat 64 (COEF + 312)) = s.getReg .x16 ∧
      RegsExcept s t [.x1, .x6, .x7, .x10, .x11, .x28] ∧ Frame s t (fun A => COEF + 288 ≤ A ∧ A < COEF + 320) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode (c := 1) (by norm_num)) lower_runs.2.2.2.2.2.2.2.1 s hpc
    (no_obl s) (no_br s)
  refine ⟨_, hst, rfl, by rw [pres_getReg]; rfl, ?_, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, ?_, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getReg]; show s.getReg .x19 + BitVec.ofNat 64 1 = _; rw [h19, ofNat_add_ofNat]
  · rw [pres_getMem]
    rw [memEval_mwc_ne _ _ _ (by aoc) (by aoc) (by aoc), memEval_mwc_ne _ _ _ (by aoc) (by aoc) (by aoc),
      memEval_mwc_ne _ _ _ (by aoc) (by aoc) (by aoc), memEval_mwc_self _ _ _ _ (by aoc)]; rfl
  · rw [pres_getMem]
    rw [memEval_mwc_ne _ _ _ (by aoc) (by aoc) (by aoc), memEval_mwc_ne _ _ _ (by aoc) (by aoc) (by aoc),
      memEval_mwc_self _ _ _ _ (by aoc)]; rfl
  · rw [pres_getMem]
    rw [memEval_mwc_ne _ _ _ (by aoc) (by aoc) (by aoc), memEval_mwc_self _ _ _ _ (by aoc)]; rfl
  · rw [pres_getMem]
    rw [memEval_mwc_self _ _ _ _ (by aoc)]; rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expSP, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by aoc)] <;> aoc

theorem step_SR (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf retI) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf 1074 ∧ t.getReg .x28 = BitVec.ofNat 64 0 ∧
      t.getReg .x13 = s.getMem (BitVec.ofNat 64 (COEF + 288)) ∧
      t.getReg .x14 = s.getMem (BitVec.ofNat 64 (COEF + 296)) ∧
      t.getReg .x15 = s.getMem (BitVec.ofNat 64 (COEF + 304)) ∧
      t.getReg .x16 = s.getMem (BitVec.ofNat 64 (COEF + 312)) ∧
      (∀ d, DigAt s (CHAINW + 48) d → DigAt t 0x20040 d) ∧
      RegsExcept s t [.x6, .x7, .x13, .x14, .x15, .x16, .x28] ∧
      Frame s t (fun A => A = 0x20048 ∨ A = 0x20040) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode (c := 1) (by norm_num)) lower_runs.2.2.2.2.2.2.2.2 s hpc
    (no_obl s) (no_br s)
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

/-- Cycle bound of one lower seed (SEED, 17 Horner steps, RET). -/
def lowerSeedC : Nat := 11 + (hornStepC * 17 + 5) + 13

theorem familyEval_nil (d : Nat) : familyEval [] d = 0 := rfl

/-- One lower seed: from `SEED` (chain `j`, the 17 coefficients at `COEF`) to `1074` with
`familyEval coefs (j + 1)` at `SEEDS`, `x13..x16` restored. -/
theorem lower_seed {im : Image} (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf seedI) {j : Nat}
    (h19 : s.getReg .x19 = BitVec.ofNat 64 j) (hj : j < 43) {coefs : List Digest} (hlen : coefs.length = 17)
    (hcoef : CoefAtN 17 s coefs) :
    ∃ u k c, Steps im s k c u ∧ c ≤ lowerSeedC ∧ u.pc = pcOf 1074 ∧ u.getReg .x28 = BitVec.ofNat 64 0 ∧
      DigAt u 0x20040 (familyEval coefs (j + 1)) ∧
      RegsExcept s u [.x1, .x6, .x7, .x10, .x11, .x12, .x17, .x28, .x29] ∧
      Frame s u (fun A => (COEF + 288 ≤ A ∧ A < COEF + 320) ∨ A = CHAINW + 48 ∨ A = CHAINW + 56 ∨ A = 0x20048 ∨
        A = 0x20040) := by
  obtain ⟨t, st, tpc, t1, t6, t7, t10, t11, t28, m13, m14, m15, m16, tr, tf⟩ := step_SP hcode s hpc h19
  have hcoef' : CoefAtN 17 t coefs := fun k hk =>
    (hcoef k hk).frame tf (by unfold COEF; omega) (by unfold COEF; omega) (by unfold COEF; omega)
  have hk : HkSt t (j + 1) coefs (16 + 1) t := by
    refine ⟨tpc, t6, by rw [t7], t28, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    rw [t10, t11, List.drop_eq_nil_of_le (by omega), familyEval_nil]
    unfold lim2; simp
  obtain ⟨u, n, c, su, hc, upc, ud, ur, uf⟩ := horner_loop hcode (N := 17) (by norm_num) (by omega) hlen hcoef'
    16 (by norm_num) t hk
  rw [t1, show pcOf retI &&& BitVec.ofNat 64 (2 ^ 64 - 2) = pcOf retI from pcOf_and_max retI] at upc
  obtain ⟨v, sv, vpc, v28, v13, v14, v15, v16, vd, vr, vf⟩ := step_SR hcode u upc
  have mu : ∀ A, COEF + 288 ≤ A → A < COEF + 320 → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A h1 h2 => uf.get (by aoc) (by aoc)
  have g : ∀ r, r ∉ [Reg.x1, .x6, .x7, .x10, .x11, .x28] → r ∉ hornRegs → r ∉ [Reg.x6, .x7, .x13, .x14, .x15, .x16, .x28] →
      v.getReg r = s.getReg r := fun r h1 h2 h3 => by rw [vr.get h3, ur.get h2, tr.get h1]
  refine ⟨v, 11 + (n + 13), 11 + (c + 13), st.trans (su.trans sv), by unfold lowerSeedC; omega, vpc, v28,
    vd _ ud, fun r hr => ?_, ?_⟩
  · by_cases h13 : r = .x13
    · subst h13; rw [v13, mu _ (by omega) (by omega), m13]
    by_cases h14 : r = .x14
    · subst h14; rw [v14, mu _ (by omega) (by omega), m14]
    by_cases h15 : r = .x15
    · subst h15; rw [v15, mu _ (by omega) (by omega), m15]
    by_cases h16 : r = .x16
    · subst h16; rw [v16, mu _ (by omega) (by omega), m16]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact g r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.2.2.1])
      (by simp [hornRegs, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, h13, h14, h15, h16])
      (by simp [hr.2.1, hr.2.2.1, h13, h14, h15, h16, hr.2.2.2.2.2.2.2.1])
  · exact ((tf.trans uf).trans vf).mono (fun A _ h => by
      rcases h with (h | h | h) | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h))))

end ClaudeWCT.W9.Machine.Sign
end
